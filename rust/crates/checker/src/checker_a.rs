// Ported from tsc/internal/checker/checker.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Wave-2 file A: `checker.go` lines 1–8204 (file start through the end of
// the function preceding `isTemplateLiteralContext`). All `func`s in that
// range are ported as `impl Checker` methods or `pub(crate)` free
// functions, in Go declaration order, except the ones already landed in
// `checker_core.rs` (`NewChecker`/`initialize_*`/`get_global_*`/name
// resolver plumbing, lines ~913–1557) and the `type Checker struct`
// itself.
//
// Cross-file calls resolve to sibling wave-2 files (`checker_b.rs`,
// `checker_c.rs`, `checker_d.rs`, `utilities.rs`, `grammarchecks.rs`,
// `jsx.go`→`jsx.rs`, `services.rs`, `relater.rs`, `flow.rs`,
// `inference.rs`, `nodebuilder*.rs`) by snake_case name — unresolved
// symbols are expected until those land.
//
// Conventions follow `checker_core.rs`/`types.rs`:
//   `*Type` → `TypeId`, `*ast.Node` → `NodeId` (`Option<NodeId>` when the
//   Go pointer is nil-able), `*ast.Symbol` → `SymbolId` (`Option<SymbolId>`
//   likewise), `*Signature` → `SignatureId`, `*IndexInfo` → `IndexInfoId`,
//   `*InferenceContext` → `InferenceContextId`, `*TypeMapper` →
//   `TypeMapperId`, `*diagnostics.Message` → `&'static tsc_diagnostics::
//   Message`, `*ast.Diagnostic` → `ast::diagnostic::DiagnosticRef`.

use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, NodeId, SymbolId, SymbolTable};
use tsc_collections::OrderedSet;
use tsc_core::context::Context;
use tsc_core::options_generated::ModuleKind;
use tsc_core::tristate::Tristate;
use tsc_evaluator as evaluator;

use crate::checker_core::{
    CheckMode, Checker, InferenceContextId, InferenceInfo, InferencePriority, WideningKind,
};
use crate::checker_types::{
    DeclarationSpaces, IterationTypeKind, IterationTypes, IterationTypesKey,
    IterationTypesResolver, IterationUse, TypeFacts, UnusedKind,
};
use crate::mapper::TypeMapperId;
use crate::types::{
    ContextFlags, IndexInfoId, NodeCheckFlags, ObjectFlags, SignatureId, SignatureKind, Ternary,
    TypeFlags, TypeId, TypePredicateKind,
};

// ======== PORT helpers (module-private; arena accessors) ========

/// `symbol.Flags` — read via the checker's symbol arena.
#[inline]
fn sym_flags(c: &Checker, s: SymbolId) -> ast::SymbolFlags {
    c.symbol_arena.borrow()[s.index()].flags
}

/// `symbol.Name`.
#[inline]
fn sym_name(c: &Checker, s: SymbolId) -> String {
    c.symbol_arena.borrow()[s.index()].name.clone()
}

/// `symbol.Declarations` (cloned — Go shares the slice).
#[inline]
fn sym_declarations(c: &Checker, s: SymbolId) -> Vec<NodeId> {
    c.symbol_arena.borrow()[s.index()].declarations.clone()
}

/// `symbol.ValueDeclaration`.
#[inline]
fn sym_value_declaration(c: &Checker, s: SymbolId) -> Option<NodeId> {
    c.symbol_arena.borrow()[s.index()].value_declaration
}

/// `symbol.Parent`.
#[inline]
fn sym_parent(c: &Checker, s: SymbolId) -> Option<SymbolId> {
    c.symbol_arena.borrow()[s.index()].parent
}

/// `symbol.ExportSymbol`.
#[inline]
fn sym_export_symbol(c: &Checker, s: SymbolId) -> Option<SymbolId> {
    c.symbol_arena.borrow()[s.index()].export_symbol
}

/// `symbol.Members` (cloned — `SymbolTable` is an ordered map).
#[inline]
fn sym_members(c: &Checker, s: SymbolId) -> SymbolTable {
    c.symbol_arena.borrow()[s.index()].members.clone()
}

/// `symbol.Exports` (cloned).
#[inline]
fn sym_exports(c: &Checker, s: SymbolId) -> SymbolTable {
    c.symbol_arena.borrow()[s.index()].exports.clone()
}

/// `t.flags` — short-lived arena read guard.
#[inline]
fn tflags(c: &Checker, t: TypeId) -> TypeFlags {
    c.types.get_ref(t).flags
}

/// `t.objectFlags`.
#[inline]
fn tobject_flags(c: &Checker, t: TypeId) -> ObjectFlags {
    c.types.get_ref(t).object_flags
}

/// `t.symbol`.
#[inline]
fn tsymbol(c: &Checker, t: TypeId) -> Option<SymbolId> {
    c.types.get_ref(t).symbol
}

/// `c.resolveName(...)` — invoke the binder name-resolver thunk.
#[inline]
fn call_resolve_name(
    c: &mut Checker,
    location: Option<NodeId>,
    name: &str,
    meaning: ast::SymbolFlags,
    name_not_found_message: Option<&'static tsc_diagnostics::Message>,
    is_use: bool,
    exclude_globals: bool,
) -> Option<SymbolId> {
    let f = self_resolve_name(c);
    f(
        c,
        location,
        name,
        meaning,
        name_not_found_message,
        is_use,
        exclude_globals,
    )
}

#[inline]
fn self_resolve_name(c: &Checker) -> Rc<crate::checker_types::NameResolverThunk<'static>> {
    c.resolve_name.clone().expect("Checker::resolve_name")
}

/// `c.resolveNameForSymbolSuggestion(...)`.
#[inline]
fn call_resolve_name_for_suggestion(
    c: &mut Checker,
    location: Option<NodeId>,
    name: &str,
    meaning: ast::SymbolFlags,
    name_not_found_message: Option<&'static tsc_diagnostics::Message>,
    is_use: bool,
    exclude_globals: bool,
) -> Option<SymbolId> {
    let f = c
        .resolve_name_for_symbol_suggestion
        .clone()
        .expect("Checker::resolve_name_for_symbol_suggestion");
    f(
        c,
        location,
        name,
        meaning,
        name_not_found_message,
        is_use,
        exclude_globals,
    )
}

/// `node.Text()` for a node known to be in `nodes`.
#[inline]
fn node_text(nodes: &[ast::Node], node: NodeId) -> String {
    nodes[node].text(nodes).into_owned()
}

// ======== checker.go ~1215 — `GetTypeAliasTypeParameters` ========

impl Checker {
    /// `(c *Checker) GetTypeAliasTypeParameters` (checker.go) — exported API.
    pub fn get_type_alias_type_parameters(&mut self, symbol: SymbolId) -> Vec<TypeId> {
        if !sym_flags(self, symbol).intersects(ast::SymbolFlags::TYPE_ALIAS) {
            panic!("Attempted to fetch type alias parameters for non-type-alias symbol")
        }
        self.get_declared_type_of_symbol(symbol);
        self.type_alias_links.get(symbol).type_parameters.clone()
    }
}

// ======== checker.go ~1558 — name-resolution error reporting ========

impl Checker {
    /// `(c *Checker) checkAndReportErrorForInvalidInitializer` (checker.go).
    pub(crate) fn check_and_report_error_for_invalid_initializer(
        &mut self,
        error_location: Option<NodeId>,
        name: &str,
        property_with_invalid_initializer: NodeId,
        result: Option<SymbolId>,
    ) -> bool {
        if !self.compiler_options.get_emit_standard_class_fields() {
            if error_location.is_some()
                && result.is_none()
                && self.check_and_report_error_for_missing_prefix(error_location, name)
            {
                return true;
            }
            // We have a match, but the reference occurred within a property initializer and the identifier also binds
            // to a local variable in the constructor where the code will be emitted. Note that this is actually allowed
            // with emitStandardClassFields because the scope semantics are different.
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((property_with_invalid_initializer).file_index());
            let prop = nodes[property_with_invalid_initializer].as_property_declaration();
            let message = if error_location.is_some()
                && prop.type_.is_some()
                && nodes[prop.type_.unwrap()]
                    .loc
                    .contains_inclusive(nodes[error_location.unwrap()].pos())
            {
                &tsc_diagnostics::Type_of_instance_member_variable_0_cannot_reference_identifier_1_declared_in_the_constructor
            } else {
                &tsc_diagnostics::Initializer_of_instance_member_variable_0_cannot_reference_identifier_1_declared_in_the_constructor
            };
            let arg0 = tsc_scanner::utilities::declaration_name_to_string(
                prop.named_member_base.name,
                &nodes,
            );
            self.error(error_location, message, &[arg0, name.to_string()]);
            return true;
        }
        false
    }

    /// `(c *Checker) checkAndReportErrorForMissingPrefix` (checker.go).
    pub(crate) fn check_and_report_error_for_missing_prefix(
        &mut self,
        error_location: Option<NodeId>,
        name: &str,
    ) -> bool {
        let Some(error_location) = error_location else {
            return false;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((error_location).file_index());
        if !ast::is_identifier(&nodes[error_location])
            || node_text(&nodes, error_location) != name
            || crate::utilities::is_type_reference_identifier(error_location, &nodes)
            || crate::utilities::is_in_type_query(error_location, &nodes)
        {
            return false;
        }
        let container = self.get_this_container(error_location, false, false);
        let mut location = container;
        while let Some(parent) = nodes[location].parent {
            if ast::is_class_like(Some(parent), &nodes) {
                let Some(class_symbol) = self.get_symbol_of_declaration(parent) else {
                    break;
                };
                // Check to see if a static member exists.
                let constructor_type = self.get_type_of_symbol(class_symbol);
                if self.get_property_of_type(constructor_type, name).is_some() {
                    let arg1 = self.symbol_to_string(class_symbol);
                    self.error(
                        Some(error_location),
                        &tsc_diagnostics::Cannot_find_name_0_Did_you_mean_the_static_member_1_0,
                        &[name.to_string(), arg1],
                    );
                    return true;
                }
                // No static member is present.
                // Check if we're in an instance method and look for a relevant instance member.
                if location == container && !ast::is_static(&nodes[location]) {
                    let class_type = self.get_declared_type_of_symbol(class_symbol);
                    let __arena_instance_type = self.types.clone();
                    let instance_type = __arena_instance_type
                        .get(class_type)
                        .as_interface_type()
                        .and_then(|i| i.this_type)
                        .expect("thisType");
                    // TODO: GH#18217
                    if self.get_property_of_type(instance_type, name).is_some() {
                        self.error(
                            Some(error_location),
                            &tsc_diagnostics::Cannot_find_name_0_Did_you_mean_the_instance_member_this_0,
                            &[name.to_string()],
                        );
                        return true;
                    }
                }
            }
            location = parent;
        }
        false
    }

    /// `(c *Checker) onFailedToResolveSymbol` (checker.go).
    pub(crate) fn on_failed_to_resolve_symbol(
        &mut self,
        error_location: Option<NodeId>,
        name: &str,
        meaning: ast::SymbolFlags,
        name_not_found_message: Option<&'static tsc_diagnostics::Message>,
    ) {
        // The `const` in a `const` assertion (`x as const`) is a syntactic marker, not a real
        // type reference, and must never be resolved or reported as an unresolvable name.
        if let Some(error_location) = error_location {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((error_location).file_index());
            if crate::utilities::is_const_type_reference_name(Some(error_location), &nodes) {
                return;
            }
        }
        let is_jsdoc_link = error_location.is_some_and(|e| {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((e).file_index());
            nodes[e]
                .parent
                .is_some_and(|p| nodes[p].kind == ast::Kind::JSDocLink)
        });
        if error_location.is_some()
            && (is_jsdoc_link
                || self.check_and_report_error_for_missing_prefix(error_location, name)
                || self.check_and_report_error_for_extending_interface(error_location)
                || self.check_and_report_error_for_using_type_as_namespace(
                    error_location,
                    name,
                    meaning,
                )
                || self.check_and_report_error_for_exporting_primitive_type(error_location, name)
                || self.check_and_report_error_for_using_namespace_as_type_or_value(
                    error_location,
                    name,
                    meaning,
                )
                || self.check_and_report_error_for_using_type_as_value(
                    error_location,
                    name,
                    meaning,
                )
                || self.check_and_report_error_for_using_value_as_type(
                    error_location,
                    name,
                    meaning,
                ))
        {
            return;
        }
        let mut declaration_name = name.to_string();
        if let Some(e) = error_location {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((e).file_index());
            if ast::is_identifier(&nodes[e]) && node_text(&nodes, e) == name {
                // use escape sequences from original file
                declaration_name =
                    tsc_scanner::utilities::declaration_name_to_string(Some(e), &nodes);
            }
        }
        // Report missing lib first
        let suggested_lib = self.get_suggested_lib_for_non_existent_name(name);
        if !suggested_lib.is_empty() {
            self.error(
                error_location,
                name_not_found_message.expect("nameNotFoundMessage"),
                &[declaration_name, suggested_lib],
            );
            return;
        }
        // Then spelling suggestions
        let suggestion =
            self.get_suggested_symbol_for_nonexistent_symbol(error_location, name, meaning);
        if let Some(suggestion) = suggestion {
            let is_ambient_global = sym_value_declaration(self, suggestion).is_some_and(|vd| {
                let __program = self.program.clone().expect("program");
                let vd_nodes = __program.nodes((vd).file_index());
                ast::is_ambient_module(&vd_nodes[vd], &vd_nodes)
                    && ast::is_global_scope_augmentation(&vd_nodes[vd])
            });
            if !is_ambient_global {
                let suggestion_name = self.symbol_to_string(suggestion);
                let is_unchecked_js =
                    self.is_unchecked_js_suggestion(error_location, Some(suggestion), false);
                let message = if meaning == ast::SymbolFlags::NAMESPACE {
                    &tsc_diagnostics::Cannot_find_namespace_0_Did_you_mean_1
                } else if is_unchecked_js {
                    &tsc_diagnostics::Could_not_find_name_0_Did_you_mean_1
                } else {
                    &tsc_diagnostics::Cannot_find_name_0_Did_you_mean_1
                };
                let diagnostic = self.new_diagnostic_for_node(
                    error_location,
                    message,
                    &[declaration_name, suggestion_name.clone()],
                );
                if let Some(vd) = sym_value_declaration(self, suggestion) {
                    let related = self.new_diagnostic_for_node(
                        Some(vd),
                        &tsc_diagnostics::X_0_is_declared_here,
                        &[suggestion_name],
                    );
                    ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(related));
                }
                self.add_error_or_suggestion(!is_unchecked_js, &diagnostic);
                return;
            }
        }
        // And then fall back to unspecified "not found"
        self.error(
            error_location,
            name_not_found_message.expect("nameNotFoundMessage"),
            &[declaration_name],
        );
    }

    /// `(c *Checker) checkAndReportErrorForUsingTypeAsNamespace` (checker.go).
    pub(crate) fn check_and_report_error_for_using_type_as_namespace(
        &mut self,
        error_location: Option<NodeId>,
        name: &str,
        meaning: ast::SymbolFlags,
    ) -> bool {
        if meaning == ast::SymbolFlags::NAMESPACE {
            let resolved = call_resolve_name(
                self,
                error_location,
                name,
                ast::SymbolFlags::TYPE.without(ast::SymbolFlags::NAMESPACE),
                None,
                false,
                false,
            );
            if let Some(symbol) = resolved.map(|r| self.resolve_symbol(r)) {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((error_location.unwrap()).file_index());
                let parent = nodes[error_location.unwrap()].parent;
                if let Some(parent) = parent {
                    if ast::is_qualified_name(&nodes[parent]) {
                        let qn = nodes[parent].as_qualified_name();
                        debug_assert!(
                            qn.left == Some(error_location.unwrap()),
                            "Should only be resolving left side of qualified name as a namespace"
                        );
                        let prop_name = node_text(&nodes, qn.right.unwrap());
                        let declared = self.get_declared_type_of_symbol(symbol);
                        let prop_type = self.get_property_of_type(declared, &prop_name);
                        if prop_type.is_some() {
                            self.error(
                                Some(parent),
                                &tsc_diagnostics::Cannot_access_0_1_because_0_is_a_type_but_not_a_namespace_Did_you_mean_to_retrieve_the_type_of_the_property_1_in_0_with_0_1,
                                &[name.to_string(), prop_name],
                            );
                            return true;
                        }
                    }
                }
                self.error(
                    error_location,
                    &tsc_diagnostics::X_0_only_refers_to_a_type_but_is_being_used_as_a_namespace_here,
                    &[name.to_string()],
                );
                return true;
            }
        }
        false
    }

    /// `(c *Checker) checkAndReportErrorForExportingPrimitiveType` (checker.go).
    pub(crate) fn check_and_report_error_for_exporting_primitive_type(
        &mut self,
        error_location: Option<NodeId>,
        name: &str,
    ) -> bool {
        let is_export_specifier = error_location.is_some_and(|e| {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((e).file_index());
            nodes[e]
                .parent
                .is_some_and(|p| nodes[p].kind == ast::Kind::ExportSpecifier)
        });
        if is_primitive_type_name(name) && is_export_specifier {
            self.error(
                error_location,
                &tsc_diagnostics::Cannot_export_0_Only_local_declarations_can_be_exported_from_a_module,
                &[name.to_string()],
            );
            return true;
        }
        false
    }

    /// `(c *Checker) checkAndReportErrorForUsingNamespaceAsTypeOrValue` (checker.go).
    pub(crate) fn check_and_report_error_for_using_namespace_as_type_or_value(
        &mut self,
        error_location: Option<NodeId>,
        name: &str,
        meaning: ast::SymbolFlags,
    ) -> bool {
        if meaning.intersects(ast::SymbolFlags::VALUE.without(ast::SymbolFlags::TYPE)) {
            let resolved = call_resolve_name(
                self,
                error_location,
                name,
                ast::SymbolFlags::NAMESPACE_MODULE,
                None,
                false,
                false,
            );
            if resolved.map(|r| self.resolve_symbol(r)).is_some() {
                // `export = ns` may legitimately reference a namespace; checkExportAssignment decides
                // whether that is an error, so don't report "cannot use namespace as a value" here.
                let is_export_assignment = error_location.is_some_and(|e| {
                    let __program = self.program.clone().expect("program");
                    let nodes = __program.nodes((e).file_index());
                    crate::utilities::is_export_assignment_expression_name(Some(e), &nodes)
                });
                if !is_export_assignment {
                    self.error(
                        error_location,
                        &tsc_diagnostics::Cannot_use_namespace_0_as_a_value,
                        &[name.to_string()],
                    );
                }
                return true;
            }
        } else if meaning.intersects(ast::SymbolFlags::TYPE.without(ast::SymbolFlags::VALUE)) {
            let resolved = call_resolve_name(
                self,
                error_location,
                name,
                ast::SymbolFlags::MODULE,
                None,
                false,
                false,
            );
            if resolved.map(|r| self.resolve_symbol(r)).is_some() {
                self.error(
                    error_location,
                    &tsc_diagnostics::Cannot_use_namespace_0_as_a_type,
                    &[name.to_string()],
                );
                return true;
            }
        }
        false
    }

    /// `(c *Checker) checkAndReportErrorForUsingTypeAsValue` (checker.go).
    pub(crate) fn check_and_report_error_for_using_type_as_value(
        &mut self,
        error_location: Option<NodeId>,
        name: &str,
        meaning: ast::SymbolFlags,
    ) -> bool {
        if meaning.intersects(ast::SymbolFlags::VALUE) {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((error_location.unwrap()).file_index());
            if is_primitive_type_name(name) {
                let grandparent = nodes[error_location.unwrap()]
                    .parent
                    .and_then(|p| nodes[p].parent);
                let is_heritage = grandparent.is_some_and(|gp| {
                    nodes[gp].parent.is_some() && ast::is_heritage_clause(&nodes[gp])
                });
                if is_heritage {
                    let grandparent = grandparent.unwrap();
                    let heritage_kind = nodes[grandparent].as_heritage_clause().token;
                    let container_kind = nodes[nodes[grandparent].parent.unwrap()].kind;
                    if container_kind == ast::Kind::InterfaceDeclaration
                        && heritage_kind == ast::Kind::ExtendsKeyword
                    {
                        self.error(
                            error_location,
                            &tsc_diagnostics::An_interface_cannot_extend_a_primitive_type_like_0_It_can_only_extend_other_named_object_types,
                            &[name.to_string()],
                        );
                    } else if ast::is_class_like(nodes[grandparent].parent, &nodes)
                        && heritage_kind == ast::Kind::ExtendsKeyword
                    {
                        self.error(
                            error_location,
                            &tsc_diagnostics::A_class_cannot_extend_a_primitive_type_like_0_Classes_can_only_extend_constructable_values,
                            &[name.to_string()],
                        );
                    } else if ast::is_class_like(nodes[grandparent].parent, &nodes)
                        && heritage_kind == ast::Kind::ImplementsKeyword
                    {
                        self.error(
                            error_location,
                            &tsc_diagnostics::A_class_cannot_implement_a_primitive_type_like_0_It_can_only_implement_other_named_object_types,
                            &[name.to_string()],
                        );
                    }
                } else {
                    self.error(
                        error_location,
                        &tsc_diagnostics::X_0_only_refers_to_a_type_but_is_being_used_as_a_value_here,
                        &[name.to_string()],
                    );
                }
                return true;
            }
            let resolved = call_resolve_name(
                self,
                error_location,
                name,
                ast::SymbolFlags::TYPE.without(ast::SymbolFlags::VALUE),
                None,
                false,
                false,
            );
            if let Some(symbol) = resolved.map(|r| self.resolve_symbol(r)) {
                let all_flags = self.get_symbol_flags(symbol);
                if !all_flags.intersects(ast::SymbolFlags::VALUE) {
                    // `export = SomeType` may legitimately reference a type-only name; checkExportAssignment
                    // decides whether that is an error, so don't report "used as a value" here.
                    if crate::utilities::is_export_assignment_expression_name(
                        error_location,
                        &nodes,
                    ) {
                        return true;
                    }
                    if is_es2015_or_later_constructor_name(name) {
                        self.error(
                            error_location,
                            &tsc_diagnostics::X_0_only_refers_to_a_type_but_is_being_used_as_a_value_here_Do_you_need_to_change_your_target_library_Try_changing_the_lib_compiler_option_to_es2015_or_later,
                            &[name.to_string()],
                        );
                    } else if self.maybe_mapped_type(error_location.unwrap(), symbol) {
                        self.error(
                            error_location,
                            &tsc_diagnostics::X_0_only_refers_to_a_type_but_is_being_used_as_a_value_here_Did_you_mean_to_use_1_in_0,
                            &[name.to_string(), tsc_core::core::if_else(name == "K", "P", "K").to_string()],
                        );
                    } else {
                        self.error(
                            error_location,
                            &tsc_diagnostics::X_0_only_refers_to_a_type_but_is_being_used_as_a_value_here,
                            &[name.to_string()],
                        );
                    }
                    return true;
                }
            }
        }
        false
    }

    /// `(c *Checker) maybeMappedType` (checker.go).
    pub(crate) fn maybe_mapped_type(&mut self, node: NodeId, symbol: SymbolId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut node = node;
        loop {
            match nodes[node].parent {
                Some(p) => node = p,
                None => break,
            }
            if !(ast::is_computed_property_name(&nodes[node])
                || ast::is_property_signature_declaration(&nodes[node]))
            {
                break;
            }
        }
        if ast::is_type_literal_node(&nodes[node])
            && nodes[node].members().map_or(0, |m| m.len()) == 1
        {
            let t = self.get_declared_type_of_symbol(symbol);
            return tflags(self, t).intersects(TypeFlags::UNION)
                && self.all_types_assignable_to_kind_ex(
                    t,
                    TypeFlags::STRING_OR_NUMBER_LITERAL,
                    true,
                );
        }
        false
    }

    /// `(c *Checker) checkAndReportErrorForUsingValueAsType` (checker.go).
    pub(crate) fn check_and_report_error_for_using_value_as_type(
        &mut self,
        error_location: Option<NodeId>,
        name: &str,
        meaning: ast::SymbolFlags,
    ) -> bool {
        if meaning.intersects(ast::SymbolFlags::TYPE.without(ast::SymbolFlags::NAMESPACE)) {
            let resolved = call_resolve_name(
                self,
                error_location,
                name,
                !ast::SymbolFlags::TYPE & ast::SymbolFlags::VALUE,
                None,
                false,
                false,
            );
            if let Some(symbol) = resolved.map(|r| self.resolve_symbol(r)) {
                if !sym_flags(self, symbol).intersects(ast::SymbolFlags::NAMESPACE) {
                    self.error(
                        error_location,
                        &tsc_diagnostics::X_0_refers_to_a_value_but_is_being_used_as_a_type_here_Did_you_mean_typeof_0,
                        &[name.to_string()],
                    );
                    return true;
                }
            }
        }
        false
    }

    /// `(c *Checker) getSuggestedLibForNonExistentName` (checker.go).
    pub(crate) fn get_suggested_lib_for_non_existent_name(&mut self, name: &str) -> String {
        let feature_map = crate::utilities::get_feature_map();
        if let Some(type_features) = feature_map.get(name) {
            return type_features[0].lib.clone();
        }
        String::new()
    }

    /// `(c *Checker) getSuggestedSymbolForNonexistentSymbol` (checker.go).
    pub(crate) fn get_suggested_symbol_for_nonexistent_symbol(
        &mut self,
        location: Option<NodeId>,
        outer_name: &str,
        meaning: ast::SymbolFlags,
    ) -> Option<SymbolId> {
        call_resolve_name_for_suggestion(self, location, outer_name, meaning, None, false, false)
    }

    /// `(c *Checker) getSuggestionForSymbolNameLookup` (checker.go).
    pub(crate) fn get_suggestion_for_symbol_name_lookup(
        &mut self,
        symbols: &SymbolTable,
        name: &str,
        meaning: ast::SymbolFlags,
    ) -> Option<SymbolId> {
        if let Some(symbol) = self.get_symbol(symbols, name, meaning) {
            return Some(symbol);
        }
        let mut candidates: Vec<SymbolId> = symbols.values().copied().collect();
        if meaning.intersects(ast::SymbolFlags::GLOBAL_LOOKUP) {
            candidates.extend(get_primitive_type_alias_suggestions(self, symbols));
        }
        self.get_spelling_suggestion_for_name(name, candidates, meaning)
    }

    /// `(c *Checker) getSpellingSuggestionForName` (checker.go).
    ///
    /// PORT: `iter.Seq[*ast.Symbol]` materializes to a `Vec<SymbolId>` — the
    /// candidate names need `&mut Checker` (`try_resolve_alias`), so they are
    /// computed eagerly before `get_spelling_suggestion` runs.
    pub(crate) fn get_spelling_suggestion_for_name(
        &mut self,
        name: &str,
        symbols: Vec<SymbolId>,
        meaning: ast::SymbolFlags,
    ) -> Option<SymbolId> {
        // getCandidateName in Go: names not matching `meaning` are filtered
        // to "" (skipped by the suggestion walk).
        let mut candidates: Vec<(SymbolId, String, SymbolId)> = Vec::with_capacity(symbols.len());
        for candidate in symbols {
            let mut candidate_name = String::new();
            let raw_name = self.symbol_display_name(candidate);
            let flags = sym_flags(self, candidate);
            if !raw_name.is_empty() && !raw_name.starts_with('"') && !raw_name.starts_with('\u{FFFD}')
            {
                if flags.intersects(meaning) {
                    candidate_name = raw_name;
                } else if flags.intersects(ast::SymbolFlags::ALIAS) {
                    if let Some(alias) = self.try_resolve_alias(candidate) {
                        if sym_flags(self, alias).intersects(meaning) {
                            candidate_name = raw_name;
                        }
                    }
                }
            }
            let merged = self.get_merged_symbol(candidate);
            candidates.push((candidate, candidate_name, merged));
        }
        let c: &Checker = self;
        tsc_core::core::get_spelling_suggestion(
            name,
            candidates.iter(),
            |cand| cand.1.as_str(),
            |a, b| c.compare_symbols_worker(Some(a.2), Some(b.2)),
        )
        .map(|cand| cand.0)
    }

    /// `(c *Checker) onSuccessfullyResolvedSymbol` (checker.go).
    pub(crate) fn on_successfully_resolved_symbol(
        &mut self,
        error_location: Option<NodeId>,
        result: SymbolId,
        meaning: ast::SymbolFlags,
        last_location: Option<NodeId>,
        associated_declaration_for_containing_initializer_or_binding_name: Option<NodeId>,
        within_deferred_context: bool,
    ) {
        let name = sym_name(self, result);
        let is_in_external_module = last_location.is_some_and(|ll| {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((ll).file_index());
            ast::is_source_file(&nodes[ll])
                && ast::is_external_or_commonjs_module(nodes[ll].as_source_file())
        });
        // Only check for block-scoped variable if we have an error location and are looking for the
        // name with variable meaning
        //      For example,
        //          declare module foo {
        //              interface bar {}
        //          }
        //      const foo/*1*/: foo/*2*/.bar;
        // The foo at /*1*/ and /*2*/ will share same symbol with two meanings:
        // block-scoped variable and namespace module. However, only when we
        // try to resolve name in /*1*/ which is used in variable position,
        // we want to check for block-scoped
        if error_location.is_some()
            && (meaning.intersects(ast::SymbolFlags::BLOCK_SCOPED_VARIABLE)
                || (meaning.intersects(ast::SymbolFlags::CLASS | ast::SymbolFlags::ENUM)
                    && meaning.contains(ast::SymbolFlags::VALUE)))
        {
            let export_or_local_symbol =
                self.get_export_symbol_of_value_symbol_if_exported(Some(result));
            if export_or_local_symbol.is_some_and(|s| {
                sym_flags(self, s).intersects(
                    ast::SymbolFlags::BLOCK_SCOPED_VARIABLE
                        | ast::SymbolFlags::CLASS
                        | ast::SymbolFlags::ENUM,
                )
            }) {
                self.check_resolved_block_scoped_variable(
                    export_or_local_symbol.unwrap(),
                    error_location.unwrap(),
                );
            }
        }
        // If we're in an external module, we can't reference value symbols created from UMD export declarations
        let error_location_flags_jsdoc = error_location.is_some_and(|e| {
            self.program_nodes(e)[e]
                .flags
                .intersects(ast::NodeFlags::JSDOC)
        });
        if is_in_external_module
            && meaning.contains(ast::SymbolFlags::VALUE)
            && !error_location_flags_jsdoc
        {
            let merged = self.get_merged_symbol(result);
            let merged_declarations = sym_declarations(self, merged);
            if !merged_declarations.is_empty()
                && tsc_core::core::every(&merged_declarations, |d| {
                    let __program = self.program.clone().expect("program");
                    let nodes = __program.nodes((*d).file_index());
                    ast::is_namespace_export_declaration(&nodes[*d])
                        || (ast::is_source_file(&nodes[*d])
                            && !nodes[*d].as_source_file().global_exports.is_empty())
                })
            {
                self.error_or_suggestion(
                    self.compiler_options.allow_umd_global_access != Tristate::True,
                    error_location,
                    &tsc_diagnostics::X_0_refers_to_a_UMD_global_but_the_current_file_is_a_module_Consider_adding_an_import_instead,
                    &[name.clone()],
                );
            }
        }
        // If we're in a parameter initializer or binding name, we can't reference the values of the parameter whose initializer we're within or parameters to the right
        if associated_declaration_for_containing_initializer_or_binding_name.is_some()
            && !within_deferred_context
            && meaning.contains(ast::SymbolFlags::VALUE)
        {
            let associated_declaration =
                associated_declaration_for_containing_initializer_or_binding_name.unwrap();
            let late_bound = self.get_late_bound_symbol(result);
            let candidate = self.get_merged_symbol(late_bound);
            let __program = self.program.clone().expect("program");
            let assoc_nodes = __program.nodes((associated_declaration).file_index());
            let root = ast::get_root_declaration(associated_declaration, &assoc_nodes);
            // A parameter initializer or binding pattern initializer within a parameter cannot refer to itself
            if Some(candidate) == self.get_symbol_of_declaration(associated_declaration) {
                let arg0 = tsc_scanner::utilities::declaration_name_to_string(
                    assoc_nodes[associated_declaration].name(),
                    &assoc_nodes,
                );
                self.error(
                    error_location,
                    &tsc_diagnostics::Parameter_0_cannot_reference_itself,
                    &[arg0],
                );
            } else {
                let root_parent = assoc_nodes[root].parent;
                let root_parent_locals = root_parent.and_then(|rp| {
                    let __program = self.program.clone().expect("program");
                    let rp_nodes = __program.nodes((rp).file_index());
                    // PORT: `Locals()` returns a shared table; clone to end the arena borrow.
                    rp_nodes[rp].locals().cloned()
                });
                let is_later_sibling = sym_value_declaration(self, candidate).is_some_and(|vd| {
                    let __program = self.program.clone().expect("program");
                    let vd_nodes = __program.nodes((vd).file_index());
                    let __program = self.program.clone().expect("program");
                    let ad_nodes = __program.nodes((associated_declaration).file_index());
                    vd_nodes[vd].pos() > ad_nodes[associated_declaration].pos()
                });
                let candidate_matches_local = root_parent_locals.is_some_and(|locals| {
                    let candidate_name = sym_name(self, candidate);
                    self.get_symbol(&locals, &candidate_name, meaning) == Some(candidate)
                });
                if is_later_sibling && candidate_matches_local {
                    let arg0 = tsc_scanner::utilities::declaration_name_to_string(
                        assoc_nodes[associated_declaration].name(),
                        &assoc_nodes,
                    );
                    let arg1 = tsc_scanner::utilities::declaration_name_to_string(
                        error_location,
                        &assoc_nodes,
                    );
                    self.error(
                        error_location,
                        &tsc_diagnostics::Parameter_0_cannot_reference_identifier_1_declared_after_it,
                        &[arg0, arg1],
                    );
                }
            }
        }
        let is_valid_type_only_use = error_location.is_some_and(|e| {
            let __program = self.program.clone().expect("program");
            let en = __program.nodes((e).file_index());
            ast::is_valid_type_only_alias_use_site(e, &en)
        });
        if error_location.is_some()
            && meaning.intersects(ast::SymbolFlags::VALUE)
            && sym_flags(self, result).intersects(ast::SymbolFlags::ALIAS)
            && !sym_flags(self, result).intersects(ast::SymbolFlags::VALUE)
            && !is_valid_type_only_use
        {
            let type_only_declaration =
                self.get_type_only_alias_declaration_ex(result, ast::SymbolFlags::VALUE);
            if let Some(type_only_declaration) = type_only_declaration {
                let __program = self.program.clone().expect("program");
                let tdn = __program.nodes((type_only_declaration).file_index());
                let message = if ast::node_kind_is(
                    &tdn[type_only_declaration],
                    &[
                        ast::Kind::ExportSpecifier,
                        ast::Kind::ExportDeclaration,
                        ast::Kind::NamespaceExport,
                    ],
                ) {
                    &tsc_diagnostics::X_0_cannot_be_used_as_a_value_because_it_was_exported_using_export_type
                } else {
                    &tsc_diagnostics::X_0_cannot_be_used_as_a_value_because_it_was_imported_using_import_type
                };
                let diagnostic = self.error(error_location, message, &[name.clone()]);
                if let Some(diagnostic) = diagnostic {
                    self.add_type_only_declaration_related_info(
                        diagnostic,
                        Some(type_only_declaration),
                        &name,
                    );
                }
            }
        }
        // Look at 'compilerOptions.isolatedModules' and not 'getIsolatedModules(...)' (which considers 'verbatimModuleSyntax')
        // here because 'verbatimModuleSyntax' will already have an error for importing a type without 'import type'.
        if self.compiler_options.isolated_modules == Tristate::True
            && is_in_external_module
            && meaning.contains(ast::SymbolFlags::VALUE)
        {
            let globals = self.globals.borrow().clone();
            let is_global = self.get_symbol(&globals, &name, meaning) == Some(result);
            let mut non_value_symbol = None;
            if is_global
                && last_location.is_some_and(|ll| {
                    let __program = self.program.clone().expect("program");
                    let nodes = __program.nodes((ll).file_index());
                    ast::is_source_file(&nodes[ll])
                })
            {
                let ll = last_location.unwrap();
                let __program = self.program.clone().expect("program");
                let ll_nodes = __program.nodes((ll).file_index());
                if let Some(locals) = ll_nodes[ll].locals().cloned() {
                    non_value_symbol = self.get_symbol(&locals, &name, !ast::SymbolFlags::VALUE);
                }
            }
            if let Some(non_value_symbol) = non_value_symbol {
                let decls = sym_declarations(self, non_value_symbol);
                let import_decl = tsc_core::core::find(&decls, |d| {
                    let __program = self.program.clone().expect("program");
                    let nodes = __program.nodes((*d).file_index());
                    ast::node_kind_is(
                        &nodes[*d],
                        &[
                            ast::Kind::ImportSpecifier,
                            ast::Kind::ImportClause,
                            ast::Kind::NamespaceImport,
                            ast::Kind::ImportEqualsDeclaration,
                        ],
                    )
                });
                if let Some(import_decl) = import_decl {
                    let __program = self.program.clone().expect("program");
                    let idn = __program.nodes((import_decl).file_index());
                    if !ast::is_type_only_import_declaration(import_decl, &idn) {
                        self.error(
                            Some(import_decl),
                            &tsc_diagnostics::Import_0_conflicts_with_global_value_used_in_this_file_so_must_be_declared_with_a_type_only_import_when_isolatedModules_is_enabled,
                            &[name.clone()],
                        );
                    }
                }
            }
        }
    }
}

// ======== checker.go ~1681–1752 — free helpers ========

/// `isPrimitiveTypeName` (checker.go).
pub(crate) fn is_primitive_type_name(s: &str) -> bool {
    s == "any" || s == "string" || s == "number" || s == "boolean" || s == "never" || s == "unknown"
}

/// `isES2015OrLaterConstructorName` (checker.go).
pub(crate) fn is_es2015_or_later_constructor_name(s: &str) -> bool {
    s == "Promise" || s == "Symbol" || s == "Map" || s == "WeakMap" || s == "Set" || s == "WeakSet"
}

/// `getPrimitiveTypeAliasSuggestions` (checker.go) — the `iter.Seq` becomes a
/// `Vec`; `primitiveTypeAliasSuggestions`' `sync.OnceValue` global holds
/// ad-hoc `*ast.Symbol`s outside any arena, which `SymbolId` cannot model —
/// so the transient alias symbols are minted into this checker's
/// `symbol_arena` on each call (they're throwaway suggestion candidates —
/// Go regenerates the same shape via `sync.OnceValue`).
pub(crate) fn get_primitive_type_alias_suggestions(
    c: &mut Checker,
    symbols: &SymbolTable,
) -> Vec<SymbolId> {
    const PAIRS: [(&str, &str); 6] = [
        ("string", "String"),
        ("number", "Number"),
        ("boolean", "Boolean"),
        ("object", "Object"),
        ("bigint", "BigInt"),
        ("symbol", "Symbol"),
    ];
    let mut result = Vec::new();
    for (primitive, builtin) in PAIRS {
        if symbols.has(builtin) {
            result.push(c.new_symbol(ast::SymbolFlags::TYPE_ALIAS, primitive));
        }
    }
    result
}

// ======== checker.go ~1932 — block-scoped use-before-declaration ========

impl Checker {
    /// `(c *Checker) checkResolvedBlockScopedVariable` (checker.go).
    pub(crate) fn check_resolved_block_scoped_variable(
        &mut self,
        result: SymbolId,
        error_location: NodeId,
    ) {
        let result_flags = sym_flags(self, result);
        tsc_debug::assert_!(
            result_flags.intersects(ast::SymbolFlags::BLOCK_SCOPED_VARIABLE)
                || result_flags.intersects(ast::SymbolFlags::CLASS)
                || result_flags.intersects(ast::SymbolFlags::ENUM)
        );
        if result_flags.intersects(
            ast::SymbolFlags::FUNCTION
                | ast::SymbolFlags::FUNCTION_SCOPED_VARIABLE
                | ast::SymbolFlags::ASSIGNMENT,
        ) && result_flags.intersects(ast::SymbolFlags::CLASS)
        {
            // constructor functions aren't block scoped
            return;
        }
        // Block-scoped variables cannot be used before their definition
        let declarations = sym_declarations(self, result);
        let declaration = tsc_core::core::find(&declarations, |d| {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((*d).file_index());
            ast::is_block_or_catch_scoped(*d, &nodes)
                || ast::is_class_like(Some(*d), &nodes)
                || ast::is_enum_declaration(&nodes[*d])
        });
        let Some(declaration) = declaration else {
            panic!("checkResolvedBlockScopedVariable could not find block-scoped declaration")
        };
        let __program = self.program.clone().expect("program");
        let declaration_nodes = __program.nodes((declaration).file_index());
        if !declaration_nodes[declaration]
            .flags
            .intersects(ast::NodeFlags::AMBIENT)
            && !self.is_block_scoped_name_declared_before_use(declaration, error_location)
        {
            let mut diagnostic = None;
            let declaration_name = tsc_scanner::utilities::declaration_name_to_string(
                ast::get_name_of_declaration(Some(declaration), &declaration_nodes),
                &declaration_nodes,
            );
            if result_flags.intersects(ast::SymbolFlags::BLOCK_SCOPED_VARIABLE) {
                diagnostic = self.error(
                    Some(error_location),
                    &tsc_diagnostics::Block_scoped_variable_0_used_before_its_declaration,
                    &[declaration_name.clone()],
                );
            } else if result_flags.intersects(ast::SymbolFlags::CLASS) {
                diagnostic = self.error(
                    Some(error_location),
                    &tsc_diagnostics::Class_0_used_before_its_declaration,
                    &[declaration_name.clone()],
                );
            } else if result_flags.intersects(ast::SymbolFlags::REGULAR_ENUM) {
                diagnostic = self.error(
                    Some(error_location),
                    &tsc_diagnostics::Enum_0_used_before_its_declaration,
                    &[declaration_name.clone()],
                );
            } else {
                tsc_debug::assert_!(result_flags.intersects(ast::SymbolFlags::CONST_ENUM));
                if self.compiler_options.get_isolated_modules() {
                    diagnostic = self.error(
                        Some(error_location),
                        &tsc_diagnostics::Enum_0_used_before_its_declaration,
                        &[declaration_name.clone()],
                    );
                }
            }
            if let Some(diagnostic) = diagnostic {
                let related = self.new_diagnostic_for_node(
                    Some(declaration),
                    &tsc_diagnostics::X_0_is_declared_here,
                    &[declaration_name],
                );
                ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(related));
            }
        }
    }

    /// `(c *Checker) isBlockScopedNameDeclaredBeforeUse` (checker.go).
    pub(crate) fn is_block_scoped_name_declared_before_use(
        &mut self,
        declaration: NodeId,
        usage: NodeId,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let declaration_nodes = __program.nodes((declaration).file_index());
        let __program = self.program.clone().expect("program");
        let usage_nodes = __program.nodes((usage).file_index());
        let declaration_file = ast::get_source_file_of_node(Some(declaration), &declaration_nodes);
        let use_file = ast::get_source_file_of_node(Some(usage), &usage_nodes);
        let decl_container =
            ast::get_enclosing_block_scope_container(declaration, &declaration_nodes);
        if declaration_file != use_file {
            // nodes are in different files and order cannot be determined
            return true;
        }
        // deferred usage in a type context is always OK regardless of the usage position:
        if usage_nodes[usage].flags.intersects(ast::NodeFlags::JSDOC)
            || crate::utilities::is_in_type_query(usage, &usage_nodes)
            || self.is_in_ambient_or_type_node(usage)
        {
            return true;
        }
        let is_property_no_initializer =
            ast::is_property_declaration(&declaration_nodes[declaration])
                && crate::utilities::is_this_property(usage_nodes[usage].parent, &usage_nodes)
                && declaration_nodes[declaration].initializer().is_none()
                && !crate::utilities::is_exclamation_token(
                    declaration_nodes[declaration].postfix_token(),
                    &declaration_nodes,
                );
        if declaration_nodes[declaration].pos() <= usage_nodes[usage].pos()
            && !is_property_no_initializer
        {
            // declaration is before usage
            match declaration_nodes[declaration].kind {
                ast::Kind::BindingElement => {
                    // still might be illegal if declaration and usage are both binding elements (eg var [a = b, b = b] = [1, 2])
                    let error_binding_element = ast::find_ancestor_kind(
                        Some(usage),
                        ast::Kind::BindingElement,
                        &usage_nodes,
                    );
                    if let Some(error_binding_element) = error_binding_element {
                        return ast::find_ancestor(
                            Some(error_binding_element),
                            &usage_nodes,
                            &mut |n, _| ast::is_binding_element(n),
                        ) != ast::find_ancestor(
                            Some(declaration),
                            &declaration_nodes,
                            &mut |n, _| ast::is_binding_element(n),
                        ) || declaration_nodes[declaration].pos()
                            < usage_nodes[error_binding_element].pos();
                    }
                    // or it might be illegal if usage happens before parent variable is declared (eg var [a] = a)
                    return self.is_block_scoped_name_declared_before_use(
                        ast::find_ancestor_kind(
                            Some(declaration),
                            ast::Kind::VariableDeclaration,
                            &declaration_nodes,
                        )
                        .expect("variable declaration"),
                        usage,
                    );
                }
                ast::Kind::VariableDeclaration => {
                    // still might be illegal if usage is in the initializer of the variable declaration (eg var a = a)
                    return !is_immediately_used_in_initializer_of_block_scoped_variable(
                        declaration,
                        usage,
                        decl_container,
                        &declaration_nodes,
                    );
                }
                _ if ast::is_class_like(Some(declaration), &declaration_nodes) => {
                    // still might be illegal if the usage is within a computed property name in the class (eg class A { static p = "a"; [A.p]() {} })
                    // or when used within a decorator in the class (e.g. `@dec(A.x) class A { static x = "x" }`),
                    // except when used in a function that is not an IIFE (e.g., `@dec(() => A.x) class A { ... }`)
                    let mut container = Some(usage);
                    while container.is_some() && container != Some(declaration) {
                        let cn = container.unwrap();
                        let cn_parent = usage_nodes[cn].parent;
                        let cn_grandparent = cn_parent.and_then(|p| usage_nodes[p].parent);
                        let is_computed = ast::is_computed_property_name(&usage_nodes[cn])
                            && cn_grandparent == Some(declaration);
                        let is_decorator_hit = !self.legacy_decorators
                            && ast::is_decorator(&usage_nodes[cn])
                            && (cn_parent == Some(declaration)
                                || (cn_parent
                                    .is_some_and(|p| ast::is_method_declaration(&usage_nodes[p]))
                                    && cn_grandparent == Some(declaration))
                                || (cn_parent.is_some_and(|p| ast::is_accessor(&usage_nodes[p]))
                                    && cn_grandparent == Some(declaration))
                                || (cn_parent.is_some_and(|p| {
                                    ast::is_property_declaration(&usage_nodes[p])
                                }) && cn_grandparent == Some(declaration))
                                || (cn_parent.is_some_and(|p| {
                                    ast::is_parameter_declaration(&usage_nodes[p])
                                }) && cn_grandparent.and_then(|gp| usage_nodes[gp].parent)
                                    == Some(declaration)));
                        if is_computed || is_decorator_hit {
                            break;
                        }
                        container = cn_parent;
                    }
                    if container.is_none() || container == Some(declaration) {
                        return true;
                    }
                    let container = container.unwrap();
                    if !self.legacy_decorators && ast::is_decorator(&usage_nodes[container]) {
                        let mut n = Some(usage);
                        while n.is_some() && n != Some(container) {
                            if ast::is_function_like(n, &usage_nodes)
                                && ast::get_immediately_invoked_function_expression(
                                    n.unwrap(),
                                    &usage_nodes,
                                )
                                .is_none()
                            {
                                break;
                            }
                            n = usage_nodes[n.unwrap()].parent;
                        }
                        return n.is_some() && n != Some(container);
                    }
                    return false;
                }
                _ if ast::is_property_declaration(&declaration_nodes[declaration]) => {
                    // still might be illegal if a self-referencing property initializer (eg private x = this.x)
                    return !is_property_immediately_referenced_within_declaration(
                        declaration,
                        usage,
                        false,
                        &declaration_nodes,
                    );
                }
                _ => {
                    // `ast.IsParameterPropertyDeclaration(declaration, declaration.Parent)`
                    if declaration_nodes[declaration].parent.is_some_and(|p| {
                        ast::is_parameter_property_declaration(
                            &declaration_nodes[declaration],
                            &declaration_nodes[p],
                        )
                    }) {
                        // foo = this.bar is illegal in emitStandardClassFields when bar is a parameter property
                        let same_class = ast::get_containing_class(declaration, &declaration_nodes)
                            == ast::get_containing_class(usage, &usage_nodes);
                        return !(self.emit_standard_class_fields
                            && same_class
                            && self.is_used_in_function_or_instance_property(
                                usage,
                                declaration,
                                decl_container,
                            ));
                    }
                }
            }
            return true;
        }
        // declaration is after usage, but it can still be legal if usage is deferred:
        // 1. inside an export specifier
        // 2. inside a function
        // 3. inside an instance property initializer, a reference to a non-instance property
        //    (except when emitStandardClassFields: true and the reference is to a parameter property)
        // 4. inside a static property initializer, a reference to a static method in the same class
        // 5. inside a TS export= declaration (since we will move the export statement during emit to avoid TDZ)
        let usage_parent = usage_nodes[usage].parent;
        if usage_parent.is_some_and(|p| ast::is_export_specifier(&usage_nodes[p]))
            || (usage_parent.is_some_and(|p| ast::is_export_assignment(&usage_nodes[p]))
                && usage_nodes[usage_parent.unwrap()]
                    .as_export_assignment()
                    .is_export_equals)
        {
            // export specifiers do not use the variable, they only make it available for use
            return true;
        }
        // When resolving symbols for exports, the `usage` location passed in can be the export site directly
        if ast::is_export_assignment(&usage_nodes[usage])
            && usage_nodes[usage].as_export_assignment().is_export_equals
        {
            return true;
        }
        if self.is_used_in_function_or_instance_property(usage, declaration, decl_container) {
            if self.emit_standard_class_fields
                && ast::get_containing_class(declaration, &declaration_nodes).is_some()
                && (ast::is_property_declaration(&declaration_nodes[declaration])
                    || declaration_nodes[declaration].parent.is_some_and(|p| {
                        ast::is_parameter_property_declaration(
                            &declaration_nodes[declaration],
                            &declaration_nodes[p],
                        )
                    }))
            {
                return !is_property_immediately_referenced_within_declaration(
                    declaration,
                    usage,
                    true,
                    &declaration_nodes,
                );
            }
            return true;
        }
        false
    }

    /// `(c *Checker) isUsedInFunctionOrInstanceProperty` (checker.go).
    pub(crate) fn is_used_in_function_or_instance_property(
        &mut self,
        usage: NodeId,
        declaration: NodeId,
        decl_container: Option<NodeId>,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((usage).file_index());
        let callback = |c: &mut Checker, current: &ast::Node, nodes: &[ast::Node]| {
            let current_id = current.id;
            if Some(current_id) == decl_container {
                return ast::FindAncestorResult::Quit;
            }
            if ast::is_function_like(Some(current_id), nodes) {
                return ast::to_find_ancestor_result(
                    ast::get_immediately_invoked_function_expression(current_id, nodes).is_none(),
                );
            }
            if ast::is_class_static_block_declaration(current) {
                return ast::to_find_ancestor_result(nodes[declaration].pos() < nodes[usage].pos());
            }

            if let Some(parent) = current.parent {
                if ast::is_property_declaration(&nodes[parent]) {
                    let property_declaration = parent;
                    let initializer_of_property =
                        nodes[property_declaration].initializer() == Some(current_id);
                    if initializer_of_property {
                        if ast::is_static(&nodes[parent]) {
                            if ast::is_method_declaration(&nodes[declaration]) {
                                return ast::FindAncestorResult::True;
                            }
                            if ast::is_property_declaration(&nodes[declaration])
                                && ast::get_containing_class(usage, nodes)
                                    == ast::get_containing_class(declaration, nodes)
                            {
                                let prop_name = nodes[declaration].name();
                                if prop_name.is_some_and(|pn| {
                                    ast::is_identifier(&nodes[pn])
                                        || ast::is_private_identifier(&nodes[pn])
                                }) {
                                    let sym =
                                        c.get_symbol_of_declaration(declaration).expect("symbol");
                                    let t = c.get_type_of_symbol(sym);
                                    let static_blocks: Vec<NodeId> = nodes
                                        [nodes[declaration].parent.unwrap()]
                                    .members()
                                    .unwrap_or(&[])
                                    .iter()
                                    .copied()
                                    .filter(|&m| ast::is_class_static_block_declaration(&nodes[m]))
                                    .collect();
                                    if c.is_property_initialized_in_static_blocks(
                                        prop_name.unwrap(),
                                        t,
                                        &static_blocks,
                                        nodes[nodes[declaration].parent.unwrap()].pos(),
                                        current.pos(),
                                    ) {
                                        return ast::FindAncestorResult::True;
                                    }
                                }
                            }
                        } else {
                            let is_declaration_instance_property =
                                ast::is_property_declaration(&nodes[declaration])
                                    && !ast::is_static(&nodes[declaration]);
                            if !is_declaration_instance_property
                                || ast::get_containing_class(usage, nodes)
                                    != ast::get_containing_class(declaration, nodes)
                            {
                                return ast::FindAncestorResult::True;
                            }
                        }
                    }
                }

                if ast::is_decorator(&nodes[parent]) {
                    let decorator = nodes[parent].as_decorator();
                    if decorator.expression == Some(current_id) {
                        if let Some(dp) = nodes[parent].parent {
                            if ast::is_parameter_declaration(&nodes[dp]) {
                                let dppp = nodes[dp].parent.and_then(|pp| nodes[pp].parent);
                                if dppp.is_some_and(|dppp| {
                                    c.is_used_in_function_or_instance_property(
                                        dppp,
                                        declaration,
                                        decl_container,
                                    )
                                }) {
                                    return ast::FindAncestorResult::True;
                                }
                                return ast::FindAncestorResult::Quit;
                            }
                            if ast::is_method_declaration(&nodes[dp]) {
                                if let Some(dpp) = nodes[dp].parent {
                                    if c.is_used_in_function_or_instance_property(
                                        dpp,
                                        declaration,
                                        decl_container,
                                    ) {
                                        return ast::FindAncestorResult::True;
                                    }
                                }
                                return ast::FindAncestorResult::Quit;
                            }
                        }
                    }
                }
            }

            ast::FindAncestorResult::False
        };
        // `ast.FindAncestorOrQuit(usage, callback) != nil` — run the walk;
        // the callback may recurse into `self` so it receives `&mut Checker`.
        let found = {
            let mut cb = |current: &ast::Node, nodes: &[ast::Node]| -> ast::FindAncestorResult {
                callback(self, current, nodes)
            };
            ast::find_ancestor_or_quit(Some(usage), &nodes, &mut cb)
        };
        found.is_some()
    }
}

/// `isImmediatelyUsedInInitializerOfBlockScopedVariable` (checker.go) —
/// free fn; takes the arena explicitly like `ast::*` helpers.
pub(crate) fn is_immediately_used_in_initializer_of_block_scoped_variable(
    declaration: NodeId,
    usage: NodeId,
    decl_container: Option<NodeId>,
    nodes: &[ast::Node],
) -> bool {
    match nodes[declaration]
        .parent
        .and_then(|p| nodes[p].parent)
        .map(|gp| nodes[gp].kind)
    {
        Some(
            ast::Kind::VariableStatement | ast::Kind::ForStatement | ast::Kind::ForOfStatement,
        ) => {
            // variable statement/for/for-of statement case,
            // use site should not be inside variable declaration (initializer of declaration or binding element)
            if is_same_scope_descendent_of(usage, Some(declaration), decl_container, nodes) {
                return true;
            }
        }
        _ => {}
    }
    // ForIn/ForOf case - use site should not be used in expression part
    let grandparent = nodes[declaration].parent.and_then(|p| nodes[p].parent);
    grandparent.is_some_and(|gp| ast::is_for_in_or_of_statement(Some(gp), nodes))
        && is_same_scope_descendent_of(
            usage,
            grandparent.and_then(|gp| nodes[gp].expression()),
            decl_container,
            nodes,
        )
}

/// `isSameScopeDescendentOf` (checker.go).
///
/// Starting from 'initial' node walk up the parent chain until 'stopAt' node is reached.
/// If at any point current node is equal to 'parent' node - return true.
/// If current node is an IIFE, continue walking up.
/// Return false if 'stopAt' node is reached or isFunctionLike(current) === true.
pub(crate) fn is_same_scope_descendent_of(
    initial: NodeId,
    parent: Option<NodeId>,
    stop_at: Option<NodeId>,
    nodes: &[ast::Node],
) -> bool {
    if parent.is_none() {
        return false;
    }
    let parent = parent.unwrap();
    let mut n = Some(initial);
    while let Some(node) = n {
        if node == parent {
            return true;
        }
        if Some(node) == stop_at
            || (ast::is_function_like(n, nodes)
                && (ast::get_immediately_invoked_function_expression(node, nodes).is_none()
                    || ast::get_function_flags(Some(&nodes[node]))
                        .intersects(ast::FunctionFlags::ASYNC_GENERATOR)))
        {
            return false;
        }
        n = nodes[node].parent;
    }
    false
}

/// `isPropertyImmediatelyReferencedWithinDeclaration` (checker.go) — used
/// for detecting ES-standard class field use-before-def errors.
pub(crate) fn is_property_immediately_referenced_within_declaration(
    declaration: NodeId,
    usage: NodeId,
    stop_at_any_property_declaration: bool,
    nodes: &[ast::Node],
) -> bool {
    // always legal if usage is after declaration
    if nodes[usage].end() > nodes[declaration].end() {
        return false;
    }
    // still might be legal if usage is deferred (e.g. x: any = () => this.x)
    // otherwise illegal if immediately referenced within the declaration (e.g. x: any = this.x)
    let mut node = Some(usage);
    while let Some(n) = node {
        if n == declaration {
            break;
        }
        match nodes[n].kind {
            ast::Kind::ArrowFunction => return false,
            ast::Kind::PropertyDeclaration => {
                // even when stopping at any property declaration, they need to come from the same class
                let decl_parent = nodes[declaration].parent;
                let same_class = (ast::is_property_declaration(&nodes[declaration])
                    && nodes[n].parent == decl_parent)
                    || (decl_parent.is_some_and(|dp| {
                        ast::is_parameter_property_declaration(&nodes[declaration], &nodes[dp])
                    }) && nodes[n].parent == decl_parent.and_then(|dp| nodes[dp].parent));
                return stop_at_any_property_declaration && same_class;
            }
            ast::Kind::Block => {
                if let Some(p) = nodes[n].parent {
                    match nodes[p].kind {
                        ast::Kind::MethodDeclaration
                        | ast::Kind::GetAccessor
                        | ast::Kind::SetAccessor => return false,
                        _ => {}
                    }
                }
            }
            _ => {}
        }
        node = nodes[n].parent;
    }
    true
}

// ======== checker.go ~2177 — type-only alias declarations ========

impl Checker {
    /// `(c *Checker) getTypeOnlyAliasDeclaration` (checker.go) — the type-only
    /// declaration node (if any) for the given alias symbol
    /// (non-transitively).
    pub fn get_type_only_alias_declaration(&mut self, symbol: SymbolId) -> Option<NodeId> {
        if sym_flags(self, symbol).intersects(ast::SymbolFlags::ALIAS) {
            self.resolve_alias(symbol);
            return self.alias_symbol_links.get(symbol).type_only_declaration;
        }
        None
    }

    /// `(c *Checker) getTypeOnlyAliasDeclarationEx` (checker.go) — the first
    /// type-only alias declaration node (if any) in the resolution chain that
    /// affects the symbol for the given meaning.
    pub(crate) fn get_type_only_alias_declaration_ex(
        &mut self,
        symbol: SymbolId,
        meaning: ast::SymbolFlags,
    ) -> Option<NodeId> {
        let mut symbol = symbol;
        while sym_flags(self, symbol).intersects(ast::SymbolFlags::ALIAS)
            && !sym_flags(self, symbol).intersects(meaning)
        {
            let resolved = self.resolve_alias(symbol);
            let type_only = self.alias_symbol_links.get(symbol).type_only_declaration;
            if type_only.is_some() {
                return type_only;
            }
            symbol = resolved;
        }
        None
    }

    /// `(c *Checker) getImmediateAliasedSymbol` (checker.go).
    pub fn get_immediate_aliased_symbol(&mut self, symbol: SymbolId) -> Option<SymbolId> {
        tsc_debug::assert_!(
            sym_flags(self, symbol).intersects(ast::SymbolFlags::ALIAS),
            "Should only get Alias here."
        );
        if self
            .alias_symbol_links
            .get(symbol)
            .immediate_target
            .is_none()
        {
            let node = self.get_declaration_of_alias_symbol(symbol);
            if node.is_none() {
                panic!("Unexpected nil in getImmediateAliasedSymbol")
            }
            let target = self.get_target_of_alias_declaration(node.unwrap());
            self.alias_symbol_links.get(symbol).immediate_target = target;
        }
        self.alias_symbol_links.get(symbol).immediate_target
    }

    /// `(c *Checker) addTypeOnlyDeclarationRelatedInfo` (checker.go).
    pub(crate) fn add_type_only_declaration_related_info(
        &mut self,
        diagnostic: ast::diagnostic::DiagnosticRef,
        type_only_declaration: Option<NodeId>,
        name: &str,
    ) -> ast::diagnostic::DiagnosticRef {
        let Some(type_only_declaration) = type_only_declaration else {
            return diagnostic;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((type_only_declaration).file_index());
        let is_export = ast::is_export_specifier(&nodes[type_only_declaration])
            || ast::is_export_declaration(&nodes[type_only_declaration])
            || ast::is_namespace_export(&nodes[type_only_declaration]);
        let related = self.new_diagnostic_for_node(
            Some(type_only_declaration),
            if is_export {
                &tsc_diagnostics::X_0_was_exported_here
            } else {
                &tsc_diagnostics::X_0_was_imported_here
            },
            &[name.to_string()],
        );
        ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(related));
        diagnostic
    }

    /// `(c *Checker) getSymbol` (checker.go).
    pub(crate) fn get_symbol(
        &mut self,
        symbols: &SymbolTable,
        name: &str,
        meaning: ast::SymbolFlags,
    ) -> Option<SymbolId> {
        if meaning.intersects(ast::SymbolFlags::ALL) {
            let symbol = symbols
                .get(name)
                .copied()
                .map(|s| self.get_merged_symbol(s));
            if let Some(symbol) = symbol {
                if sym_flags(self, symbol).intersects(meaning) {
                    return Some(symbol);
                }
                if sym_flags(self, symbol).intersects(ast::SymbolFlags::ALIAS) {
                    let target_flags = self.get_symbol_flags(symbol);
                    // `target_flags` will be `SymbolFlags::ALL` if an error occurred in alias
                    // resolution; this avoids cascading errors
                    if target_flags.intersects(meaning) {
                        return Some(symbol);
                    }
                }
            }
        }
        // return nil if we can't find a symbol
        None
    }
}

// ======== checker.go ~2240 — source file / element checking ========

/// Drop guard standing in for Go's `defer tr.Push(...)()` — the returned
/// closure runs at scope exit.
struct TraceGuard(Option<Box<dyn FnOnce()>>);

impl Drop for TraceGuard {
    fn drop(&mut self) {
        if let Some(f) = self.0.take() {
            f()
        }
    }
}

impl Checker {
    /// `(c *Checker) checkSourceFile` (checker.go).
    pub(crate) fn check_source_file(
        &mut self,
        ctx: Context,
        source_file: NodeId,
        check_unused: bool,
    ) {
        self.ctx = ctx;
        let __check_t = std::time::Instant::now();
        let __program = self.program.clone().expect("program");
        // PORT(borrowck): descendant checks take `nodes_mut`; hold the arena
        // `Ref` only to extract source-file metadata, then drop it.
        let (is_declaration_file, file_name, statements, is_external_commonjs) = {
            let nodes = __program.nodes((source_file).file_index());
            (
                nodes[source_file].as_source_file().is_declaration_file,
                nodes[source_file].as_source_file().file_name.to_string(),
                nodes[source_file]
                    .as_source_file()
                    .statements
                    .as_ref()
                    .map(|l| l.nodes().to_vec())
                    .unwrap_or_default(),
                ast::is_external_or_commonjs_module(nodes[source_file].as_source_file()),
            )
        };
        if !self.source_file_links.get(source_file).type_checked {
            let _guard = self.tracer.as_ref().map(|tr| {
                let mut args = tsc_tracing::TraceArgs::new();
                args.insert(
                    "path".to_string(),
                    serde_json::Value::from(file_name.clone()),
                );
                TraceGuard(Some(tr.push(
                    tsc_tracing::PHASE_CHECK,
                    "checkSourceFile",
                    &mut args,
                    true,
                )))
            });
            // Grammar checking
            let __gt = std::time::Instant::now();
            self.check_grammar_source_file(source_file);
            let __t_gram = __gt.elapsed();
            self.renamed_binding_elements_in_types = Vec::new();
            let __gt = std::time::Instant::now();
            self.check_source_elements(&statements);
            let __t_elems = __gt.elapsed();
            let __gt = std::time::Instant::now();
            self.check_deferred_nodes(source_file);
            let __t_def = __gt.elapsed();
            if is_external_commonjs {
                self.check_external_module_exports(source_file);
                self.register_for_unused_identifiers_check(source_file);
            }
            if !is_declaration_file && !self.is_canceled() {
                self.check_unused_renamed_binding_elements();
            }
            let __gt = std::time::Instant::now();
            self.produce_deferred_diagnostics();
            let __t_defdiag = __gt.elapsed();
            self.reported_unreachable_nodes.clear();
            self.source_file_links.get(source_file).type_checked = true;
            if std::env::var("TSC_FILE_TIME").is_ok() && __check_t.elapsed().as_millis() > 500 {
                eprintln!(
                    "[phases] {file_name} gram={__t_gram:?} elems={__t_elems:?} defer={__t_def:?} defdiag={__t_defdiag:?}"
                );
            }
        }
        if check_unused && !self.source_file_links.get(source_file).unused_checked {
            // The unused identifiers check relies on a full type check having first been performed
            if !is_declaration_file && !self.is_canceled() {
                let identifier_check_nodes = self
                    .source_file_links
                    .get(source_file)
                    .identifier_check_nodes
                    .clone();
                self.check_unused_identifiers(&identifier_check_nodes);
            }
            self.source_file_links.get(source_file).unused_checked = true;
        }
        if self.is_canceled() {
            self.was_canceled = true;
        }
        self.ctx = Context::default();
        if std::env::var("TSC_FILE_TIME").is_ok() {
            eprintln!("[file-time] {:?} {file_name}", __check_t.elapsed());
        }
    }

    /// `(c *Checker) checkSourceElements` (checker.go).
    pub(crate) fn check_source_elements(&mut self, nodes: &[NodeId]) {
        let __per_kind = std::env::var("TSC_FILE_TIME").is_ok();
        let mut __times: rustc_hash::FxHashMap<ast::Kind, std::time::Duration> =
            Default::default();
        for &node in nodes {
            if self.is_canceled() {
                break;
            }
            if __per_kind {
                let __p = self.program.clone().expect("program");
                let __k = __p.nodes(node.file_index())[node].kind;
                let __t = std::time::Instant::now();
                self.check_source_element(Some(node));
                *__times.entry(__k).or_default() += __t.elapsed();
            } else {
                self.check_source_element(Some(node));
            }
        }
        if __per_kind {
            let mut v: Vec<_> = __times.into_iter().collect();
            v.sort_by_key(|(_, d)| std::cmp::Reverse(*d));
            for (k, d) in v.into_iter().take(12) {
                eprintln!("[kind-time] {k:?} {d:?}");
            }
        }
    }

    /// `(c *Checker) checkSourceElement` (checker.go) — the return value
    /// exists for `ForEachChild` (always `false`: never stop early).
    pub(crate) fn check_source_element(&mut self, node: Option<NodeId>) -> bool {
        if let Some(node) = node {
            let save_current_node = self.current_node;
            let save_within_unreachable_code = self.within_unreachable_code;
            self.current_node = Some(node);
            self.instantiation_count = 0;
            self.check_source_element_worker(node);
            self.current_node = save_current_node;
            self.within_unreachable_code = save_within_unreachable_code;
        }
        false
    }

    /// `(c *Checker) checkSourceElementWorker` (checker.go).
    pub(crate) fn check_source_element_worker(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        // PORT(borrowck): collect jsdoc work + the dispatch `kind`, then drop
        // the arena `Ref` — descendant checks take `nodes_mut` on the same
        // cell, which panics while any shared borrow is live.
        let (jsdoc_work, kind) = {
            let nodes = __program.nodes((node).file_index());
            let jsdoc_work: Vec<(NodeId, Vec<NodeId>)> = ast::eager_js_doc(&nodes, node, None)
                .into_iter()
                .map(|jsdoc| {
                    let tags = nodes[jsdoc]
                        .as_js_doc()
                        .tags
                        .as_ref()
                        .map(|t| t.nodes.iter().copied().collect())
                        .unwrap_or_default();
                    (jsdoc, tags)
                })
                .collect();
            (jsdoc_work, nodes[node].kind)
        };
        for (jsdoc, tags) in jsdoc_work {
            self.check_js_doc_comments(jsdoc);
            for tag in tags {
                self.check_js_doc_comments(tag);
            }
        }

        if !self.within_unreachable_code
            && self.compiler_options.allow_unreachable_code != Tristate::True
        {
            if self.check_source_element_unreachable(node) {
                self.within_unreachable_code = true;
            }
        }

        match kind {
            ast::Kind::TypeParameter => self.check_type_parameter(node),
            ast::Kind::Parameter => self.check_parameter(node),
            ast::Kind::PropertyDeclaration => self.check_property_declaration(node),
            ast::Kind::PropertySignature => self.check_property_signature(node),
            ast::Kind::ConstructorType
            | ast::Kind::FunctionType
            | ast::Kind::CallSignature
            | ast::Kind::ConstructSignature
            | ast::Kind::IndexSignature => self.check_signature_declaration(node),
            ast::Kind::MethodDeclaration | ast::Kind::MethodSignature => {
                self.check_method_declaration(node)
            }
            ast::Kind::ClassStaticBlockDeclaration => {
                self.check_class_static_block_declaration(node)
            }
            ast::Kind::Constructor => self.check_constructor_declaration(node),
            ast::Kind::GetAccessor | ast::Kind::SetAccessor => {
                self.check_accessor_declaration(node)
            }
            ast::Kind::TypeReference => self.check_type_reference_node(node),
            ast::Kind::TypePredicate => self.check_type_predicate(node),
            ast::Kind::TypeQuery => self.check_type_query(node),
            ast::Kind::TypeLiteral => self.check_type_literal(node),
            ast::Kind::ArrayType => self.check_array_type(node),
            ast::Kind::TupleType => self.check_tuple_type(node),
            ast::Kind::UnionType | ast::Kind::IntersectionType => {
                self.check_union_or_intersection_type(node)
            }
            ast::Kind::ParenthesizedType | ast::Kind::OptionalType | ast::Kind::RestType => {
                // PORT(borrowck): collect children, drop the `Ref`, then
                // recurse — child checks may take `nodes_mut`.
                let children: Vec<NodeId> = {
                    let nodes = __program.nodes((node).file_index());
                    let mut v = Vec::new();
                    nodes[node].for_each_child(&nodes, &mut |child| {
                        v.push(child);
                        false
                    });
                    v
                };
                for child in children {
                    self.check_source_element(Some(child));
                }
            }
            ast::Kind::ThisType => self.check_this_type(node),
            ast::Kind::TypeOperator => self.check_type_operator(node),
            ast::Kind::ConditionalType => self.check_conditional_type(node),
            ast::Kind::InferType => self.check_infer_type(node),
            ast::Kind::TemplateLiteralType => self.check_template_literal_type(node),
            ast::Kind::ImportType => self.check_import_type(node),
            ast::Kind::NamedTupleMember => self.check_named_tuple_member(node),
            ast::Kind::IndexedAccessType => self.check_indexed_access_type(node),
            ast::Kind::MappedType => self.check_mapped_type(node),
            ast::Kind::FunctionDeclaration => self.check_function_declaration(node),
            ast::Kind::Block | ast::Kind::ModuleBlock => self.check_block(node),
            ast::Kind::VariableStatement => self.check_variable_statement(node),
            ast::Kind::ExpressionStatement => self.check_expression_statement(node),
            ast::Kind::IfStatement => self.check_if_statement(node),
            ast::Kind::DoStatement => self.check_do_statement(node),
            ast::Kind::WhileStatement => self.check_while_statement(node),
            ast::Kind::ForStatement => self.check_for_statement(node),
            ast::Kind::ForInStatement => self.check_for_in_statement(node),
            ast::Kind::ForOfStatement => self.check_for_of_statement(node),
            ast::Kind::ContinueStatement | ast::Kind::BreakStatement => {
                self.check_break_or_continue_statement(node)
            }
            ast::Kind::ReturnStatement => self.check_return_statement(node),
            ast::Kind::WithStatement => self.check_with_statement(node),
            ast::Kind::SwitchStatement => self.check_switch_statement(node),
            ast::Kind::LabeledStatement => self.check_labeled_statement(node),
            ast::Kind::ThrowStatement => self.check_throw_statement(node),
            ast::Kind::TryStatement => self.check_try_statement(node),
            ast::Kind::VariableDeclaration => self.check_variable_declaration(node),
            ast::Kind::BindingElement => self.check_binding_element(node),
            ast::Kind::ClassDeclaration => self.check_class_declaration(node),
            ast::Kind::InterfaceDeclaration => self.check_interface_declaration(node),
            ast::Kind::TypeAliasDeclaration | ast::Kind::JSTypeAliasDeclaration => {
                self.check_type_alias_declaration(node)
            }
            ast::Kind::EnumDeclaration => self.check_enum_declaration(node),
            ast::Kind::EnumMember => self.check_enum_member(node),
            ast::Kind::ModuleDeclaration => self.check_module_declaration(node),
            ast::Kind::ImportDeclaration | ast::Kind::JSImportDeclaration => {
                self.check_import_declaration(node)
            }
            ast::Kind::ImportEqualsDeclaration => self.check_import_equals_declaration(node),
            ast::Kind::ExportDeclaration => self.check_export_declaration(node),
            ast::Kind::ExportAssignment => self.check_export_assignment(node),
            ast::Kind::EmptyStatement | ast::Kind::DebuggerStatement => {
                self.check_grammar_statement_in_ambient_context(node);
            }
            ast::Kind::MissingDeclaration => self.check_missing_declaration(node),
            ast::Kind::JSDocNonNullableType
            | ast::Kind::JSDocNullableType
            | ast::Kind::JSDocAllType
            | ast::Kind::JSDocTypeLiteral => self.check_js_doc_type(node),
            _ => {}
        }
    }

    /// `(c *Checker) checkSourceElementUnreachable` (checker.go).
    pub(crate) fn check_source_element_unreachable(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !ast::is_potentially_executable_node(&nodes[node], &nodes) {
            return false;
        }

        if self.reported_unreachable_nodes.has(&node) {
            return true;
        }

        if !self.is_source_element_unreachable(node) {
            return false;
        }

        self.reported_unreachable_nodes.add(node);

        let source_file = ast::get_source_file_of_node(Some(node), &nodes);

        let mut start_node = node;
        let mut end_node = node;

        let parent = nodes[node].parent;
        if parent.is_some_and(|p| nodes[p].can_have_statements()) {
            let statements: Vec<NodeId> =
                nodes[parent.unwrap()].statements().unwrap_or(&[]).to_vec();
            if let Some(offset) = statements.iter().position(|&s| s == node) {
                // Scan backwards to find the first unreachable unreported node;
                // this may happen when producing region diagnostics where not all nodes
                // will have been visited.
                // TODO: enable this code once we support region diagnostics again.
                let first = offset;
                // for i := offset - 1; i >= 0; i-- {
                // 	prevNode := statements[i]
                // 	if !ast.IsPotentiallyExecutableNode(prevNode) || c.reportedUnreachableNodes.Has(prevNode) || !c.isSourceElementUnreachable(prevNode) {
                // 		break
                // 	}
                // 	firstUnreachableIndex = i
                // 	c.reportedUnreachableNodes.Add(prevNode)
                // }

                let mut last = offset;
                for i in (offset + 1)..statements.len() {
                    let next_node = statements[i];
                    if !ast::is_potentially_executable_node(&nodes[next_node], &nodes)
                        || !self.is_source_element_unreachable(next_node)
                    {
                        break;
                    }
                    last = i;
                    self.reported_unreachable_nodes.add(next_node);
                }

                start_node = statements[first];
                end_node = statements[last];
            }
        }

        let sf = source_file.map(|sf| nodes[sf].as_source_file());
        let start = tsc_scanner::scanner::get_token_pos_of_node(
            start_node,
            sf.expect("source file"),
            false,
            &nodes,
        );

        let diagnostic = ast::diagnostic::new_diagnostic(
            source_file.map(|sf| ast::diagnostic::DiagnosticFile::from_node(sf, &nodes)),
            tsc_core::text::TextRange::new(start, nodes[end_node].end()),
            &tsc_diagnostics::Unreachable_code_detected,
            &[] as &[String],
        );
        self.add_error_or_suggestion(
            self.compiler_options.allow_unreachable_code == Tristate::False,
            &diagnostic,
        );

        true
    }

    /// `(c *Checker) isSourceElementUnreachable` (checker.go). Precondition:
    /// `ast.IsPotentiallyExecutableNode` is true.
    pub(crate) fn is_source_element_unreachable(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if nodes[node].flags.intersects(ast::NodeFlags::UNREACHABLE) {
            // The binder has determined that this code is unreachable.
            // Ignore const enums unless preserveConstEnums is set.
            match nodes[node].kind {
                ast::Kind::EnumDeclaration => {
                    return !ast::is_enum_const(node, &nodes)
                        || self.compiler_options.should_preserve_const_enums();
                }
                ast::Kind::ModuleDeclaration => {
                    return ast::is_instantiated_module(
                        node,
                        self.compiler_options.should_preserve_const_enums(),
                        &nodes,
                    );
                }
                _ => return true,
            }
        } else if let Some(flow_node) = nodes[node].flow_node_data().and_then(|d| d.flow_node) {
            // For code the binder doesn't know is unreachable, use control flow / types.
            return !self.is_reachable_flow_node(node, flow_node);
        }
        false
    }

    /// `(c *Checker) checkNodeDeferred` (checker.go).
    ///
    /// Function and class expression bodies are checked after all statements in the enclosing body. This is
    /// to ensure constructs like the following are permitted:
    ///
    /// ```ignore
    /// 	const foo = function () {
    /// 	   const s = foo();
    /// 	   return "hello";
    /// 	}
    /// ```
    ///
    /// Here, performing a full type check of the body of the function expression whilst in the process of
    /// determining the type of foo would cause foo to be given type any because of the recursive reference.
    /// Delaying the type check of the body ensures foo has been assigned a type.
    pub(crate) fn check_node_deferred(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let enclosing_file = ast::get_source_file_of_node(Some(node), &nodes);
        if let Some(enclosing_file) = enclosing_file {
            let links = self.source_file_links.get(enclosing_file);
            if !links.type_checked {
                links.deferred_nodes.add(node);
            }
        }
    }

    /// `(c *Checker) checkDeferredNodes` (checker.go). Go iterates the live
    /// ordered set: a node remains a member while it is being checked, so a
    /// node that re-defers itself during its own deferred check is a no-op,
    /// and nodes deferred *during* the pass are appended and visited once.
    /// The set is cleared afterward.
    pub(crate) fn check_deferred_nodes(&mut self, context: NodeId) {
        let mut index = 0usize;
        while let Some(&node) = self
            .source_file_links
            .get(context)
            .deferred_nodes
            .get_at(index)
        {
            if self.is_canceled() {
                break;
            }
            self.check_deferred_node(node);
            index += 1;
        }
        self.source_file_links.get(context).deferred_nodes = OrderedSet::new();
    }

    /// `(c *Checker) checkDeferredNode` (checker.go).
    pub(crate) fn check_deferred_node(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let _guard = self.tracer.as_ref().map(|tr| {
            let mut args = tsc_tracing::TraceArgs::new();
            args.insert(
                "kind".to_string(),
                serde_json::Value::from(nodes[node].kind_string()),
            );
            args.insert(
                "pos".to_string(),
                serde_json::Value::from(nodes[node].pos()),
            );
            args.insert(
                "end".to_string(),
                serde_json::Value::from(nodes[node].end()),
            );
            let path = ast::get_source_file_of_node(Some(node), &nodes)
                .map(|sf| nodes[sf].as_source_file().file_name.to_string())
                .unwrap_or_default();
            args.insert("path".to_string(), serde_json::Value::from(path));
            TraceGuard(Some(tr.push(
                tsc_tracing::PHASE_CHECK,
                "checkDeferredNode",
                &mut args,
                false,
            )))
        });
        let save_current_node = self.current_node;
        self.current_node = Some(node);
        self.instantiation_count = 0;
        match nodes[node].kind {
            ast::Kind::CallExpression
            | ast::Kind::NewExpression
            | ast::Kind::TaggedTemplateExpression
            | ast::Kind::Decorator
            | ast::Kind::JsxOpeningElement => {
                // These node kinds are deferred checked when overload resolution fails. To save on work,
                // we ensure the arguments are checked just once in a deferred way.
                self.resolve_untyped_call(node);
            }
            ast::Kind::FunctionExpression
            | ast::Kind::ArrowFunction
            | ast::Kind::MethodDeclaration
            | ast::Kind::MethodSignature => {
                self.check_function_expression_or_object_literal_method_deferred(node)
            }
            ast::Kind::GetAccessor | ast::Kind::SetAccessor => {
                self.check_accessor_declaration(node)
            }
            ast::Kind::ClassExpression => self.check_class_expression_deferred(node),
            ast::Kind::TypeParameter => self.check_type_parameter_deferred(node),
            ast::Kind::JsxSelfClosingElement => self.check_jsx_self_closing_element_deferred(node),
            ast::Kind::JsxElement => self.check_jsx_element_deferred(node),
            ast::Kind::TypeAssertionExpression | ast::Kind::AsExpression => {
                self.check_assertion_deferred(node)
            }
            ast::Kind::VoidExpression => {
                if let Some(expr) = nodes[node].expression() {
                    self.check_expression(expr);
                }
            }
            ast::Kind::BinaryExpression => {
                if ast::is_instance_of_expression(&nodes[node], &nodes) {
                    self.resolve_untyped_call(node);
                }
            }
            ast::Kind::ObjectLiteralExpression | ast::Kind::JsxAttributes => {
                self.check_contextual_deprecations(node)
            }
            _ => {}
        }
        self.current_node = save_current_node;
    }

    /// `(c *Checker) checkJSDocComments` (checker.go).
    pub(crate) fn check_js_doc_comments(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let comments: Vec<NodeId> = nodes[node]
            .comments()
            .map(|c| c.to_vec())
            .unwrap_or_default();
        for comment in comments {
            self.check_js_doc_comment(comment);
        }
    }

    /// `(c *Checker) checkJSDocComment` (checker.go).
    ///
    /// This performs minimal checking of JSDoc nodes to ensure that @link references to entities are recorded
    /// for purposes of checking unused identifiers.
    pub(crate) fn check_js_doc_comment(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::JSDocLink | ast::Kind::JSDocLinkCode | ast::Kind::JSDocLinkPlain => {
                let name = nodes[node].name();
                self.resolve_js_doc_member_name(name);
            }
            _ => {}
        }
    }

    /// `(c *Checker) resolveJSDocMemberName` (checker.go).
    pub(crate) fn resolve_js_doc_member_name(&mut self, name: Option<NodeId>) -> Option<SymbolId> {
        if let Some(name) = name {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((name).file_index());
            if ast::is_entity_name(&nodes[name]) {
                let meaning =
                    ast::SymbolFlags::TYPE | ast::SymbolFlags::NAMESPACE | ast::SymbolFlags::VALUE;
                let host_signature = ast::get_host_signature_from_js_doc(name, &nodes);
                if let Some(symbol) =
                    self.resolve_entity_name(Some(name), meaning, true, true, host_signature)
                {
                    return Some(symbol);
                }
                if ast::is_qualified_name(&nodes[name]) {
                    let (left, right) = {
                        let qn = nodes[name].as_qualified_name();
                        (qn.left, qn.right)
                    };
                    if let Some(symbol) = self.resolve_js_doc_member_name(left) {
                        let mut t = None;
                        if sym_flags(self, symbol).intersects(ast::SymbolFlags::VALUE) {
                            let sym_type = self.get_type_of_symbol(symbol);
                            let proto = self.get_property_of_type(sym_type, "prototype");
                            if let Some(proto) = proto {
                                t = Some(self.get_type_of_symbol(proto));
                            }
                        }
                        if t.is_none() {
                            t = Some(self.get_declared_type_of_symbol(symbol));
                        }
                        return self
                            .get_property_of_type(t.unwrap(), &node_text(&nodes, right.unwrap()));
                    }
                }
            }
        }
        None
    }

    /// `(c *Checker) checkJSDocType` (checker.go).
    pub(crate) fn check_js_doc_type(&mut self, node: NodeId) {
        self.check_js_doc_type_is_in_js_file(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        nodes[node].for_each_child(&nodes, &mut |child| self.check_source_element(Some(child)));
    }

    /// `(c *Checker) checkJSDocTypeIsInJsFile` (checker.go).
    pub(crate) fn check_js_doc_type_is_in_js_file(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !ast::is_in_js_file(Some(node), &nodes) {
            if ast::is_js_doc_non_nullable_type(&nodes[node])
                || ast::is_js_doc_nullable_type(&nodes[node])
            {
                let token = if ast::is_js_doc_non_nullable_type(&nodes[node]) {
                    "!"
                } else {
                    "?"
                };
                let node_type = nodes[node].type_().expect("JSDoc nullable type");
                let postfix = nodes[node].pos() == nodes[node_type].pos();
                let message = if postfix {
                    &tsc_diagnostics::X_0_at_the_end_of_a_type_is_not_valid_TypeScript_syntax_Did_you_mean_to_write_1
                } else {
                    &tsc_diagnostics::X_0_at_the_start_of_a_type_is_not_valid_TypeScript_syntax_Did_you_mean_to_write_1
                };
                let mut t = self.get_type_from_type_node(node_type);
                if ast::is_js_doc_nullable_type(&nodes[node])
                    && t != self.never_type
                    && t != self.void_type
                {
                    t = self.get_nullable_type(
                        t,
                        if postfix {
                            TypeFlags::UNDEFINED
                        } else {
                            TypeFlags::NULLABLE
                        },
                    );
                }
                let arg1 = self.type_to_string(t);
                self.grammar_error_on_node(node, message, &[token.to_string(), arg1]);
            } else {
                self.grammar_error_on_node(
                    node,
                    &tsc_diagnostics::JSDoc_types_can_only_be_used_inside_documentation_comments,
                    &[],
                );
            }
        }
    }

    /// `(c *Checker) checkTypeParameter` (checker.go).
    pub(crate) fn check_type_parameter(&mut self, node: NodeId) {
        // Grammar Checking
        self.check_grammar_modifiers(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(expr) = nodes[node].as_type_parameter_declaration().expression {
            self.grammar_error_on_first_token(expr, &tsc_diagnostics::Type_expected, &[]);
        }
        let constraint = nodes[node].as_type_parameter_declaration().constraint;
        let default_type_node = nodes[node].as_type_parameter_declaration().default_type;
        self.check_source_element(constraint);
        self.check_source_element(default_type_node);
        let tp_symbol = self
            .get_symbol_of_declaration(node)
            .expect("type parameter symbol");
        let type_parameter = self.get_declared_type_of_type_parameter(tp_symbol);
        // Resolve base constraint to reveal circularity errors
        self.get_base_constraint_of_type(type_parameter);
        if self.get_resolved_type_parameter_default(type_parameter)
            == Some(self.circular_constraint_type)
        {
            let arg = self.type_to_string(type_parameter);
            self.error(
                default_type_node,
                &tsc_diagnostics::Type_parameter_0_has_a_circular_default,
                &[arg],
            );
        }
        let constraint_type = self.get_constraint_of_type_parameter(type_parameter);
        let default_type = self.get_default_from_type_parameter(type_parameter);
        if constraint_type.is_some() && default_type.is_some() {
            let mapper =
                crate::mapper::new_simple_type_mapper(self, type_parameter, default_type.unwrap());
            let instantiated = self.instantiate_type(constraint_type.unwrap(), Some(mapper));
            let with_this = self.get_type_with_this_argument(instantiated, default_type, false);
            self.check_type_assignable_to(
                default_type.unwrap(),
                with_this,
                default_type_node,
                Some(&tsc_diagnostics::Type_0_does_not_satisfy_the_constraint_1),
            );
        }
        if let Some(name) = nodes[node].name() {
            self.check_type_name_is_reserved(
                name,
                &tsc_diagnostics::Type_parameter_name_cannot_be_0,
            );
        }
        self.check_node_deferred(node);
    }

    /// `(c *Checker) checkTypeParameterDeferred` (checker.go).
    pub(crate) fn check_type_parameter_deferred(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let parent = nodes[node].parent;
        let is_variance_candidate = parent.is_some_and(|p| {
            ast::is_interface_declaration(&nodes[p])
                || ast::is_class_like(Some(p), &nodes)
                || ast::is_type_alias_declaration(&nodes[p])
                || ast::is_js_type_alias_declaration(&nodes[p])
        });
        if is_variance_candidate {
            let tp_symbol = self
                .get_symbol_of_declaration(node)
                .expect("type parameter symbol");
            let type_parameter = self.get_declared_type_of_type_parameter(tp_symbol);
            let modifiers = self.get_type_parameter_modifiers(type_parameter)
                & (ast::ModifierFlags::IN | ast::ModifierFlags::OUT);
            if modifiers != ast::ModifierFlags::NONE {
                let symbol = self.get_symbol_of_declaration(parent.unwrap());
                let is_bad_alias_target = parent.is_some_and(|p| {
                    matches!(
                        nodes[p].kind,
                        ast::Kind::TypeAliasDeclaration | ast::Kind::JSTypeAliasDeclaration
                    )
                }) && !self
                    .types_handle()
                    .get(self.get_declared_type_of_symbol(symbol.expect("symbol")))
                    .object_flags
                    .intersects(ObjectFlags::ANONYMOUS | ObjectFlags::MAPPED);
                if is_bad_alias_target {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Variance_annotations_are_only_supported_in_type_aliases_for_object_function_constructor_and_mapped_types,
                        &[],
                    );
                } else if modifiers == ast::ModifierFlags::IN
                    || modifiers == ast::ModifierFlags::OUT
                {
                    let symbol = symbol.expect("symbol");
                    let declared = self.get_declared_type_of_symbol(symbol);
                    let _guard = self.tracer.as_ref().map(|tr| {
                        let mut args = tsc_tracing::TraceArgs::new();
                        args.insert(
                            "parent".to_string(),
                            serde_json::Value::from(self.types.get_ref(declared).id.0),
                        );
                        args.insert(
                            "id".to_string(),
                            serde_json::Value::from(self.types.get_ref(type_parameter).id.0),
                        );
                        TraceGuard(Some(tr.push(
                            tsc_tracing::PHASE_CHECK_TYPES,
                            "checkTypeParameterDeferred",
                            &mut args,
                            false,
                        )))
                    });
                    let source = self.create_marker_type(
                        Some(symbol),
                        type_parameter,
                        tsc_core::core::if_else(
                            modifiers == ast::ModifierFlags::OUT,
                            self.marker_sub_type_for_check,
                            self.marker_super_type_for_check,
                        ),
                    );
                    let target = self.create_marker_type(
                        Some(symbol),
                        type_parameter,
                        tsc_core::core::if_else(
                            modifiers == ast::ModifierFlags::OUT,
                            self.marker_super_type_for_check,
                            self.marker_sub_type_for_check,
                        ),
                    );
                    let save_variance_type_parameter = type_parameter;
                    self.variance_type_parameter = Some(type_parameter);
                    self.check_type_assignable_to(
                        source,
                        target,
                        Some(node),
                        Some(&tsc_diagnostics::Type_0_is_not_assignable_to_type_1_as_implied_by_variance_annotation),
                    );
                    self.variance_type_parameter = Some(save_variance_type_parameter);
                }
            }
        }
    }

    /// `(c *Checker) shouldCheckErasableSyntax` (checker.go).
    pub(crate) fn should_check_erasable_syntax(&self, node: NodeId) -> bool {
        self.compiler_options.erasable_syntax_only.is_true()
            && !ast::is_in_js_file(Some(node), &self.program_nodes(node))
    }

    /// `(c *Checker) checkParameter` (checker.go).
    pub(crate) fn check_parameter(&mut self, node: NodeId) {
        // Grammar checking
        // It is a SyntaxError if the Identifier "eval" or the Identifier "arguments" occurs as the
        // Identifier in a PropertySetParameterList of a PropertyAssignment that is contained in strict code
        // or if its FunctionBody is strict code(11.1.5).
        self.check_grammar_modifiers(node);
        self.check_variable_like_declaration(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let fn_ = ast::get_containing_function(node, &nodes)
            .expect("checkParameter: containing function");
        let mut param_name = String::new();
        if let Some(name) = nodes[node].name() {
            if ast::is_identifier(&nodes[name]) {
                param_name = node_text(&nodes, name);
            }
        }
        if ast::has_syntactic_modifier(
            &nodes[node],
            ast::ModifierFlags::PARAMETER_PROPERTY_MODIFIER,
        ) {
            if self.should_check_erasable_syntax(node) {
                self.error(
                    Some(node),
                    &tsc_diagnostics::This_syntax_is_not_allowed_when_erasableSyntaxOnly_is_enabled,
                    &[],
                );
            }
            if !(ast::is_constructor_declaration(&nodes[fn_])
                && ast::node_is_present(nodes[fn_].body(), &nodes))
            {
                self.error(
                    Some(node),
                    &tsc_diagnostics::A_parameter_property_is_only_allowed_in_a_constructor_implementation,
                    &[],
                );
            }
            if ast::is_constructor_declaration(&nodes[fn_]) && param_name == "constructor" {
                self.error(
                    nodes[node].name(),
                    &tsc_diagnostics::X_constructor_cannot_be_used_as_a_parameter_property_name,
                    &[],
                );
            }
        }
        if nodes[node].initializer().is_none()
            && crate::utilities::is_optional_declaration(&nodes[node], &nodes)
            && nodes[node]
                .name()
                .is_some_and(|n| ast::is_binding_pattern(&nodes[n]))
            && nodes[fn_].body().is_some()
        {
            self.error(
                Some(node),
                &tsc_diagnostics::A_binding_pattern_parameter_cannot_be_optional_in_an_implementation_signature,
                &[],
            );
        }
        if param_name == "this" || param_name == "new" {
            if nodes[fn_]
                .parameters()
                .unwrap_or(&[])
                .iter()
                .position(|&p| p == node)
                != Some(0)
            {
                self.error(
                    Some(node),
                    &tsc_diagnostics::A_0_parameter_must_be_the_first_parameter,
                    &[param_name.clone()],
                );
            }
            if ast::is_constructor_declaration(&nodes[fn_])
                || ast::is_construct_signature_declaration(&nodes[fn_])
                || ast::is_constructor_type_node(&nodes[fn_])
            {
                self.error(
                    Some(node),
                    &tsc_diagnostics::A_constructor_cannot_have_a_this_parameter,
                    &[],
                );
            }
            if ast::is_arrow_function(&nodes[fn_]) {
                self.error(
                    Some(node),
                    &tsc_diagnostics::An_arrow_function_cannot_have_a_this_parameter,
                    &[],
                );
            }
            if ast::is_accessor(&nodes[fn_]) {
                self.error(
                    Some(node),
                    &tsc_diagnostics::X_get_and_set_accessors_cannot_declare_this_parameters,
                    &[],
                );
            }
        }
        // Only check rest parameter type if it's not a binding pattern. Since binding patterns are
        // not allowed in a rest parameter, we already have an error from checkGrammarParameterList.
        if crate::utilities::has_dot_dot_dot_token(&nodes[node], &nodes)
            && !nodes[node]
                .name()
                .is_some_and(|n| ast::is_binding_pattern(&nodes[n]))
            && !{
                let param_sym = nodes[node].symbol().expect("parameter symbol");
                let sym_t = self.get_type_of_symbol(param_sym);
                let reduced = self.get_reduced_type(sym_t);
                self.is_type_assignable_to(reduced, self.any_readonly_array_type)
            }
        {
            self.error(
                Some(node),
                &tsc_diagnostics::A_rest_parameter_must_be_of_an_array_type,
                &[],
            );
        }
    }

    /// `(c *Checker) checkPropertyDeclaration` (checker.go).
    pub(crate) fn check_property_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Grammar checking
        if !self.check_grammar_modifiers(node) && !self.check_grammar_property(node) {
            if let Some(name) = nodes[node].name() {
                self.check_grammar_computed_property_name(name);
            }
        }
        self.check_variable_like_declaration(node);
        self.set_node_links_for_private_identifier_scope(node);
        // property signatures already report "initializer not allowed in ambient context" elsewhere
        if ast::has_syntactic_modifier(&nodes[node], ast::ModifierFlags::ABSTRACT)
            && ast::is_property_declaration(&nodes[node])
        {
            if nodes[node].initializer().is_some() {
                let arg =
                    tsc_scanner::utilities::declaration_name_to_string(nodes[node].name(), &nodes);
                self.error(
                    Some(node),
                    &tsc_diagnostics::Property_0_cannot_have_an_initializer_because_it_is_marked_abstract,
                    &[arg],
                );
            }
        }
    }

    /// `(c *Checker) checkPropertySignature` (checker.go).
    pub(crate) fn check_property_signature(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if nodes[node]
            .name()
            .is_some_and(|n| ast::is_private_identifier(&nodes[n]))
        {
            self.error(
                Some(node),
                &tsc_diagnostics::Private_identifiers_are_not_allowed_outside_class_bodies,
                &[],
            );
        }
        self.check_property_declaration(node);
    }

    /// `(c *Checker) checkSignatureDeclaration` (checker.go).
    pub(crate) fn check_signature_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        // PORT(borrowck): nearly every callee below can reach `nodes_mut`
        // (type resolution, nested checks, jsdoc lazy-parse). Hold the arena
        // `Ref` only long enough to extract this node's data; Go relies on
        // the shared `*ast.Node` heap instead.
        let (kind, function_flags, type_parameters, parameters, return_type_node, is_index_sig) = {
            let nodes = __program.nodes((node).file_index());
            (
                nodes[node].kind,
                ast::get_function_flags(Some(&nodes[node])),
                nodes[node].type_parameters().unwrap_or(&[]).to_vec(),
                nodes[node].parameters().unwrap_or(&[]).to_vec(),
                nodes[node].type_(),
                ast::is_index_signature_declaration(&nodes[node]),
            )
        };
        // Grammar checking
        match kind {
            ast::Kind::IndexSignature => {
                self.check_grammar_index_signature(node);
            }
            ast::Kind::FunctionType
            | ast::Kind::FunctionDeclaration
            | ast::Kind::ConstructorType
            | ast::Kind::CallSignature
            | ast::Kind::Constructor
            | ast::Kind::ConstructSignature => {
                self.check_grammar_function_like_declaration(node);
            }
            _ => {}
        }
        if !function_flags.intersects(ast::FunctionFlags::INVALID) {
            // Async generators prior to ES2018 require the __await and __asyncGenerator helpers
            if function_flags.contains(ast::FunctionFlags::ASYNC_GENERATOR)
                && self.language_version
                    < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET.async_generators
            {
                self.check_external_emit_helpers(
                    node,
                    crate::types::ExternalEmitHelpers::ASYNC_GENERATOR_INCLUDES,
                );
            }
            if function_flags & ast::FunctionFlags::ASYNC_GENERATOR == ast::FunctionFlags::ASYNC
                && self.language_version
                    < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET.async_functions
            {
                self.check_external_emit_helpers(node, crate::types::ExternalEmitHelpers::AWAITER);
            }
        }
        self.check_type_parameters(&type_parameters);
        // PORT(borrowck): `checkUnmatchedJSDocParameters` only needs `&mut`
        // for lazy JSDoc parsing (`ast::js_doc` may append parsed JSDoc
        // nodes to the arena); Go mutates the shared graph. Run in place
        // when the arena is free; when an ancestor holds a `Ref`, run it
        // against the checker's per-file scratch clone (cloned once per
        // file — see `jsdoc_scratch_arenas`). The only side effect lost is
        // the JSDoc lazy-parse cache, which simply re-parses on demand.
        {
            // NOTE: never in-place — `check_unmatched_js_doc_parameters`
            // calls back into `self` (`contains_arguments_reference`,
            // `get_type_from_type_node`, error emission), which re-borrows
            // `program.nodes` — a held `RefMut` would panic. The per-file
            // scratch (see `jsdoc_scratch_arenas`) is a detached `Vec`, so
            // re-entrant borrows of the live cell stay legal. Diagnostics
            // resolve file/span eagerly against `nodes`, so scratch-minted
            // JSDoc ids are safe here.
            let fi = (node).file_index();
            let arena = __program.nodes_handle(fi);
            if !self.jsdoc_scratch_arenas.contains_key(&fi) {
                self.jsdoc_scratch_arenas
                    .insert(fi, arena.snapshot().to_vec());
            }
            // Take-out/reinsert so the `&mut Vec` doesn't alias `self`.
            let mut nodes = self.jsdoc_scratch_arenas.remove(&fi).unwrap();
            self.check_unmatched_js_doc_parameters(&mut nodes, node);
            self.jsdoc_scratch_arenas.insert(fi, nodes);
        }
        self.check_source_elements(&parameters);
        if return_type_node.is_some() {
            self.check_source_element(return_type_node);
        }
        if self.no_implicit_any && return_type_node.is_none() {
            match kind {
                ast::Kind::ConstructSignature => {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Construct_signature_which_lacks_return_type_annotation_implicitly_has_an_any_return_type,
                        &[],
                    );
                }
                ast::Kind::CallSignature => {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Call_signature_which_lacks_return_type_annotation_implicitly_has_an_any_return_type,
                        &[],
                    );
                }
                _ => {}
            }
        }
        if let Some(return_type_node) = return_type_node {
            if (function_flags & (ast::FunctionFlags::INVALID | ast::FunctionFlags::GENERATOR))
                == ast::FunctionFlags::GENERATOR
            {
                let return_type = self.get_type_from_type_node(return_type_node);
                if return_type == self.void_type {
                    self.error(
                        Some(return_type_node),
                        &tsc_diagnostics::A_generator_cannot_have_a_void_type_annotation,
                        &[],
                    );
                } else {
                    self.check_generator_instantiation_assignability_to_return_type(
                        return_type,
                        function_flags,
                        Some(return_type_node),
                    );
                }
            } else if (function_flags & ast::FunctionFlags::ASYNC_GENERATOR)
                == ast::FunctionFlags::ASYNC
            {
                self.check_async_function_return_type(node, return_type_node);
            }
        }
        if !is_index_sig {
            self.register_for_unused_identifiers_check(node);
        }
    }

    /// `(c *Checker) checkAsyncFunctionReturnType` (checker.go).
    ///
    /// Checks the return type of an async function to ensure it is a compatible
    /// Promise implementation.
    pub(crate) fn check_async_function_return_type(
        &mut self,
        node: NodeId,
        return_type_node: NodeId,
    ) {
        let return_type = self.get_type_from_type_node(return_type_node);
        if crate::utilities::is_error_type(&self.types, return_type) {
            return;
        }
        let global_promise_type = {
            let thunk = self
                .get_global_promise_type_checked
                .clone()
                .expect("getGlobalPromiseTypeChecked");
            thunk(self)
        };
        if global_promise_type != self.empty_generic_type
            && !self.is_reference_to_type(return_type, global_promise_type)
        {
            // The promise type was not a valid type reference to the global promise type, so we
            // report an error and return the unknown type.
            let awaited = self
                .get_awaited_type_no_alias(return_type)
                .unwrap_or(self.void_type);
            let arg = self.type_to_string(awaited);
            self.error(
                Some(return_type_node),
                &tsc_diagnostics::The_return_type_of_an_async_function_or_method_must_be_the_global_Promise_T_type_Did_you_mean_to_write_Promise_0,
                &[arg],
            );
            return;
        }
        self.check_awaited_type(
            return_type,
            false, /*withAlias*/
            Some(node),
            &tsc_diagnostics::The_return_type_of_an_async_function_must_either_be_a_valid_promise_or_must_not_contain_a_callable_then_member,
            &[],
        );
    }

    /// `(c *Checker) checkMethodDeclaration` (checker.go).
    pub(crate) fn check_method_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Grammar checking
        if !self.check_grammar_method(node) {
            if let Some(name) = nodes[node].name() {
                self.check_grammar_computed_property_name(name);
            }
            if ast::is_method_declaration(&nodes[node])
                && nodes[node]
                    .as_method_declaration()
                    .function_like_with_body_base
                    .body_base
                    .asterisk_token
                    .is_some()
                && nodes[node].name().is_some_and(|n| {
                    ast::is_identifier(&nodes[n]) && &*nodes[n].text(&nodes) == "constructor"
                })
            {
                self.error(
                    nodes[node].name(),
                    &tsc_diagnostics::Class_constructor_may_not_be_a_generator,
                    &[],
                );
            }
        }
        // Grammar checking for modifiers is done inside the function checkGrammarFunctionLikeDeclaration
        self.check_function_or_method_declaration(node);
        // method signatures already report "implementation not allowed in ambient context" elsewhere
        if ast::has_syntactic_modifier(&nodes[node], ast::ModifierFlags::ABSTRACT)
            && ast::is_method_declaration(&nodes[node])
            && nodes[node].body().is_some()
        {
            let arg =
                tsc_scanner::utilities::declaration_name_to_string(nodes[node].name(), &nodes);
            self.error(
                Some(node),
                &tsc_diagnostics::Method_0_cannot_have_an_implementation_because_it_is_marked_abstract,
                &[arg],
            );
        }
        // Private named methods are only allowed in class declarations
        if nodes[node]
            .name()
            .is_some_and(|n| ast::is_private_identifier(&nodes[n]))
            && ast::get_containing_class(node, &nodes).is_none()
        {
            self.error(
                Some(node),
                &tsc_diagnostics::Private_identifiers_are_not_allowed_outside_class_bodies,
                &[],
            );
        }
        self.set_node_links_for_private_identifier_scope(node);
    }

    /// `(c *Checker) checkClassStaticBlockDeclaration` (checker.go).
    pub(crate) fn check_class_static_block_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Grammar checking
        self.check_grammar_modifiers(node);
        nodes[node].for_each_child(&nodes, &mut |child| self.check_source_element(Some(child)));
        if nodes[node].locals().is_some_and(|l| !l.is_empty()) {
            self.register_for_unused_identifiers_check(node);
        }
    }

    /// `(c *Checker) checkConstructorDeclaration` (checker.go).
    pub(crate) fn check_constructor_declaration(&mut self, node: NodeId) {
        // Grammar check on signature of constructor and modifier of the constructor is done in checkSignatureDeclaration function.
        self.check_signature_declaration(node);
        // Grammar check for checking only related to constructorDeclaration
        if !self.check_grammar_constructor_type_parameters(node) {
            self.check_grammar_constructor_type_annotation(node);
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_source_element(nodes[node].body());
        let symbol = self.get_symbol_of_declaration(node);
        self.check_function_or_constructor_symbol(symbol);
        // exit early in the case of signature - super checks are not relevant to them
        if ast::node_is_missing(nodes[node].body(), &nodes) {
            return;
        }
        // TS 1.0 spec (April 2014): 8.3.2
        // Constructors of classes with no extends clause may not contain super calls, whereas
        // constructors of derived classes must contain at least one super call somewhere in their function body.
        let containing_class_decl = nodes[node].parent;
        if containing_class_decl.is_none()
            || ast::get_class_extends_heritage_element(
                &nodes[containing_class_decl.unwrap()],
                &nodes,
            )
            .is_none()
        {
            return;
        }
        let containing_class_decl = containing_class_decl.unwrap();
        let class_extends_null = self.class_declaration_extends_null(containing_class_decl);
        let super_call = self.find_first_super_call(nodes[node].body().expect("body"));
        if let Some(super_call) = super_call {
            if class_extends_null {
                self.error(
                    Some(super_call),
                    &tsc_diagnostics::A_constructor_cannot_contain_a_super_call_when_its_class_extends_null,
                    &[],
                );
            }
            // A super call must be root-level in a constructor if both of the following are true:
            // - The containing class is a derived class.
            // - The constructor declares parameter properties
            //   or the containing class declares instance member variables with initializers.
            let super_call_should_be_root_level = !self.emit_standard_class_fields
                && (nodes[containing_class_decl]
                    .members()
                    .unwrap_or(&[])
                    .iter()
                    .any(|&m| {
                        is_instance_property_with_initializer_or_private_identifier_property(
                            &nodes[m], &nodes,
                        )
                    })
                    || nodes[node].parameters().unwrap_or(&[]).iter().any(|&p| {
                        ast::has_syntactic_modifier(
                            &nodes[p],
                            ast::ModifierFlags::PARAMETER_PROPERTY_MODIFIER,
                        )
                    }));
            if super_call_should_be_root_level {
                // Until we have better flow analysis, it is an error to place the super call within any kind of block or conditional
                // See GH #8277
                let body = nodes[node].body().expect("body");
                if !super_call_is_root_level_in_constructor(super_call, body, &nodes) {
                    self.error(
                        Some(super_call),
                        &tsc_diagnostics::A_super_call_must_be_a_root_level_statement_within_a_constructor_of_a_derived_class_that_contains_initialized_properties_parameter_properties_or_private_identifiers,
                        &[],
                    );
                } else {
                    let mut super_call_statement = None;
                    for &statement in nodes[body].statements().unwrap_or(&[]) {
                        if ast::is_expression_statement(&nodes[statement])
                            && nodes[statement].expression().is_some_and(|e| {
                                crate::utilities::is_super_call(
                                    ast::skip_outer_expressions(
                                        e,
                                        ast::outer_expression_kinds::ALL,
                                        &nodes,
                                    ),
                                    &nodes,
                                )
                            })
                        {
                            super_call_statement = Some(statement);
                            break;
                        }
                        if node_immediately_references_super_or_this(statement, &nodes) {
                            break;
                        }
                    }
                    // Until we have better flow analysis, it is an error to place the super call within any kind of block or conditional
                    // See GH #8277
                    if super_call_statement.is_none() {
                        self.error(
                            Some(node),
                            &tsc_diagnostics::A_super_call_must_be_the_first_statement_in_the_constructor_to_refer_to_super_or_this_when_a_derived_class_contains_initialized_properties_parameter_properties_or_private_identifiers,
                            &[],
                        );
                    }
                }
            }
        } else if !class_extends_null {
            self.error(
                Some(node),
                &tsc_diagnostics::Constructors_for_derived_classes_must_contain_a_super_call,
                &[],
            );
        }
    }

    /// `(c *Checker) findFirstSuperCall` (checker.go).
    pub(crate) fn find_first_super_call(&mut self, node: NodeId) -> Option<NodeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut super_call: Option<NodeId> = None;
        // Iterative pre-order walk standing in for the Go recursive
        // `visit` closure; `for_each_child` cannot short-circuit a parent
        // match, so we drive an explicit stack.
        let mut stack = vec![node];
        while let Some(n) = stack.pop() {
            if crate::utilities::is_super_call(n, &nodes) {
                super_call = Some(n);
                break;
            }
            if ast::is_function_like(Some(n), &nodes) {
                continue;
            }
            // Push children in reverse so traversal is left-to-right.
            let mut children = Vec::new();
            nodes[n].for_each_child(&nodes, &mut |c| {
                children.push(c);
                false
            });
            for &c in children.iter().rev() {
                stack.push(c);
            }
        }
        super_call
    }

    /// `(c *Checker) checkAccessorDeclaration` (checker.go).
    pub(crate) fn check_accessor_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Grammar checking accessors
        if !self.check_grammar_function_like_declaration(node) && !self.check_grammar_accessor(node)
        {
            if let Some(name) = nodes[node].name() {
                self.check_grammar_computed_property_name(name);
            }
        }
        let name = nodes[node].name();
        if name.is_some_and(|n| {
            ast::is_identifier(&nodes[n]) && &*nodes[n].text(&nodes) == "constructor"
        }) && nodes[node]
            .parent
            .is_some_and(|p| ast::is_class_like(Some(p), &nodes))
        {
            self.error(
                name,
                &tsc_diagnostics::Class_constructor_may_not_be_an_accessor,
                &[],
            );
        }
        self.check_decorators(node);
        self.check_signature_declaration(node);
        if ast::is_get_accessor_declaration(&nodes[node]) {
            if !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
                && ast::node_is_present(nodes[node].body(), &nodes)
                && nodes[node]
                    .flags
                    .intersects(ast::NodeFlags::HAS_IMPLICIT_RETURN)
            {
                if !nodes[node]
                    .flags
                    .intersects(ast::NodeFlags::HAS_EXPLICIT_RETURN)
                {
                    self.error(
                        name,
                        &tsc_diagnostics::A_get_accessor_must_return_a_value,
                        &[],
                    );
                }
            }
        }
        // Do not use hasDynamicName here, because that returns false for well known symbols.
        // We want to perform checkComputedPropertyName for all computed properties, including
        // well known symbols.
        if name.is_some_and(|n| ast::is_computed_property_name(&nodes[n])) {
            self.check_computed_property_name(name.expect("name"));
        }
        if self.has_bindable_name(node) {
            // TypeScript 1.0 spec (April 2014): 8.4.3
            // Accessors for the same member name must specify the same accessibility.
            let symbol = self.get_symbol_of_declaration(node);
            let (getter, setter) = symbol
                .map(|s| {
                    let arena = self.symbol_arena.borrow();
                    (
                        ast::get_declaration_of_kind(
                            &arena[s.index()],
                            ast::Kind::GetAccessor,
                            &nodes,
                        ),
                        ast::get_declaration_of_kind(
                            &arena[s.index()],
                            ast::Kind::SetAccessor,
                            &nodes,
                        ),
                    )
                })
                .unwrap_or((None, None));
            if getter.is_some()
                && setter.is_some()
                && !self
                    .node_links
                    .get(getter.unwrap())
                    .flags
                    .intersects(NodeCheckFlags::TYPE_CHECKED)
            {
                self.node_links
                    .get(getter.unwrap())
                    .flags
                    .insert(NodeCheckFlags::TYPE_CHECKED);
                let getter_flags = nodes[getter.unwrap()].modifier_flags();
                let setter_flags = nodes[setter.unwrap()].modifier_flags();
                if (getter_flags & ast::ModifierFlags::ABSTRACT)
                    != (setter_flags & ast::ModifierFlags::ABSTRACT)
                {
                    self.error(
                        nodes[getter.unwrap()].name(),
                        &tsc_diagnostics::Accessors_must_both_be_abstract_or_non_abstract,
                        &[],
                    );
                    self.error(
                        nodes[setter.unwrap()].name(),
                        &tsc_diagnostics::Accessors_must_both_be_abstract_or_non_abstract,
                        &[],
                    );
                }
                if (getter_flags.intersects(ast::ModifierFlags::PROTECTED)
                    && !setter_flags
                        .intersects(ast::ModifierFlags::PROTECTED | ast::ModifierFlags::PRIVATE))
                    || (getter_flags.intersects(ast::ModifierFlags::PRIVATE)
                        && !setter_flags.intersects(ast::ModifierFlags::PRIVATE))
                {
                    self.error(
                        nodes[getter.unwrap()].name(),
                        &tsc_diagnostics::A_get_accessor_must_be_at_least_as_accessible_as_the_setter,
                        &[],
                    );
                    self.error(
                        nodes[setter.unwrap()].name(),
                        &tsc_diagnostics::A_get_accessor_must_be_at_least_as_accessible_as_the_setter,
                        &[],
                    );
                }
            }
        }
        let accessor_symbol = self
            .get_symbol_of_declaration(node)
            .unwrap_or(self.unknown_symbol);
        let return_type = self.get_type_of_accessors(accessor_symbol);
        if nodes[node].kind == ast::Kind::GetAccessor {
            self.check_all_code_paths_in_non_void_function_return_or_throw(node, Some(return_type));
        }
        self.check_source_element(nodes[node].body());
        self.set_node_links_for_private_identifier_scope(node);
    }

    /// `(c *Checker) checkTypeReferenceNode` (checker.go).
    pub(crate) fn check_type_reference_node(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let type_argument_list = nodes[node].type_argument_list().cloned();
        self.check_grammar_type_arguments(node, type_argument_list.as_ref());
        if ast::is_type_reference_node(&nodes[node])
            && !nodes[node].flags.intersects(ast::NodeFlags::JSDOC)
        {
            let data = nodes[node].as_type_reference_node();
            if let (Some(tal), Some(tn)) = (nodes[node].type_argument_list(), data.type_name)
                && nodes[tn].end() != tal.pos()
            {
                // If there was a token between the type name and the type arguments, check if it was a DotToken
                let source_file = ast::get_source_file_of_node(Some(node), &nodes);
                if let Some(source_file) = source_file {
                    if tsc_scanner::scanner::scan_token_at_position(
                        nodes[source_file].as_source_file(),
                        nodes[data.type_name.unwrap()].end() as usize,
                    ) == ast::Kind::DotToken
                    {
                        let start = tsc_scanner::scanner::skip_trivia(
                            nodes[source_file].as_source_file().text(),
                            nodes[data.type_name.unwrap()].end(),
                        );
                        self.grammar_error_at_pos(
                            node,
                            start,
                            1,
                            &tsc_diagnostics::JSDoc_types_can_only_be_used_inside_documentation_comments,
                            &[],
                        );
                    }
                }
            }
        }
        let type_arguments = nodes[node].type_arguments().unwrap_or(&[]).to_vec();
        self.check_source_elements(&type_arguments);
        if !(crate::utilities::is_const_type_reference(node, &nodes)
            && nodes[node]
                .parent
                .is_some_and(|p| ast::is_assertion_expression(&nodes[p])))
        {
            self.check_type_reference_or_import(node);
        }
    }

    /// `(c *Checker) checkTypeReferenceOrImport` (checker.go).
    pub(crate) fn check_type_reference_or_import(&mut self, node: NodeId) {
        let t = self.get_type_from_type_node(node);
        if !crate::utilities::is_error_type(&self.types, t) {
            let __program = self.program.clone().expect("program");
            let has_type_arguments = {
                let nodes = __program.nodes((node).file_index());
                nodes[node].type_arguments().map_or(0, |a| a.len()) != 0
            };
            if has_type_arguments {
                let type_parameters = self.get_type_parameters_for_type_reference_or_import(node);
                if type_parameters.as_ref().is_some_and(|tp| !tp.is_empty()) {
                    self.check_type_argument_constraints(
                        node,
                        type_parameters.as_deref().unwrap_or(&[]),
                    );
                }
            }
            if let Some(symbol) = self.get_resolved_symbol_or_nil(node) {
                let declarations = sym_declarations(self, symbol);
                if declarations.iter().any(|&d| {
                    let __program = self.program.clone().expect("program");
                    let is_type_declaration = {
                        let dn = __program.nodes((d).file_index());
                        ast::is_type_declaration(d, &dn)
                    };
                    // PORT(borrowck): `dn` is dropped before the call so the
                    // lazy-JSDoc `nodes_mut` inside `is_deprecated_declaration`
                    // can take the arena.
                    is_type_declaration && self.is_deprecated_declaration(d)
                }) {
                    let name = sym_name(self, symbol);
                    let suggestion_node = self.get_deprecated_suggestion_node(node);
                    self.add_deprecated_suggestion(suggestion_node, &declarations, &name);
                }
            }
        }
    }

    /// `(c *Checker) checkTypeArgumentConstraints` (checker.go).
    pub(crate) fn check_type_argument_constraints(
        &mut self,
        node: NodeId,
        type_parameters: &[TypeId],
    ) -> bool {
        let mut type_arguments: Option<Vec<TypeId>> = None;
        let mut mapper: Option<TypeMapperId> = None;
        let mut result = true;
        for (i, &type_parameter) in type_parameters.iter().enumerate() {
            if let Some(constraint) = self.get_constraint_of_type_parameter(type_parameter) {
                if type_arguments.is_none() {
                    type_arguments = Some(self.get_effective_type_arguments(node, type_parameters));
                    mapper = Some(crate::mapper::new_type_mapper(
                        self,
                        type_parameters.to_vec(),
                        type_arguments.clone().unwrap(),
                    ));
                }
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((node).file_index());
                let error_node = nodes[node]
                    .type_arguments()
                    .and_then(|args| args.get(i).copied());
                let instantiated = self.instantiate_type(constraint, mapper);
                result = result
                    && self.check_type_assignable_to(
                        type_arguments.as_ref().unwrap()[i],
                        instantiated,
                        error_node,
                        Some(&tsc_diagnostics::Type_0_does_not_satisfy_the_constraint_1),
                    );
            }
        }
        result
    }

    /// `(c *Checker) getDeprecatedSuggestionNode` (checker.go).
    pub(crate) fn get_deprecated_suggestion_node(&mut self, node: NodeId) -> NodeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let node = ast::skip_parentheses(node, &nodes);
        match nodes[node].kind {
            ast::Kind::CallExpression | ast::Kind::Decorator | ast::Kind::NewExpression => {
                return self
                    .get_deprecated_suggestion_node(nodes[node].expression().expect("expression"));
            }
            ast::Kind::TaggedTemplateExpression => {
                return self.get_deprecated_suggestion_node(
                    nodes[node]
                        .as_tagged_template_expression()
                        .tag
                        .expect("tag"),
                );
            }
            ast::Kind::JsxOpeningElement | ast::Kind::JsxSelfClosingElement => {
                return self
                    .get_deprecated_suggestion_node(nodes[node].tag_name().expect("tag name"));
            }
            ast::Kind::ElementAccessExpression => {
                return nodes[node]
                    .as_element_access_expression()
                    .argument_expression
                    .expect("argument expression");
            }
            ast::Kind::PropertyAccessExpression => return nodes[node].name().expect("name"),
            ast::Kind::TypeReference => {
                let type_name = nodes[node].as_type_reference_node().type_name;
                if let Some(type_name) = type_name {
                    if ast::is_qualified_name(&nodes[type_name]) {
                        return nodes[type_name]
                            .as_qualified_name()
                            .right
                            .expect("qualified name right");
                    }
                }
            }
            _ => {}
        }
        node
    }

    /// `(c *Checker) checkTypePredicate` (checker.go).
    pub(crate) fn check_type_predicate(&mut self, node: NodeId) {
        // Always check the predicate's type so nested type errors are reported even when the
        // predicate is in an invalid position, keeping diagnostics stable.
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_source_element(nodes[node].type_());
        let Some(parent) = self.get_type_predicate_parent(node) else {
            // The parent must not be valid.
            self.error(
                Some(node),
                &tsc_diagnostics::A_type_predicate_is_only_allowed_in_return_type_position_for_functions_and_methods,
                &[],
            );
            return;
        };
        let signature = self.get_signature_from_declaration(parent);
        let Some(type_predicate) = self.get_type_predicate_of_signature(signature) else {
            return;
        };
        let parameter_name = nodes[node].as_type_predicate_node().parameter_name;
        if type_predicate.kind != TypePredicateKind::This
            && type_predicate.kind != TypePredicateKind::AssertsThis
        {
            if type_predicate.parameter_index >= 0 {
                let sig = self.signature_arena.get(signature);
                if crate::checker_c::signature_has_rest_parameter(sig)
                    && type_predicate.parameter_index as usize == sig.parameters.len() - 1
                {
                    self.error(
                        parameter_name,
                        &tsc_diagnostics::A_type_predicate_cannot_reference_a_rest_parameter,
                        &[],
                    );
                } else {
                    if let Some(t) = type_predicate.t {
                        let param_type = self.get_type_of_symbol(
                            self.signature_arena.get(signature).parameters
                                [type_predicate.parameter_index as usize],
                        );
                        let mut diags: Vec<ast::diagnostic::DiagnosticRef> = Vec::new();
                        if !self.check_type_assignable_to_ex(
                            t,
                            param_type,
                            nodes[node].type_(),
                            None, /*headMessage*/
                            Some(&mut diags),
                        ) {
                            self.add_diagnostic(&ast::diagnostic::new_diagnostic_chain(
                                diags.first(),
                                &tsc_diagnostics::A_type_predicate_s_type_must_be_assignable_to_its_parameter_s_type,
                                &[] as &[String],
                            ));
                        }
                    }
                }
            } else if let Some(parameter_name) = parameter_name {
                let mut has_reported_error = false;
                for &param in nodes[parent].parameters().unwrap_or(&[]) {
                    if let Some(name) = nodes[param].name() {
                        if ast::is_binding_pattern(&nodes[name])
                            && self.check_if_type_predicate_variable_is_declared_in_binding_pattern(
                                name,
                                parameter_name,
                                &type_predicate.parameter_name,
                            )
                        {
                            has_reported_error = true;
                            break;
                        }
                    }
                }
                if !has_reported_error {
                    self.error(
                        Some(parameter_name),
                        &tsc_diagnostics::Cannot_find_parameter_0,
                        &[type_predicate.parameter_name.clone()],
                    );
                }
            }
        }
    }

    /// `(c *Checker) getTypePredicateParent` (checker.go).
    pub(crate) fn get_type_predicate_parent(&self, node: NodeId) -> Option<NodeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(parent) = nodes[node].parent {
            match nodes[parent].kind {
                ast::Kind::ArrowFunction
                | ast::Kind::CallSignature
                | ast::Kind::FunctionDeclaration
                | ast::Kind::FunctionExpression
                | ast::Kind::FunctionType
                | ast::Kind::MethodDeclaration
                | ast::Kind::MethodSignature => {
                    if Some(node) == nodes[parent].type_() {
                        return Some(parent);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// `(c *Checker) checkIfTypePredicateVariableIsDeclaredInBindingPattern` (checker.go).
    pub(crate) fn check_if_type_predicate_variable_is_declared_in_binding_pattern(
        &mut self,
        pattern: NodeId,
        predicate_variable_node: NodeId,
        predicate_variable_name: &str,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((pattern).file_index());
        for &element in nodes[pattern].elements().unwrap_or(&[]) {
            let Some(name) = nodes[element].name() else {
                continue;
            };
            if ast::is_identifier(&nodes[name])
                && &*nodes[name].text(&nodes) == predicate_variable_name
            {
                self.error(
                    Some(predicate_variable_node),
                    &tsc_diagnostics::A_type_predicate_cannot_reference_element_0_in_a_binding_pattern,
                    &[predicate_variable_name.to_string()],
                );
                return true;
            }
            if ast::is_array_binding_pattern(&nodes[name])
                || ast::is_object_binding_pattern(&nodes[name])
            {
                if self.check_if_type_predicate_variable_is_declared_in_binding_pattern(
                    name,
                    predicate_variable_node,
                    predicate_variable_name,
                ) {
                    return true;
                }
            }
        }
        false
    }

    /// `(c *Checker) checkTypeQuery` (checker.go).
    pub(crate) fn check_type_query(&mut self, node: NodeId) {
        self.get_type_from_type_query_node(node);
    }

    /// `(c *Checker) checkTypeLiteral` (checker.go).
    pub(crate) fn check_type_literal(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let members = nodes[node].members().unwrap_or(&[]).to_vec();
        self.check_source_elements(&members);
        let t = self.get_type_from_type_literal_or_function_or_constructor_type_node(node);
        let symbol = self.types.get_ref(t).symbol;
        self.check_index_constraints(t, symbol, false /*isStaticIndex*/);
        self.check_type_for_duplicate_index_signatures(node);
        self.check_object_type_for_duplicate_declarations(node, false /*checkPrivateNames*/);
    }

    /// `(c *Checker) checkObjectTypeForDuplicateDeclarations` (checker.go).
    pub(crate) fn check_object_type_for_duplicate_declarations(
        &mut self,
        node: NodeId,
        check_private_names: bool,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut instance_names: FxHashMap<String, i32> = FxHashMap::default();
        let mut static_names: FxHashMap<String, i32> = FxHashMap::default();
        let mut private_names: FxHashMap<String, i32> = FxHashMap::default();
        let node_in_ambient_context = nodes[node].flags.intersects(ast::NodeFlags::AMBIENT);

        // PORT: Go's `checkPropertyOrAccessor` closure mutates the lazily
        // allocated name maps; `Option<FxHashMap>` mirrors the nil-map
        // states 0/1/2/3 exactly.
        fn check_property_or_accessor(
            c: &mut Checker,
            instance_names: &mut FxHashMap<String, i32>,
            static_names: &mut FxHashMap<String, i32>,
            node: NodeId,
            symbol: Option<SymbolId>,
            kind: i32,
            is_static: bool,
        ) {
            let Some(symbol) = symbol else { return };
            if c.symbol_arena.borrow()[symbol.index()].declarations.len() > 1 {
                let name = c.symbol_arena.borrow()[symbol.index()].name.clone();
                let names = if is_static {
                    &mut *static_names
                } else {
                    &mut *instance_names
                };
                let state = *names.get(&name).unwrap_or(&0);
                if state == 0 {
                    // On first occurrence just record the kind
                    names.insert(name, kind);
                } else if state == 1 || (state == 2 && kind != 2) {
                    // Error on second property or combination of property and accessor
                    c.report_duplicate_member_errors(
                        node,
                        &name,
                        true,
                        is_static,
                        &tsc_diagnostics::Duplicate_identifier_0,
                    );
                    // Record that errors have been reported
                    names.insert(name, 3);
                }
            }
        }

        for &member in nodes[node].members().unwrap_or(&[]) {
            if ast::is_constructor_declaration(&nodes[member]) {
                for &param in nodes[member].parameters().unwrap_or(&[]) {
                    if ast::is_parameter_property_declaration(&nodes[param], &nodes[member])
                        && !nodes[param]
                            .name()
                            .is_some_and(|n| ast::is_binding_pattern(&nodes[n]))
                    {
                        let param_symbol = self.get_symbol_of_declaration(param);
                        check_property_or_accessor(
                            self,
                            &mut instance_names,
                            &mut static_names,
                            node,
                            param_symbol,
                            1,
                            false, /*isStatic*/
                        );
                    }
                }
            } else {
                let symbol = self.get_symbol_of_declaration(member);
                let is_static = ast::has_static_modifier(&nodes[member]);
                // In non-ambient contexts, check that static members are not named 'prototype'.
                if !node_in_ambient_context
                    && is_static
                    && symbol.is_some_and(|s| sym_name(self, s) == "prototype")
                {
                    let decl_sym = self.get_symbol_of_declaration(node);
                    let arg1 = self.symbol_to_string(decl_sym);
                    self.error(
                        nodes[member].name(),
                        &tsc_diagnostics::Static_property_0_conflicts_with_built_in_property_Function_0_of_constructor_function_1,
                        &["prototype".to_string(), arg1],
                    );
                }
                // Check that this object type declaration doesn't contain multiple declarations of the same property,
                // or accessor and property declarations with the same name.
                if (ast::is_property_declaration(&nodes[member])
                    && !ast::has_accessor_modifier(&nodes[member]))
                    || ast::is_property_signature_declaration(&nodes[member])
                {
                    check_property_or_accessor(
                        self,
                        &mut instance_names,
                        &mut static_names,
                        node,
                        symbol,
                        1,
                        is_static,
                    );
                } else if ast::is_accessor(&nodes[member])
                    || (ast::is_property_declaration(&nodes[member])
                        && ast::has_accessor_modifier(&nodes[member]))
                {
                    check_property_or_accessor(
                        self,
                        &mut instance_names,
                        &mut static_names,
                        node,
                        symbol,
                        2,
                        is_static,
                    );
                }
                // Check that each private identifier is used only for instance members or only for static members. It is an
                // error for an instance and a static member to have the same private identifier.
                if check_private_names
                    && nodes[member]
                        .name()
                        .is_some_and(|n| ast::is_private_identifier(&nodes[n]))
                {
                    if let Some(symbol) = symbol {
                        let name = sym_name(self, symbol);
                        let flags = *private_names.get(&name).unwrap_or(&0);
                        if flags != 3 {
                            let flags = flags
                                | tsc_core::core::if_else(ast::is_static(&nodes[member]), 2, 1);
                            private_names.insert(name.clone(), flags);
                            if flags == 3 {
                                self.report_duplicate_member_errors(
                                    node,
                                    &name,
                                    false,
                                    false,
                                    &tsc_diagnostics::Duplicate_identifier_0_Static_and_instance_elements_cannot_share_the_same_private_name,
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    /// `(c *Checker) reportDuplicateMemberErrors` (checker.go).
    pub(crate) fn report_duplicate_member_errors(
        &mut self,
        node: NodeId,
        name: &str,
        check_static: bool,
        is_static: bool,
        message: &'static tsc_diagnostics::Message,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        for &member in nodes[node].members().unwrap_or(&[]) {
            if ast::is_constructor_declaration(&nodes[member]) {
                for &param in nodes[member].parameters().unwrap_or(&[]) {
                    if ast::is_parameter_property_declaration(&nodes[param], &nodes[member])
                        && !nodes[param]
                            .name()
                            .is_some_and(|n| ast::is_binding_pattern(&nodes[n]))
                    {
                        if let Some(symbol) = self.get_symbol_of_declaration(param) {
                            if sym_name(self, symbol) == name {
                                let arg = self.symbol_to_string(symbol);
                                self.error(nodes[param].name(), message, &[arg]);
                            }
                        }
                    }
                }
            } else if let Some(symbol) = self.get_symbol_of_declaration(member) {
                if sym_name(self, symbol) == name
                    && (!check_static || is_static == ast::is_static(&nodes[member]))
                {
                    let arg = self.symbol_to_string(symbol);
                    self.error(nodes[member].name(), message, &[arg]);
                }
            }
        }
    }

    /// `(c *Checker) checkArrayType` (checker.go).
    pub(crate) fn check_array_type(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let element_type = nodes[node].as_array_type_node().element_type;
        self.check_source_element(element_type);
    }

    /// `(c *Checker) checkTupleType` (checker.go).
    pub(crate) fn check_tuple_type(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut seen_optional_element = false;
        let mut seen_rest_element = false;
        let elements = nodes[node].elements().unwrap_or(&[]).to_vec();
        for &e in &elements {
            let mut flags = self.get_tuple_element_flags(e);
            if flags.intersects(crate::types::ElementFlags::VARIADIC) {
                let t = self.get_type_from_type_node(nodes[e].type_().expect("tuple element type"));
                if !self.is_array_like_type(t) {
                    self.error(
                        Some(e),
                        &tsc_diagnostics::A_rest_element_type_must_be_an_array_type,
                        &[],
                    );
                    break;
                }
                if self.is_array_type(t)
                    || (crate::checker_core::is_tuple_type(&self.types, t)
                        && self
                            .types_handle()
                            .target_tuple_type(t)
                            .is_some_and(|target| {
                                self.types_handle()
                                    .get(target)
                                    .as_tuple_type()
                                    .combined_flags
                                    .intersects(crate::types::ElementFlags::REST)
                            }))
                {
                    flags |= crate::types::ElementFlags::REST;
                }
            }
            if flags.intersects(crate::types::ElementFlags::REST) {
                if seen_rest_element {
                    self.grammar_error_on_node(
                        e,
                        &tsc_diagnostics::A_rest_element_cannot_follow_another_rest_element,
                        &[],
                    );
                    break;
                }
                seen_rest_element = true;
            } else if flags.intersects(crate::types::ElementFlags::OPTIONAL) {
                if seen_rest_element {
                    self.grammar_error_on_node(
                        e,
                        &tsc_diagnostics::An_optional_element_cannot_follow_a_rest_element,
                        &[],
                    );
                    break;
                }
                seen_optional_element = true;
            } else if flags.intersects(crate::types::ElementFlags::REQUIRED)
                && seen_optional_element
            {
                self.grammar_error_on_node(
                    e,
                    &tsc_diagnostics::A_required_element_cannot_follow_an_optional_element,
                    &[],
                );
                break;
            }
        }
        self.check_source_elements(&elements);
        self.get_type_from_type_node(node);
    }

    /// `(c *Checker) checkUnionOrIntersectionType` (checker.go).
    pub(crate) fn check_union_or_intersection_type(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        nodes[node].for_each_child(&nodes, &mut |child| self.check_source_element(Some(child)));
        self.get_type_from_type_node(node);
    }

    /// `(c *Checker) checkThisType` (checker.go).
    pub(crate) fn check_this_type(&mut self, node: NodeId) {
        self.get_type_from_this_type_node(node);
    }

    /// `(c *Checker) checkTypeOperator` (checker.go).
    pub(crate) fn check_type_operator(&mut self, node: NodeId) {
        self.check_grammar_type_operator_node(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_source_element(nodes[node].type_());
    }

    /// `(c *Checker) checkConditionalType` (checker.go).
    pub(crate) fn check_conditional_type(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        nodes[node].for_each_child(&nodes, &mut |child| self.check_source_element(Some(child)));
    }

    /// `(c *Checker) checkInferType` (checker.go).
    pub(crate) fn check_infer_type(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if ast::find_ancestor(Some(node), &nodes, &mut |n, nodes| {
            n.parent.is_some_and(|p| {
                nodes[p].kind == ast::Kind::ConditionalType
                    && nodes[p].as_conditional_type_node().extends_type == Some(n.id)
            })
        })
        .is_none()
        {
            self.grammar_error_on_node(
                node,
                &tsc_diagnostics::X_infer_declarations_are_only_permitted_in_the_extends_clause_of_a_conditional_type,
                &[],
            );
        }
        let type_parameter_declaration_node = nodes[node].as_infer_type_node().type_parameter;
        self.check_source_element(type_parameter_declaration_node);
        let symbol =
            self.get_symbol_of_declaration(type_parameter_declaration_node.expect("typeParameter"));
        if let Some(symbol) = symbol {
            if self.symbol_arena.borrow()[symbol.index()]
                .declarations
                .len()
                > 1
            {
                let links = self.declared_type_links.get(symbol);
                if !links.type_parameters_checked {
                    links.type_parameters_checked = true;
                    let type_parameter = self.get_declared_type_of_type_parameter(symbol);
                    let declarations = crate::utilities::get_declarations_of_kind(
                        self,
                        symbol,
                        ast::Kind::TypeParameter);
                    if !self.are_type_parameters_identical(
                        &declarations,
                        &[type_parameter],
                        &mut |decl: NodeId, _nodes: &[ast::Node]| vec![decl],
                    ) {
                        // Report an error on every conflicting declaration.
                        let name = self.symbol_to_string(symbol);
                        for &declaration in &declarations {
                            // PORT(borrowck): hoist `program_nodes` so its `Ref`
                            // drops before the `&mut self` `error` call.
                            let __name_node = self.program_nodes(declaration)[declaration].name();
                            self.error(
                                __name_node,
                                &tsc_diagnostics::All_declarations_of_0_must_have_identical_constraints,
                                &[name.clone()],
                            );
                        }
                    }
                }
            }
        }
        self.register_for_unused_identifiers_check(node);
    }

    /// `(c *Checker) checkTemplateLiteralType` (checker.go).
    pub(crate) fn check_template_literal_type(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let spans: Vec<NodeId> = nodes[node]
            .as_template_literal_type_node()
            .template_spans
            .as_ref()
            .map(|l| l.nodes().to_vec())
            .unwrap_or_default();
        for span in spans {
            let ty = nodes[span].type_();
            self.check_source_element(ty);
            let t = self.get_type_from_type_node(ty.expect("span type"));
            self.check_type_assignable_to(t, self.template_constraint_type, ty, None);
        }
        self.get_type_from_type_node(node);
    }

    /// `(c *Checker) checkImportType` (checker.go).
    pub(crate) fn check_import_type(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let argument = nodes[node].as_import_type_node().argument;
        self.check_source_element(argument);
        if let Some(attributes) = nodes[node].as_import_type_node().attributes {
            self.check_grammar_import_attribute_values(attributes);
            self.get_resolution_mode_override(attributes, true /*reportErrors*/);
        }
        self.check_type_reference_or_import(node);
        self.check_import_attributes(node);
    }

    /// `(c *Checker) getResolutionModeOverride` (checker.go).
    ///
    /// PORT: Go passes `*ast.ImportAttributes` (the struct); the port passes
    /// the owning `ImportAttributes` `NodeId`.
    pub(crate) fn get_resolution_mode_override(
        &mut self,
        node: NodeId,
        report_errors: bool,
    ) -> tsc_core::compileroptions::ResolutionMode {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // PORT: Go passes `c.grammarErrorOnNode` as a callback that fires on
        // the offending value node; the ast helper invokes the thunk with
        // the node and the caller reports the fixed message.
        let mut error_value: Option<NodeId> = None;
        let (mode, _) = {
            let mut on_error = |value: NodeId| {
                error_value = Some(value);
            };
            ast::import_attributes_resolution_mode_override(
                Some(node),
                if report_errors {
                    Some(&mut on_error as &mut dyn FnMut(NodeId))
                } else {
                    None
                },
                &nodes,
            )
        };
        if let Some(value) = error_value {
            self.grammar_error_on_node(
                value,
                &tsc_diagnostics::X_resolution_mode_should_be_either_require_or_import,
                &[],
            );
        }
        mode
    }

    /// `(c *Checker) checkNamedTupleMember` (checker.go).
    pub(crate) fn check_named_tuple_member(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let tuple_member = nodes[node].as_named_tuple_member();
        if tuple_member.dot_dot_dot_token.is_some() && tuple_member.question_token.is_some() {
            self.grammar_error_on_node(
                node,
                &tsc_diagnostics::A_tuple_member_cannot_be_both_optional_and_rest,
                &[],
            );
        }
        if let Some(ty) = tuple_member.type_ {
            if nodes[ty].kind == ast::Kind::OptionalType {
                self.grammar_error_on_node(
                    ty,
                    &tsc_diagnostics::A_labeled_tuple_element_is_declared_as_optional_with_a_question_mark_after_the_name_and_before_the_colon_rather_than_after_the_type,
                    &[],
                );
            }
            if nodes[ty].kind == ast::Kind::RestType {
                self.grammar_error_on_node(
                    ty,
                    &tsc_diagnostics::A_labeled_tuple_element_is_declared_as_rest_with_a_before_the_name_rather_than_before_the_type,
                    &[],
                );
            }
        }
        self.check_source_element(nodes[node].type_());
        self.get_type_from_type_node(node);
    }

    /// `(c *Checker) checkIndexedAccessType` (checker.go).
    pub(crate) fn check_indexed_access_type(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        nodes[node].for_each_child(&nodes, &mut |child| self.check_source_element(Some(child)));
        let t = self.get_type_from_indexed_access_type_node(node);
        self.check_indexed_access_index_type(t, node);
    }

    /// `(c *Checker) checkMappedType` (checker.go).
    pub(crate) fn check_mapped_type(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_grammar_mapped_type(node);
        let mapped = nodes[node].as_mapped_type_node();
        self.check_source_element(mapped.type_parameter);
        self.check_source_element(mapped.name_type);
        self.check_source_element(mapped.type_);
        if mapped.type_.is_none() {
            self.report_implicit_any(node, self.any_type, WideningKind::Normal);
        }
        let t = self.get_type_from_mapped_type_node(node);
        if let Some(name_type) = self.get_name_type_from_mapped_type(t) {
            self.check_type_assignable_to(
                name_type,
                self.string_number_symbol_type,
                mapped.name_type,
                None,
            );
        } else {
            let constraint_type = self.get_constraint_type_from_mapped_type(t);
            let constraint = mapped
                .type_parameter
                .and_then(|tp| nodes[tp].as_type_parameter_declaration().constraint);
            self.check_type_assignable_to(
                constraint_type.expect("constraintType"),
                self.string_number_symbol_type,
                constraint,
                None,
            );
        }
    }
}

// ======== checker.go ~2955 — free helpers ========

/// `isInstancePropertyWithInitializerOrPrivateIdentifierProperty` (checker.go).
pub(crate) fn is_instance_property_with_initializer_or_private_identifier_property(
    n: &ast::Node,
    nodes: &[ast::Node],
) -> bool {
    ast::is_private_identifier_class_element_declaration(n, nodes)
        || (ast::is_property_declaration(n) && !ast::is_static(n) && n.initializer().is_some())
}

/// `superCallIsRootLevelInConstructor` (checker.go).
pub(crate) fn super_call_is_root_level_in_constructor(
    super_call: NodeId,
    body: NodeId,
    nodes: &[ast::Node],
) -> bool {
    let super_call_parent =
        ast::walk_up_parenthesized_expressions(nodes[super_call].parent.expect("parent"), nodes);
    super_call_parent
        .is_some_and(|p| ast::is_expression_statement(&nodes[p]) && nodes[p].parent == Some(body))
}

/// `nodeImmediatelyReferencesSuperOrThis` (checker.go).
pub(crate) fn node_immediately_references_super_or_this(node: NodeId, nodes: &[ast::Node]) -> bool {
    match nodes[node].kind {
        ast::Kind::SuperKeyword | ast::Kind::ThisKeyword => return true,
        ast::Kind::ArrowFunction
        | ast::Kind::FunctionDeclaration
        | ast::Kind::FunctionExpression
        | ast::Kind::PropertyDeclaration => return false,
        ast::Kind::Block => {
            if let Some(parent) = nodes[node].parent {
                match nodes[parent].kind {
                    ast::Kind::Constructor
                    | ast::Kind::MethodDeclaration
                    | ast::Kind::GetAccessor
                    | ast::Kind::SetAccessor => return false,
                    _ => {}
                }
            }
        }
        _ => {}
    }
    let mut result = false;
    nodes[node].for_each_child(nodes, &mut |child| {
        if node_immediately_references_super_or_this(child, nodes) {
            result = true;
            return true;
        }
        false
    });
    result
}

// ======== checker.go ~3434 — function/method declaration checking ========

impl Checker {
    /// `(c *Checker) checkFunctionDeclaration` (checker.go).
    pub(crate) fn check_function_declaration(&mut self, node: NodeId) {
        self.check_function_or_method_declaration(node);
        self.check_grammar_for_generator(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_collisions_for_declaration_name(node, nodes[node].name());
    }

    /// `(c *Checker) checkFunctionOrMethodDeclaration` (checker.go).
    pub(crate) fn check_function_or_method_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        self.check_decorators(node);
        // PORT(borrowck): `check_signature_declaration` takes `nodes_mut` —
        // borrow the arena only after it returns.
        self.check_signature_declaration(node);
        let nodes = __program.nodes((node).file_index());
        let function_flags = ast::get_function_flags(Some(&nodes[node]));
        // Do not use hasDynamicName here, because that returns false for well known symbols.
        // We want to perform checkComputedPropertyName for all computed properties, including
        // well known symbols.
        if let Some(name) = nodes[node].name() {
            if ast::is_computed_property_name(&nodes[name]) {
                // This check will account for methods in class/interface declarations,
                // as well as accessors in classes/object literals
                self.check_computed_property_name(name);
            }
        }
        if self.has_bindable_name(node) {
            // first we want to check the local symbol that contain this declaration
            // - if node.localSymbol !== undefined - this is current declaration is exported and localSymbol points to the local symbol
            // - if node.localSymbol === undefined - this node is non-exported so we can just pick the result of getSymbolOfNode
            let symbol = self.get_symbol_of_declaration(node);
            let local_symbol = nodes[node].local_symbol().or(symbol);
            // Since the javascript won't do semantic analysis like typescript, ignore javascript function
            // declarations so that redeclaring a function in a JS file is not reported as a duplicate.
            if !nodes[node]
                .flags
                .intersects(ast::NodeFlags::JAVA_SCRIPT_FILE)
            {
                self.check_function_or_constructor_symbol(local_symbol);
            }
            if symbol.is_some_and(|s| sym_parent(self, s).is_some()) {
                // run check on export symbol to check that modifiers agree across all exported declarations
                self.check_function_or_constructor_symbol(symbol);
            }
        }
        let body = nodes[node].body();
        self.check_source_element(body);
        let return_type = self.get_return_type_from_annotation(node);
        self.check_all_code_paths_in_non_void_function_return_or_throw(node, return_type);
        if let Some(full_signature) = nodes[node]
            .function_like_data()
            .and_then(|d| d.full_signature)
        {
            self.check_source_element(Some(full_signature));
            let sig_type = self.get_type_from_type_node(full_signature);
            if self.get_contextual_call_signature(sig_type, node).is_none() {
                self.error(
                    Some(full_signature),
                    &tsc_diagnostics::A_JSDoc_type_tag_on_a_function_must_have_a_signature_with_the_correct_number_of_arguments,
                    &[],
                );
            }
        }
        if nodes[node].type_().is_none() {
            // Report an implicit any error if there is no body, no explicit return type, and node is not a private method
            // in an ambient context
            if ast::node_is_missing(body, &nodes)
                && !crate::utilities::is_private_within_ambient(&nodes[node], &nodes)
            {
                self.report_implicit_any(node, self.any_type, WideningKind::Normal);
            }
            if function_flags.intersects(ast::FunctionFlags::GENERATOR)
                && ast::node_is_present(body, &nodes)
            {
                // A generator with a body and no type annotation can still cause errors. It can error if the
                // yielded values have no common supertype, or it can give an implicit any error if it has no
                // yielded values. The only way to trigger these errors is to try checking its return type.
                let sig = self.get_signature_from_declaration(node);
                self.get_return_type_of_signature(sig);
            }
        }
    }

    /// `(c *Checker) checkFunctionOrConstructorSymbol` (checker.go).
    pub(crate) fn check_function_or_constructor_symbol(&mut self, symbol: Option<SymbolId>) {
        // Only check the symbol once
        if let Some(symbol) = symbol {
            let links = self.value_symbol_links.get(symbol);
            if !links.function_or_constructor_checked {
                links.function_or_constructor_checked = true;
                self.check_function_or_constructor_symbol_worker(symbol);
            }
        }
    }

    /// `checkFunctionOrConstructorSymbolWorker` helper — the Go
    /// `getCanonicalOverload` closure.
    fn get_canonical_overload(
        overloads: &[NodeId],
        implementation: Option<NodeId>,
        nodes: &[ast::Node],
    ) -> NodeId {
        // Consider the canonical set of flags to be the flags of the bodyDeclaration or the first declaration
        // Error on all deviations from this canonical set of flags
        // The caveat is that if some overloads are defined in lib.d.ts, we don't want to
        // report the errors on those. To achieve this, we will say that the implementation is
        // the canonical signature only if it is in the same container as the first overload
        let implementation_shares_container_with_first_overload =
            implementation.is_some_and(|i| {
                i.file_index() == overloads[0].file_index()
                    && nodes[i].parent == nodes[overloads[0]].parent
            });
        if implementation_shares_container_with_first_overload {
            implementation.unwrap()
        } else {
            overloads[0]
        }
    }

    /// `checkFunctionOrConstructorSymbolWorker` helper — the Go
    /// `checkFlagAgreementBetweenOverloads` closure.
    fn check_flag_agreement_between_overloads(
        &mut self,
        overloads: &[NodeId],
        implementation: Option<NodeId>,
        flags_to_check: ast::ModifierFlags,
        some_overload_flags: ast::ModifierFlags,
        all_overload_flags: ast::ModifierFlags,
    ) {
        // Error if some overloads have a flag that is not shared by all overloads. To find the
        // deviations, we XOR someOverloadFlags with allOverloadFlags
        let some_but_not_all_overload_flags = some_overload_flags.without(all_overload_flags)
            | all_overload_flags.without(some_overload_flags);
        if some_but_not_all_overload_flags.is_empty() {
            return;
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((overloads[0]).file_index());
        let canonical_flags = self.get_effective_declaration_flags(
            Self::get_canonical_overload(overloads, implementation, &nodes),
            flags_to_check,
        );
        let mut groups: FxHashMap<NodeId, Vec<NodeId>> = FxHashMap::default();
        let mut group_order: Vec<NodeId> = Vec::new();
        for &overload in overloads {
            let overload_nodes = __program.nodes(overload.file_index());
            let source_file = ast::get_source_file_of_node(Some(overload), &overload_nodes);
            if let Some(source_file) = source_file {
                groups
                    .entry(source_file)
                    .or_insert_with(|| {
                        group_order.push(source_file);
                        Vec::new()
                    })
                    .push(overload);
            }
        }
        for source_file in group_order {
            let overloads_in_file = &groups[&source_file];
            let file_nodes = __program.nodes(overloads_in_file[0].file_index());
            let canonical_flags_for_file = self.get_effective_declaration_flags(
                Self::get_canonical_overload(overloads_in_file, implementation, &file_nodes),
                flags_to_check,
            );
            for &overload in overloads_in_file {
                let deviation_flags =
                    self.get_effective_declaration_flags(overload, flags_to_check);
                let deviation = deviation_flags.without(canonical_flags)
                    | canonical_flags.without(deviation_flags);
                let deviation_in_file = deviation_flags.without(canonical_flags_for_file)
                    | canonical_flags_for_file.without(deviation_flags);
                if deviation_in_file.intersects(ast::ModifierFlags::EXPORT) {
                    // Overloads in different files need not all have export modifiers. This is ok:
                    //   // lib.d.ts
                    //   declare function foo(s: number): string;
                    //   declare function foo(s: string): number;
                    //   export { foo };
                    //
                    //   // app.ts
                    //   declare module "lib" {
                    //     export function foo(s: boolean): boolean;
                    //   }
                    self.error(
                        ast::get_name_of_declaration(Some(overload), &nodes),
                        &tsc_diagnostics::Overload_signatures_must_all_be_exported_or_non_exported,
                        &[],
                    );
                } else if deviation_in_file.intersects(ast::ModifierFlags::AMBIENT) {
                    // Though rare, a module augmentation (necessarily ambient) is allowed to add overloads
                    // to a non-ambient function in an implementation file.
                    self.error(
                        ast::get_name_of_declaration(Some(overload), &nodes),
                        &tsc_diagnostics::Overload_signatures_must_all_be_ambient_or_non_ambient,
                        &[],
                    );
                } else if deviation
                    .intersects(ast::ModifierFlags::PRIVATE | ast::ModifierFlags::PROTECTED)
                {
                    self.error(
                        Some(
                            ast::get_name_of_declaration(Some(overload), &nodes)
                                .unwrap_or(overload),
                        ),
                        &tsc_diagnostics::Overload_signatures_must_all_be_public_private_or_protected,
                        &[],
                    );
                } else if deviation.intersects(ast::ModifierFlags::ABSTRACT) {
                    self.error(
                        ast::get_name_of_declaration(Some(overload), &nodes),
                        &tsc_diagnostics::Overload_signatures_must_all_be_abstract_or_non_abstract,
                        &[],
                    );
                }
            }
        }
    }

    /// `checkFunctionOrConstructorSymbolWorker` helper — the Go
    /// `checkQuestionTokenAgreementBetweenOverloads` closure.
    fn check_question_token_agreement_between_overloads(
        &mut self,
        overloads: &[NodeId],
        implementation: Option<NodeId>,
        some_have_question_token: bool,
        all_have_question_token: bool,
    ) {
        if some_have_question_token != all_have_question_token {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((overloads[0]).file_index());
            let canonical_has_question_token = crate::utilities::is_optional_declaration(
                &nodes[Self::get_canonical_overload(overloads, implementation, &nodes)],
                &nodes,
            );
            for &o in overloads {
                if crate::utilities::is_optional_declaration(&nodes[o], &nodes)
                    != canonical_has_question_token
                {
                    self.error(
                        ast::get_name_of_declaration(Some(o), &nodes),
                        &tsc_diagnostics::Overload_signatures_must_all_be_optional_or_required,
                        &[],
                    );
                }
            }
        }
    }

    /// `checkFunctionOrConstructorSymbolWorker` helper — the Go
    /// `reportImplementationExpectedError` closure (captures `isConstructor`).
    fn report_implementation_expected_error(&mut self, node: NodeId, is_constructor: bool) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let name = nodes[node].name();
        if name.is_some_and(|n| ast::node_is_missing(Some(n), &nodes)) {
            return;
        }
        let mut seen = false;
        let mut subsequent_node: Option<NodeId> = None;
        if let Some(parent) = nodes[node].parent {
            nodes[parent].for_each_child(&nodes, &mut |child| {
                if seen {
                    subsequent_node = Some(child);
                    return true;
                }
                seen = child == node;
                false
            });
        }
        // We may be here because of some extra nodes between overloads that could not be parsed into a valid node.
        // In this case the subsequent node is not really consecutive (.pos !== node.end), and we must ignore it here.
        if let Some(subsequent_node) = subsequent_node {
            if nodes[subsequent_node].pos() == nodes[node].end() {
                if nodes[subsequent_node].kind == nodes[node].kind {
                    let subsequent_name = nodes[subsequent_node].name();
                    let error_node = subsequent_name.unwrap_or(subsequent_node);
                    if name.is_some() && subsequent_name.is_some() && {
                        let name = name.unwrap();
                        let subsequent_name = subsequent_name.unwrap();
                        (ast::is_private_identifier(&nodes[name])
                            && ast::is_private_identifier(&nodes[subsequent_name])
                            && nodes[name].text(&nodes) == nodes[subsequent_name].text(&nodes))
                            || (ast::is_computed_property_name(&nodes[name])
                                && ast::is_computed_property_name(&nodes[subsequent_name])
                                && {
                                    let t1 = self.check_computed_property_name(name);
                                    let t2 = self.check_computed_property_name(subsequent_name);
                                    self.is_type_identical_to(t1, t2)
                                })
                            || (ast::is_property_name_literal(&nodes[name])
                                && ast::is_property_name_literal(&nodes[subsequent_name])
                                && nodes[name].text(&nodes) == nodes[subsequent_name].text(&nodes))
                    } {
                        let report_error = (ast::is_method_declaration(&nodes[node])
                            || ast::is_method_signature_declaration(&nodes[node]))
                            && ast::is_static(&nodes[node])
                                != ast::is_static(&nodes[subsequent_node]);
                        // we can get here in two cases
                        // 1. mixed static and instance class members
                        // 2. something with the same name was defined before the set of overloads that prevents them from merging
                        // here we'll report error only for the first case since for second we should already report error in binder
                        if report_error {
                            let diagnostic = if ast::is_static(&nodes[node]) {
                                &tsc_diagnostics::Function_overload_must_be_static
                            } else {
                                &tsc_diagnostics::Function_overload_must_not_be_static
                            };
                            self.error(Some(error_node), diagnostic, &[]);
                        }
                        return;
                    }
                    if ast::node_is_present(nodes[subsequent_node].body(), &nodes) {
                        let arg = tsc_scanner::utilities::declaration_name_to_string(name, &nodes);
                        self.error(
                            Some(error_node),
                            &tsc_diagnostics::Function_implementation_name_must_be_0,
                            &[arg],
                        );
                        return;
                    }
                }
            }
        }
        let error_node = name.unwrap_or(node);
        if is_constructor {
            self.error(
                Some(error_node),
                &tsc_diagnostics::Constructor_implementation_is_missing,
                &[],
            );
        } else {
            // Report different errors regarding non-consecutive blocks of declarations depending on whether
            // the node in question is abstract.
            if ast::has_syntactic_modifier(&nodes[node], ast::ModifierFlags::ABSTRACT) {
                self.error(
                    Some(error_node),
                    &tsc_diagnostics::All_declarations_of_an_abstract_method_must_be_consecutive,
                    &[],
                );
            } else {
                self.error(
                    Some(error_node),
                    &tsc_diagnostics::Function_implementation_is_missing_or_not_immediately_following_the_declaration,
                    &[],
                );
            }
        }
    }

    /// `(c *Checker) checkFunctionOrConstructorSymbolWorker` (checker.go).
    pub(crate) fn check_function_or_constructor_symbol_worker(&mut self, symbol: SymbolId) {
        let flags_to_check = ast::ModifierFlags::EXPORT
            | ast::ModifierFlags::AMBIENT
            | ast::ModifierFlags::PRIVATE
            | ast::ModifierFlags::PROTECTED
            | ast::ModifierFlags::ABSTRACT;
        let mut some_node_flags = ast::ModifierFlags::NONE;
        let mut all_node_flags = flags_to_check;
        let mut some_have_question_token = false;
        let mut all_have_question_token = true;
        let mut has_overloads = false;
        let mut body_declaration: Option<NodeId> = None;
        let mut last_seen_non_ambient_declaration: Option<NodeId> = None;
        let mut previous_declaration: Option<NodeId> = None;
        let declarations = sym_declarations(self, symbol);
        let is_constructor = sym_flags(self, symbol).intersects(ast::SymbolFlags::CONSTRUCTOR);
        let mut duplicate_function_declaration = false;
        let mut multiple_constructor_implementation = false;
        let mut has_non_ambient_class = false;
        let mut function_declarations: Vec<NodeId> = Vec::new();
        for &node in &declarations {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            let in_ambient_context = nodes[node].flags.intersects(ast::NodeFlags::AMBIENT);
            let in_ambient_context_or_interface = in_ambient_context
                || nodes[node].parent.is_some_and(|p| {
                    ast::is_interface_declaration(&nodes[p]) || ast::is_type_literal_node(&nodes[p])
                });
            if in_ambient_context_or_interface {
                // check if declarations are consecutive only if they are non-ambient
                // 1. ambient declarations can be interleaved
                // i.e. this is legal
                //     declare function foo();
                //     declare function bar();
                //     declare function foo();
                // 2. mixing ambient and non-ambient declarations is a separate error that will be reported - do not want to report an extra one
                previous_declaration = None;
            }
            if ast::is_class_like(Some(node), &nodes) && !in_ambient_context {
                has_non_ambient_class = true;
            }
            if ast::is_function_declaration(&nodes[node])
                || ast::is_method_declaration(&nodes[node])
                || ast::is_method_signature_declaration(&nodes[node])
                || ast::is_constructor_declaration(&nodes[node])
            {
                function_declarations.push(node);
                let current_node_flags = self.get_effective_declaration_flags(node, flags_to_check);
                some_node_flags |= current_node_flags;
                all_node_flags &= current_node_flags;
                let optional = crate::utilities::is_optional_declaration(&nodes[node], &nodes);
                some_have_question_token = some_have_question_token || optional;
                all_have_question_token = all_have_question_token && optional;
                let body_is_present = ast::node_is_present(nodes[node].body(), &nodes);
                if body_is_present && body_declaration.is_some() {
                    if is_constructor {
                        multiple_constructor_implementation = true;
                    } else {
                        duplicate_function_declaration = true;
                    }
                } else if previous_declaration.is_some_and(|p| {
                    // `p` may live in a different file's arena than `node`
                    // (symbol declarations span files); resolve it in its own
                    // arena like Go's direct pointer access.
                    let p_nodes = __program.nodes(p.file_index());
                    p_nodes[p].parent == nodes[node].parent
                        && p_nodes[p].end() != nodes[node].pos()
                        && !p_nodes[p].flags.intersects(ast::NodeFlags::REPARSED)
                }) {
                    self.report_implementation_expected_error(
                        previous_declaration.unwrap(),
                        is_constructor,
                    );
                }
                if body_is_present {
                    if body_declaration.is_none() {
                        body_declaration = Some(node);
                    }
                } else {
                    has_overloads = true;
                }
                previous_declaration = Some(node);
                if !in_ambient_context_or_interface {
                    last_seen_non_ambient_declaration = Some(node);
                }
            }
        }
        if multiple_constructor_implementation {
            for &declaration in &function_declarations {
                self.error(
                    Some(declaration),
                    &tsc_diagnostics::Multiple_constructor_implementations_are_not_allowed,
                    &[],
                );
            }
        }
        if duplicate_function_declaration {
            for &declaration in &function_declarations {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((declaration).file_index());
                self.error(
                    Some(
                        ast::get_name_of_declaration(Some(declaration), &nodes)
                            .unwrap_or(declaration),
                    ),
                    &tsc_diagnostics::Duplicate_function_implementation,
                    &[],
                );
            }
        }
        if has_non_ambient_class
            && !is_constructor
            && sym_flags(self, symbol).intersects(ast::SymbolFlags::FUNCTION)
            && !declarations.is_empty()
        {
            let mut related_diagnostics: Vec<ast::diagnostic::DiagnosticRef> = Vec::new();
            for &declaration in &declarations {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((declaration).file_index());
                if ast::is_class_declaration(&nodes[declaration]) {
                    related_diagnostics.push(self.new_diagnostic_for_node(
                        Some(declaration),
                        &tsc_diagnostics::Consider_adding_a_declare_modifier_to_this_class,
                        &[] as &[String],
                    ));
                }
            }
            for &declaration in &declarations {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((declaration).file_index());
                let diagnostic: Option<&'static tsc_diagnostics::Message> =
                    match nodes[declaration].kind {
                        ast::Kind::ClassDeclaration => Some(
                            &tsc_diagnostics::Class_declaration_cannot_implement_overload_list_for_0,
                        ),
                        ast::Kind::FunctionDeclaration => Some(
                            &tsc_diagnostics::Function_with_bodies_can_only_merge_with_classes_that_are_ambient,
                        ),
                        _ => None,
                    };
                if let Some(diagnostic) = diagnostic {
                    let name = sym_name(self, symbol);
                    if let Some(d) = self.error(
                        Some(
                            ast::get_name_of_declaration(Some(declaration), &nodes)
                                .unwrap_or(declaration),
                        ),
                        diagnostic,
                        &[name],
                    ) {
                        ast::diagnostic::lock_diagnostic(&d)
                            .set_related_info(related_diagnostics.clone());
                    }
                }
            }
        }
        // Abstract methods can't have an implementation -- in particular, they don't need one.
        if let Some(last) = last_seen_non_ambient_declaration {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((last).file_index());
            if nodes[last].body().is_none()
                && !ast::has_syntactic_modifier(&nodes[last], ast::ModifierFlags::ABSTRACT)
                && !crate::utilities::is_optional_declaration(&nodes[last], &nodes)
            {
                self.report_implementation_expected_error(last, is_constructor);
            }
        }
        if has_overloads {
            self.check_flag_agreement_between_overloads(
                &declarations,
                body_declaration,
                flags_to_check,
                some_node_flags,
                all_node_flags,
            );
            self.check_question_token_agreement_between_overloads(
                &declarations,
                body_declaration,
                some_have_question_token,
                all_have_question_token,
            );
            if let Some(body_declaration) = body_declaration {
                let signatures = self.get_signatures_of_symbol(Some(symbol));
                let body_signature = self.get_signature_from_declaration(body_declaration);
                for signature in signatures {
                    if !self.is_implementation_compatible_with_overload(body_signature, signature) {
                        let error_node = self.signature_arena.get(signature).declaration;
                        let related = self.new_diagnostic_for_node(
                            Some(body_declaration),
                            &tsc_diagnostics::The_implementation_signature_is_declared_here,
                            &[] as &[String],
                        );
                        if let Some(d) = self.error(
                            error_node,
                            &tsc_diagnostics::This_overload_signature_is_not_compatible_with_its_implementation_signature,
                            &[],
                        ) {
                            ast::diagnostic::lock_diagnostic(&d).add_related_info(Some(related));
                        }
                        break;
                    }
                }
            }
        }
    }

    /// `(c *Checker) getEffectiveDeclarationFlags` (checker.go).
    pub fn get_effective_declaration_flags(
        &mut self,
        n: NodeId,
        flags_to_check: ast::ModifierFlags,
    ) -> ast::ModifierFlags {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((n).file_index());
        self.get_effective_declaration_flags_in(n, flags_to_check, &nodes)
    }

    /// `getEffectiveDeclarationFlags` resolving `n`'s arena through
    /// [`crate::printer_util::resolve_arena_for`] — the declaration transform
    /// passes its emitted arena as `work`, so ids minted mid-transform
    /// resolve against the live buffer rather than the program snapshot.
    pub(crate) fn get_effective_declaration_flags_with(
        &mut self,
        n: NodeId,
        flags_to_check: ast::ModifierFlags,
        work: &[ast::Node],
    ) -> ast::ModifierFlags {
        let __program = self.program.clone().expect("program");
        let nodes = crate::printer_util::resolve_arena_for(&__program, work, n);
        self.get_effective_declaration_flags_in(n, flags_to_check, &nodes)
    }

    fn get_effective_declaration_flags_in(
        &mut self,
        n: NodeId,
        flags_to_check: ast::ModifierFlags,
        nodes: &[ast::Node],
    ) -> ast::ModifierFlags {
        let mut flags = self.get_combined_modifier_flags_in(n, nodes);
        // children of classes (even ambient classes) should not be marked as ambient or export
        // because those flags have no useful semantics there.
        let parent = nodes[n].parent;
        if !parent.is_some_and(|p| {
            ast::is_interface_declaration(&nodes[p])
                || ast::is_class_declaration(&nodes[p])
                || ast::is_class_expression(&nodes[p])
        }) && nodes[n].flags.intersects(ast::NodeFlags::AMBIENT)
        {
            let container = crate::utilities::get_enclosing_container(n, &nodes);
            if container.is_some_and(|container| {
                nodes[container]
                    .flags
                    .intersects(ast::NodeFlags::EXPORT_CONTEXT)
                    && !flags.intersects(ast::ModifierFlags::AMBIENT)
                    && !(parent.is_some_and(|p| ast::is_module_block(&nodes[p]))
                        && parent
                            .and_then(|p| nodes[p].parent)
                            .is_some_and(|gp| ast::is_global_scope_augmentation(&nodes[gp])))
            }) {
                // It is nested in an ambient export context, which means it is automatically exported
                flags |= ast::ModifierFlags::EXPORT;
            }
            flags |= ast::ModifierFlags::AMBIENT;
        }
        flags & flags_to_check
    }

    /// `(c *Checker) isImplementationCompatibleWithOverload` (checker.go).
    pub(crate) fn is_implementation_compatible_with_overload(
        &mut self,
        implementation: SignatureId,
        overload: SignatureId,
    ) -> bool {
        let erased_source = self.get_erased_signature(implementation);
        let erased_target = self.get_erased_signature(overload);
        // First see if the return types are compatible in either direction.
        let source_return_type = self.get_return_type_of_signature(erased_source);
        let target_return_type = self.get_return_type_of_signature(erased_target);
        if target_return_type == self.void_type
            || {
                let relation = self.assignable_relation.clone();
                self.is_type_related_to(target_return_type, source_return_type, &relation)
            }
            || {
                let relation = self.assignable_relation.clone();
                self.is_type_related_to(source_return_type, target_return_type, &relation)
            }
        {
            return self.is_signature_assignable_to(
                erased_source,
                erased_target,
                true, /*ignoreReturnTypes*/
            );
        }
        false
    }

    /// `(c *Checker) checkAllCodePathsInNonVoidFunctionReturnOrThrow` (checker.go).
    pub(crate) fn check_all_code_paths_in_non_void_function_return_or_throw(
        &mut self,
        fn_: NodeId,
        return_type: Option<TypeId>,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((fn_).file_index());
        let function_flags = ast::get_function_flags(Some(&nodes[fn_]));
        let mut t: Option<TypeId> = None;
        if let Some(return_type) = return_type {
            t = self.unwrap_return_type(return_type, function_flags);
        }
        // Functions with an explicitly specified return type that includes `void` or is exactly `any` or `undefined` don't
        // need any return statements.
        if let Some(t) = t {
            if self.maybe_type_of_kind(t, TypeFlags::VOID)
                || tflags(self, t).intersects(TypeFlags::ANY | TypeFlags::UNDEFINED)
            {
                return;
            }
        }
        // If all we have is a function signature, or an arrow function with an expression body, then there is nothing to check.
        // also if HasImplicitReturn flag is not set this means that all codepaths in function body end with return or throw
        if ast::is_method_signature_declaration(&nodes[fn_])
            || ast::node_is_missing(nodes[fn_].body(), &nodes)
            || !nodes[fn_].body().is_some_and(|b| ast::is_block(&nodes[b]))
            || !self.function_has_implicit_return(fn_)
        {
            return;
        }
        let has_explicit_return = nodes[fn_]
            .flags
            .intersects(ast::NodeFlags::HAS_EXPLICIT_RETURN);
        let mut error_node = nodes[fn_].type_();
        if error_node.is_none() {
            if let Some(data) = nodes[fn_].function_like_data() {
                if data.full_signature.is_some() {
                    error_node = data.full_signature;
                }
            }
        }
        let error_node = error_node.unwrap_or(fn_);
        if let Some(t) = t {
            if tflags(self, t).intersects(TypeFlags::NEVER) {
                self.error(
                    Some(error_node),
                    &tsc_diagnostics::A_function_returning_never_cannot_have_a_reachable_end_point,
                    &[],
                );
                return;
            }
            if !has_explicit_return {
                // minimal check: function has syntactic return type annotation and no explicit return statements in the body
                // this function does not conform to the specification.
                self.error(
                    Some(error_node),
                    &tsc_diagnostics::A_function_whose_declared_type_is_neither_undefined_void_nor_any_must_return_a_value,
                    &[],
                );
                return;
            }
            if self.strict_null_checks && !self.is_type_assignable_to(self.undefined_type, t) {
                self.error(
                    Some(error_node),
                    &tsc_diagnostics::Function_lacks_ending_return_statement_and_return_type_does_not_include_undefined,
                    &[],
                );
                return;
            }
        }
        if self.compiler_options.no_implicit_returns == Tristate::True {
            if t.is_none() {
                // If return type annotation is omitted check if function has any explicit return statements.
                // If it does not have any - its inferred return type is void - don't do any checks.
                // Otherwise get inferred return type from function body and report error only if it is not void / anytype
                if !has_explicit_return {
                    return;
                }
                let sig = self.get_signature_from_declaration(fn_);
                let inferred_return_type = self.get_return_type_of_signature(sig);
                if self.is_unwrapped_return_type_undefined_void_or_any(fn_, inferred_return_type) {
                    return;
                }
            }
            self.error(
                Some(error_node),
                &tsc_diagnostics::Not_all_code_paths_return_a_value,
                &[],
            );
        }
    }

    /// `(c *Checker) isUnwrappedReturnTypeUndefinedVoidOrAny` (checker.go).
    pub(crate) fn is_unwrapped_return_type_undefined_void_or_any(
        &mut self,
        fn_: NodeId,
        return_type: TypeId,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((fn_).file_index());
        let t = self.unwrap_return_type(return_type, ast::get_function_flags(Some(&nodes[fn_])));
        t.is_some_and(|t| {
            self.maybe_type_of_kind(t, TypeFlags::VOID)
                || tflags(self, t).intersects(TypeFlags::ANY | TypeFlags::UNDEFINED)
        })
    }

    /// `(c *Checker) checkBlock` (checker.go).
    pub(crate) fn check_block(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Grammar checking for SyntaxKind.Block
        if nodes[node].kind == ast::Kind::Block {
            self.check_grammar_statement_in_ambient_context(node);
        }
        if ast::is_function_or_module_block(&nodes[node], &nodes) {
            let save_flow_analysis_disabled = self.flow_analysis_disabled;
            let statements = nodes[node].statements().unwrap_or(&[]).to_vec();
            self.check_source_elements(&statements);
            self.flow_analysis_disabled = save_flow_analysis_disabled;
        } else {
            let statements = nodes[node].statements().unwrap_or(&[]).to_vec();
            self.check_source_elements(&statements);
        }
        if nodes[node].locals().is_some_and(|l| !l.is_empty()) {
            self.register_for_unused_identifiers_check(node);
        }
    }

    /// `(c *Checker) checkIfStatement` (checker.go).
    pub(crate) fn check_if_statement(&mut self, node: NodeId) {
        self.check_grammar_statement_in_ambient_context(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let expr = nodes[node].expression().expect("if condition");
        let t = self.check_truthiness_expression(expr, CheckMode::NORMAL);
        let data = nodes[node].as_if_statement();
        let (then_statement, else_statement) = (data.then_statement, data.else_statement);
        self.check_testing_known_truthy_callable_or_awaitable_or_enum_member_type(
            expr,
            t,
            then_statement,
        );
        self.check_source_element(then_statement);
        if then_statement.is_some_and(|s| ast::is_empty_statement(&nodes[s])) {
            self.error(
                then_statement,
                &tsc_diagnostics::The_body_of_an_if_statement_cannot_be_the_empty_statement,
                &[],
            );
        }
        self.check_source_element(else_statement);
    }

    /// `(c *Checker) checkTestingKnownTruthyCallableOrAwaitableOrEnumMemberType` (checker.go).
    pub(crate) fn check_testing_known_truthy_callable_or_awaitable_or_enum_member_type(
        &mut self,
        cond_expr: NodeId,
        cond_type: TypeId,
        body: Option<NodeId>,
    ) {
        if !self.strict_null_checks {
            return;
        }
        self.check_testing_known_truthy_types(cond_expr, cond_type, body);
    }

    /// `(c *Checker) checkTestingKnownTruthyTypes` (checker.go).
    pub(crate) fn check_testing_known_truthy_types(
        &mut self,
        cond_expr: NodeId,
        cond_type: TypeId,
        body: Option<NodeId>,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((cond_expr).file_index());
        let mut cond_expr = ast::skip_parentheses(cond_expr, &nodes);
        self.check_testing_known_truthy_type(cond_expr, cond_type, body);
        while ast::is_binary_expression(&nodes[cond_expr])
            && nodes[cond_expr]
                .as_binary_expression()
                .operator_token
                .is_some_and(|ot| {
                    nodes[ot].kind == ast::Kind::BarBarToken
                        || nodes[ot].kind == ast::Kind::QuestionQuestionToken
                })
        {
            cond_expr = ast::skip_parentheses(
                nodes[cond_expr].as_binary_expression().left.expect("left"),
                &nodes,
            );
            self.check_testing_known_truthy_type(cond_expr, cond_type, body);
        }
    }

    /// `(c *Checker) checkTestingKnownTruthyType` (checker.go).
    pub(crate) fn check_testing_known_truthy_type(
        &mut self,
        cond_expr: NodeId,
        cond_type: TypeId,
        body: Option<NodeId>,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((cond_expr).file_index());
        let mut location = cond_expr;
        if ast::is_logical_or_coalescing_binary_expression(&nodes[cond_expr], &nodes) {
            location = ast::skip_parentheses(
                nodes[cond_expr]
                    .as_binary_expression()
                    .right
                    .expect("right"),
                &nodes,
            );
        }
        if ast::is_module_exports_access_expression(&nodes[location], &nodes) {
            return;
        }
        if ast::is_logical_or_coalescing_binary_expression(&nodes[location], &nodes) {
            self.check_testing_known_truthy_types(location, cond_type, body);
            return;
        }
        let mut t = cond_type;
        if location != cond_expr {
            t = self.check_expression(location);
        }
        if tflags(self, t).intersects(TypeFlags::ENUM_LITERAL)
            && ast::is_property_access_expression(&nodes[location])
            && {
                let expr = nodes[location].expression();
                let sym = expr
                    .and_then(|e| self.get_resolved_symbol_or_nil(e))
                    .unwrap_or(self.unknown_symbol);
                sym_flags(self, sym).intersects(ast::SymbolFlags::ENUM)
            }
        {
            // EnumLiteral type at condition with known value is always truthy or always falsy, likely an error
            let __arena___guard_value = self.types.clone();
            let __guard_value = __arena___guard_value.get(t).clone();
            let value = __guard_value.as_literal_type().value.clone();
            let arg = tsc_core::core::if_else(
                evaluator::is_truthy(value.as_ref().expect("literal value")),
                "true",
                "false",
            )
            .to_string();
            self.error(
                Some(location),
                &tsc_diagnostics::This_condition_will_always_return_0,
                &[arg],
            );
            return;
        }
        let is_property_expression_cast = ast::is_property_access_expression(&nodes[location])
            && nodes[location]
                .expression()
                .is_some_and(|e| crate::utilities::is_type_assertion(e, &nodes));
        if !self.has_type_facts(t, TypeFacts::TRUTHY) || is_property_expression_cast {
            return;
        }
        // While it technically should be invalid for any known-truthy value
        // to be tested, we de-scope to functions and Promises unreferenced in
        // the block as a heuristic to identify the most common bugs. There
        // are too many false positives for values sourced from type
        // definitions without strictNullChecks otherwise.
        let call_signatures = self.get_signatures_of_type(t, SignatureKind::Call);
        let is_promise = self.get_awaited_type_of_promise(t).is_some();
        if call_signatures.is_empty() && !is_promise {
            return;
        }
        let mut tested_node: Option<NodeId> = None;
        if ast::is_identifier(&nodes[location]) {
            tested_node = Some(location);
        } else if ast::is_property_access_expression(&nodes[location]) {
            tested_node = nodes[location].name();
        }
        let mut tested_symbol: Option<SymbolId> = None;
        if let Some(tested_node) = tested_node {
            tested_symbol = self.get_symbol_at_location(tested_node, false);
        }
        if tested_symbol.is_none() && !is_promise {
            return;
        }
        let is_used = (tested_symbol.is_some()
            && nodes[cond_expr]
                .parent
                .is_some_and(|p| ast::is_binary_expression(&nodes[p]))
            && self.is_symbol_used_in_binary_expression_chain(
                nodes[cond_expr].parent.unwrap(),
                tested_symbol.unwrap(),
            ))
            || (tested_symbol.is_some()
                && body.is_some()
                && self.is_symbol_used_in_condition_body(
                    cond_expr,
                    body.unwrap(),
                    tested_node,
                    tested_symbol.unwrap(),
                ));
        if !is_used {
            if is_promise {
                let type_name = self.get_type_name_for_error_display(t);
                self.error_and_maybe_suggest_await(
                    location,
                    true,
                    &tsc_diagnostics::This_condition_will_always_return_true_since_this_0_is_always_defined,
                    &[type_name],
                );
            } else {
                self.error(
                    Some(location),
                    &tsc_diagnostics::This_condition_will_always_return_true_since_this_function_is_always_defined_Did_you_mean_to_call_it_instead,
                    &[],
                );
            }
        }
    }

    /// `(c *Checker) isSymbolUsedInBinaryExpressionChain` (checker.go).
    pub(crate) fn is_symbol_used_in_binary_expression_chain(
        &mut self,
        node: NodeId,
        tested_symbol: SymbolId,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut node = Some(node);
        while let Some(n) = node {
            let is_amp_amp = ast::is_binary_expression(&nodes[n])
                && nodes[n]
                    .as_binary_expression()
                    .operator_token
                    .is_some_and(|ot| nodes[ot].kind == ast::Kind::AmpersandAmpersandToken);
            if !is_amp_amp {
                break;
            }
            let right = nodes[n].as_binary_expression().right.expect("right");
            let mut found = false;
            let mut stack = vec![right];
            while let Some(child) = stack.pop() {
                if found {
                    break;
                }
                if ast::is_identifier(&nodes[child])
                    && self.get_symbol_at_location(child, false) == Some(tested_symbol)
                {
                    found = true;
                    break;
                }
                nodes[child].for_each_child(&nodes, &mut |cc| {
                    stack.push(cc);
                    false
                });
            }
            if found {
                return true;
            }
            node = nodes[n].parent;
        }
        false
    }

    /// `(c *Checker) isSymbolUsedInConditionBody` (checker.go).
    pub(crate) fn is_symbol_used_in_condition_body(
        &mut self,
        expr: NodeId,
        body: NodeId,
        tested_node: Option<NodeId>,
        tested_symbol: SymbolId,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((body).file_index());
        let is_expr_ident = ast::is_identifier(&nodes[expr]);
        // Pre-order DFS over `body`'s descendants (Go: `body.ForEachChild(visit)`).
        let mut stack: Vec<NodeId> = Vec::new();
        nodes[body].for_each_child(&nodes, &mut |cc| {
            stack.push(cc);
            false
        });
        while let Some(child_node) = stack.pop() {
            if !ast::is_identifier(&nodes[child_node]) {
                nodes[child_node].for_each_child(&nodes, &mut |cc| {
                    stack.push(cc);
                    false
                });
                continue;
            }
            let child_symbol = self.get_symbol_at_location(child_node, false);
            if child_symbol != Some(tested_symbol) {
                nodes[child_node].for_each_child(&nodes, &mut |cc| {
                    stack.push(cc);
                    false
                });
                continue;
            }
            // If the test was a simple identifier, the above check is sufficient
            if is_expr_ident
                || (tested_node.is_some_and(|t| {
                    ast::is_identifier(&nodes[t])
                        && nodes[t]
                            .parent
                            .is_some_and(|p| ast::is_binary_expression(&nodes[p]))
                }))
            {
                return true;
            }
            // Otherwise we need to ensure the symbol is called on the same target
            let mut tested_expression = tested_node.and_then(|t| nodes[t].parent);
            let mut child_expression = nodes[child_node].parent;
            while let (Some(te), Some(ce)) = (tested_expression, child_expression) {
                if (ast::is_identifier(&nodes[te]) && ast::is_identifier(&nodes[ce]))
                    || (nodes[te].kind == ast::Kind::ThisKeyword
                        && nodes[ce].kind == ast::Kind::ThisKeyword)
                {
                    if self.get_symbol_at_location(te, false)
                        == self.get_symbol_at_location(ce, false)
                    {
                        return true;
                    }
                    break;
                } else if ast::is_property_access_expression(&nodes[te])
                    && ast::is_property_access_expression(&nodes[ce])
                {
                    let tn = nodes[te].name();
                    let cn = nodes[ce].name();
                    let ts = tn.and_then(|t| self.get_symbol_at_location(t, false));
                    let cs = cn.and_then(|c| self.get_symbol_at_location(c, false));
                    if ts != cs {
                        break;
                    }
                    child_expression = nodes[ce].expression();
                    tested_expression = nodes[te].expression();
                } else if ast::is_call_expression(&nodes[te]) && ast::is_call_expression(&nodes[ce])
                {
                    child_expression = nodes[ce].expression();
                    tested_expression = nodes[te].expression();
                } else {
                    break;
                }
            }
        }
        false
    }

    /// `(c *Checker) checkDoStatement` (checker.go).
    pub(crate) fn check_do_statement(&mut self, node: NodeId) {
        self.check_grammar_statement_in_ambient_context(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_source_element(nodes[node].statement());
        self.check_truthiness_expression(
            nodes[node].expression().expect("do expression"),
            CheckMode::NORMAL,
        );
    }

    /// `(c *Checker) checkWhileStatement` (checker.go).
    pub(crate) fn check_while_statement(&mut self, node: NodeId) {
        self.check_grammar_statement_in_ambient_context(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_truthiness_expression(
            nodes[node].expression().expect("while expression"),
            CheckMode::NORMAL,
        );
        self.check_source_element(nodes[node].statement());
    }

    /// `(c *Checker) checkForStatement` (checker.go).
    pub(crate) fn check_for_statement(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !self.check_grammar_statement_in_ambient_context(node) {
            if let Some(init) = nodes[node].initializer() {
                if nodes[init].kind == ast::Kind::VariableDeclarationList {
                    self.check_grammar_variable_declaration_list(init);
                }
            }
        }
        let data = nodes[node].as_for_statement();
        let (initializer, condition, incrementor, statement) = (
            data.initializer,
            data.condition,
            data.incrementor,
            nodes[node].statement(),
        );
        if let Some(initializer) = initializer {
            if ast::is_variable_declaration_list(&nodes[initializer]) {
                self.check_variable_declaration_list(initializer);
            } else {
                self.check_expression(initializer);
            }
        }
        if let Some(condition) = condition {
            self.check_truthiness_expression(condition, CheckMode::NORMAL);
        }
        if let Some(incrementor) = incrementor {
            self.check_expression(incrementor);
        }
        self.check_source_element(statement);
        if nodes[node].locals().is_some() {
            self.register_for_unused_identifiers_check(node);
        }
    }

    /// `(c *Checker) checkForInStatement` (checker.go).
    pub(crate) fn check_for_in_statement(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_grammar_for_in_or_for_of_statement(node);
        let data = nodes[node].as_for_in_or_of_statement();
        let (initializer, expression, statement) =
            (data.initializer, data.expression, data.statement);
        let expr_t = self.check_expression(expression.expect("for-in expression"));
        let right_type = self.get_non_nullable_type_if_needed(expr_t);
        // TypeScript 1.0 spec (April 2014): 5.4
        // In a 'for-in' statement of the form
        // for (let VarDecl in Expr) Statement
        //   VarDecl must be a variable declaration without a type annotation that declares a variable of type Any,
        //   and Expr must be an expression of type Any, an object type, or a type parameter type.
        if ast::is_variable_declaration_list(&nodes[initializer.expect("for-in initializer")]) {
            let initializer = initializer.unwrap();
            let declarations: Vec<NodeId> = nodes[initializer]
                .as_variable_declaration_list()
                .declarations
                .as_ref()
                .map(|l| l.nodes().to_vec())
                .unwrap_or_default();
            if !declarations.is_empty()
                && nodes[declarations[0]]
                    .name()
                    .is_some_and(|n| ast::is_binding_pattern(&nodes[n]))
            {
                self.error(
                    nodes[declarations[0]].name(),
                    &tsc_diagnostics::The_left_hand_side_of_a_for_in_statement_cannot_be_a_destructuring_pattern,
                    &[],
                );
            }
            self.check_variable_declaration_list(initializer);
        } else {
            // In a 'for-in' statement of the form
            // for (Var in Expr) Statement
            //   Var must be an expression classified as a reference of type Any or the String primitive type,
            //   and Expr must be an expression of type Any, an object type, or a type parameter type.
            let var_expr = initializer.expect("for-in initializer");
            let left_type = self.check_expression(var_expr);
            if ast::is_array_literal_expression(&nodes[var_expr])
                || ast::is_object_literal_expression(&nodes[var_expr])
            {
                self.error(
                    Some(var_expr),
                    &tsc_diagnostics::The_left_hand_side_of_a_for_in_statement_cannot_be_a_destructuring_pattern,
                    &[],
                );
            } else if {
                let index_type = self.get_index_type_or_string(right_type);
                !self.is_type_assignable_to(index_type, left_type)
            } {
                self.error(
                    Some(var_expr),
                    &tsc_diagnostics::The_left_hand_side_of_a_for_in_statement_must_be_of_type_string_or_any,
                    &[],
                );
            } else {
                // run check only former check succeeded to avoid cascading errors
                self.check_reference_expression(
                    var_expr,
                    &tsc_diagnostics::The_left_hand_side_of_a_for_in_statement_must_be_a_variable_or_a_property_access,
                    &tsc_diagnostics::The_left_hand_side_of_a_for_in_statement_may_not_be_an_optional_property_access,
                );
            }
        }
        // unknownType is returned i.e. if node.expression is identifier whose name cannot be resolved
        // in this case error about missing name is already reported - do not report extra one
        if right_type == self.never_type
            || !self.is_type_assignable_to_kind(
                right_type,
                TypeFlags::NON_PRIMITIVE | TypeFlags::INSTANTIABLE_NON_PRIMITIVE,
            )
        {
            let arg = self.type_to_string(right_type);
            self.error(
                expression,
                &tsc_diagnostics::The_right_hand_side_of_a_for_in_statement_must_be_of_type_any_an_object_type_or_a_type_parameter_but_here_has_type_0,
                &[arg],
            );
        }
        self.check_source_element(statement);
        if nodes[node].locals().is_some() {
            self.register_for_unused_identifiers_check(node);
        }
    }

    /// `(c *Checker) getIndexTypeOrString` (checker.go).
    pub(crate) fn get_index_type_or_string(&mut self, t: TypeId) -> TypeId {
        let index_t = self.get_index_type(t);
        let index_type = self.get_extract_string_type(index_t);
        tsc_core::core::if_else(
            tflags(self, index_type).intersects(TypeFlags::NEVER),
            self.string_type,
            index_type,
        )
    }

    /// `(c *Checker) checkForOfStatement` (checker.go).
    pub(crate) fn check_for_of_statement(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_grammar_for_in_or_for_of_statement(node);
        let data = nodes[node].as_for_in_or_of_statement();
        let (await_modifier, initializer, expression, statement) = (
            data.await_modifier,
            data.initializer,
            data.expression,
            data.statement,
        );
        let container =
            crate::utilities::get_containing_function_or_class_static_block(node, &nodes);
        if let Some(await_modifier) = await_modifier {
            if container.is_some_and(|c| ast::is_class_static_block_declaration(&nodes[c])) {
                self.grammar_error_on_node(
                    await_modifier,
                    &tsc_diagnostics::X_for_await_loops_cannot_be_used_inside_a_class_static_block,
                    &[],
                );
            } else {
                let function_flags = ast::get_function_flags(container.map(|c| &nodes[c]));
                if (function_flags & (ast::FunctionFlags::INVALID | ast::FunctionFlags::ASYNC))
                    == ast::FunctionFlags::ASYNC
                    && self.language_version
                        < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET.for_await_of
                {
                    // for..await..of in an async function or async generator function prior to ESNext requires the __asyncValues helper
                    self.check_external_emit_helpers(
                        node,
                        crate::types::ExternalEmitHelpers::FOR_AWAIT_OF_INCLUDES,
                    );
                }
            }
        } // Check the LHS and RHS
        // If the LHS is a declaration, just check it as a variable declaration, which will in turn check the RHS
        // via checkRightHandSideOfForOf.
        // If the LHS is an expression, check the LHS, as a destructuring assignment or as a reference.
        // Then check that the RHS is assignable to it.
        if ast::is_variable_declaration_list(&nodes[initializer.expect("for-of initializer")]) {
            self.check_variable_declaration_list(initializer.unwrap());
        } else {
            let var_expr = initializer.expect("for-of initializer");
            let iterated_type = self.check_right_hand_side_of_for_of(node);
            // There may be a destructuring assignment on the left side
            if ast::is_array_literal_expression(&nodes[var_expr])
                || ast::is_object_literal_expression(&nodes[var_expr])
            {
                // iteratedType may be undefined. In this case, we still want to check the structure of
                // varExpr, in particular making sure it's a valid LeftHandSideExpression. But we'd like
                // to short circuit the type relation checking as much as possible, so we pass the unknownType.
                self.check_destructuring_assignment(
                    var_expr,
                    if iterated_type == TypeId::NONE {
                        self.error_type
                    } else {
                        iterated_type
                    },
                    CheckMode::NORMAL,
                    false,
                );
            } else {
                let left_type = self.check_expression(var_expr);
                self.check_reference_expression(
                    var_expr,
                    &tsc_diagnostics::The_left_hand_side_of_a_for_of_statement_must_be_a_variable_or_a_property_access,
                    &tsc_diagnostics::The_left_hand_side_of_a_for_of_statement_may_not_be_an_optional_property_access,
                );
                // iteratedType will be undefined if the rightType was missing properties/signatures
                // required to get its iteratedType (like [Symbol.iterator] or next). This may be
                // because we accessed properties from anyType, or it may have led to an error inside
                // getElementTypeOfIterable.
                if iterated_type != TypeId::NONE {
                    self.check_type_assignable_to_and_optionally_elaborate(
                        iterated_type,
                        left_type,
                        Some(var_expr),
                        expression,
                        None,
                        None,
                    );
                }
            }
        }
        self.check_source_element(statement);
        if nodes[node].locals().is_some() {
            self.register_for_unused_identifiers_check(node);
        }
    }

    /// `(c *Checker) checkBreakOrContinueStatement` (checker.go).
    pub(crate) fn check_break_or_continue_statement(&mut self, node: NodeId) {
        if !self.check_grammar_statement_in_ambient_context(node) {
            self.check_grammar_break_or_continue_statement(node);
        }
    }

    /// `(c *Checker) checkReturnStatement` (checker.go).
    pub(crate) fn check_return_statement(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Always check the return expression so its identifiers are resolved even when the
        // return statement is misplaced (grammar error), keeping diagnostics stable
        // regardless of traversal order.
        let expr_node = nodes[node].expression();
        let mut expr_type = self.undefined_type;
        if let Some(expr_node) = expr_node {
            expr_type = self.check_expression_cached(expr_node);
        }
        if self.check_grammar_statement_in_ambient_context(node) {
            return;
        }
        let container =
            crate::utilities::get_containing_function_or_class_static_block(node, &nodes);
        if container.is_some_and(|c| ast::is_class_static_block_declaration(&nodes[c])) {
            self.grammar_error_on_first_token(
                node,
                &tsc_diagnostics::A_return_statement_cannot_be_used_inside_a_class_static_block,
                &[],
            );
            return;
        }
        let Some(container) = container else {
            self.grammar_error_on_first_token(
                node,
                &tsc_diagnostics::A_return_statement_can_only_be_used_within_a_function_body,
                &[],
            );
            return;
        };
        let signature = self.get_signature_from_declaration(container);
        let return_type = self.get_return_type_of_signature(signature);
        let function_flags = ast::get_function_flags(Some(&nodes[container]));
        if self.strict_null_checks
            || expr_node.is_some()
            || tflags(self, return_type).intersects(TypeFlags::NEVER)
        {
            if ast::is_set_accessor_declaration(&nodes[container]) {
                if expr_node.is_some() {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Setters_cannot_return_a_value,
                        &[],
                    );
                }
            } else if ast::is_constructor_declaration(&nodes[container]) {
                if expr_node.is_some()
                    && !self.check_type_assignable_to_and_optionally_elaborate(
                        expr_type,
                        return_type,
                        Some(node),
                        expr_node,
                        None,
                        None,
                    )
                {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Return_type_of_constructor_signature_must_be_assignable_to_the_instance_type_of_the_class,
                        &[],
                    );
                }
            } else if self.get_return_type_from_annotation(container).is_some() {
                let unwrapped_return_type = self
                    .unwrap_return_type(return_type, function_flags)
                    .unwrap_or(return_type);
                self.check_return_expression(
                    container,
                    unwrapped_return_type,
                    node,
                    nodes[node].expression(),
                    expr_type,
                    false,
                );
            }
        } else if !ast::is_constructor_declaration(&nodes[container])
            && self.compiler_options.no_implicit_returns.is_true()
            && !self.is_unwrapped_return_type_undefined_void_or_any(container, return_type)
        {
            // The function has a return type, but the return statement doesn't have an expression.
            self.error(
                Some(node),
                &tsc_diagnostics::Not_all_code_paths_return_a_value,
                &[],
            );
        }
    }

    /// `(c *Checker) checkReturnExpression` (checker.go).
    ///
    /// When checking an arrow expression such as `(x) => exp`, then `node` is the expression `exp`.
    /// Otherwise, `node` is a return statement.
    pub(crate) fn check_return_expression(
        &mut self,
        container: NodeId,
        unwrapped_return_type: TypeId,
        node: NodeId,
        expr: Option<NodeId>,
        expr_type: TypeId,
        in_conditional_expression: bool,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut unwrapped_expr_type = expr_type;
        let function_flags = ast::get_function_flags(Some(&nodes[container]));
        if let Some(expr) = expr {
            let unwrapped_expr = ast::skip_parentheses(expr, &nodes);
            if ast::is_conditional_expression(&nodes[unwrapped_expr]) {
                let when_true = nodes[unwrapped_expr]
                    .as_conditional_expression()
                    .when_true
                    .expect("whenTrue");
                let when_false = nodes[unwrapped_expr]
                    .as_conditional_expression()
                    .when_false
                    .expect("whenFalse");
                let when_true_type = self.check_expression(when_true);
                self.check_return_expression(
                    container,
                    unwrapped_return_type,
                    node,
                    Some(when_true),
                    when_true_type,
                    true, /*inConditionalExpression*/
                );
                let when_false_type = self.check_expression(when_false);
                self.check_return_expression(
                    container,
                    unwrapped_return_type,
                    node,
                    Some(when_false),
                    when_false_type,
                    true, /*inConditionalExpression*/
                );
                return;
            }
        }
        let in_return_statement = nodes[node].kind == ast::Kind::ReturnStatement;
        if function_flags.intersects(ast::FunctionFlags::ASYNC) {
            unwrapped_expr_type = self.check_awaited_type(
                expr_type,
                false, /*withAlias*/
                Some(node),
                &tsc_diagnostics::The_return_type_of_an_async_function_must_either_be_a_valid_promise_or_must_not_contain_a_callable_then_member,
                &[],
            );
        }
        let mut effective_expr = expr; // The effective expression for diagnostics purposes.
        if let Some(expr) = expr {
            effective_expr = Some(self.get_effective_check_node(expr));
        }
        let error_node = if in_return_statement && !in_conditional_expression {
            node
        } else {
            effective_expr.unwrap_or(node)
        };
        self.check_type_assignable_to_and_optionally_elaborate(
            unwrapped_expr_type,
            unwrapped_return_type,
            Some(error_node),
            effective_expr,
            None,
            None,
        );
    }

    /// `(c *Checker) checkWithStatement` (checker.go).
    pub(crate) fn check_with_statement(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !self.check_grammar_statement_in_ambient_context(node) {
            if nodes[node].flags.intersects(ast::NodeFlags::AWAIT_CONTEXT) {
                self.grammar_error_on_first_token(
                    node,
                    &tsc_diagnostics::X_with_statements_are_not_allowed_in_an_async_function_block,
                    &[],
                );
            }
        }
        if let Some(expr) = nodes[node].expression() {
            self.check_expression(expr);
        }
        let source_file = ast::get_source_file_of_node(Some(node), &nodes);
        if let Some(sf) = source_file
            && !self.has_parse_diagnostics(sf)
        {
            let start = tsc_scanner::scanner::skip_trivia(
                nodes[sf].as_source_file().text(),
                nodes[node].pos(),
            );
            let end = nodes[node]
                .statement()
                .map(|s| nodes[s].pos())
                .unwrap_or(nodes[node].end());
            self.grammar_error_at_pos(
                sf,
                start,
                end - start,
                &tsc_diagnostics::The_with_statement_is_not_supported_All_symbols_in_a_with_block_will_have_type_any,
                &[],
            );
        }
    }

    /// `(c *Checker) checkSwitchStatement` (checker.go).
    pub(crate) fn check_switch_statement(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Grammar checking
        self.check_grammar_statement_in_ambient_context(node);
        let mut first_default_clause: Option<NodeId> = None;
        let mut has_duplicate_default_clause = false;
        let expression_type =
            self.check_expression(nodes[node].expression().expect("switch expression"));
        let case_block = nodes[node].as_switch_statement().case_block;
        let clauses: Vec<NodeId> = case_block
            .and_then(|cb| {
                nodes[cb]
                    .as_case_block()
                    .clauses
                    .as_ref()
                    .map(|l| l.nodes().to_vec())
            })
            .unwrap_or_default();
        for clause in clauses {
            // Grammar check for duplicate default clauses, skip if we already report duplicate default clause
            if ast::is_default_clause(&nodes[clause]) && !has_duplicate_default_clause {
                if first_default_clause.is_none() {
                    first_default_clause = Some(clause);
                } else {
                    self.grammar_error_on_node(
                        clause,
                        &tsc_diagnostics::A_default_clause_cannot_appear_more_than_once_in_a_switch_statement,
                        &[],
                    );
                    has_duplicate_default_clause = true;
                }
            }
            if ast::is_case_clause(&nodes[clause]) {
                let clause_expr = nodes[clause].expression().expect("case expression");
                let case_type = self.check_expression(clause_expr);
                if !self.is_type_equality_comparable_to(expression_type, case_type) {
                    // expressionType is not comparable to caseType, try the reversed check and report errors if it fails
                    self.check_type_comparable_to(
                        case_type,
                        expression_type,
                        Some(clause_expr),
                        None, /*headMessage*/
                    );
                }
            }
            let statements = nodes[clause].statements().unwrap_or(&[]).to_vec();
            self.check_source_elements(&statements);
            if self
                .compiler_options
                .no_fallthrough_cases_in_switch
                .is_true()
            {
                if let Some(flow_node) = nodes[clause]
                    .as_case_or_default_clause()
                    .fallthrough_flow_node
                {
                    if self.is_reachable_flow_node(clause, flow_node) {
                        self.error(
                            Some(clause),
                            &tsc_diagnostics::Fallthrough_case_in_switch,
                            &[],
                        );
                    }
                }
            }
        }
        if case_block.is_some_and(|cb| nodes[cb].locals().is_some()) {
            self.register_for_unused_identifiers_check(case_block.unwrap());
        }
    }

    /// `(c *Checker) checkLabeledStatement` (checker.go).
    pub(crate) fn check_labeled_statement(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let label_node = nodes[node].as_labeled_statement().label.expect("label");
        let label_text = node_text(&nodes, label_node);
        if !self.check_grammar_statement_in_ambient_context(node) {
            let mut current = nodes[node].parent;
            while let Some(c) = current {
                if ast::is_function_like(Some(c), &nodes) {
                    break;
                }
                if ast::is_labeled_statement(&nodes[c])
                    && nodes[c]
                        .label()
                        .is_some_and(|l| &*nodes[l].text(&nodes) == label_text.as_str())
                {
                    self.grammar_error_on_node(
                        label_node,
                        &tsc_diagnostics::Duplicate_label_0,
                        &[label_text.clone()],
                    );
                    break;
                }
                current = nodes[c].parent;
            }
        }
        if nodes[label_node]
            .flags
            .intersects(ast::NodeFlags::UNREACHABLE)
            && self.compiler_options.allow_unused_labels != Tristate::True
        {
            self.error_or_suggestion(
                self.compiler_options.allow_unused_labels == Tristate::False,
                Some(label_node),
                &tsc_diagnostics::Unused_label,
                &[],
            );
        }
        let statement = nodes[node].as_labeled_statement().statement;
        self.check_source_element(statement);
    }

    /// `(c *Checker) checkThrowStatement` (checker.go).
    pub(crate) fn check_throw_statement(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let throw_expr = nodes[node].expression();
        if !self.check_grammar_statement_in_ambient_context(node) {
            if throw_expr
                .is_some_and(|e| ast::is_identifier(&nodes[e]) && nodes[e].text(&nodes).is_empty())
            {
                let throw_expr = throw_expr.unwrap();
                self.grammar_error_at_pos(
                    node,
                    nodes[throw_expr].pos(),
                    0, /*length*/
                    &tsc_diagnostics::Line_break_not_permitted_here,
                    &[],
                );
            }
        }
        if let Some(throw_expr) = throw_expr {
            self.check_expression(throw_expr);
        }
    }

    /// `(c *Checker) checkTryStatement` (checker.go).
    pub(crate) fn check_try_statement(&mut self, node: NodeId) {
        self.check_grammar_statement_in_ambient_context(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let data = nodes[node].as_try_statement();
        let (try_block, catch_clause, finally_block) =
            (data.try_block, data.catch_clause, data.finally_block);
        if let Some(try_block) = try_block {
            self.check_block(try_block);
        }
        if let Some(catch_clause) = catch_clause {
            self.check_catch_clause(catch_clause);
        }
        if let Some(finally_block) = finally_block {
            self.check_block(finally_block);
        }
    }

    /// `(c *Checker) checkCatchClause` (checker.go).
    pub(crate) fn check_catch_clause(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let declaration = nodes[node].as_catch_clause().variable_declaration;
        if let Some(declaration) = declaration {
            self.check_variable_like_declaration(declaration);
            let type_node = nodes[declaration].type_();
            if let Some(type_node) = type_node {
                let t = self.get_type_from_type_node(type_node);
                if !tflags(self, t).intersects(TypeFlags::ANY_OR_UNKNOWN) {
                    self.grammar_error_on_first_token(
                        type_node,
                        &tsc_diagnostics::Catch_clause_variable_type_annotation_must_be_any_or_unknown_if_specified,
                        &[],
                    );
                }
            } else if let Some(initializer) = nodes[declaration].initializer() {
                self.grammar_error_on_first_token(
                    initializer,
                    &tsc_diagnostics::Catch_clause_variable_cannot_have_an_initializer,
                    &[],
                );
            } else {
                let block_locals = nodes[node]
                    .as_catch_clause()
                    .block
                    .and_then(|b| nodes[b].locals().cloned());
                if let Some(block_locals) = block_locals {
                    let node_locals = nodes[node].locals().cloned().unwrap_or_default();
                    for (caught_name, _local) in node_locals.entries() {
                        if let Some(block_local) = block_locals.get(caught_name) {
                            let (value_declaration, flags) = {
                                let arena = self.symbol_arena.borrow();
                                (
                                    arena[block_local.index()].value_declaration,
                                    arena[block_local.index()].flags,
                                )
                            };
                            if value_declaration.is_some()
                                && flags.intersects(ast::SymbolFlags::BLOCK_SCOPED_VARIABLE)
                            {
                                self.grammar_error_on_node(
                                    value_declaration.expect("value declaration"),
                                    &tsc_diagnostics::Cannot_redeclare_identifier_0_in_catch_clause,
                                    &[caught_name.to_string()],
                                );
                            }
                        }
                    }
                }
            }
        }
        let block = nodes[node].as_catch_clause().block;
        if let Some(block) = block {
            self.check_block(block);
        }
    }

    /// `(c *Checker) checkBindingElement` (checker.go).
    pub(crate) fn check_binding_element(&mut self, node: NodeId) {
        self.check_grammar_binding_element(node);
        self.check_variable_like_declaration(node);
    }

    /// `(c *Checker) checkClassDeclaration` (checker.go).
    pub(crate) fn check_class_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let first_decorator = nodes[node]
            .modifier_nodes()
            .unwrap_or(&[])
            .iter()
            .copied()
            .find(|&m| ast::is_decorator(&nodes[m]));
        if self.legacy_decorators
            && first_decorator.is_some()
            && nodes[node].members().unwrap_or(&[]).iter().any(|&p| {
                ast::has_static_modifier(&nodes[p])
                    && ast::is_private_identifier_class_element_declaration(&nodes[p], &nodes)
            })
        {
            self.grammar_error_on_node(
                first_decorator.expect("first decorator"),
                &tsc_diagnostics::Class_decorators_can_t_be_used_with_static_private_identifier_Consider_removing_the_experimental_decorator,
                &[],
            );
        }
        if nodes[node].name().is_none()
            && !ast::has_syntactic_modifier(&nodes[node], ast::ModifierFlags::DEFAULT)
        {
            self.grammar_error_on_first_token(
                node,
                &tsc_diagnostics::A_class_declaration_without_the_default_modifier_must_have_a_name,
                &[],
            );
        }
        self.check_class_like_declaration(node);
        let members = nodes[node].members().unwrap_or(&[]).to_vec();
        self.check_source_elements(&members);
        self.check_constructor_declared_properties(node);
        self.register_for_unused_identifiers_check(node);
    }

    /// `(c *Checker) checkConstructorDeclaredProperties` (checker.go).
    pub(crate) fn check_constructor_declared_properties(&mut self, node: NodeId) {
        if !ast::is_in_js_file(Some(node), &self.program_nodes(node)) {
            return;
        }
        let __h5621_13 = self.get_symbol_of_declaration(node).expect("class symbol");

        let class_type = self.get_declared_type_of_symbol(__h5621_13);
        for property in self.get_properties_of_type(class_type) {
            if let (kind, Some(constructor)) = self.is_constructor_declared_this_property(property)
            {
                if kind == crate::checker_types::ThisAssignmentDeclarationKind::Constructor
                    && self.program_nodes(constructor)[constructor].parent == Some(node)
                {
                    self.get_type_of_symbol(property);
                }
            }
        }
    }

    /// `(c *Checker) checkClassLikeDeclaration` (checker.go).
    pub(crate) fn check_class_like_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_grammar_class_like_declaration(node);
        self.check_decorators(node);
        self.check_collisions_for_declaration_name(node, nodes[node].name());
        let type_parameters = nodes[node].type_parameters().unwrap_or(&[]).to_vec();
        self.check_type_parameters(&type_parameters);
        self.check_exports_on_merged_declarations(node);
        let symbol = self.get_symbol_of_declaration(node).expect("class symbol");
        let class_type = self.get_declared_type_of_symbol(symbol);
        let __arena___guard_this_type = self.types.clone();
        let __guard_this_type = __arena___guard_this_type.get(class_type).clone();
        let this_type = __guard_this_type
            .as_interface_type()
            .and_then(|i| i.this_type);
        let type_with_this = self.get_type_with_this_argument(class_type, None, false);
        let static_type = self.get_type_of_symbol(symbol);
        self.check_type_parameter_lists_identical(symbol);
        self.check_function_or_constructor_symbol(Some(symbol));
        self.check_object_type_for_duplicate_declarations(node, true /*checkPrivateNames*/);

        // Only check for reserved static identifiers on non-ambient context.
        let node_in_ambient_context = nodes[node].flags.intersects(ast::NodeFlags::AMBIENT);
        if !node_in_ambient_context {
            self.check_class_for_static_property_name_conflicts(node);
        }

        if let Some(base_type_node) = ast::get_class_extends_heritage_element(&nodes[node], &nodes)
        {
            let base_type_arguments = nodes[base_type_node]
                .type_arguments()
                .unwrap_or(&[])
                .to_vec();
            self.check_source_elements(&base_type_arguments);
            let base_types = self.get_base_types(class_type);
            if !base_types.is_empty() {
                let base_type = base_types[0];
                self.check_js_doc_augments_tag_matches_extends(node, base_type_node, base_type);
                let base_constructor_type = self.get_base_constructor_type_of_class(class_type);
                let static_base_type = self.get_apparent_type(base_constructor_type);
                self.check_base_type_accessibility(static_base_type, base_type_node);
                let expr = nodes[base_type_node].expression();
                self.check_source_element(expr);
                if !base_type_arguments.is_empty() {
                    self.check_source_elements(&base_type_arguments);
                    for constructor in self.get_constructors_for_type_arguments(
                        static_base_type,
                        &base_type_arguments,
                        base_type_node,
                    ) {
                        let constructor_tps = self
                            .signature_arena
                            .get(constructor)
                            .type_parameters
                            .clone();
                        if !self.check_type_argument_constraints(base_type_node, &constructor_tps) {
                            break;
                        }
                    }
                }
                let base_with_this = self.get_type_with_this_argument(base_type, this_type, false);
                if !self.check_type_assignable_to(type_with_this, base_with_this, None, None) {
                    self.issue_member_specific_error(
                        node,
                        type_with_this,
                        base_with_this,
                        &tsc_diagnostics::Class_0_incorrectly_extends_base_class_1,
                    );
                } else {
                    // Report static side error only when instance type is assignable
                    let base_no_sigs = self.get_type_without_signatures(static_base_type);
                    let name_node = nodes[node].name().unwrap_or(node);
                    self.check_type_assignable_to(
                        static_type,
                        base_no_sigs,
                        Some(name_node),
                        Some(
                            &tsc_diagnostics::Class_static_side_0_incorrectly_extends_base_class_static_side_1,
                        ),
                    );
                }
                if tflags(self, base_constructor_type).intersects(TypeFlags::TYPE_VARIABLE) {
                    if !self.is_mixin_constructor_type(static_type) {
                        self.error(
                            Some(nodes[node].name().unwrap_or(node)),
                            &tsc_diagnostics::A_mixin_class_must_have_a_constructor_with_a_single_rest_parameter_of_type_any,
                            &[],
                        );
                    } else {
                        let construct_signatures = self.get_signatures_of_type(
                            base_constructor_type,
                            SignatureKind::Construct,
                        );
                        if construct_signatures.iter().any(|&s| {
                            self.signature_arena
                                .get(s)
                                .flags
                                .intersects(crate::types::SignatureFlags::ABSTRACT)
                        }) && !ast::has_syntactic_modifier(
                            &nodes[node],
                            ast::ModifierFlags::ABSTRACT,
                        ) {
                            self.error(
                                Some(nodes[node].name().unwrap_or(node)),
                                &tsc_diagnostics::A_mixin_class_that_extends_from_a_type_variable_containing_an_abstract_construct_signature_must_also_be_declared_abstract,
                                &[],
                            );
                        }
                    }
                }
                if !(self
                    .types_handle()
                    .get(static_base_type)
                    .symbol
                    .is_some_and(|s| sym_flags(self, s).intersects(ast::SymbolFlags::CLASS)))
                    && !tflags(self, base_constructor_type).intersects(TypeFlags::TYPE_VARIABLE)
                {
                    // When the static base type is a "class-like" constructor function (but not actually a class), we verify
                    // that all instantiated base constructor signatures return the same type.
                    let constructors = self.get_instantiated_constructors_for_type_arguments(
                        static_base_type,
                        &base_type_arguments,
                        base_type_node,
                    );
                    if !constructors.iter().all(|&sig| {
                        let rt = self.get_return_type_of_signature(sig);
                        self.is_type_identical_to(rt, base_type)
                    }) {
                        self.error(
                            nodes[base_type_node].expression(),
                            &tsc_diagnostics::Base_constructors_must_all_have_the_same_return_type,
                            &[],
                        );
                    }
                }
                self.check_kinds_of_property_member_overrides(class_type, base_type);
            }
        }
        self.check_members_for_override_modifier(node, class_type, type_with_this, static_type);
        let implemented_type_nodes: Vec<NodeId> =
            ast::get_implements_heritage_clause_elements(&nodes[node], &nodes)
                .map(|s| s.to_vec())
                .unwrap_or_default();
        for type_ref_node in implemented_type_nodes {
            if ast::is_expression_with_type_arguments(&nodes[type_ref_node]) {
                if let Some(expr) = nodes[type_ref_node].expression() {
                    if !ast::is_entity_name_expression(&nodes[expr], &nodes)
                        || ast::is_optional_chain(&nodes[expr])
                    {
                        self.error(
                            Some(expr),
                            &tsc_diagnostics::A_class_can_only_implement_an_identifier_Slashqualified_name_with_optional_type_arguments,
                            &[],
                        );
                    }
                }
            }
            self.check_type_reference_node(type_ref_node);
            let tn_t = self.get_type_from_type_node(type_ref_node);
            let t = self.get_reduced_type(tn_t);
            if !crate::utilities::is_error_type(&self.types, t) {
                if self.is_valid_base_type(t) {
                    let generic_diag = if self
                        .types_handle()
                        .get(t)
                        .symbol
                        .is_some_and(|s| sym_flags(self, s).intersects(ast::SymbolFlags::CLASS))
                    {
                        &tsc_diagnostics::Class_0_incorrectly_implements_class_1_Did_you_mean_to_extend_1_and_inherit_its_members_as_a_subclass
                    } else {
                        &tsc_diagnostics::Class_0_incorrectly_implements_interface_1
                    };
                    let base_with_this = self.get_type_with_this_argument(t, this_type, false);
                    if !self.check_type_assignable_to(type_with_this, base_with_this, None, None) {
                        self.issue_member_specific_error(
                            node,
                            type_with_this,
                            base_with_this,
                            generic_diag,
                        );
                    }
                } else {
                    self.error(
                        Some(type_ref_node),
                        &tsc_diagnostics::A_class_can_only_implement_an_object_type_or_intersection_of_object_types_with_statically_known_members,
                        &[],
                    );
                }
            }
        }
        self.check_index_constraints(class_type, Some(symbol), false /*isStaticIndex*/);
        self.check_index_constraints(static_type, Some(symbol), true /*isStaticIndex*/);
        self.check_class_or_interface_for_duplicate_index_signatures(node);
        self.check_property_initialization(node);
    }

    /// `(c *Checker) checkJSDocAugmentsTagMatchesExtends` (checker.go).
    pub(crate) fn check_js_doc_augments_tag_matches_extends(
        &mut self,
        node: NodeId,
        base_type_node: NodeId,
        base_type: TypeId,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !ast::is_in_js_file(Some(node), &nodes) {
            return;
        }
        let file = ast::get_source_file_of_node(Some(node), &nodes);
        for j in ast::eager_js_doc(&nodes, node, file) {
            let Some(tags) = nodes[j].as_js_doc().tags.clone() else {
                continue;
            };
            for &tag in tags.nodes.iter() {
                if nodes[tag].kind != ast::Kind::JSDocAugmentsTag {
                    continue;
                }
                let source_type_node = nodes[tag].class_name();
                if let Some(source_type_node) = source_type_node {
                    let st = self.get_type_from_type_node(source_type_node);
                    if self.is_type_identical_to(st, base_type) {
                        continue;
                    }
                    let target_name = nodes[base_type_node].expression().and_then(|e| {
                        crate::grammarchecks::get_identifier_from_entity_name_expression(e, &nodes)
                    });
                    let source_name = nodes[source_type_node].expression().and_then(|e| {
                        crate::grammarchecks::get_identifier_from_entity_name_expression(e, &nodes)
                    });
                    if target_name.is_some() && source_name.is_some() {
                        let tag_name = nodes[tag].tag_name().map(|tn| node_text(&nodes, tn));
                        let (source_name, target_name) =
                            (source_name.unwrap(), target_name.unwrap());
                        self.error(
                            Some(source_name),
                            &tsc_diagnostics::JSDoc_0_1_does_not_match_the_extends_2_clause,
                            &[
                                tag_name.unwrap_or_default(),
                                node_text(&nodes, source_name),
                                node_text(&nodes, target_name),
                            ],
                        );
                    }
                }
            }
        }
    }

    /// `(c *Checker) checkClassForStaticPropertyNameConflicts` (checker.go).
    pub(crate) fn check_class_for_static_property_name_conflicts(&mut self, node: NodeId) {
        if self.compiler_options.get_use_define_for_class_fields() {
            return;
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        for &member in nodes[node].members().unwrap_or(&[]) {
            let member_name_node = nodes[member].name();
            let is_static_member = ast::is_static(&nodes[member]);
            if is_static_member {
                if let Some(member_name_node) = member_name_node {
                    let (member_name, _) =
                        self.get_effective_property_name_for_property_name_node(member_name_node);
                    match member_name.as_str() {
                        "name" | "length" | "caller" | "arguments" => {
                            let member_sym =
                                self.get_symbol_of_declaration(node).expect("member symbol");
                            let arg1 = self.symbol_to_string(member_sym);
                            self.error(
                                Some(member_name_node),
                                &tsc_diagnostics::Static_property_0_conflicts_with_built_in_property_Function_0_of_constructor_function_1,
                                &[member_name, arg1],
                            );
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    /// `(c *Checker) checkTypeParameterListsIdentical` (checker.go).
    ///
    /// Check that type parameter lists are identical across multiple declarations
    pub(crate) fn check_type_parameter_lists_identical(&mut self, symbol: SymbolId) {
        if self.symbol_arena.borrow()[symbol.index()]
            .declarations
            .len()
            == 1
        {
            return;
        }
        let links = self.declared_type_links.get(symbol);
        if !links.type_parameters_checked {
            links.type_parameters_checked = true;
            let declarations = self.get_class_or_interface_declarations_of_symbol(symbol);
            if declarations.len() <= 1 {
                return;
            }
            let t = self.get_declared_type_of_symbol(symbol);
            let __arena___guard_target_parameters = self.types.clone();
            let __guard_target_parameters = __arena___guard_target_parameters.get(t).clone();
            let target_parameters = __guard_target_parameters
                .as_interface_type()
                .map(|i| i.local_type_parameters().to_vec())
                .unwrap_or_default();
            if !self.are_type_parameters_identical(
                &declarations,
                &target_parameters,
                &mut |decl: NodeId, nodes: &[ast::Node]| {
                    nodes[decl].type_parameters().unwrap_or(&[]).to_vec()
                },
            ) {
                // Report an error on every conflicting declaration.
                let name = self.symbol_to_string(symbol);
                for &declaration in &declarations {
                    let __name_node = self.program_nodes(declaration)[declaration].name();
                    self.error(
                        __name_node,
                        &tsc_diagnostics::All_declarations_of_0_must_have_identical_type_parameters,
                        &[name.clone()],
                    );
                }
            }
        }
    }

    /// `(c *Checker) getClassOrInterfaceDeclarationsOfSymbol` (checker.go).
    pub(crate) fn get_class_or_interface_declarations_of_symbol(
        &mut self,
        symbol: SymbolId,
    ) -> Vec<NodeId> {
        sym_declarations(self, symbol)
            .into_iter()
            .filter(|&d| {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((d).file_index());
                ast::is_class_declaration(&nodes[d]) || ast::is_interface_declaration(&nodes[d])
            })
            .collect()
    }

    /// `(c *Checker) areTypeParametersIdentical` (checker.go).
    pub(crate) fn are_type_parameters_identical(
        &mut self,
        declarations: &[NodeId],
        target_parameters: &[TypeId],
        get_type_parameter_declarations: &mut dyn FnMut(NodeId, &[ast::Node]) -> Vec<NodeId>,
    ) -> bool {
        let max_type_argument_count = target_parameters.len();
        let min_type_argument_count = self.get_min_type_argument_count(target_parameters);
        for &declaration in declarations {
            // If this declaration has too few or too many type parameters, we report an error
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((declaration).file_index());
            let source_parameters = get_type_parameter_declarations(declaration, &nodes);
            if source_parameters.len() < min_type_argument_count as usize
                || source_parameters.len() > max_type_argument_count
            {
                return false;
            }
            for (i, &source) in source_parameters.iter().enumerate() {
                let target = target_parameters[i];
                // If the type parameter node does not have the same name as the resolved type
                // parameter at this position, we report an error.
                let source_name = nodes[source]
                    .name()
                    .map(|n| node_text(&nodes, n))
                    .unwrap_or_default();
                let target_name = tsymbol(self, target)
                    .map(|s| sym_name(self, s))
                    .unwrap_or_default();
                if source_name != target_name {
                    return false;
                }
                // If the type parameter node does not have an identical constraintNode as the resolved
                // type parameter at this position, we report an error.
                let constraint_node = nodes[source].as_type_parameter_declaration().constraint;
                let target_constraint = self.get_constraint_of_type_parameter(target);
                // relax check if later interface augmentation has no constraint, it's more broad and is OK to merge with
                // a more constrained interface (this could be generalized to a full hierarchy check, but that's maybe overkill)
                if let (Some(constraint_node), Some(target_constraint)) =
                    (constraint_node, target_constraint)
                {
                    let st = self.get_type_from_type_node(constraint_node);
                    if !self.is_type_identical_to(st, target_constraint) {
                        return false;
                    }
                }
                // If the type parameter node has a default and it is not identical to the default
                // for the type parameter at this position, we report an error.
                let default_node = nodes[source].as_type_parameter_declaration().default_type;
                let target_default = self.get_default_from_type_parameter(target);
                if let (Some(default_node), Some(target_default)) = (default_node, target_default) {
                    let st = self.get_type_from_type_node(default_node);
                    if !self.is_type_identical_to(st, target_default) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// `(c *Checker) checkBaseTypeAccessibility` (checker.go).
    pub(crate) fn check_base_type_accessibility(&mut self, t: TypeId, node: NodeId) {
        let signatures = self.get_signatures_of_type(t, SignatureKind::Construct);
        if let Some(accessibility_error) =
            self.get_constructor_accessibility_error(node, &signatures, ast::ModifierFlags::PRIVATE)
        {
            let declaring_symbol = self.types.get_ref(accessibility_error.declaring_class)
                .symbol
                .unwrap_or(self.unknown_symbol);
            let name = self.get_fully_qualified_name(declaring_symbol, None);
            self.error(
                Some(node),
                &tsc_diagnostics::Cannot_extend_a_class_0_Class_constructor_is_marked_as_private,
                &[name],
            );
        }
    }

    /// `(c *Checker) issueMemberSpecificError` (checker.go).
    pub(crate) fn issue_member_specific_error(
        &mut self,
        node: NodeId,
        type_with_this: TypeId,
        base_with_this: TypeId,
        broad_diag: &'static tsc_diagnostics::Message,
    ) {
        // iterate over all implemented properties and issue errors on each one which isn't compatible, rather than the class as a whole, if possible
        let mut issued_member_error = false;
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        for &member in nodes[node].members().unwrap_or(&[]) {
            if ast::is_static(&nodes[member]) {
                continue;
            }
            if let Some(declared_prop) = self.get_symbol_of_declaration(member) {
                let declared_prop_name = sym_name(self, declared_prop);
                if declared_prop_name != ast::INTERNAL_SYMBOL_NAME_COMPUTED {
                    let prop = self.get_property_of_type(type_with_this, &declared_prop_name);
                    let base_prop = self.get_property_of_type(base_with_this, &declared_prop_name);
                    if let (Some(prop), Some(base_prop)) = (prop, base_prop) {
                        let prop_t = self.get_type_of_symbol(prop);
                        let base_prop_t = self.get_type_of_symbol(base_prop);
                        let mut diags: Vec<ast::diagnostic::DiagnosticRef> = Vec::new();
                        if !self.check_type_assignable_to_ex(
                            prop_t,
                            base_prop_t,
                            Some(nodes[member].name().unwrap_or(member)),
                            None, /*headMessage*/
                            Some(&mut diags),
                        ) {
                            let arg0 = self.symbol_to_string(declared_prop);
                            let arg1 = self.type_to_string(type_with_this);
                            let arg2 = self.type_to_string(base_with_this);
                            self.add_diagnostic(&ast::diagnostic::new_diagnostic_chain(
                                diags.first(),
                                &tsc_diagnostics::Property_0_in_type_1_is_not_assignable_to_the_same_property_in_base_type_2,
                                &[arg0, arg1, arg2],
                            ));
                            issued_member_error = true;
                        }
                    }
                }
            }
        }
        if !issued_member_error {
            // check again with diagnostics to generate a less-specific error
            self.check_type_assignable_to(
                type_with_this,
                base_with_this,
                Some(nodes[node].name().unwrap_or(node)),
                Some(broad_diag),
            );
        }
    }

    /// `(c *Checker) getTypeWithoutSignatures` (checker.go).
    pub(crate) fn get_type_without_signatures(&mut self, t: TypeId) -> TypeId {
        if tflags(self, t).intersects(TypeFlags::OBJECT) {
            let resolved = self.resolve_structured_type_members(t);
            let (has_signatures, members, properties) = {
                let guard_st = self.types.get_ref(resolved);
                let st = &guard_st.as_object_type().structured_type;
                (
                    !st.signatures.is_empty(),
                    st.members.clone(),
                    st.properties.clone(),
                )
            };
            if has_signatures {
                let result = self.new_object_type(ObjectFlags::ANONYMOUS, tsymbol(self, t));
                {
                    let __arena_r = self.types.clone();
                    let mut r = __arena_r.get_mut(result);
                    r.object_flags |= ObjectFlags::MEMBERS_RESOLVED;
                    let data = r.as_object_type_mut().expect("object type");
                    data.structured_type.members = members;
                    data.structured_type.properties = properties;
                }
                return result;
            }
        } else if tflags(self, t).intersects(TypeFlags::INTERSECTION) {
            let __arena___guard_types = self.types.clone();
            let __guard_types = __arena___guard_types.get(t).clone();
            let types = __guard_types
                .as_intersection_type()
                .union_or_intersection
                .types
                .clone();
            let mapped: Vec<TypeId> = types
                .iter()
                .map(|&t| self.get_type_without_signatures(t))
                .collect();
            return self.get_intersection_type(&mapped);
        }
        t
    }

    /// `(c *Checker) checkKindsOfPropertyMemberOverrides` (checker.go).
    pub(crate) fn check_kinds_of_property_member_overrides(
        &mut self,
        t: TypeId,
        base_type: TypeId,
    ) {
        // TypeScript 1.0 spec (April 2014): 8.2.3
        // A derived class inherits all members from its base class it doesn't override.
        // ... (see Go source for the full comment)
        struct MemberInfo {
            missed_properties: Vec<String>,
            base_type_name: String,
            type_name: String,
        }
        let mut not_implemented_info: FxHashMap<Option<NodeId>, MemberInfo> = FxHashMap::default();
        'base_property_check: for base_property in self.get_properties_of_type(base_type) {
            let base = self.get_target_symbol(base_property);
            if sym_flags(self, base).intersects(ast::SymbolFlags::PROTOTYPE) {
                continue;
            }
            let base_name = sym_name(self, base);
            let Some(base_symbol) = self.get_property_of_object_type(t, &base_name) else {
                continue;
            };
            let derived = self.get_target_symbol(base_symbol);
            let base_declaration_flags =
                crate::utilities::get_declaration_modifier_flags_from_symbol(self, base);
            // In order to resolve whether the inherited method was overridden in the base class or not,
            // we compare the Symbols obtained. Since getTargetSymbol returns the symbol on the *uninstantiated*
            // type declaration, derived and base resolve to the same symbol even in the case of generic classes.
            if derived == base {
                // derived class inherits base without override/redeclaration.
                if base_declaration_flags.intersects(ast::ModifierFlags::ABSTRACT) {
                    // It is an error to inherit an abstract member without implementing it or being declared abstract.
                    // If there is no declaration for the derived class (as in the case of class expressions),
                    // then the class cannot be declared abstract.
                    let t_symbol = self.types.get_ref(t).symbol;
                    let derived_class_decl = t_symbol.and_then(|s| {
                        sym_declarations(self, s).iter().copied().find(|&d| {
                            let __program = self.program.clone().expect("program");
                            let dn = __program.nodes((d).file_index());
                            ast::is_class_like(Some(d), &dn)
                        })
                    });
                    if derived_class_decl.is_none() || {
                        let d = derived_class_decl.unwrap();
                        let __program = self.program.clone().expect("program");
                        let dn = __program.nodes((d).file_index());
                        !ast::has_syntactic_modifier(&dn[d], ast::ModifierFlags::ABSTRACT)
                    } {
                        // Searches other base types for a declaration that would satisfy the inherited abstract member.
                        // (The class may have more than one base type via declaration merging with an interface with the
                        // same name.)
                        for other_base_type in self.get_base_types(t) {
                            if other_base_type == base_type {
                                continue;
                            }
                            if let Some(other_base_symbol) =
                                self.get_property_of_object_type(other_base_type, &base_name)
                            {
                                if base != self.get_target_symbol(other_base_symbol) {
                                    // Derived property exists elsewhere.
                                    continue 'base_property_check;
                                }
                            }
                        }
                        let base_type_name = self.type_to_string(base_type);
                        let type_name = self.type_to_string(t);
                        let missed = self.symbol_to_string(base_property);
                        let info = not_implemented_info
                            .entry(derived_class_decl)
                            .or_insert_with(|| MemberInfo {
                                missed_properties: Vec::new(),
                                base_type_name,
                                type_name,
                            });
                        info.missed_properties.push(missed);
                    }
                }
            } else {
                // derived overrides base.
                let derived_declaration_flags =
                    crate::utilities::get_declaration_modifier_flags_from_symbol(self, derived);
                if base_declaration_flags.intersects(ast::ModifierFlags::PRIVATE)
                    || derived_declaration_flags.intersects(ast::ModifierFlags::PRIVATE)
                {
                    // either base or derived property is private - not override, skip it
                    continue;
                }
                let mut error_message: Option<&'static tsc_diagnostics::Message> = None;
                let base_property_flags =
                    sym_flags(self, base) & ast::SymbolFlags::PROPERTY_OR_ACCESSOR;
                let derived_property_flags =
                    sym_flags(self, derived) & ast::SymbolFlags::PROPERTY_OR_ACCESSOR;
                if base_property_flags != ast::SymbolFlags::NONE
                    && derived_property_flags != ast::SymbolFlags::NONE
                {
                    // property/accessor is overridden with property/accessor
                    let base_check_flags = {
                        let arena = self.symbol_arena.borrow();
                        arena[base.index()].check_flags
                    };
                    if base_check_flags.intersects(ast::checkflags::CheckFlags::MAPPED)
                        || sym_value_declaration(self, derived).is_some_and(|vd| {
                            let __program = self.program.clone().expect("program");
                            let dn = __program.nodes((vd).file_index());
                            ast::is_binary_expression(&dn[vd])
                        })
                        || self.are_properties_abstract_or_interface(base, base_declaration_flags)
                    {
                        // when the base property is abstract or from an interface, base/derived flags don't need to match
                        // for intersection properties, this must be true of *any* of the declarations, for others it must be true of *all*
                        // same when the derived property is from an assignment
                        continue;
                    }
                    let overridden_instance_property = base_property_flags
                        != ast::SymbolFlags::PROPERTY
                        && derived_property_flags == ast::SymbolFlags::PROPERTY;
                    let overridden_instance_accessor = base_property_flags
                        == ast::SymbolFlags::PROPERTY
                        && derived_property_flags != ast::SymbolFlags::PROPERTY;
                    if overridden_instance_property || overridden_instance_accessor {
                        let error_message = if overridden_instance_property {
                            &tsc_diagnostics::X_0_is_defined_as_an_accessor_in_class_1_but_is_overridden_here_in_2_as_an_instance_property
                        } else {
                            &tsc_diagnostics::X_0_is_defined_as_a_property_in_class_1_but_is_overridden_here_in_2_as_an_accessor
                        };
                        let location = sym_value_declaration(self, derived).map(|vd| {
                            let __program = self.program.clone().expect("program");
                            let dn = __program.nodes((vd).file_index());
                            ast::get_name_of_declaration(Some(vd), &dn).unwrap_or(vd)
                        });
                        let arg0 = self.symbol_to_string(base);
                        let arg1 = self.type_to_string(base_type);
                        let arg2 = self.type_to_string(t);
                        self.error(location, error_message, &[arg0, arg1, arg2]);
                    } else if self.compiler_options.get_use_define_for_class_fields() {
                        let derived_declarations = sym_declarations(self, derived);
                        let uninitialized = derived_declarations.iter().copied().find(|&d| {
                            let __program = self.program.clone().expect("program");
                            let dn = __program.nodes((d).file_index());
                            ast::is_property_declaration(&dn[d]) && dn[d].initializer().is_none()
                        });
                        if let Some(uninitialized) = uninitialized {
                            let __program = self.program.clone().expect("program");
                            let un = __program.nodes((uninitialized).file_index());
                            let derived_flags = sym_flags(self, derived);
                            if !derived_flags.intersects(ast::SymbolFlags::TRANSIENT)
                                && !base_declaration_flags.intersects(ast::ModifierFlags::ABSTRACT)
                                && !derived_declaration_flags
                                    .intersects(ast::ModifierFlags::ABSTRACT)
                                && !derived_declarations.iter().any(|&d| {
                                    self.program_nodes(d)[d]
                                        .flags
                                        .intersects(ast::NodeFlags::AMBIENT)
                                })
                            {
                                let t_symbol = self.types.get_ref(t).symbol;
                                let constructor = t_symbol
                                    .and_then(|s| {
                                        sym_declarations(self, s).iter().copied().find(|&d| {
                                            let __program = self.program.clone().expect("program");
                                            let dn = __program.nodes((d).file_index());
                                            ast::is_class_like(Some(d), &dn)
                                        })
                                    })
                                    .and_then(|class_decl| {
                                        let __program = self.program.clone().expect("program");
                                        let dn = __program.nodes((class_decl).file_index());
                                        ast::find_constructor_declaration(&dn[class_decl], &dn)
                                    });
                                let prop_name = un[uninitialized].name();
                                if un[uninitialized]
                                    .postfix_token()
                                    .is_some_and(|t| un[t].kind == ast::Kind::ExclamationToken)
                                    || constructor.is_none()
                                    || !prop_name.is_some_and(|p| ast::is_identifier(&un[p]))
                                    || !self.strict_null_checks
                                    || !self.is_property_initialized_in_constructor(
                                        prop_name.expect("propName"),
                                        t,
                                        constructor.expect("constructor"),
                                    )
                                {
                                    let location = sym_value_declaration(self, derived).map(|vd| {
                                        let __program = self.program.clone().expect("program");
                                        let dn = __program.nodes((vd).file_index());
                                        ast::get_name_of_declaration(Some(vd), &dn).unwrap_or(vd)
                                    });
                                    let arg0 = self.symbol_to_string(base);
                                    let arg1 = self.type_to_string(base_type);
                                    self.error(
                                        location,
                                        &tsc_diagnostics::Property_0_will_overwrite_the_base_property_in_1_If_this_is_intentional_add_an_initializer_Otherwise_add_a_declare_modifier_or_remove_the_redundant_declaration,
                                        &[arg0, arg1],
                                    );
                                }
                            }
                        }
                    }
                    // correct case
                    continue;
                } else if self.is_prototype_symbol(base) {
                    if self.is_prototype_symbol(derived)
                        || sym_flags(self, derived).intersects(ast::SymbolFlags::PROPERTY)
                    {
                        // method is overridden with method or property -- correct case
                        continue;
                    } else {
                        error_message = Some(
                            &tsc_diagnostics::Class_0_defines_instance_member_function_1_but_extended_class_2_defines_it_as_instance_member_accessor,
                        );
                    }
                } else if sym_flags(self, base).intersects(ast::SymbolFlags::ACCESSOR) {
                    error_message = Some(
                        &tsc_diagnostics::Class_0_defines_instance_member_accessor_1_but_extended_class_2_defines_it_as_instance_member_function,
                    );
                } else {
                    error_message = Some(
                        &tsc_diagnostics::Class_0_defines_instance_member_property_1_but_extended_class_2_defines_it_as_instance_member_function,
                    );
                }
                let location = sym_value_declaration(self, derived).map(|vd| {
                    let __program = self.program.clone().expect("program");
                    let dn = __program.nodes((vd).file_index());
                    ast::get_name_of_declaration(Some(vd), &dn).unwrap_or(vd)
                });
                let arg0 = self.type_to_string(base_type);
                let arg1 = self.symbol_to_string(base);
                let arg2 = self.type_to_string(t);
                self.error(
                    location,
                    error_message.expect("errorMessage"),
                    &[arg0, arg1, arg2],
                );
            }
        }
        for (error_node, member_info) in not_implemented_info {
            match member_info.missed_properties.len() {
                1 => {
                    let missed_property = &member_info.missed_properties[0];
                    if error_node
                        .is_some_and(|e| ast::is_class_expression(&self.program_nodes(e)[e]))
                    {
                        self.error(
                            error_node,
                            &tsc_diagnostics::Non_abstract_class_expression_does_not_implement_inherited_abstract_member_0_from_class_1,
                            &[missed_property.clone(), member_info.base_type_name.clone()],
                        );
                    } else {
                        self.error(
                            error_node,
                            &tsc_diagnostics::Non_abstract_class_0_does_not_implement_inherited_abstract_member_1_from_class_2,
                            &[
                                member_info.type_name.clone(),
                                missed_property.clone(),
                                member_info.base_type_name.clone(),
                            ],
                        );
                    }
                }
                n if n > 5 => {
                    let missed_properties = crate::utilities::quoted_and_comma_separated(
                        &member_info.missed_properties[..4],
                    );
                    let remaining = (n - 4).to_string();
                    if error_node
                        .is_some_and(|e| ast::is_class_expression(&self.program_nodes(e)[e]))
                    {
                        self.error(
                            error_node,
                            &tsc_diagnostics::Non_abstract_class_expression_is_missing_implementations_for_the_following_members_of_0_Colon_1_and_2_more,
                            &[member_info.base_type_name.clone(), missed_properties, remaining],
                        );
                    } else {
                        self.error(
                            error_node,
                            &tsc_diagnostics::Non_abstract_class_0_is_missing_implementations_for_the_following_members_of_1_Colon_2_and_3_more,
                            &[
                                member_info.type_name.clone(),
                                member_info.base_type_name.clone(),
                                missed_properties,
                                remaining,
                            ],
                        );
                    }
                }
                _ => {
                    let missed_properties = crate::utilities::quoted_and_comma_separated(
                        &member_info.missed_properties,
                    );
                    if error_node
                        .is_some_and(|e| ast::is_class_expression(&self.program_nodes(e)[e]))
                    {
                        self.error(
                            error_node,
                            &tsc_diagnostics::Non_abstract_class_expression_is_missing_implementations_for_the_following_members_of_0_Colon_1,
                            &[member_info.base_type_name.clone(), missed_properties],
                        );
                    } else {
                        self.error(
                            error_node,
                            &tsc_diagnostics::Non_abstract_class_0_is_missing_implementations_for_the_following_members_of_1_Colon_2,
                            &[
                                member_info.type_name.clone(),
                                member_info.base_type_name.clone(),
                                missed_properties,
                            ],
                        );
                    }
                }
            }
        }
    }

    /// `(c *Checker) arePropertiesAbstractOrInterface` (checker.go).
    pub(crate) fn are_properties_abstract_or_interface(
        &mut self,
        base: SymbolId,
        base_declaration_flags: ast::ModifierFlags,
    ) -> bool {
        let check_flags = self.symbol_arena.borrow()[base.index()].check_flags;
        let declarations = sym_declarations(self, base);
        if check_flags.intersects(ast::checkflags::CheckFlags::SYNTHETIC) {
            return declarations
                .iter()
                .any(|&d| self.is_property_abstract_or_interface(d, base_declaration_flags));
        }
        declarations
            .iter()
            .all(|&d| self.is_property_abstract_or_interface(d, base_declaration_flags))
    }

    /// `isPrototypeProperty` (checker.go) — pure predicate on a symbol.
    fn is_prototype_symbol(&self, symbol: SymbolId) -> bool {
        let arena = self.symbol_arena.borrow();
        let s = &arena[symbol.index()];
        s.flags.intersects(ast::SymbolFlags::METHOD)
            || s.check_flags
                .intersects(ast::checkflags::CheckFlags::SYNTHETIC_METHOD)
    }

    /// `(c *Checker) isPropertyAbstractOrInterface` (checker.go).
    pub(crate) fn is_property_abstract_or_interface(
        &mut self,
        declaration: NodeId,
        base_declaration_flags: ast::ModifierFlags,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((declaration).file_index());
        nodes[declaration]
            .parent
            .is_some_and(|p| ast::is_interface_declaration(&nodes[p]))
            || base_declaration_flags.intersects(ast::ModifierFlags::ABSTRACT)
                && (!ast::is_property_declaration(&nodes[declaration])
                    || nodes[declaration].initializer().is_none())
    }

    /// `(c *Checker) checkMembersForOverrideModifier` (checker.go).
    pub(crate) fn check_members_for_override_modifier(
        &mut self,
        node: NodeId,
        t: TypeId,
        type_with_this: TypeId,
        static_type: TypeId,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut base_with_this: Option<TypeId> = None;
        let base_type_node = ast::get_class_extends_heritage_element(&nodes[node], &nodes);
        if base_type_node.is_some() {
            let base_types = self.get_base_types(t);
            if let Some(&first) = base_types.first() {
                let __arena___guard_this_arg = self.types.clone();
                let __guard_this_arg = __arena___guard_this_arg.get(t).clone();
                let this_arg = __guard_this_arg
                    .as_interface_type()
                    .and_then(|i| i.this_type);
                base_with_this = Some(self.get_type_with_this_argument(first, this_arg, false));
            }
        }
        let base_static_type = self.get_base_constructor_type_of_class(t);
        for &member in nodes[node].members().unwrap_or(&[]) {
            if !ast::has_ambient_modifier(&nodes[member]) {
                if ast::is_constructor_declaration(&nodes[member]) {
                    for &param in nodes[member].parameters().unwrap_or(&[]) {
                        if ast::is_parameter_property_declaration(&nodes[param], &nodes[member]) {
                            self.check_member_for_override_modifier(
                                node,
                                static_type,
                                base_static_type,
                                base_with_this,
                                t,
                                type_with_this,
                                param,
                            );
                        }
                    }
                } else {
                    self.check_member_for_override_modifier(
                        node,
                        static_type,
                        base_static_type,
                        base_with_this,
                        t,
                        type_with_this,
                        member,
                    );
                }
            }
        }
    }

    /// `(c *Checker) checkMemberForOverrideModifier` (checker.go).
    pub(crate) fn check_member_for_override_modifier(
        &mut self,
        node: NodeId,
        static_type: TypeId,
        base_static_type: TypeId,
        base_with_this: Option<TypeId>,
        t: TypeId,
        type_with_this: TypeId,
        member: NodeId,
    ) {
        let Some(symbol) = self.get_symbol_of_declaration(member) else {
            return;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((member).file_index());
        let member_has_override_modifier =
            ast::has_syntactic_modifier(&nodes[member], ast::ModifierFlags::OVERRIDE);
        let member_has_abstract_modifier = ast::has_abstract_modifier(&nodes[member]);
        let member_is_static = ast::is_static(&nodes[member]);
        let member_is_parameter_property = ast::is_parameter_declaration(&nodes[member]);
        self.check_member_for_override_modifier_worker(
            node,
            static_type,
            base_static_type,
            base_with_this,
            t,
            type_with_this,
            member_has_override_modifier,
            member_has_abstract_modifier,
            member_is_static,
            member_is_parameter_property,
            symbol,
            Some(member),
        );
    }

    /// `(c *Checker) getMemberOverrideModifierStatus` (checker.go).
    pub fn get_member_override_modifier_status(
        &mut self,
        node: NodeId,
        member: NodeId,
        member_symbol: Option<SymbolId>,
    ) -> crate::types::MemberOverrideStatus {
        use crate::types::MemberOverrideStatus;
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((member).file_index());
        if nodes[member].name().is_none() || member_symbol.is_none() {
            return MemberOverrideStatus::NONE;
        }
        let member_symbol = member_symbol.unwrap();
        let Some(class_symbol) = self.get_symbol_of_declaration(node) else {
            return MemberOverrideStatus::NONE;
        };
        let t = self.get_declared_type_of_symbol(class_symbol);
        let type_with_this = self.get_type_with_this_argument(t, None, false);
        let static_type = self.get_type_of_symbol(class_symbol);
        let mut base_with_this: Option<TypeId> = None;
        if ast::get_class_extends_heritage_element(&nodes[node], &nodes).is_some() {
            let base_types = self.get_base_types(t);
            if let Some(&first) = base_types.first() {
                let __arena___guard_this_arg = self.types.clone();
                let __guard_this_arg = __arena___guard_this_arg.get(t).clone();
                let this_arg = __guard_this_arg
                    .as_interface_type()
                    .and_then(|i| i.this_type);
                base_with_this = Some(self.get_type_with_this_argument(first, this_arg, false));
            }
        }
        let base_ctor = self.get_base_constructor_type_of_class(t);
        self.check_member_for_override_modifier_worker(
            node,
            static_type,
            base_ctor,
            base_with_this,
            t,
            type_with_this,
            ast::has_syntactic_modifier(&nodes[member], ast::ModifierFlags::OVERRIDE),
            ast::has_abstract_modifier(&nodes[member]),
            ast::is_static(&nodes[member]),
            false, /*memberIsParameterProperty*/
            member_symbol,
            None, /*errorNode*/
        )
    }

    /// `(c *Checker) checkMemberForOverrideModifierWorker` (checker.go).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_member_for_override_modifier_worker(
        &mut self,
        node: NodeId,
        static_type: TypeId,
        base_static_type: TypeId,
        base_with_this: Option<TypeId>,
        t: TypeId,
        type_with_this: TypeId,
        member_has_override_modifier: bool,
        member_has_abstract_modifier: bool,
        member_is_static: bool,
        member_is_parameter_property: bool,
        member: SymbolId,
        error_node: Option<NodeId>,
    ) -> crate::types::MemberOverrideStatus {
        use crate::types::MemberOverrideStatus;
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let is_js = ast::is_in_js_file(Some(node), &nodes);
        let member_value_declaration = {
            let arena = self.symbol_arena.borrow();
            arena[member.index()].value_declaration
        };
        if member_has_override_modifier
            && member_value_declaration.is_some_and(|vd| {
                ast::is_class_element(&nodes[vd])
                    && nodes[vd]
                        .name()
                        .is_some_and(|n| self.is_non_bindable_dynamic_name(n))
            })
        {
            if let Some(error_node) = error_node {
                let message = if is_js {
                    &tsc_diagnostics::This_member_cannot_have_a_JSDoc_comment_with_an_override_tag_because_its_name_is_dynamic
                } else {
                    &tsc_diagnostics::This_member_cannot_have_an_override_modifier_because_its_name_is_dynamic
                };
                self.error(Some(error_node), message, &[]);
            }
            return MemberOverrideStatus::HAS_INVALID_OVERRIDE;
        }
        if base_with_this.is_some()
            && (member_has_override_modifier
                || self.compiler_options.no_implicit_override.is_true())
        {
            let base_with_this = base_with_this.unwrap();
            let this_type = if member_is_static {
                static_type
            } else {
                type_with_this
            };
            let base_type = if member_is_static {
                base_static_type
            } else {
                base_with_this
            };
            let member_name = sym_name(self, member);
            let prop = self.get_property_of_type(this_type, &member_name);
            let base_prop = self.get_property_of_type(base_type, &member_name);
            if prop.is_some() && base_prop.is_none() && member_has_override_modifier {
                if let Some(error_node) = error_node {
                    let suggestion = self
                        .get_suggested_symbol_for_nonexistent_class_member(&member_name, base_type);
                    if let Some(suggestion) = suggestion {
                        let message = if is_js {
                            &tsc_diagnostics::This_member_cannot_have_a_JSDoc_comment_with_an_override_tag_because_it_is_not_declared_in_the_base_class_0_Did_you_mean_1
                        } else {
                            &tsc_diagnostics::This_member_cannot_have_an_override_modifier_because_it_is_not_declared_in_the_base_class_0_Did_you_mean_1
                        };
                        let arg0 = self.type_to_string(base_with_this);
                        let arg1 = self.symbol_to_string(suggestion);
                        self.error(Some(error_node), message, &[arg0, arg1]);
                    } else {
                        let message = if is_js {
                            &tsc_diagnostics::This_member_cannot_have_a_JSDoc_comment_with_an_override_tag_because_it_is_not_declared_in_the_base_class_0
                        } else {
                            &tsc_diagnostics::This_member_cannot_have_an_override_modifier_because_it_is_not_declared_in_the_base_class_0
                        };
                        let arg0 = self.type_to_string(base_with_this);
                        self.error(Some(error_node), message, &[arg0]);
                    }
                }
                return MemberOverrideStatus::HAS_INVALID_OVERRIDE;
            }
            if prop.is_some()
                && base_prop.is_some()
                && !sym_declarations(self, base_prop.unwrap()).is_empty()
                && self.compiler_options.no_implicit_override.is_true()
                && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
            {
                let base_prop = base_prop.unwrap();
                let base_has_abstract = sym_declarations(self, base_prop)
                    .iter()
                    .any(|&d| ast::has_abstract_modifier(&self.program_nodes(d)[d]));
                if member_has_override_modifier {
                    return MemberOverrideStatus::NONE;
                }
                if !base_has_abstract {
                    if let Some(error_node) = error_node {
                        let message: &'static tsc_diagnostics::Message =
                            if member_is_parameter_property {
                                if is_js {
                                    &tsc_diagnostics::This_parameter_property_must_have_a_JSDoc_comment_with_an_override_tag_because_it_overrides_a_member_in_the_base_class_0
                                } else {
                                    &tsc_diagnostics::This_parameter_property_must_have_an_override_modifier_because_it_overrides_a_member_in_base_class_0
                                }
                            } else if is_js {
                                &tsc_diagnostics::This_member_must_have_a_JSDoc_comment_with_an_override_tag_because_it_overrides_a_member_in_the_base_class_0
                            } else {
                                &tsc_diagnostics::This_member_must_have_an_override_modifier_because_it_overrides_a_member_in_the_base_class_0
                            };
                        let arg0 = self.type_to_string(base_with_this);
                        self.error(Some(error_node), message, &[arg0]);
                    }
                    return MemberOverrideStatus::NEEDS_OVERRIDE;
                }
                if member_has_abstract_modifier {
                    if let Some(error_node) = error_node {
                        let arg0 = self.type_to_string(base_with_this);
                        self.error(
                            Some(error_node),
                            &tsc_diagnostics::This_member_must_have_an_override_modifier_because_it_overrides_an_abstract_method_that_is_declared_in_the_base_class_0,
                            &[arg0],
                        );
                    }
                    return MemberOverrideStatus::NEEDS_OVERRIDE;
                }
            }
        } else if member_has_override_modifier {
            if let Some(error_node) = error_node {
                let message = if is_js {
                    &tsc_diagnostics::This_member_cannot_have_a_JSDoc_comment_with_an_override_tag_because_its_containing_class_0_does_not_extend_another_class
                } else {
                    &tsc_diagnostics::This_member_cannot_have_an_override_modifier_because_its_containing_class_0_does_not_extend_another_class
                };
                let arg0 = self.type_to_string(t);
                self.error(Some(error_node), message, &[arg0]);
            }
            return MemberOverrideStatus::HAS_INVALID_OVERRIDE;
        }
        MemberOverrideStatus::NONE
    }

    /// `(c *Checker) getSuggestedSymbolForNonexistentClassMember` (checker.go).
    pub(crate) fn get_suggested_symbol_for_nonexistent_class_member(
        &mut self,
        name: &str,
        base_type: TypeId,
    ) -> Option<SymbolId> {
        let props = self.get_properties_of_type(base_type);
        self.get_spelling_suggestion_for_name(name, props, ast::SymbolFlags::CLASS_MEMBER)
    }

    /// `(c *Checker) checkIndexConstraints` (checker.go).
    pub(crate) fn check_index_constraints(
        &mut self,
        t: TypeId,
        symbol: Option<SymbolId>,
        is_static_index: bool,
    ) {
        let index_infos = self.get_index_infos_of_type(t);
        if index_infos.is_empty() {
            return;
        }
        for prop in self.get_properties_of_object_type(t) {
            let prop_flags = sym_flags(self, prop);
            if !(is_static_index && prop_flags.intersects(ast::SymbolFlags::PROTOTYPE)) {
                let prop_name_type = self.get_literal_type_from_property(
                    prop,
                    TypeFlags::STRING_OR_NUMBER_LITERAL_OR_UNIQUE,
                    true, /*includeNonPublic*/
                );
                let prop_type = self.get_non_missing_type_of_symbol(prop);
                self.check_index_constraint_for_property(t, prop, prop_name_type, prop_type);
            }
        }
        let type_declaration = symbol.and_then(|s| sym_value_declaration(self, s));
        if let Some(type_declaration) = type_declaration {
            let __program = self.program.clone().expect("program");
            let dn = __program.nodes((type_declaration).file_index());
            if ast::is_class_like(Some(type_declaration), &dn) {
                for &member in dn[type_declaration].members().unwrap_or(&[]) {
                    // Only process instance properties against instance index signatures and static properties against static index signatures
                    if ast::is_static(&dn[member]) == is_static_index
                        && !self.has_bindable_name(member)
                    {
                        let symbol = self.get_symbol_of_declaration(member);
                        let prop_name_type = self.get_type_of_expression(
                            dn[member]
                                .name()
                                .and_then(|n| dn[n].expression())
                                .expect("computed name expression"),
                        );
                        let prop_type = symbol
                            .map(|s| self.get_non_missing_type_of_symbol(s))
                            .unwrap_or(self.error_type);
                        self.check_index_constraint_for_property(
                            t,
                            symbol.expect("member symbol"),
                            prop_name_type,
                            prop_type,
                        );
                    }
                }
            }
        }
        if index_infos.len() > 1 {
            for &info in &index_infos {
                self.check_index_constraint_for_index_signature(t, info);
            }
        }
    }

    /// `(c *Checker) checkIndexConstraintForProperty` (checker.go).
    pub(crate) fn check_index_constraint_for_property(
        &mut self,
        t: TypeId,
        prop: SymbolId,
        prop_name_type: TypeId,
        prop_type: TypeId,
    ) {
        let declaration = sym_value_declaration(self, prop);
        let name = declaration.and_then(|d| {
            let __program = self.program.clone().expect("program");
            let dn = __program.nodes((d).file_index());
            ast::get_name_of_declaration(Some(d), &dn)
        });
        if name.is_some_and(|n| {
            let __program = self.program.clone().expect("program");
            let nn = __program.nodes((n).file_index());
            ast::is_private_identifier(&nn[n])
        }) {
            return;
        }
        let index_infos = self.get_applicable_index_infos(t, prop_name_type);
        if index_infos.is_empty() {
            return;
        }
        let t_symbol = self.types.get_ref(t).symbol;
        let mut interface_declaration: Option<NodeId> = None;
        if tobject_flags(self, t).intersects(ObjectFlags::INTERFACE) {
            interface_declaration = t_symbol.and_then(|s| {
                sym_declarations(self, s)
                    .iter()
                    .copied()
                    .find(|&d| self.program_nodes(d)[d].kind == ast::Kind::InterfaceDeclaration)
            });
        }
        let prop_declaration = if declaration.is_some_and(|d| {
            let __program = self.program.clone().expect("program");
            let dn = __program.nodes((d).file_index());
            ast::is_binary_expression(&dn[d])
        }) || name.is_some_and(|n| {
            let __program = self.program.clone().expect("program");
            let nn = __program.nodes((n).file_index());
            ast::is_computed_property_name(&nn[n])
        }) {
            declaration
        } else {
            None
        };
        let local_prop_declaration = if self.get_parent_of_symbol(prop) == t_symbol {
            declaration
        } else {
            None
        };
        for &info in &index_infos {
            let info_declaration = self.index_info_arena.get(info).declaration;
            let local_index_declaration = if info_declaration.is_some_and(|d| {
                let sym = self.get_symbol_of_declaration(d);
                sym.is_some() && self.get_parent_of_symbol(sym.unwrap()) == t_symbol
            }) {
                info_declaration
            } else {
                None
            };
            // We check only when (a) the property is declared in the containing type, or (b) the applicable index signature is declared
            // in the containing type, or (c) the containing type is an interface and no base interface contains both the property and
            // the index signature (i.e. property and index signature are declared in separate inherited interfaces).
            let mut error_node = local_prop_declaration.or(local_index_declaration);
            if error_node.is_none() && interface_declaration.is_some() && {
                let prop_name = sym_name(self, prop);
                let info_key_type = self.index_info_arena.get(info).key_type;
                let base_types = self.get_base_types(t);
                !base_types.iter().any(|&base| {
                    self.get_property_of_object_type(base, &prop_name).is_some()
                        && self
                            .get_index_type_of_type(base, info_key_type.unwrap_or(self.error_type))
                            .is_some()
                })
            } {
                error_node = interface_declaration;
            }
            let info_key_type = self.index_info_arena.get(info).key_type;
            let info_value_type = self.index_info_arena.get(info).value_type;
            if error_node.is_some()
                && !self
                    .is_type_assignable_to(prop_type, info_value_type.unwrap_or(self.error_type))
            {
                let arg0 = self.symbol_to_string(prop);
                let arg1 = self.type_to_string(prop_type);
                let arg2 = self.type_to_string(info_key_type.unwrap_or(self.error_type));
                let arg3 = self.type_to_string(info_value_type.unwrap_or(self.error_type));
                let diagnostic = self.new_diagnostic_for_node(
                    error_node,
                    &tsc_diagnostics::Property_0_of_type_1_is_not_assignable_to_2_index_type_3,
                    &[arg0, arg1, arg2, arg3],
                );
                if prop_declaration.is_some() && error_node != prop_declaration {
                    let arg0 = self.symbol_to_string(prop);
                    let related = self.new_diagnostic_for_node(
                        prop_declaration,
                        &tsc_diagnostics::X_0_is_declared_here,
                        &[arg0],
                    );
                    ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(related));
                }
                self.add_diagnostic(&diagnostic);
            }
        }
    }

    /// `(c *Checker) checkIndexConstraintForIndexSignature` (checker.go).
    pub(crate) fn check_index_constraint_for_index_signature(
        &mut self,
        t: TypeId,
        check_info: IndexInfoId,
    ) {
        let (check_key_type, check_value_type, declaration) = {
            let info = self.index_info_arena.get(check_info);
            (info.key_type, info.value_type, info.declaration)
        };
        let index_infos =
            self.get_applicable_index_infos(t, check_key_type.unwrap_or(self.error_type));
        if index_infos.is_empty() {
            return;
        }
        let t_symbol = self.types.get_ref(t).symbol;
        let mut interface_declaration: Option<NodeId> = None;
        if tobject_flags(self, t).intersects(ObjectFlags::INTERFACE) {
            interface_declaration = t_symbol.and_then(|s| {
                sym_declarations(self, s)
                    .iter()
                    .copied()
                    .find(|&d| self.program_nodes(d)[d].kind == ast::Kind::InterfaceDeclaration)
            });
        }
        let local_check_declaration = if declaration.is_some_and(|d| {
            let sym = self.get_symbol_of_declaration(d);
            sym.is_some() && self.get_parent_of_symbol(sym.unwrap()) == t_symbol
        }) {
            declaration
        } else {
            None
        };
        for &info in &index_infos {
            if info == check_info {
                continue;
            }
            let (info_key_type, info_value_type, info_declaration) = {
                let info = self.index_info_arena.get(info);
                (info.key_type, info.value_type, info.declaration)
            };
            let local_index_declaration = if info_declaration.is_some_and(|d| {
                let sym = self.get_symbol_of_declaration(d);
                sym.is_some() && self.get_parent_of_symbol(sym.unwrap()) == t_symbol
            }) {
                info_declaration
            } else {
                None
            };
            // We check only when (a) the check index signature is declared in the containing type, or (b) the applicable index
            // signature is declared in the containing type, or (c) the containing type is an interface and no base interface contains
            // both index signatures (i.e. the index signatures are declared in separate inherited interfaces).
            let mut error_node = local_check_declaration.or(local_index_declaration);
            if error_node.is_none() && interface_declaration.is_some() && {
                let base_types = self.get_base_types(t);
                !base_types.iter().any(|&base| {
                    self.get_index_info_of_type(base, check_key_type.unwrap_or(self.error_type))
                        .is_some()
                        && self
                            .get_index_type_of_type(base, info_key_type.unwrap_or(self.error_type))
                            .is_some()
                })
            } {
                error_node = interface_declaration;
            }
            if error_node.is_some()
                && !self.is_type_assignable_to(
                    check_value_type.unwrap_or(self.error_type),
                    info_value_type.unwrap_or(self.error_type),
                )
            {
                let arg0 = self.type_to_string(check_key_type);
                let arg1 = self.type_to_string(check_value_type);
                let arg2 = self.type_to_string(info_key_type);
                let arg3 = self.type_to_string(info_value_type);
                self.error(
                    error_node,
                    &tsc_diagnostics::X_0_index_type_1_is_not_assignable_to_2_index_type_3,
                    &[arg0, arg1, arg2, arg3],
                );
            }
        }
    }

    /// `(c *Checker) checkClassOrInterfaceForDuplicateIndexSignatures` (checker.go).
    pub(crate) fn check_class_or_interface_for_duplicate_index_signatures(&mut self, node: NodeId) {
        // Only check the type once
        if let Some(symbol) = self.get_symbol_of_declaration(node) {
            let links = self.declared_type_links.get(symbol);
            if !links.index_signatures_checked {
                links.index_signatures_checked = true;
                self.check_type_for_duplicate_index_signatures(node);
            }
        }
    }

    /// `(c *Checker) checkTypeForDuplicateIndexSignatures` (checker.go).
    pub(crate) fn check_type_for_duplicate_index_signatures(&mut self, node: NodeId) {
        // TypeScript 1.0 spec (April 2014)
        // 3.7.4: An object type can contain at most one string index signature and one numeric index signature.
        // 8.5: A class declaration can have at most one string index member declaration and one numeric index member declaration
        let index_symbol = self
            .get_symbol_of_declaration(node)
            .and_then(|s| self.get_index_symbol(s));
        let Some(index_symbol) = index_symbol else {
            return;
        };
        let declarations = sym_declarations(self, index_symbol);
        if declarations.len() <= 1 {
            return;
        }
        let mut index_signature_map: FxHashMap<TypeId, Vec<NodeId>> = FxHashMap::default();
        let mut order: Vec<TypeId> = Vec::new();
        for &declaration in &declarations {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((declaration).file_index());
            if ast::is_index_signature_declaration(&nodes[declaration]) {
                let parameters = nodes[declaration].parameters().unwrap_or(&[]).to_vec();
                if parameters.len() == 1 {
                    if let Some(param_type_node) = nodes[parameters[0]].type_() {
                        let param_type = self.get_type_from_type_node(param_type_node);
                        // Bind first — a `for`-head temporary would hold the
                        // arena read guard for the whole loop body.
                        let distributed =
                            self.types.get_ref(param_type).distributed(param_type);
                        for t in distributed {
                            index_signature_map
                                .entry(t)
                                .or_insert_with(|| {
                                    order.push(t);
                                    Vec::new()
                                })
                                .push(declaration);
                        }
                    }
                }
            }
            // Do nothing for late-bound index signatures: allow these to duplicate one another and explicit indexes
        }
        for t in order {
            let declarations = &index_signature_map[&t];
            if declarations.len() > 1 {
                let arg0 = self.type_to_string(t);
                for &declaration in declarations {
                    self.error(
                        Some(declaration),
                        &tsc_diagnostics::Duplicate_index_signature_for_type_0,
                        &[arg0.clone()],
                    );
                }
            }
        }
    }

    /// `(c *Checker) checkPropertyInitialization` (checker.go).
    pub(crate) fn check_property_initialization(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !self.strict_null_checks
            || !self.strict_property_initialization
            || nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
        {
            return;
        }
        let constructor = ast::find_constructor_declaration(&nodes[node], &nodes);
        for &member in nodes[node].members().unwrap_or(&[]) {
            if nodes[member]
                .modifier_flags()
                .intersects(ast::ModifierFlags::AMBIENT)
            {
                continue;
            }
            if !ast::is_static(&nodes[member]) && self.is_property_without_initializer(member) {
                let prop_name = nodes[member].name();
                if prop_name.is_some_and(|p| {
                    ast::is_identifier(&nodes[p])
                        || ast::is_private_identifier(&nodes[p])
                        || ast::is_computed_property_name(&nodes[p])
                }) {
                    let prop_name = prop_name.unwrap();
                    let member_sym = self
                        .get_symbol_of_declaration(member)
                        .expect("member symbol");
                    let t = self.get_type_of_symbol(member_sym);
                    if !(tflags(self, t).intersects(TypeFlags::ANY_OR_UNKNOWN)
                        || self.contains_undefined_type(t))
                    {
                        if constructor.is_none()
                            || !self.is_property_initialized_in_constructor(
                                prop_name,
                                t,
                                constructor.unwrap(),
                            )
                        {
                            let arg = tsc_scanner::utilities::declaration_name_to_string(
                                Some(prop_name),
                                &nodes,
                            );
                            self.error(
                                Some(prop_name),
                                &tsc_diagnostics::Property_0_has_no_initializer_and_is_not_definitely_assigned_in_the_constructor,
                                &[arg],
                            );
                        }
                    }
                }
            }
        }
    }

    /// `(c *Checker) isPropertyWithoutInitializer` (checker.go).
    pub(crate) fn is_property_without_initializer(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        ast::is_property_declaration(&nodes[node])
            && !ast::has_abstract_modifier(&nodes[node])
            && !nodes[node]
                .postfix_token()
                .is_some_and(|t| nodes[t].kind == ast::Kind::ExclamationToken)
            && nodes[node].initializer().is_none()
    }

    /// `(c *Checker) isPropertyInitializedInStaticBlocks` (checker.go).
    pub(crate) fn is_property_initialized_in_static_blocks(
        &mut self,
        prop_name: NodeId,
        prop_type: TypeId,
        static_blocks: &[NodeId],
        start_pos: i32,
        end_pos: i32,
    ) -> bool {
        for &static_block in static_blocks {
            // static block must be within the provided range as they are evaluated in document order (unlike constructors)
            let __program = self.program.clone().expect("program");
            let bn = __program.nodes((static_block).file_index());
            if bn[static_block].pos() >= start_pos && bn[static_block].pos() <= end_pos {
                let flow_node = bn[static_block]
                    .as_class_static_block_declaration()
                    .return_flow_node;
                let reference =
                    self.make_this_property_reference(prop_name, static_block, flow_node);
                let opt_type = self.get_optional_type(prop_type, false);
                let flow_type = self.get_flow_type_of_reference_ex(
                    reference,
                    prop_type,
                    Some(opt_type),
                    None,
                    None,
                );
                if !self.contains_undefined_type(flow_type) {
                    return true;
                }
            }
        }
        false
    }

    /// `(c *Checker) isPropertyInitializedInConstructor` (checker.go).
    pub(crate) fn is_property_initialized_in_constructor(
        &mut self,
        prop_name: NodeId,
        prop_type: TypeId,
        constructor: NodeId,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let flow_node = __program.nodes((constructor).file_index())[constructor]
            .as_constructor_declaration()
            .return_flow_node;
        let reference = self.make_this_property_reference(prop_name, constructor, flow_node);
        let opt_type = self.get_optional_type(prop_type, false);
        let flow_type =
            self.get_flow_type_of_reference_ex(reference, prop_type, Some(opt_type), None, None);
        !self.contains_undefined_type(flow_type)
    }

    /// `isPropertyInitializedIn{Constructor,StaticBlocks}` helper — Go's
    ///
    /// ```ignore
    /// reference := c.factory.New{Property,Element}AccessExpression(c.factory.NewKeywordExpression(KindThisKeyword), nil, propName, NodeFlagsNone)
    /// reference.Expression().Parent = reference
    /// reference.Parent = parent
    /// reference.FlowNodeData().FlowNode = flowNode
    /// ```
    ///
    /// The port writes into the containing file's arena via the
    /// sibling-owned `program_nodes_mut`/`set_program_node` convention
    /// (mirroring `create_synthetic_expression` call sites in checker_b.rs).
    fn make_this_property_reference(
        &mut self,
        prop_name: NodeId,
        parent: NodeId,
        flow_node: Option<ast::FlowNodeId>,
    ) -> NodeId {
        let argument = {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((prop_name).file_index());
            if ast::is_computed_property_name(&nodes[prop_name]) {
                nodes[prop_name].expression()
            } else {
                None
            }
        };
        let file_index = prop_name.file_index();
        // PORT(borrowck): take the arena through a cloned `Rc<Program>` so the
        // RefMut borrows a local, not `*self` (factory calls need `self`).
        let program = self.program.clone().expect("program");
        let mut arena = program.nodes_mut(file_index);
        let old_file_index = self.factory.file_index();
        self.factory.set_file_index(file_index);
        let this = self
            .factory
            .new_keyword_expression(&mut arena, ast::Kind::ThisKeyword);
        let reference = if argument.is_some() {
            self.factory.new_element_access_expression(
                &mut arena,
                Some(this),
                None,
                argument,
                ast::NodeFlags::NONE,
            )
        } else {
            self.factory.new_property_access_expression(
                &mut arena,
                Some(this),
                None,
                Some(prop_name),
                ast::NodeFlags::NONE,
            )
        };
        self.factory.set_file_index(old_file_index);
        // `reference.Expression().Parent = reference`
        arena[this].parent = Some(reference);
        // `reference.Parent = parent` + `reference.FlowNodeData().FlowNode = flowNode`
        let reference_node = &mut arena[reference];
        reference_node.parent = Some(parent);
        if let Some(data) = reference_node.data.flow_node_data_mut() {
            data.flow_node = flow_node;
        }
        reference
    }

    // ======== checker.go ~5098 — interface / enum / module checking ========

    /// `(c *Checker) checkInterfaceDeclaration` (checker.go).
    pub(crate) fn check_interface_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !self.check_grammar_modifiers(node) {
            self.check_grammar_interface_declaration(node);
        }
        if !crate::utilities::container_allows_block_scoped_variable(
            nodes[node].parent.expect("interface parent"),
            &nodes,
        ) {
            self.grammar_error_on_node(
                node,
                &tsc_diagnostics::X_0_declarations_can_only_be_declared_inside_a_block,
                &["interface".to_string()],
            );
        }
        let type_parameters = nodes[node].type_parameters().unwrap_or(&[]).to_vec();
        self.check_type_parameters(&type_parameters);
        if let Some(name) = nodes[node].name() {
            self.check_type_name_is_reserved(name, &tsc_diagnostics::Interface_name_cannot_be_0);
        }
        self.check_exports_on_merged_declarations(node);
        let symbol = self.get_symbol_of_declaration(node);
        self.check_type_parameter_lists_identical(symbol.expect("interface symbol"));
        // Check once per checker, but report on the first interface declaration,
        // independently of which declaration is checked first.
        let symbol = symbol.unwrap();
        let links = self.declared_type_links.get(symbol);
        if !links.interface_checked {
            links.interface_checked = true;
            let first_interface_declaration = sym_declarations(self, symbol)
                .iter()
                .copied()
                .find(|&d| self.program_nodes(d)[d].kind == ast::Kind::InterfaceDeclaration)
                .expect("first interface declaration");
            let t = self.get_declared_type_of_symbol(symbol);
            let type_with_this = self.get_type_with_this_argument(t, None, false);
            // run subsequent checks only if first set succeeded
            let __program = self.program.clone().expect("program");
            let first_name = __program.nodes((first_interface_declaration).file_index())
                [first_interface_declaration]
                .name();
            if self.check_inherited_properties_are_identical(t, first_name) {
                let base_types = self.get_base_types(t);
                for base_type in base_types {
                    // The `get` guard is a statement temporary — bind the
                    // value first so the arena read lock drops before
                    // `get_type_with_this_argument` can allocate a type.
                    let this_type = self
                        .types_handle()
                        .get(t)
                        .as_interface_type()
                        .and_then(|i| i.this_type);
                    let target =
                        self.get_type_with_this_argument(base_type, this_type, false);
                    self.check_type_assignable_to(
                        type_with_this,
                        target,
                        first_name,
                        Some(&tsc_diagnostics::Interface_0_incorrectly_extends_interface_1),
                    );
                }
                self.check_index_constraints(t, Some(symbol), false /*isStaticIndex*/);
            }
        }
        self.check_object_type_for_duplicate_declarations(node, false /*checkPrivateNames*/);
        let extends_elements: Vec<NodeId> =
            ast::get_extends_heritage_clause_elements(&nodes[node], &nodes)
                .map(|s| s.to_vec())
                .unwrap_or_default();
        for heritage_element in extends_elements {
            if ast::is_expression_with_type_arguments(&nodes[heritage_element]) {
                let expr = nodes[heritage_element].expression();
                if let Some(expr) = expr {
                    if !ast::is_entity_name_expression(&nodes[expr], &nodes)
                        || ast::is_optional_chain(&nodes[expr])
                    {
                        self.error(
                            Some(expr),
                            &tsc_diagnostics::An_interface_can_only_extend_an_identifier_Slashqualified_name_with_optional_type_arguments,
                            &[],
                        );
                    }
                }
            }
            self.check_type_reference_node(heritage_element);
        }
        let members = nodes[node].members().unwrap_or(&[]).to_vec();
        self.check_source_elements(&members);
        self.check_class_or_interface_for_duplicate_index_signatures(node);
        self.register_for_unused_identifiers_check(node);
    }

    /// `(c *Checker) checkInheritedPropertiesAreIdentical` (checker.go).
    pub(crate) fn check_inherited_properties_are_identical(
        &mut self,
        t: TypeId,
        type_node: Option<NodeId>,
    ) -> bool {
        let base_types = self.get_base_types(t);
        if base_types.len() < 2 {
            return true;
        }
        let mut seen: FxHashMap<String, (SymbolId, TypeId)> = FxHashMap::default();
        let resolved_t = self.resolve_declared_members(t);
        let __arena___guard_declared = self.types.clone();
        let __guard_declared = __arena___guard_declared.get(resolved_t).clone();
        let declared = __guard_declared
            .as_interface_type()
            .expect("interface type")
            .declared_members
            .clone();
        for (id, p) in declared.entries() {
            if self.is_named_member(*p, id) {
                seen.insert(id.to_string(), (*p, t));
            }
        }
        let mut identical = true;
        let __arena___guard_this_type = self.types.clone();
        let __guard_this_type = __arena___guard_this_type.get(t).clone();
        let this_type = __guard_this_type
            .as_interface_type()
            .and_then(|i| i.this_type);
        for base in base_types {
            let base_with_this = self.get_type_with_this_argument(base, this_type, false);
            for prop in self.get_properties_of_type(base_with_this) {
                let prop_name = sym_name(self, prop);
                match seen.get(&prop_name).copied() {
                    None => {
                        seen.insert(prop_name, (prop, base));
                    }
                    Some((existing_prop, existing_containing)) => {
                        let is_inherited_property = existing_containing != t;
                        if is_inherited_property
                            && !self.is_property_identical_to(existing_prop, prop)
                        {
                            identical = false;
                            let type_name1 = self.type_to_string(existing_containing);
                            let type_name2 = self.type_to_string(base);
                            let arg0 = self.symbol_to_string(prop);
                            let t_name = self.type_to_string(t);
                            let error_info = self.new_diagnostic_for_node(
                                type_node,
                                &tsc_diagnostics::Named_property_0_of_types_1_and_2_are_not_identical,
                                &[arg0, type_name1.clone(), type_name2.clone()],
                            );
                            self.add_diagnostic(&ast::diagnostic::new_diagnostic_chain(
                                Some(&error_info),
                                &tsc_diagnostics::Interface_0_cannot_simultaneously_extend_types_1_and_2,
                                &[t_name, type_name1, type_name2],
                            ));
                        }
                    }
                }
            }
        }
        identical
    }

    /// `(c *Checker) isPropertyIdenticalTo` (checker.go).
    pub(crate) fn is_property_identical_to(
        &mut self,
        source_prop: SymbolId,
        target_prop: SymbolId,
    ) -> bool {
        self.compare_properties(source_prop, target_prop, &mut |c, s, t| {
            c.compare_types_identical(s, t)
        }) != Ternary::FALSE
    }

    /// `(c *Checker) checkEnumDeclaration` (checker.go).
    pub(crate) fn check_enum_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_grammar_modifiers(node);
        self.check_collisions_for_declaration_name(node, nodes[node].name());
        self.check_exports_on_merged_declarations(node);
        let members = nodes[node].members().unwrap_or(&[]).to_vec();
        self.check_source_elements(&members);
        if self.should_check_erasable_syntax(node)
            && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
        {
            self.error(
                Some(node),
                &tsc_diagnostics::This_syntax_is_not_allowed_when_erasableSyntaxOnly_is_enabled,
                &[],
            );
        }
        self.compute_enum_member_values(node);
        // Spec 2014 - Section 9.3:
        // It isn't possible for one enum declaration to continue the automatic numbering sequence of another,
        // and when an enum type has multiple declarations, only one declaration is permitted to omit a value
        // for the first member.
        //
        // Only perform this check once per symbol
        let enum_symbol = self.get_symbol_of_declaration(node).expect("enum symbol");
        let links = self.declared_type_links.get(enum_symbol);
        if !links.enum_checked {
            links.enum_checked = true;
            let declarations = sym_declarations(self, enum_symbol);
            if declarations.len() > 1 {
                let first_enum_declaration = declarations
                    .iter()
                    .copied()
                    .find(|&d| self.program_nodes(d)[d].kind == ast::Kind::EnumDeclaration)
                    .expect("first enum declaration");
                let enum_is_const = ast::is_enum_const(
                    first_enum_declaration,
                    &self.program_nodes(first_enum_declaration),
                );
                // check that const is placed\omitted on all enum declarations
                for &decl in &declarations {
                    let __program = self.program.clone().expect("program");
                    let dn = __program.nodes((decl).file_index());
                    if ast::is_enum_declaration(&dn[decl])
                        && ast::is_enum_const(decl, &dn) != enum_is_const
                    {
                        self.error(
                            ast::get_name_of_declaration(Some(decl), &dn),
                            &tsc_diagnostics::Enum_declarations_must_all_be_const_or_non_const,
                            &[],
                        );
                    }
                }
            }
            let mut seen_enum_missing_initial_initializer = false;
            for &declaration in &declarations {
                // return true if we hit a violation of the rule, false otherwise
                let __program = self.program.clone().expect("program");
                let dn = __program.nodes((declaration).file_index());
                if dn[declaration].kind != ast::Kind::EnumDeclaration {
                    continue;
                }
                let members = dn[declaration].members().unwrap_or(&[]).to_vec();
                if members.is_empty() {
                    continue;
                }
                let first_enum_member = members[0];
                if dn[first_enum_member].initializer().is_none() {
                    if seen_enum_missing_initial_initializer {
                        self.error(
                            dn[first_enum_member].name(),
                            &tsc_diagnostics::In_an_enum_with_multiple_declarations_only_one_declaration_can_omit_an_initializer_for_its_first_enum_element,
                            &[],
                        );
                    } else {
                        seen_enum_missing_initial_initializer = true;
                    }
                }
            }
        }
    }

    /// `(c *Checker) checkEnumMember` (checker.go).
    pub(crate) fn check_enum_member(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(name) = nodes[node].name() {
            if ast::is_private_identifier(&nodes[name]) {
                self.error(
                    Some(node),
                    &tsc_diagnostics::An_enum_member_cannot_be_named_with_a_private_identifier,
                    &[],
                );
            }
            if ast::is_computed_property_name(&nodes[name]) {
                let expr = nodes[name].expression().expect("computed expr");
                self.check_expression(expr);
            }
        }
        if let Some(initializer) = nodes[node].initializer() {
            self.check_expression(initializer);
        }
    }

    /// `(c *Checker) checkModuleDeclaration` (checker.go).
    pub(crate) fn check_module_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(body) = nodes[node].body() {
            self.check_source_element(Some(body));
            if !ast::is_global_scope_augmentation(&nodes[node]) {
                self.register_for_unused_identifiers_check(node);
            }
        }
        let is_global_augmentation = ast::is_global_scope_augmentation(&nodes[node]);
        let in_ambient_context = nodes[node].flags.intersects(ast::NodeFlags::AMBIENT);
        if is_global_augmentation && !in_ambient_context {
            self.error(
                nodes[node].name(),
                &tsc_diagnostics::Augmentations_for_the_global_scope_should_have_declare_modifier_unless_they_appear_in_already_ambient_context,
                &[],
            );
        }
        let attributes = nodes[node].as_module_declaration().attributes;
        if let Some(attributes) = attributes {
            self.check_import_attributes_type(attributes);
        }
        let is_ambient_external_module = ast::is_ambient_module(&nodes[node], &nodes);
        let context_error_message: &'static tsc_diagnostics::Message = if is_ambient_external_module
        {
            &tsc_diagnostics::An_ambient_module_declaration_is_only_allowed_at_the_top_level_in_a_file
        } else {
            &tsc_diagnostics::A_namespace_declaration_is_only_allowed_at_the_top_level_of_a_namespace_or_module
        };
        if self.check_grammar_module_element_context(node, context_error_message) {
            // If we hit a module declaration in an illegal context, just bail out to avoid cascading errors.
            return;
        }
        if !self.check_grammar_modifiers(node)
            && !in_ambient_context
            && nodes[node]
                .name()
                .is_some_and(|n| ast::is_string_literal(&nodes[n]))
        {
            self.grammar_error_on_node(
                nodes[node].name().unwrap(),
                &tsc_diagnostics::Only_ambient_modules_can_use_quoted_names,
                &[],
            );
        }
        if nodes[node]
            .name()
            .is_some_and(|n| ast::is_identifier(&nodes[n]))
        {
            self.check_collisions_for_declaration_name(node, nodes[node].name());
            if nodes[node].as_module_declaration().keyword == ast::Kind::ModuleKeyword {
                self.error(
                    nodes[node].name(),
                    &tsc_diagnostics::A_namespace_declaration_should_not_be_declared_using_the_module_keyword_Please_use_the_namespace_keyword_instead,
                    &[],
                );
            }
        }
        self.check_exports_on_merged_declarations(node);
        let symbol = self.get_symbol_of_declaration(node).expect("module symbol");
        // The following checks only apply on a non-ambient instantiated module declaration.
        if sym_flags(self, symbol).intersects(ast::SymbolFlags::VALUE_MODULE)
            && !in_ambient_context
            && is_instantiated_module(
                node,
                self.compiler_options.should_preserve_const_enums(),
                &nodes,
            )
        {
            if self.should_check_erasable_syntax(node) {
                self.error(
                    Some(node),
                    &tsc_diagnostics::This_syntax_is_not_allowed_when_erasableSyntaxOnly_is_enabled,
                    &[],
                );
            }
            if self.compiler_options.get_isolated_modules() && {
                let source_file =
                    ast::get_source_file_of_node(Some(node), &nodes).expect("source file");
                nodes[source_file]
                    .as_source_file()
                    .external_module_indicator
                    .is_none()
            } {
                // This could be loosened a little if needed. The only problem we are trying to avoid is unqualified
                // references to namespace members declared in other files. But use of namespaces is discouraged anyway,
                // so for now we will just not allow them in scripts, which is the only place they can merge cross-file.
                let flag_name = self.get_isolated_modules_like_flag_name();
                self.error(
                    nodes[node].name(),
                    &tsc_diagnostics::Namespaces_are_not_allowed_in_global_script_files_when_0_is_enabled_If_this_file_is_not_intended_to_be_a_global_script_set_moduleDetection_to_force_or_add_an_empty_export_statement,
                    &[flag_name],
                );
            }
            let declarations = sym_declarations(self, symbol);
            if declarations.len() > 1 {
                let first_non_ambient_class_or_func =
                    get_first_non_ambient_class_or_function_declaration(self, symbol);
                if let Some(first) = first_non_ambient_class_or_func {
                    let source_file = ast::get_source_file_of_node(Some(node), &nodes);
                    let __program = self.program.clone().expect("program");
                    let first_nodes = __program.nodes((first).file_index());
                    let first_source_file = ast::get_source_file_of_node(Some(first), &first_nodes);
                    if source_file != first_source_file {
                        self.error(
                            nodes[node].name(),
                            &tsc_diagnostics::A_namespace_declaration_cannot_be_in_a_different_file_from_a_class_or_function_with_which_it_is_merged,
                            &[],
                        );
                    } else if nodes[node].pos() < first_nodes[first].pos() {
                        self.error(
                            nodes[node].name(),
                            &tsc_diagnostics::A_namespace_declaration_cannot_be_located_prior_to_a_class_or_function_with_which_it_is_merged,
                            &[],
                        );
                    }
                }
            }
            if self.compiler_options.verbatim_module_syntax.is_true()
                && nodes[node]
                    .parent
                    .is_some_and(|p| ast::is_source_file(&nodes[p]))
                && nodes[node]
                    .modifier_flags()
                    .intersects(ast::ModifierFlags::EXPORT)
                && self
                    .program
                    .as_ref()
                    .expect("program")
                    .get_emit_module_format_of_file(
                        nodes[nodes[node].parent.unwrap()].as_source_file(),
                    )
                    == ModuleKind::CommonJS
            {
                let export_modifier = nodes[node]
                    .modifier_nodes()
                    .unwrap_or(&[])
                    .iter()
                    .copied()
                    .find(|&m| nodes[m].kind == ast::Kind::ExportKeyword);
                self.error(
                    export_modifier,
                    &tsc_diagnostics::A_top_level_export_modifier_cannot_be_used_on_value_declarations_in_a_CommonJS_module_when_verbatimModuleSyntax_is_enabled,
                    &[],
                );
            }
        }
        if is_ambient_external_module {
            if ast::is_external_module_augmentation(&nodes[node], &nodes) {
                if let Some(attributes) = attributes {
                    self.error(
                        Some(attributes),
                        &tsc_diagnostics::Import_attributes_are_not_allowed_on_a_module_augmentation,
                        &[],
                    );
                }
                // body of the augmentation should be checked for consistency only if augmentation was applied to its target (either global scope or module)
                // otherwise we'll be swamped in cascading errors.
                // We can detect if augmentation was applied using following rules:
                // - augmentation for a global scope is always applied
                // - augmentation for some external module is applied if symbol for augmentation is merged (it was combined with target module).
                let decl_symbol = self.get_symbol_of_declaration(node).unwrap_or(symbol);
                let check_body = is_global_augmentation
                    || sym_flags(self, decl_symbol).intersects(ast::SymbolFlags::TRANSIENT);
                if check_body {
                    if let Some(body) = nodes[node].body() {
                        let statements = nodes[body].statements().unwrap_or(&[]).to_vec();
                        for statement in statements {
                            self.check_module_augmentation_element(statement);
                        }
                    }
                }
            } else if nodes[node]
                .parent
                .is_some_and(|p| ast::is_global_source_file(&nodes[p], &nodes))
            {
                if is_global_augmentation {
                    self.error(
                        nodes[node].name(),
                        &tsc_diagnostics::Augmentations_for_the_global_scope_can_only_be_directly_nested_in_external_modules_or_ambient_module_declarations,
                        &[],
                    );
                } else if nodes[node].name().is_some_and(|n| {
                    tsc_tspath::is_external_module_name_relative(nodes[n].text(&nodes).as_ref())
                }) {
                    self.error(
                        nodes[node].name(),
                        &tsc_diagnostics::Ambient_module_declaration_cannot_specify_relative_module_name,
                        &[],
                    );
                }
            } else {
                if is_global_augmentation {
                    self.error(
                        nodes[node].name(),
                        &tsc_diagnostics::Augmentations_for_the_global_scope_can_only_be_directly_nested_in_external_modules_or_ambient_module_declarations,
                        &[],
                    );
                } else {
                    // Node is not an augmentation and is not located on the script level.
                    // This means that this is declaration of ambient module that is located in other module or namespace which is prohibited.
                    self.error(
                        nodes[node].name(),
                        &tsc_diagnostics::Ambient_modules_cannot_be_nested_in_other_modules_or_namespaces,
                        &[],
                    );
                }
            }
        }
    }

    /// `(c *Checker) checkImportAttributesType` (checker.go).
    pub(crate) fn check_import_attributes_type(&mut self, attributes: NodeId) {
        self.check_grammar_import_attributes_type(attributes);
        self.check_source_element(Some(attributes));
        let import_attributes_type = self.get_global_import_attributes_type_checked();
        let module_attributes_type =
            self.get_type_of_module_declaration_import_attributes(Some(attributes));
        if import_attributes_type != self.empty_object_type {
            self.check_type_assignable_to(
                module_attributes_type,
                import_attributes_type,
                Some(attributes),
                None,
            );
        }
    }

    /// `(c *Checker) getTypeOfModuleDeclarationImportAttributes` (checker.go).
    pub(crate) fn get_type_of_module_declaration_import_attributes(
        &mut self,
        attributes: Option<NodeId>,
    ) -> TypeId {
        match attributes {
            None => self.empty_object_type,
            Some(attributes) => self.get_type_from_type_node(attributes),
        }
    }

    /// `(c *Checker) getTypeOfModuleImportAttributes` (checker.go).
    pub(crate) fn get_type_of_module_import_attributes(&mut self, symbol: SymbolId) -> TypeId {
        if let Some(&t) = self.module_import_attributes_types.get(&symbol) {
            return t;
        }
        let declarations = sym_declarations(self, symbol);
        let module_decl = declarations.iter().copied().find(|&d| {
            let __program = self.program.clone().expect("program");
            let dn = __program.nodes((d).file_index());
            ast::is_module_with_string_literal_name(&dn[d], &dn)
        });
        let result = match module_decl {
            None => self.empty_object_type,
            Some(module_decl) => {
                let __program = self.program.clone().expect("program");
                let dn = __program.nodes((module_decl).file_index());
                self.get_type_of_module_declaration_import_attributes(
                    dn[module_decl].as_module_declaration().attributes,
                )
            }
        };
        self.module_import_attributes_types.insert(symbol, result);
        result
    }

    /// `(c *Checker) getIsolatedModulesLikeFlagName` (checker.go).
    pub(crate) fn get_isolated_modules_like_flag_name(&self) -> String {
        tsc_core::core::if_else(
            self.compiler_options.verbatim_module_syntax.is_true(),
            "verbatimModuleSyntax",
            "isolatedModules",
        )
        .to_string()
    }

    /// `(c *Checker) checkModuleAugmentationElement` (checker.go).
    pub(crate) fn check_module_augmentation_element(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::VariableStatement => {
                // error each individual name in variable statement instead of marking the entire variable statement
                let decls = nodes[node]
                    .as_variable_statement()
                    .declaration_list
                    .map(|dl| {
                        nodes[dl]
                            .as_variable_declaration_list()
                            .declarations
                            .as_ref()
                            .map(|l| l.nodes().to_vec())
                            .unwrap_or_default()
                    })
                    .unwrap_or_default();
                for decl in decls {
                    self.check_module_augmentation_element(decl);
                }
            }
            ast::Kind::ExportAssignment | ast::Kind::ExportDeclaration => {
                self.grammar_error_on_first_token(
                    node,
                    &tsc_diagnostics::Exports_and_export_assignments_are_not_permitted_in_module_augmentations,
                    &[],
                );
            }
            ast::Kind::ImportEqualsDeclaration => {
                // import a = e.x; in module augmentation is ok, but not import a = require('fs')
                if !ast::is_internal_module_import_equals_declaration(&nodes[node], &nodes) {
                    self.grammar_error_on_first_token(
                        node,
                        &tsc_diagnostics::Imports_are_not_permitted_in_module_augmentations_Consider_moving_them_to_the_enclosing_external_module,
                        &[],
                    );
                }
            }
            ast::Kind::ImportDeclaration | ast::Kind::JSImportDeclaration => {
                self.grammar_error_on_first_token(
                    node,
                    &tsc_diagnostics::Imports_are_not_permitted_in_module_augmentations_Consider_moving_them_to_the_enclosing_external_module,
                    &[],
                );
            }
            ast::Kind::BindingElement | ast::Kind::VariableDeclaration => {
                if let Some(name) = nodes[node].name() {
                    if ast::is_binding_pattern(&nodes[name]) {
                        for &el in nodes[name].elements().unwrap_or(&[]) {
                            // mark individual names in binding pattern
                            self.check_module_augmentation_element(el);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// `(c *Checker) checkImportDeclaration` (checker.go).
    pub(crate) fn check_import_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Grammar checking
        let diagnostic: &'static tsc_diagnostics::Message = if ast::is_in_js_file(
            Some(node),
            &nodes,
        ) {
            &tsc_diagnostics::An_import_declaration_can_only_be_used_at_the_top_level_of_a_module
        } else {
            &tsc_diagnostics::An_import_declaration_can_only_be_used_at_the_top_level_of_a_namespace_or_module
        };
        if self.check_grammar_module_element_context(node, diagnostic) {
            // If we hit an import declaration in an illegal context, just bail out to avoid cascading errors.
            self.check_external_module_name_in_global_scope(node);
            return;
        }
        if !self.check_grammar_modifiers(node) && nodes[node].modifiers().is_some() {
            self.grammar_error_on_first_token(
                node,
                &tsc_diagnostics::An_import_declaration_cannot_have_modifiers,
                &[],
            );
        }
        if self.check_external_import_or_export_declaration(node) {
            let attributes = ast::get_import_attributes(&nodes[node]);
            let mut resolved_module: Option<SymbolId> = None;
            let import_clause = nodes[node].import_clause();
            let module_specifier = nodes[node].module_specifier();
            if import_clause.is_some() && !self.check_grammar_import_clause(import_clause.unwrap())
            {
                let import_clause = import_clause.unwrap();
                if nodes[import_clause].name().is_some() {
                    self.check_import_binding(import_clause);
                }
                let mut needs_import_star = false;
                let named_bindings = nodes[import_clause].as_import_clause().named_bindings;
                if let Some(named_bindings) = named_bindings {
                    if ast::is_namespace_import(&nodes[named_bindings]) {
                        self.check_import_binding(named_bindings);
                        if self
                            .program
                            .as_ref()
                            .expect("program")
                            .get_emit_module_format_of_file(
                                nodes[ast::get_source_file_of_node(Some(node), &nodes)
                                    .expect("source file")]
                                .as_source_file(),
                            )
                            == ModuleKind::CommonJS
                        {
                            // import * as ns from "foo";
                            needs_import_star = true;
                            self.check_external_emit_helpers(
                                node,
                                crate::types::ExternalEmitHelpers::IMPORT_STAR,
                            );
                        }
                    } else {
                        let attrs_ty = self.get_type_from_import_attributes(attributes);
                        resolved_module = self.resolve_external_module_name(
                            node,
                            module_specifier,
                            false,
                            attrs_ty,
                        );
                        if resolved_module.is_some() {
                            for &binding in nodes[named_bindings].elements().unwrap_or(&[]) {
                                self.check_import_binding(binding);
                            }
                        }
                    }
                }
                if nodes[import_clause].name().is_some()
                    && !needs_import_star
                    && self
                        .program
                        .as_ref()
                        .expect("program")
                        .get_emit_module_format_of_file(
                            nodes[ast::get_source_file_of_node(Some(node), &nodes)
                                .expect("source file")]
                            .as_source_file(),
                        )
                        == ModuleKind::CommonJS
                {
                    // import d from "foo";
                    self.check_external_emit_helpers(
                        node,
                        crate::types::ExternalEmitHelpers::IMPORT_DEFAULT,
                    );
                }
                if !nodes[import_clause].is_type_only()
                    && (ModuleKind::Node18..=ModuleKind::NodeNext).contains(&self.module_kind)
                    && module_specifier.is_some()
                    && {
                        let attrs_ty = self.get_type_from_import_attributes(attributes);
                        self.is_only_importable_as_default(
                            module_specifier.unwrap(),
                            resolved_module,
                            attrs_ty,
                        )
                    }
                    && !has_type_json_import_attribute(node, &nodes)
                {
                    let arg = format!("{}", self.module_kind);
                    self.error(
                        module_specifier,
                        &tsc_diagnostics::Importing_a_JSON_file_into_an_ECMAScript_module_requires_a_type_Colon_json_import_attribute_when_module_is_set_to_0,
                        &[arg],
                    );
                }
            } else if self
                .compiler_options
                .no_unchecked_side_effect_imports
                .is_true_or_unknown()
                && import_clause.is_none()
            {
                let ignore_errors = self.compiler_options.no_check.is_true();
                let error_message: Option<&'static tsc_diagnostics::Message> = if !ignore_errors {
                    Some(
                        &tsc_diagnostics::Cannot_find_module_or_type_declarations_for_side_effect_import_of_0,
                    )
                } else {
                    None
                };
                let attrs_ty = self.get_type_from_import_attributes(attributes);
                self.resolve_external_module_name_worker(
                    node,
                    module_specifier,
                    error_message,
                    ignore_errors,
                    false, /*isForAugmentation*/
                    attrs_ty,
                );
            }
        }
        self.check_import_attributes(node);
    }

    /// `(c *Checker) checkExternalImportOrExportDeclaration` (checker.go).
    pub(crate) fn check_external_import_or_export_declaration(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let module_name = ast::get_external_module_name(&nodes[node], &nodes);
        if module_name.is_none()
            || module_name.is_some_and(|m| ast::node_is_missing(Some(m), &nodes))
        {
            // Should be a parse error.
            return false;
        }
        let module_name = module_name.unwrap();
        if !ast::is_string_literal(&nodes[module_name]) {
            self.error(
                Some(module_name),
                &tsc_diagnostics::String_literal_expected,
                &[],
            );
            return false;
        }
        let in_ambient_external_module = nodes[node]
            .parent
            .is_some_and(|p| ast::is_module_block(&nodes[p]))
            && nodes[node]
                .parent
                .and_then(|p| nodes[p].parent)
                .is_some_and(|gp| ast::is_ambient_module(&nodes[gp], &nodes));
        if !nodes[node]
            .parent
            .is_some_and(|p| ast::is_source_file(&nodes[p]))
            && !in_ambient_external_module
        {
            let message: &'static tsc_diagnostics::Message =
                if ast::is_export_declaration(&nodes[node]) {
                    &tsc_diagnostics::Export_declarations_are_not_permitted_in_a_namespace
                } else {
                    &tsc_diagnostics::Import_declarations_in_a_namespace_cannot_reference_a_module
                };
            self.error(Some(module_name), message, &[]);
            return false;
        }
        if in_ambient_external_module
            && tsc_tspath::is_external_module_name_relative(
                nodes[module_name].text(&nodes).as_ref(),
            )
        {
            // we have already reported errors on top level imports/exports in external module augmentations in checkModuleDeclaration
            // no need to do this again.
            if !crate::utilities::is_top_level_in_external_module_augmentation(node, &nodes) {
                // TypeScript 1.0 spec (April 2013): 12.1.6
                // An ExternalImportDeclaration in an AmbientExternalModuleDeclaration may reference
                // other external modules only through top - level external module names.
                // Relative external module names are not permitted.
                self.error(
                    Some(node),
                    &tsc_diagnostics::Import_or_export_declaration_in_an_ambient_module_declaration_cannot_reference_module_through_relative_module_name,
                    &[],
                );
                return false;
            }
        }
        if !ast::is_import_equals_declaration(&nodes[node]) {
            let attributes = ast::get_import_attributes(&nodes[node]);
            if let Some(attributes) = attributes {
                if self.check_grammar_import_attribute_values(attributes) {
                    return false;
                }
            }
        }
        true
    }

    /// `(c *Checker) checkImportBinding` (checker.go).
    pub(crate) fn check_import_binding(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_collisions_for_declaration_name(node, nodes[node].name());
        self.check_alias_symbol(node);
        if ast::is_import_specifier(&nodes[node]) {
            self.check_module_export_name(
                nodes[node].property_name(),
                true, /*allowStringLiteral*/
            );
            if nodes[node]
                .property_name_or_name()
                .is_some_and(|n| ast::module_export_name_is_default(&nodes[n], &nodes))
                && self
                    .program
                    .as_ref()
                    .expect("program")
                    .get_emit_module_format_of_file(
                        nodes[ast::get_source_file_of_node(Some(node), &nodes)
                            .expect("source file")]
                        .as_source_file(),
                    )
                    == ModuleKind::CommonJS
            {
                self.check_external_emit_helpers(
                    node,
                    crate::types::ExternalEmitHelpers::IMPORT_DEFAULT,
                );
            }
        }
    }

    /// `(c *Checker) checkModuleExportName` (checker.go).
    pub(crate) fn check_module_export_name(
        &mut self,
        name: Option<NodeId>,
        allow_string_literal: bool,
    ) {
        let Some(name) = name else { return };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((name).file_index());
        if nodes[name].kind != ast::Kind::StringLiteral {
            return;
        }
        if !allow_string_literal {
            self.grammar_error_on_node(name, &tsc_diagnostics::Identifier_expected, &[]);
        } else if self.module_kind == ModuleKind::ES2015 || self.module_kind == ModuleKind::ES2020 {
            let source_file =
                ast::get_source_file_of_node(Some(name), &nodes).expect("source file");
            if !nodes[source_file].as_source_file().is_declaration_file {
                self.grammar_error_on_node(
                    name,
                    &tsc_diagnostics::String_literal_import_and_export_names_are_not_supported_when_the_module_flag_is_set_to_es2015_or_es2020,
                    &[],
                );
            }
        }
    }

    /// `(c *Checker) checkImportAttributes` (checker.go).
    pub(crate) fn check_import_attributes(&mut self, declaration: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((declaration).file_index());
        let Some(node) = ast::get_import_attributes(&nodes[declaration]) else {
            return;
        };
        let import_attributes_type = self.get_global_import_attributes_type_checked();
        if import_attributes_type != self.empty_object_type {
            let from_attributes = self
                .get_type_from_import_attributes(Some(node))
                .unwrap_or(self.error_type);
            let nullable = self.get_nullable_type(import_attributes_type, TypeFlags::UNDEFINED);
            self.check_type_assignable_to(from_attributes, nullable, Some(node), None);
        }
        let is_type_only = ast::is_exclusively_type_only_import_or_export(declaration, &nodes)
            || ast::is_import_type_node(&nodes[declaration]);
        let override_ = self.get_resolution_mode_override(node, is_type_only);
        if is_type_only {
            return; // Other grammar checks do not apply to type-only imports with import attributes
        }
        if !self.module_kind.supports_import_attributes() {
            self.grammar_error_on_node(
                node,
                &tsc_diagnostics::Import_attributes_are_only_supported_when_the_module_option_is_set_to_esnext_node18_node20_nodenext_or_preserve,
                &[],
            );
            return;
        }
        if let Some(module_specifier) = ast::get_external_module_name(&nodes[declaration], &nodes) {
            if self.get_emit_syntax_for_module_specifier_expression(module_specifier)
                == tsc_core::compileroptions::RESOLUTION_MODE_COMMON_JS
            {
                self.grammar_error_on_node(
                    node,
                    &tsc_diagnostics::Import_attributes_are_not_allowed_on_statements_that_compile_to_CommonJS_require_calls,
                    &[],
                );
                return;
            }
        }
        if override_ != tsc_core::compileroptions::RESOLUTION_MODE_NONE {
            self.grammar_error_on_node(
                node,
                &tsc_diagnostics::X_resolution_mode_can_only_be_set_for_type_only_imports,
                &[],
            );
        }
    }

    /// `(c *Checker) getTypeFromImportAttributes` (checker.go).
    pub(crate) fn get_type_from_import_attributes(
        &mut self,
        node: Option<NodeId>,
    ) -> Option<TypeId> {
        let node = node?;
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if ast::is_import_attributes(&nodes[node]) {
            Some(self.check_import_attributes_expression(node))
        } else {
            Some(self.check_expression_cached(node))
        }
    }

    /// `(c *Checker) checkImportAttributesExpression` (checker.go).
    pub(crate) fn check_import_attributes_expression(&mut self, node: NodeId) -> TypeId {
        if self.type_node_links.get(node).resolved_type.is_none() {
            let symbol = self.new_symbol(
                ast::SymbolFlags::OBJECT_LITERAL,
                ast::INTERNAL_SYMBOL_NAME_IMPORT_ATTRIBUTES,
            );
            let mut members: ast::SymbolTable = ast::SymbolTable::default();
            let attributes: Vec<NodeId> = {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((node).file_index());
                nodes[node]
                    .as_import_attributes()
                    .attributes
                    .as_ref()
                    .map(|l| l.nodes().to_vec())
                    .unwrap_or_default()
            };
            for attribute in attributes {
                let __program = self.program.clone().expect("program");
                let an = __program.nodes((attribute).file_index());
                let member_name = an[attribute]
                    .name()
                    .map(|n| node_text(&an, n))
                    .unwrap_or_default();
                let member = self.new_symbol(ast::SymbolFlags::PROPERTY, member_name.as_str());
                let value = an[attribute].as_import_attribute().value.expect("value");
                let __h8212_59 = self.check_expression_cached(value);

                let resolved = self.get_regular_type_of_literal_type(__h8212_59);
                self.value_symbol_links.get(member).resolved_type = Some(resolved);
                members.set(member_name.into(), member);
            }
            let t = self.new_anonymous_type(Some(symbol), members, &[], &[], &[]);
            self.types_handle().get_mut(t).object_flags |=
                ObjectFlags::OBJECT_LITERAL | ObjectFlags::NON_INFERRABLE_TYPE;
            self.type_node_links.get(node).resolved_type = Some(t);
        }
        self.type_node_links.get(node).resolved_type.unwrap()
    }

    /// `(c *Checker) getImportAttributesTypeForModuleSpecifier` (checker.go).
    pub(crate) fn get_import_attributes_type_for_module_specifier(
        &mut self,
        module_specifier: NodeId,
    ) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((module_specifier).file_index());
        let parent = nodes[module_specifier].parent.expect("specifier parent");
        if matches!(
            nodes[parent].kind,
            ast::Kind::ImportDeclaration | ast::Kind::JSImportDeclaration
        ) || ast::is_export_declaration(&nodes[parent])
        {
            return self
                .get_type_from_import_attributes(ast::get_import_attributes(&nodes[parent]));
        }
        if ast::is_literal_type_node(&nodes[parent])
            && nodes[parent]
                .parent
                .is_some_and(|gp| ast::is_literal_import_type_node(&nodes[gp], &nodes))
        {
            let gp = nodes[parent].parent.unwrap();
            let attrs = ast::get_import_attributes(&nodes[gp]);
            return self.get_type_from_import_attributes(attrs);
        }
        if ast::is_import_call(&nodes[parent], &nodes)
            && nodes[parent].arguments().unwrap_or(&[]).len() > 1
        {
            let options = nodes[parent].arguments().unwrap()[1];
            let options_type = self.check_expression_cached(options);
            return self.get_type_of_property_of_type(options_type, "with");
        }
        None
    }

    /// `(c *Checker) checkImportEqualsDeclaration` (checker.go).
    pub(crate) fn check_import_equals_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let diagnostic: &'static tsc_diagnostics::Message = if ast::is_in_js_file(
            Some(node),
            &nodes,
        ) {
            &tsc_diagnostics::An_import_declaration_can_only_be_used_at_the_top_level_of_a_module
        } else {
            &tsc_diagnostics::An_import_declaration_can_only_be_used_at_the_top_level_of_a_namespace_or_module
        };
        if self.check_grammar_module_element_context(node, diagnostic) {
            self.check_external_module_name_in_global_scope(node);
            return; // If we hit an import declaration in an illegal context, just bail out to avoid cascading errors.
        }
        self.check_grammar_modifiers(node);
        if self.should_check_erasable_syntax(node)
            && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
        {
            self.error(
                Some(node),
                &tsc_diagnostics::This_syntax_is_not_allowed_when_erasableSyntaxOnly_is_enabled,
                &[],
            );
        }
        if ast::is_internal_module_import_equals_declaration(&nodes[node], &nodes)
            || self.check_external_import_or_export_declaration(node)
        {
            self.check_import_binding(node);
            self.mark_linked_references(
                node,
                crate::checker_types::ReferenceHint::ExportImportEquals,
                None,
                None,
            
                None,
            );
            let module_reference = nodes[node].as_import_equals_declaration().module_reference;
            let module_reference = module_reference.expect("moduleReference");
            if !ast::is_external_module_reference(&nodes[module_reference]) {
                let alias_sym = self.get_symbol_of_declaration(node).expect("alias symbol");
                let target = self.resolve_alias(alias_sym);
                if target != self.unknown_symbol {
                    let target_flags = self.get_symbol_flags(target);
                    if target_flags.intersects(ast::SymbolFlags::VALUE) {
                        // Target is a value symbol, check that it is not hidden by a local declaration with the same name
                        let module_name = ast::get_first_identifier(module_reference, &nodes);
                        if self
                            .resolve_entity_name(
                                Some(module_name),
                                ast::SymbolFlags::VALUE | ast::SymbolFlags::NAMESPACE,
                                false,
                                false,
                                None,
                            )
                            .is_none_or(|s| {
                                !sym_flags(self, s).intersects(ast::SymbolFlags::NAMESPACE)
                            })
                        {
                            let arg = tsc_scanner::utilities::declaration_name_to_string(
                                Some(module_name),
                                &nodes,
                            );
                            self.error(
                                Some(module_name),
                                &tsc_diagnostics::Module_0_is_hidden_by_a_local_declaration_with_the_same_name,
                                &[arg],
                            );
                        }
                    }
                    if target_flags.intersects(ast::SymbolFlags::TYPE) {
                        if let Some(name) = nodes[node].name() {
                            self.check_type_name_is_reserved(
                                name,
                                &tsc_diagnostics::Import_name_cannot_be_0,
                            );
                        }
                    }
                }
                if nodes[node].is_type_only() {
                    self.grammar_error_on_node(
                        node,
                        &tsc_diagnostics::An_import_alias_cannot_use_import_type,
                        &[],
                    );
                }
            } else {
                if (ModuleKind::ES2015..=ModuleKind::ESNext).contains(&self.module_kind)
                    && !nodes[node].is_type_only()
                    && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
                {
                    // Import equals declaration cannot be emitted as ESM
                    self.grammar_error_on_node(
                        node,
                        &tsc_diagnostics::Import_assignment_cannot_be_used_when_targeting_ECMAScript_modules_Consider_using_import_Asterisk_as_ns_from_mod_import_a_from_mod_import_d_from_mod_or_another_module_format_instead,
                        &[],
                    );
                }
            }
        }
    }

    /// `(c *Checker) checkExportDeclaration` (checker.go).
    pub(crate) fn check_export_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let diagnostic: &'static tsc_diagnostics::Message = if ast::is_in_js_file(
            Some(node),
            &nodes,
        ) {
            &tsc_diagnostics::An_export_declaration_can_only_be_used_at_the_top_level_of_a_module
        } else {
            &tsc_diagnostics::An_export_declaration_can_only_be_used_at_the_top_level_of_a_namespace_or_module
        };
        if self.check_grammar_module_element_context(node, diagnostic) {
            self.check_external_module_name_in_global_scope(node);
            return; // If we hit an export in an illegal context, just bail out to avoid cascading errors.
        }
        let export_decl = nodes[node].as_export_declaration();
        let (module_specifier, export_clause) =
            (export_decl.module_specifier, export_decl.export_clause);
        if !self.check_grammar_modifiers(node) && nodes[node].modifiers().is_some() {
            self.grammar_error_on_first_token(
                node,
                &tsc_diagnostics::An_export_declaration_cannot_have_modifiers,
                &[],
            );
        }
        self.check_grammar_export_declaration(node);
        if module_specifier.is_none() || self.check_external_import_or_export_declaration(node) {
            if let Some(export_clause) = export_clause {
                if !ast::is_namespace_export(&nodes[export_clause]) {
                    // export { x, y }
                    // export { x, y } from "foo"
                    for &binding in nodes[export_clause].elements().unwrap_or(&[]) {
                        self.check_export_specifier(binding);
                    }
                    let in_ambient_external_module = nodes[node]
                        .parent
                        .is_some_and(|p| ast::is_module_block(&nodes[p]))
                        && nodes[node]
                            .parent
                            .and_then(|p| nodes[p].parent)
                            .is_some_and(|gp| ast::is_ambient_module(&nodes[gp], &nodes));
                    let in_ambient_namespace_declaration = !in_ambient_external_module
                        && nodes[node]
                            .parent
                            .is_some_and(|p| ast::is_module_block(&nodes[p]))
                        && module_specifier.is_none()
                        && nodes[node].flags.intersects(ast::NodeFlags::AMBIENT);

                    if !nodes[node]
                        .parent
                        .is_some_and(|p| ast::is_source_file(&nodes[p]))
                        && !in_ambient_external_module
                        && !in_ambient_namespace_declaration
                    {
                        self.error(
                            Some(node),
                            &tsc_diagnostics::Export_declarations_are_not_permitted_in_a_namespace,
                            &[],
                        );
                    }
                }
            }
            if export_clause.is_none() || ast::is_namespace_export(&nodes[export_clause.unwrap()]) {
                let __h8423_21 =
                    self.get_type_from_import_attributes(ast::get_import_attributes(&nodes[node]));

                // export * from "foo"
                // export * as ns from "foo";
                let module_symbol =
                    self.resolve_external_module_name(node, module_specifier, false, __h8423_21);
                if let Some(module_symbol) = module_symbol {
                    if crate::utilities::has_export_assignment_symbol(self, module_symbol) {
                        let arg = self.symbol_to_string(module_symbol);
                        self.error(
                            module_specifier,
                            &tsc_diagnostics::Module_0_uses_export_and_cannot_be_used_with_export_Asterisk,
                            &[arg],
                        );
                    }
                }
                if !(module_symbol
                    .is_some_and(|ms| crate::utilities::has_export_assignment_symbol(self, ms)))
                {
                    if let Some(export_clause) = export_clause {
                        self.check_alias_symbol(export_clause);
                        self.check_module_export_name(
                            nodes[export_clause].name(),
                            true, /*allowStringLiteral*/
                        );
                    }
                }
                // Go: the emit-helpers check lives inside the
                // `export *`/`export * as ns` else-branch — `export { x }`
                // declarations do not request helpers.
                if self
                    .program
                    .as_ref()
                    .expect("program")
                    .get_emit_module_format_of_file(
                        nodes[ast::get_source_file_of_node(Some(node), &nodes)
                            .expect("source file")]
                        .as_source_file(),
                    )
                    == ModuleKind::CommonJS
                {
                    if export_clause.is_some() {
                        // export * as ns from "foo";
                        self.check_external_emit_helpers(
                            node,
                            crate::types::ExternalEmitHelpers::IMPORT_STAR,
                        );
                    } else {
                        // export * from "foo"
                        self.check_external_emit_helpers(
                            node,
                            crate::types::ExternalEmitHelpers::EXPORT_STAR,
                        );
                    }
                }
            }
        }
        self.check_import_attributes(node);
    }

    /// `(c *Checker) checkExternalModuleNameInGlobalScope` (checker.go).
    pub(crate) fn check_external_module_name_in_global_scope(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let container = crate::utilities::get_enclosing_container(node, &nodes);
        if container.map(|c| nodes[c].kind) != Some(ast::Kind::SourceFile)
            || (matches!(
                nodes[node].kind,
                ast::Kind::ImportDeclaration | ast::Kind::JSImportDeclaration
            ) && nodes[node].import_clause().is_none())
        {
            return;
        }
        if let Some(module_name) = ast::get_external_module_name(&nodes[node], &nodes) {
            let attributes = if ast::has_import_attributes(&nodes[node]) {
                ast::get_import_attributes(&nodes[node])
            } else {
                None
            };
            let import_attributes_type = self.get_type_from_import_attributes(attributes);
            self.resolve_external_module_name(
                node,
                Some(module_name),
                false,
                import_attributes_type,
            );
        }
    }

    /// `(c *Checker) checkExportSpecifier` (checker.go).
    pub(crate) fn check_export_specifier(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_alias_symbol(node);
        let has_module_specifier = nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .is_some_and(|gp| nodes[gp].module_specifier().is_some());
        self.check_module_export_name(nodes[node].property_name(), has_module_specifier);
        self.check_module_export_name(nodes[node].name(), true /*allowStringLiteral*/);
        if !has_module_specifier {
            let exported_name = nodes[node].property_name_or_name().expect("exportedName");
            if nodes[exported_name].kind == ast::Kind::StringLiteral {
                return; // Skip for invalid syntax like this: export { "x" }
            }
            // find immediate value referenced by exported name (SymbolFlags.Alias is set so we don't chase down aliases)
            let name_text = node_text(&nodes, exported_name);
            let symbol = call_resolve_name(
                self,
                Some(exported_name),
                &name_text,
                ast::SymbolFlags::VALUE
                    | ast::SymbolFlags::TYPE
                    | ast::SymbolFlags::NAMESPACE
                    | ast::SymbolFlags::ALIAS,
                None, /*nameNotFoundMessage*/
                true, /*isUse*/
                false,
            );
            if let Some(symbol) = symbol {
                if symbol == self.undefined_symbol
                    || symbol == self.global_this_symbol
                    || (!sym_declarations(self, symbol).is_empty() && {
                        let d = sym_declarations(self, symbol)[0];
                        let __program = self.program.clone().expect("program");
                        let dn = __program.nodes((d).file_index());
                        let container = ast::get_declaration_container(d, &dn);
                        container.is_some_and(|c| ast::is_global_source_file(&dn[c], &dn))
                    })
                {
                    self.error(
                        Some(exported_name),
                        &tsc_diagnostics::Cannot_export_0_Only_local_declarations_can_be_exported_from_a_module,
                        &[name_text],
                    );
                    return;
                }
            }
            self.mark_linked_references(
                node,
                crate::checker_types::ReferenceHint::ExportSpecifier,
                None, /*propSymbol*/
                None, /*parentType*/
            
                None,
            );
        } else if self
            .program
            .as_ref()
            .expect("program")
            .get_emit_module_format_of_file(
                nodes[ast::get_source_file_of_node(Some(node), &nodes).expect("source file")]
                    .as_source_file(),
            )
            == ModuleKind::CommonJS
            && nodes[node]
                .property_name_or_name()
                .is_some_and(|n| ast::module_export_name_is_default(&nodes[n], &nodes))
        {
            self.check_external_emit_helpers(
                node,
                crate::types::ExternalEmitHelpers::IMPORT_DEFAULT,
            );
        }
    }

    /// `(c *Checker) checkExportAssignment` (checker.go).
    pub(crate) fn check_export_assignment(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let is_export_equals = nodes[node].as_export_assignment().is_export_equals;
        // Always check the exported expression so its identifiers are resolved even when the
        // export assignment is misplaced (grammar error), keeping diagnostics stable
        // regardless of traversal order.
        let expr_node = nodes[node].expression().expect("export assignment expr");
        let expr_type = self.check_expression_cached(expr_node);
        let illegal_context_message: &'static tsc_diagnostics::Message = if is_export_equals {
            &tsc_diagnostics::An_export_assignment_must_be_at_the_top_level_of_a_file_or_module_declaration
        } else {
            &tsc_diagnostics::A_default_export_must_be_at_the_top_level_of_a_file_or_module_declaration
        };
        if self.check_grammar_module_element_context(node, illegal_context_message) {
            return; // If we hit an export assignment in an illegal context, just bail out to avoid cascading errors.
        }
        if self.should_check_erasable_syntax(node)
            && is_export_equals
            && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
        {
            self.error(
                Some(node),
                &tsc_diagnostics::This_syntax_is_not_allowed_when_erasableSyntaxOnly_is_enabled,
                &[],
            );
        }
        if is_contained_by_namespace(node, &nodes) {
            // TODO(danielr): should these be grammar errors?
            if is_export_equals {
                self.error(
                    Some(node),
                    &tsc_diagnostics::An_export_assignment_cannot_be_used_in_a_namespace,
                    &[],
                );
            } else {
                self.error(
                    Some(node),
                    &tsc_diagnostics::A_default_export_can_only_be_used_in_an_ECMAScript_style_module,
                    &[],
                );
            }
            return;
        }
        if !self.check_grammar_modifiers(node)
            && ast::is_export_assignment(&nodes[node])
            && nodes[node].modifiers().is_some()
        {
            self.grammar_error_on_first_token(
                node,
                &tsc_diagnostics::An_export_assignment_cannot_have_modifiers,
                &[],
            );
        }
        let source_file = ast::get_source_file_of_node(Some(node), &nodes).expect("source file");
        let is_illegal_export_default_in_cjs = !is_export_equals
            && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
            && self.compiler_options.verbatim_module_syntax.is_true()
            && self
                .program
                .as_ref()
                .expect("program")
                .get_emit_module_format_of_file(nodes[source_file].as_source_file())
                == ModuleKind::CommonJS;
        if ast::is_identifier(&nodes[expr_node]) {
            let id = expr_node;
            let resolved = self.resolve_entity_name(
                Some(id),
                ast::SymbolFlags::ALL,
                true, /*ignoreErrors*/
                true, /*dontResolveAlias*/
                Some(node),
            );
            let sym =
                resolved.and_then(|s| self.get_export_symbol_of_value_symbol_if_exported(Some(s)));
            if let Some(sym) = sym {
                self.mark_linked_references(
                    node,
                    crate::checker_types::ReferenceHint::ExportAssignment,
                    None,
                    None,
                
                None,
            );
                let type_only_declaration =
                    self.get_type_only_alias_declaration_ex(sym, ast::SymbolFlags::VALUE);
                // If not a value, we're interpreting the identifier as a type export, along the lines of (`export { Id as default }`)
                if self
                    .get_symbol_flags(sym)
                    .intersects(ast::SymbolFlags::VALUE)
                {
                    // However if it is a value, we need to check it's being used correctly
                    if !is_illegal_export_default_in_cjs
                        && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
                        && self.compiler_options.verbatim_module_syntax.is_true()
                        && type_only_declaration.is_some()
                    {
                        let message: &'static tsc_diagnostics::Message = if is_export_equals {
                            &tsc_diagnostics::An_export_declaration_must_reference_a_real_value_when_verbatimModuleSyntax_is_enabled_but_0_resolves_to_a_type_only_declaration
                        } else {
                            &tsc_diagnostics::An_export_default_must_reference_a_real_value_when_verbatimModuleSyntax_is_enabled_but_0_resolves_to_a_type_only_declaration
                        };
                        self.error(Some(id), message, &[node_text(&nodes, id)]);
                    }
                } else if !is_illegal_export_default_in_cjs
                    && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
                    && self.compiler_options.verbatim_module_syntax.is_true()
                {
                    let message: &'static tsc_diagnostics::Message = if is_export_equals {
                        &tsc_diagnostics::An_export_declaration_must_reference_a_value_when_verbatimModuleSyntax_is_enabled_but_0_only_refers_to_a_type
                    } else {
                        &tsc_diagnostics::An_export_default_must_reference_a_value_when_verbatimModuleSyntax_is_enabled_but_0_only_refers_to_a_type
                    };
                    self.error(Some(id), message, &[node_text(&nodes, id)]);
                }
                if !is_illegal_export_default_in_cjs
                    && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
                    && self.compiler_options.get_isolated_modules()
                    && !sym_flags(self, sym).intersects(ast::SymbolFlags::VALUE)
                {
                    let non_local_meanings = self.get_symbol_flags_ex(
                        sym, false, /*excludeTypeOnlyMeanings*/
                        true,  /*excludeLocalMeanings*/
                    );
                    if sym_flags(self, sym).intersects(ast::SymbolFlags::ALIAS)
                        && non_local_meanings.intersects(ast::SymbolFlags::TYPE)
                        && !non_local_meanings.intersects(ast::SymbolFlags::VALUE)
                        && (type_only_declaration.is_none()
                            || type_only_declaration.is_some_and(|tod| {
                                let tod_file = ast::get_source_file_of_node(
                                    Some(tod),
                                    &self.program_nodes(tod),
                                );
                                tod_file != Some(source_file)
                            }))
                    {
                        // import { SomeType } from "./someModule";
                        // export default SomeType; OR
                        // export = SomeType;
                        let message: &'static tsc_diagnostics::Message = if is_export_equals {
                            &tsc_diagnostics::X_0_resolves_to_a_type_and_must_be_marked_type_only_in_this_file_before_re_exporting_when_1_is_enabled_Consider_using_import_type_where_0_is_imported
                        } else {
                            &tsc_diagnostics::X_0_resolves_to_a_type_and_must_be_marked_type_only_in_this_file_before_re_exporting_when_1_is_enabled_Consider_using_export_type_0_as_default
                        };
                        let flag_name = self.get_isolated_modules_like_flag_name();
                        self.error(Some(id), message, &[node_text(&nodes, id), flag_name]);
                    } else if type_only_declaration.is_some_and(|tod| {
                        let tod_file =
                            ast::get_source_file_of_node(Some(tod), &self.program_nodes(tod));
                        tod_file != Some(source_file)
                    }) {
                        // import { SomeTypeOnlyValue } from "./someModule";
                        // export default SomeTypeOnlyValue; OR
                        // export = SomeTypeOnlyValue;
                        let message: &'static tsc_diagnostics::Message = if is_export_equals {
                            &tsc_diagnostics::X_0_resolves_to_a_type_only_declaration_and_must_be_marked_type_only_in_this_file_before_re_exporting_when_1_is_enabled_Consider_using_import_type_where_0_is_imported
                        } else {
                            &tsc_diagnostics::X_0_resolves_to_a_type_only_declaration_and_must_be_marked_type_only_in_this_file_before_re_exporting_when_1_is_enabled_Consider_using_export_type_0_as_default
                        };
                        let flag_name = self.get_isolated_modules_like_flag_name();
                        let diagnostic =
                            self.error(Some(id), message, &[node_text(&nodes, id), flag_name]);
                        if let Some(diagnostic) = diagnostic {
                            self.add_type_only_declaration_related_info(
                                diagnostic,
                                type_only_declaration,
                                &node_text(&nodes, id),
                            );
                        }
                    }
                }
            }
        }
        if is_illegal_export_default_in_cjs {
            let message = get_verbatim_module_syntax_error_message(node, &nodes);
            self.error(Some(node), message, &[]);
        }
        let mut container = nodes[node].parent;
        if !container.is_some_and(|c| ast::is_source_file(&nodes[c])) {
            container = container.and_then(|c| nodes[c].parent);
        }
        if let Some(container) = container {
            self.check_external_module_exports(container);
        }
        let type_node = nodes[node].type_();
        if type_node.is_some() && nodes[node].kind == ast::Kind::ExportAssignment {
            let t = self.get_type_from_type_node(type_node.unwrap());
            self.check_type_assignable_to_and_optionally_elaborate(
                expr_type,
                t,
                Some(expr_node),
                Some(expr_node),
                None, /*headMessage*/
                None,
            );
        }
        if nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
            && !ast::is_entity_name_expression(&nodes[expr_node], &nodes)
        {
            self.grammar_error_on_node(
                expr_node,
                &tsc_diagnostics::The_expression_of_an_export_assignment_must_be_an_identifier_or_qualified_name_in_an_ambient_context,
                &[],
            );
        }
        if is_export_equals {
            // Forbid export= in esm implementation files, and esm mode declaration files
            let implied_format = self
                .program
                .as_ref()
                .expect("program")
                .get_implied_node_format_for_emit(nodes[source_file].as_source_file());
            if self.module_kind >= ModuleKind::ES2015
                && self.module_kind != ModuleKind::Preserve
                && ((nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
                    && implied_format == ModuleKind::ESNext)
                    || (!nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
                        && implied_format != ModuleKind::CommonJS))
            {
                // export assignment is not supported in es6 modules
                self.grammar_error_on_node(
                    node,
                    &tsc_diagnostics::Export_assignment_cannot_be_used_when_targeting_ECMAScript_modules_Consider_using_export_default_or_another_module_format_instead,
                    &[],
                );
            } else if self.module_kind == ModuleKind::System
                && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
            {
                // system modules does not support export assignment
                self.grammar_error_on_node(
                    node,
                    &tsc_diagnostics::Export_assignment_is_not_supported_when_module_flag_is_system,
                    &[],
                );
            }
        }
    }

    /// `(c *Checker) checkExternalModuleExports` (checker.go).
    pub(crate) fn check_external_module_exports(&mut self, node: NodeId) {
        let Some(module_symbol) = self.get_symbol_of_declaration(node) else {
            return;
        };
        if self.module_symbol_links.get(module_symbol).exports_checked {
            return;
        }
        {
            let export_equals_symbol = self.symbol_arena.borrow()[module_symbol.index()]
                .exports
                .get(ast::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
                .copied();
            // An export assignment is in error if (a) the module exports value members or (b) if the module exports type or
            // namespace members and the exported entity also exports type or namespace members.
            if let Some(export_equals_symbol) = export_equals_symbol {
                if self.has_exported_members_of_kind(module_symbol, ast::SymbolFlags::VALUE)
                    || self.has_shadowed_namespace(export_equals_symbol)
                {
                    let declaration = self
                        .get_declaration_of_alias_symbol(export_equals_symbol)
                        .or_else(|| sym_value_declaration(self, export_equals_symbol));
                    if declaration.is_some_and(|d| {
                        let __program = self.program.clone().expect("program");
                        let dn = __program.nodes((d).file_index());
                        !crate::utilities::is_top_level_in_external_module_augmentation(
                            Some(d),
                            &dn,
                        )
                    }) {
                        self.error(
                            declaration,
                            &tsc_diagnostics::An_export_assignment_cannot_be_used_in_a_module_with_other_exported_elements,
                            &[],
                        );
                    }
                }
            }
            // Checks for export * conflicts
            let exports = self.get_exports_of_module(module_symbol);
            for (id, symbol) in exports.entries() {
                if id.as_ref() == ast::INTERNAL_SYMBOL_NAME_EXPORT_STAR {
                    continue;
                }
                let symbol = *symbol;
                let symbol_flags = sym_flags(self, symbol);
                // ECMA262: 15.2.1.1 It is a Syntax Error if the ExportedNames of ModuleItemList contains any duplicate entries.
                // (TS Exceptions: namespaces, function overloads, enums, and interfaces)
                if symbol_flags.intersects(ast::SymbolFlags::NAMESPACE | ast::SymbolFlags::ENUM) {
                    continue;
                }
                let declarations = sym_declarations(self, symbol);
                let exported_declarations_count = declarations
                    .iter()
                    .filter(|&&d| {
                        let __program = self.program.clone().expect("program");
                        let dn = __program.nodes((d).file_index());
                        is_not_overload(&dn[d], &dn)
                            && !ast::is_accessor(&dn[d])
                            && !ast::is_interface_declaration(&dn[d])
                    })
                    .count();
                if symbol_flags.intersects(ast::SymbolFlags::TYPE_ALIAS)
                    && exported_declarations_count <= 2
                {
                    // it is legal to merge type alias with other values
                    // so count should be either 1 (just type alias) or 2 (type alias + merged value)
                    continue;
                }
                if exported_declarations_count > 1
                    && !declarations.iter().all(|&d| {
                        let __program = self.program.clone().expect("program");
                        let dn = __program.nodes((d).file_index());
                        ast::get_assignment_declaration_kind(d, &dn)
                            == ast::JsDeclarationKind::ExportsProperty
                    })
                {
                    for &declaration in &declarations {
                        let __program = self.program.clone().expect("program");
                        let dn = __program.nodes((declaration).file_index());
                        if is_not_overload(&dn[declaration], &dn) {
                            self.error(
                                Some(declaration),
                                &tsc_diagnostics::Cannot_redeclare_exported_variable_0,
                                &[id.to_string()],
                            );
                        }
                    }
                }
            }
            self.module_symbol_links.get(module_symbol).exports_checked = true;
        }
    }

    /// `(c *Checker) hasExportedMembersOfKind` (checker.go).
    pub(crate) fn has_exported_members_of_kind(
        &mut self,
        module_symbol: SymbolId,
        kind: ast::SymbolFlags,
    ) -> bool {
        let exports = sym_exports(self, module_symbol);
        let entries: Vec<(String, SymbolId)> =
            exports.entries().map(|(k, &v)| (k.to_string(), v)).collect();
        for (name, symbol) in entries {
            if name != ast::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
                && self.get_symbol_flags(symbol).intersects(kind)
            {
                return true;
            }
        }
        false
    }

    /// `(c *Checker) hasShadowedNamespace` (checker.go).
    pub(crate) fn has_shadowed_namespace(&mut self, symbol: SymbolId) -> bool {
        let flags = sym_flags(self, symbol);
        if flags.intersects(ast::SymbolFlags::NAMESPACE_MODULE)
            && flags.intersects(ast::SymbolFlags::ALIAS)
        {
            let target = self.resolve_alias(symbol);
            if sym_flags(self, target).intersects(ast::SymbolFlags::NAMESPACE)
                && self.has_exported_members_of_kind(
                    target,
                    ast::SymbolFlags::TYPE | ast::SymbolFlags::NAMESPACE,
                )
            {
                return true;
            }
        }
        false
    }

    /// `(c *Checker) checkMissingDeclaration` (checker.go).
    pub(crate) fn check_missing_declaration(&mut self, node: NodeId) {
        self.check_decorators(node);
    }

    /// `(c *Checker) checkVariableStatement` (checker.go).
    pub(crate) fn check_variable_statement(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let declaration_list = nodes[node].as_variable_statement().declaration_list;
        let declaration_list = declaration_list.expect("declarationList");
        if !self.check_grammar_modifiers(node)
            && !self.check_grammar_variable_declaration_list(declaration_list)
        {
            self.check_grammar_for_disallowed_block_scoped_variable_statement(node);
        }
        self.check_variable_declaration_list(declaration_list);
    }

    /// `(c *Checker) checkVariableDeclarationList` (checker.go).
    pub(crate) fn check_variable_declaration_list(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let block_scope_kind =
            ast::get_combined_node_flags(node, &nodes) & ast::NodeFlags::BLOCK_SCOPED;
        if (block_scope_kind == ast::NodeFlags::USING
            || block_scope_kind == ast::NodeFlags::AWAIT_USING)
            && self.language_version
                < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET.using_and_await_using
        {
            self.check_external_emit_helpers(
                node,
                crate::types::ExternalEmitHelpers::ADD_DISPOSABLE_RESOURCE_AND_DISPOSE_RESOURCES,
            );
        }
        let decls = nodes[node]
            .as_variable_declaration_list()
            .declarations
            .as_ref()
            .map(|l| l.nodes().to_vec())
            .unwrap_or_default();
        self.check_source_elements(&decls);
    }

    /// `(c *Checker) checkVariableDeclaration` (checker.go).
    pub(crate) fn check_variable_declaration(&mut self, node: NodeId) {
        self.check_grammar_variable_declaration(node);
        self.check_variable_like_declaration(node);
    }

    /// `(c *Checker) checkVariableLikeDeclaration` (checker.go).
    ///
    /// Check variable, parameter, or property declaration
    pub(crate) fn check_variable_like_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_decorators(node);
        let Some(name) = nodes[node].name() else {
            return; // Missing array binding elements have no name
        };
        let type_node = nodes[node].type_();
        let initializer = nodes[node].initializer();
        if !ast::is_binding_element(&nodes[node]) {
            self.check_source_element(type_node);
        }
        // For a computed property, just check the initializer and exit
        // Do not use hasDynamicName here, because that returns false for well known symbols.
        // We want to perform checkComputedPropertyName for all computed properties, including
        // well known symbols.
        if ast::is_computed_property_name(&nodes[name]) {
            self.check_computed_property_name(name);
            if let Some(initializer) = initializer {
                self.check_expression_cached(initializer);
            }
        }
        if ast::is_binding_element(&nodes[node]) {
            let prop_name = nodes[node].property_name();
            if let Some(prop_name) = prop_name {
                if ast::is_private_identifier(&nodes[prop_name]) {
                    self.grammar_error_on_node(
                        prop_name,
                        &tsc_diagnostics::Private_identifiers_cannot_be_used_in_destructuring_patterns,
                        &[],
                    );
                }
            }
            if prop_name.is_some()
                && ast::is_identifier(&nodes[name])
                && ast::is_part_of_parameter_declaration(node, &nodes)
                && {
                    let f = crate::utilities::get_containing_function(node, &nodes);
                    f.is_some_and(|f| {
                        let __program = self.program.clone().expect("program");
                        let fn_ = __program.nodes((f).file_index());
                        ast::node_is_missing(fn_[f].body(), &fn_)
                    })
                }
            {
                // type F = ({a: string}) => void;
                //               ^^^^^^
                // variable renaming in function type notation is confusing,
                // so we forbid it even if noUnusedLocals is not enabled
                self.renamed_binding_elements_in_types.push(node);
                return;
            }
            if nodes[node]
                .parent
                .is_some_and(|p| ast::is_object_binding_pattern(&nodes[p]))
                && crate::utilities::has_dot_dot_dot_token(&nodes[node], &nodes)
                && self.language_version
                    < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET.object_spread_rest
            {
                self.check_external_emit_helpers(node, crate::types::ExternalEmitHelpers::REST);
            }
            // check computed properties inside property names of binding elements
            if let Some(prop_name) = prop_name {
                if ast::is_computed_property_name(&nodes[prop_name]) {
                    self.check_computed_property_name(prop_name);
                }
            }
            // check private/protected variable access
            let parent = nodes[node].parent.and_then(|p| nodes[p].parent);
            let parent_check_mode = if crate::utilities::has_dot_dot_dot_token(&nodes[node], &nodes)
            {
                CheckMode::REST_BINDING_ELEMENT
            } else {
                CheckMode::NORMAL
            };
            let parent_type =
                parent.and_then(|p| self.get_type_for_binding_element_parent(p, parent_check_mode));
            let prop_name_name = nodes[node].property_name_or_name();
            if parent_type.is_some()
                && !prop_name_name.is_some_and(|p| ast::is_binding_pattern(&nodes[p]))
            {
                if let Some(prop_name_name) = prop_name_name {
                    let expr_type = self.get_literal_type_from_property_name(prop_name_name);
                    if crate::types::is_type_usable_as_property_name(&self.types, expr_type) {
                        let name_text =
                            crate::utilities::get_property_name_from_type(&self.types, expr_type);
                        let property = self.get_property_of_type(parent_type.unwrap(), &name_text);
                        if let Some(property) = property {
                            self.mark_property_as_referenced(
                                property, None,  /*nodeForCheckWriteOnly*/
                                false, /*isSelfTypeAccess*/
                            );
                            // A destructuring is never a write-only reference.
                            let parent_node = parent.unwrap();
                            let __program = self.program.clone().expect("program");
                            let pn = __program.nodes((parent_node).file_index());
                            let is_super = pn[parent_node]
                                .initializer()
                                .is_some_and(|i| pn[i].kind == ast::Kind::SuperKeyword);
                            self.check_property_accessibility(
                                node,
                                is_super,
                                false, /*writing*/
                                parent_type.unwrap(),
                                property,
                            );
                        }
                    }
                }
            }
        }
        // For a binding pattern, check contained binding elements
        if ast::is_binding_pattern(&nodes[name]) {
            let elements = nodes[name].elements().unwrap_or(&[]).to_vec();
            self.check_source_elements(&elements);
        }
        // For a parameter declaration with an initializer, error and exit if the containing function doesn't have a body
        if initializer.is_some() && ast::is_part_of_parameter_declaration(node, &nodes) {
            let f = crate::utilities::get_containing_function(node, &nodes);
            if f.is_some_and(|f| {
                let __program = self.program.clone().expect("program");
                let fn_ = __program.nodes((f).file_index());
                ast::node_is_missing(fn_[f].body(), &fn_)
            }) {
                self.error(
                    Some(node),
                    &tsc_diagnostics::A_parameter_initializer_is_only_allowed_in_a_function_or_constructor_implementation,
                    &[],
                );
                return;
            }
        }
        // For a binding pattern, validate the initializer and exit
        if ast::is_binding_pattern(&nodes[name]) {
            if self.is_in_ambient_or_type_node(node) {
                return;
            }
            let need_check_initializer = initializer.is_some()
                && nodes[node]
                    .parent
                    .and_then(|p| nodes[p].parent)
                    .is_none_or(|gp| nodes[gp].kind != ast::Kind::ForInStatement);
            let need_check_widened_type = !nodes[name]
                .elements()
                .unwrap_or(&[])
                .iter()
                .any(|&n| nodes[n].name().is_some());
            if need_check_initializer || need_check_widened_type {
                // Don't validate for-in initializer as it is already an error
                let widened_type = self.get_widened_type_for_variable_like_declaration(
                    node, false, /*reportErrors*/
                );
                if need_check_initializer {
                    let initializer = initializer.unwrap();
                    let initializer_type = self.check_expression_cached(initializer);
                    if self.strict_null_checks && need_check_widened_type {
                        self.check_non_null_non_void_type(initializer_type, node);
                    } else {
                        let widened =
                            self.get_widened_type_for_variable_like_declaration(node, false);
                        self.check_type_assignable_to_and_optionally_elaborate(
                            initializer_type,
                            widened,
                            Some(node),
                            Some(initializer),
                            None,
                            None,
                        );
                    }
                }
                // check the binding pattern with empty elements
                if need_check_widened_type {
                    if ast::is_array_binding_pattern(&nodes[name]) {
                        self.check_iterated_type_or_element_type(
                            crate::checker_types::IterationUse::DESTRUCTURING,
                            widened_type,
                            self.undefined_type,
                            Some(node),
                        );
                    } else if self.strict_null_checks {
                        self.check_non_null_non_void_type(widened_type, node);
                    }
                }
            }
            return;
        }
        // For a commonjs `const x = require`, validate the alias and exit
        let symbol = self
            .get_symbol_of_declaration(node)
            .expect("declaration symbol");
        if sym_flags(self, symbol).intersects(ast::SymbolFlags::ALIAS)
            && ast::is_variable_declaration_initialized_to_require(node, &nodes)
        {
            self.check_alias_symbol(node);
            return;
        }
        if ast::is_big_int_literal(&nodes[name]) {
            self.error(
                Some(name),
                &tsc_diagnostics::A_bigint_literal_cannot_be_used_as_a_property_name,
                &[],
            );
        }
        let sym_t = self.get_type_of_symbol(symbol);
        let t = self.convert_auto_to_any(sym_t);
        if Some(node) == sym_value_declaration(self, symbol) {
            // Node is the primary declaration of the symbol, just validate the initializer
            // Don't validate for-in initializer as it is already an error
            if let Some(initializer) = initializer {
                if !nodes[node]
                    .parent
                    .and_then(|p| nodes[p].parent)
                    .is_some_and(|gp| ast::is_for_in_statement(&nodes[gp]))
                {
                    let initializer_type = self.check_expression_cached(initializer);
                    self.check_type_assignable_to_and_optionally_elaborate(
                        initializer_type,
                        t,
                        Some(node),
                        Some(initializer),
                        None, /*headMessage*/
                        None,
                    );
                    let block_scope_kind =
                        self.get_combined_node_flags_cached(node) & ast::NodeFlags::BLOCK_SCOPED;
                    if block_scope_kind == ast::NodeFlags::AWAIT_USING {
                        let global_async_disposable_type = self.get_global_async_disposable_type();
                        let global_disposable_type = self.get_global_disposable_type();
                        if global_async_disposable_type != self.empty_object_type
                            && global_disposable_type != self.empty_object_type
                        {
                            let optional_disposable_type = self.get_union_type(&[
                                global_async_disposable_type,
                                global_disposable_type,
                                self.null_type,
                                self.undefined_type,
                            ]);
                            let widened = self.widen_type_for_variable_like_declaration(
                                Some(initializer_type),
                                node,
                                false,
                            );
                            self.check_type_assignable_to(
                                widened,
                                optional_disposable_type,
                                Some(initializer),
                                Some(
                                    &tsc_diagnostics::The_initializer_of_an_await_using_declaration_must_be_either_an_object_with_a_Symbol_asyncDispose_or_Symbol_dispose_method_or_be_null_or_undefined,
                                ),
                            );
                        }
                    } else if block_scope_kind == ast::NodeFlags::USING {
                        let global_disposable_type = self.get_global_disposable_type();
                        if global_disposable_type != self.empty_object_type {
                            let optional_disposable_type = self.get_union_type(&[
                                global_disposable_type,
                                self.null_type,
                                self.undefined_type,
                            ]);
                            let widened_initializer_type = self
                                .widen_type_for_variable_like_declaration(
                                    Some(initializer_type),
                                    node,
                                    false,
                                );
                            let mut diags: Vec<ast::diagnostic::DiagnosticRef> = Vec::new();
                            if !self.check_type_assignable_to_ex(
                                widened_initializer_type,
                                optional_disposable_type,
                                Some(initializer),
                                Some(
                                    &tsc_diagnostics::The_initializer_of_a_using_declaration_must_be_either_an_object_with_a_Symbol_dispose_method_or_be_null_or_undefined,
                                ),
                                Some(&mut diags),
                            ) {
                                let global_async_disposable_type =
                                    self.get_global_async_disposable_type();
                                let optional_async_disposable_type = self.get_union_type(&[
                                    global_async_disposable_type,
                                    self.null_type,
                                    self.undefined_type,
                                ]);
                                if global_async_disposable_type != self.empty_object_type
                                    && self.is_type_assignable_to(
                                        widened_initializer_type,
                                        optional_async_disposable_type,
                                    )
                                {
                                    ast::diagnostic::lock_diagnostic(&diags[0])
                                        .add_message_chain(
                                            Some(ast::diagnostic::new_diagnostic_chain(
                                                None,
                                                &tsc_diagnostics::This_initializer_has_a_Symbol_asyncDispose_method_Did_you_mean_to_use_await_using,
                                                &[] as &[String],
                                            )),
                                        );
                                }
                                if let Some(d) = diags.into_iter().next() {
                                    self.add_diagnostic(&d);
                                }
                            }
                        }
                    }
                }
            }
            if sym_declarations(self, symbol).len() > 1 {
                let has_mismatched = sym_declarations(self, symbol).iter().any(|&d| {
                    d != node
                        && {
                            let __program = self.program.clone().expect("program");
                            let dn = __program.nodes((d).file_index());
                            ast::is_variable_like(&dn[d])
                        }
                        && !self.are_declaration_flags_identical(d, node)
                });
                if has_mismatched {
                    let arg =
                        tsc_scanner::utilities::declaration_name_to_string(Some(name), &nodes);
                    self.error(
                        Some(name),
                        &tsc_diagnostics::All_declarations_of_0_must_have_identical_modifiers,
                        &[arg],
                    );
                }
            }
        } else {
            // Node is a secondary declaration, check that type is identical to primary declaration and check that
            // initializer is consistent with type associated with the node
            let widened = self.get_widened_type_for_variable_like_declaration(node, false);
            let declaration_type = self.convert_auto_to_any(widened);
            if !crate::utilities::is_error_type(&self.types, t)
                && !crate::utilities::is_error_type(&self.types, declaration_type)
                && !self.is_type_identical_to(t, declaration_type)
                && !sym_flags(self, symbol).intersects(ast::SymbolFlags::ASSIGNMENT)
            {
                self.error_next_variable_or_property_declaration_must_have_same_type(
                    sym_value_declaration(self, symbol),
                    t,
                    node,
                    declaration_type,
                );
            }
            if let Some(initializer) = initializer {
                let initializer_type = self.check_expression_cached(initializer);
                self.check_type_assignable_to_and_optionally_elaborate(
                    initializer_type,
                    declaration_type,
                    Some(node),
                    Some(initializer),
                    None, /*headMessage*/
                    None,
                );
            }
            if sym_value_declaration(self, symbol).is_some()
                && !self.are_declaration_flags_identical(
                    node,
                    sym_value_declaration(self, symbol).unwrap(),
                )
            {
                let arg = tsc_scanner::utilities::declaration_name_to_string(Some(name), &nodes);
                self.error(
                    Some(name),
                    &tsc_diagnostics::All_declarations_of_0_must_have_identical_modifiers,
                    &[arg],
                );
            }
        }
        if !ast::is_property_declaration(&nodes[node])
            && !ast::is_property_signature_declaration(&nodes[node])
        {
            // We know we don't have a binding pattern or computed name here
            self.check_exports_on_merged_declarations(node);
            if ast::is_variable_declaration(&nodes[node]) || ast::is_binding_element(&nodes[node]) {
                self.check_var_declared_names_not_shadowed(node);
            }
            self.check_collisions_for_declaration_name(node, nodes[node].name());
        }
    }

    /// `(c *Checker) errorNextVariableOrPropertyDeclarationMustHaveSameType` (checker.go).
    pub(crate) fn error_next_variable_or_property_declaration_must_have_same_type(
        &mut self,
        first_declaration: Option<NodeId>,
        first_type: TypeId,
        next_declaration: NodeId,
        next_type: TypeId,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((next_declaration).file_index());
        let next_declaration_name = ast::get_name_of_declaration(Some(next_declaration), &nodes);
        let message: &'static tsc_diagnostics::Message = if ast::is_property_declaration(
            &nodes[next_declaration],
        )
            || ast::is_property_signature_declaration(&nodes[next_declaration])
        {
            &tsc_diagnostics::Subsequent_property_declarations_must_have_the_same_type_Property_0_must_be_of_type_1_but_here_has_type_2
        } else {
            &tsc_diagnostics::Subsequent_variable_declarations_must_have_the_same_type_Variable_0_must_be_of_type_1_but_here_has_type_2
        };
        let decl_name =
            tsc_scanner::utilities::declaration_name_to_string(next_declaration_name, &nodes);
        let arg1 = self.type_to_string(first_type);
        let arg2 = self.type_to_string(next_type);
        if let Some(err) = self.error(
            next_declaration_name,
            message,
            &[decl_name.clone(), arg1, arg2],
        ) {
            if first_declaration.is_some() {
                let related = self.new_diagnostic_for_node(
                    first_declaration,
                    &tsc_diagnostics::X_0_was_also_declared_here,
                    &[decl_name],
                );
                ast::diagnostic::lock_diagnostic(&err).add_related_info(Some(related));
            }
        }
    }

    /// `(c *Checker) checkVarDeclaredNamesNotShadowed` (checker.go).
    pub(crate) fn check_var_declared_names_not_shadowed(&mut self, node: NodeId) {
        // - ScriptBody : StatementList
        // It is a Syntax Error if any element of the LexicallyDeclaredNames of StatementList
        // also occurs in the VarDeclaredNames of StatementList.
        // (see Go source for the full comment)
        //
        // skip block-scoped variables and parameters
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if self
            .get_combined_node_flags_cached(node)
            .intersects(ast::NodeFlags::BLOCK_SCOPED)
            || ast::is_part_of_parameter_declaration(node, &nodes)
        {
            return;
        }
        // NOTE: in ES6 spec initializer is required in variable declarations where name is binding pattern
        // so we'll always treat binding elements as initialized
        let symbol = self
            .get_symbol_of_declaration(node)
            .expect("declaration symbol");
        let name = nodes[node].name().expect("name");
        if sym_flags(self, symbol).intersects(ast::SymbolFlags::FUNCTION_SCOPED_VARIABLE) {
            if !ast::is_identifier(&nodes[name]) {
                panic!("Identifier expected")
            }
            let name_text = node_text(&nodes, name);
            let local_declaration_symbol = call_resolve_name(
                self,
                Some(node),
                &name_text,
                ast::SymbolFlags::VARIABLE,
                None,  /*nameNotFoundMessage*/
                false, /*isUse*/
                false,
            );
            if let Some(local_declaration_symbol) = local_declaration_symbol {
                if local_declaration_symbol != symbol
                    && sym_flags(self, local_declaration_symbol)
                        .intersects(ast::SymbolFlags::BLOCK_SCOPED_VARIABLE)
                {
                    if self
                        .get_declaration_node_flags_from_symbol(local_declaration_symbol)
                        .intersects(ast::NodeFlags::BLOCK_SCOPED)
                    {
                        let value_decl = sym_value_declaration(self, local_declaration_symbol);
                        let var_decl_list = value_decl.and_then(|vd| {
                            let __program = self.program.clone().expect("program");
                            let dn = __program.nodes((vd).file_index());
                            ast::find_ancestor_kind(
                                Some(vd),
                                ast::Kind::VariableDeclarationList,
                                &dn,
                            )
                        });
                        let mut container: Option<NodeId> = None;
                        if let Some(var_decl_list) = var_decl_list {
                            let __program = self.program.clone().expect("program");
                            let dn = __program.nodes((var_decl_list).file_index());
                            if dn[var_decl_list]
                                .parent
                                .is_some_and(|p| ast::is_variable_statement(&dn[p]))
                                && dn[var_decl_list]
                                    .parent
                                    .and_then(|p| dn[p].parent)
                                    .is_some()
                            {
                                container = dn[var_decl_list].parent.and_then(|p| dn[p].parent);
                            }
                        }
                        // names of block-scoped and function scoped variables can collide only
                        // if block scoped variable is defined in the function\module\source file scope (because of variable hoisting)
                        let names_share_scope = container.is_some_and(|c| {
                            let __program = self.program.clone().expect("program");
                            let cn = __program.nodes((c).file_index());
                            (ast::is_block(&cn[c])
                                && cn[c]
                                    .parent
                                    .is_some_and(|p| ast::is_function_like(Some(p), &cn)))
                                || ast::is_module_block(&cn[c])
                                || ast::is_module_declaration(&cn[c])
                                || ast::is_source_file(&cn[c])
                        });
                        // here we know that function scoped variable is "shadowed" by block scoped one
                        // a var declaration can't hoist past a lexical declaration and it results in a SyntaxError at runtime
                        if !names_share_scope {
                            let name = self.symbol_to_string(local_declaration_symbol);
                            self.error(
                                Some(node),
                                &tsc_diagnostics::Cannot_initialize_outer_scoped_variable_0_in_the_same_scope_as_block_scoped_declaration_1,
                                &[name.clone(), name],
                            );
                        }
                    }
                }
            }
        }
    }

    /// `(c *Checker) checkDecorators` (checker.go).
    pub(crate) fn check_decorators(&mut self, node: NodeId) {
        // skip this check for nodes that cannot have decorators. These should have already had an error reported by
        // checkGrammarModifiers.
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !ast::can_have_decorators(&nodes[node])
            || !ast::has_decorators(&nodes[node])
            || !ast::node_can_be_decorated(
                self.legacy_decorators,
                node,
                nodes[node].parent,
                nodes[node].parent.and_then(|p| nodes[p].parent),
                &nodes,
            )
        {
            return;
        }
        let Some(first_decorator) = nodes[node]
            .modifier_nodes()
            .unwrap_or(&[])
            .iter()
            .copied()
            .find(|&m| ast::is_decorator(&nodes[m]))
        else {
            return;
        };
        if self.legacy_decorators {
            self.check_external_emit_helpers(
                first_decorator,
                crate::types::ExternalEmitHelpers::DECORATE,
            );
            if ast::is_parameter_declaration(&nodes[node]) {
                self.check_external_emit_helpers(
                    first_decorator,
                    crate::types::ExternalEmitHelpers::PARAM,
                );
            }
        } else if self.language_version
            < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET.class_and_class_element_decorators
        {
            self.check_external_emit_helpers(
                first_decorator,
                crate::types::ExternalEmitHelpers::ES_DECORATE_AND_RUN_INITIALIZERS,
            );
            if ast::is_class_declaration(&nodes[node]) {
                if nodes[node].name().is_none()
                    || self
                        .get_first_transformable_static_class_element(node)
                        .is_some()
                {
                    self.check_external_emit_helpers(
                        first_decorator,
                        crate::types::ExternalEmitHelpers::SET_FUNCTION_NAME,
                    );
                }
            } else if !ast::is_class_expression(&nodes[node]) {
                let name = nodes[node].name();
                if name.is_some_and(|n| ast::is_private_identifier(&nodes[n]))
                    && (ast::is_method_declaration(&nodes[node])
                        || ast::is_accessor(&nodes[node])
                        || ast::is_auto_accessor_property_declaration(&nodes[node]))
                {
                    self.check_external_emit_helpers(
                        first_decorator,
                        crate::types::ExternalEmitHelpers::SET_FUNCTION_NAME,
                    );
                }
                if name.is_some_and(|n| ast::is_computed_property_name(&nodes[n])) {
                    self.check_external_emit_helpers(
                        first_decorator,
                        crate::types::ExternalEmitHelpers::PROP_KEY,
                    );
                }
            }
        }
        self.mark_linked_references(
            node,
            crate::checker_types::ReferenceHint::Decorator,
            None,
            None,
        
                None,
            );
        for &modifier in nodes[node].modifier_nodes().unwrap_or(&[]) {
            if ast::is_decorator(&nodes[modifier]) {
                self.check_decorator(modifier);
            }
        }
    }

    /// `(c *Checker) checkDecorator` (checker.go).
    pub(crate) fn check_decorator(&mut self, node: NodeId) {
        self.check_grammar_decorator(node);
        let signature = self
            .get_resolved_signature(node, None, CheckMode::NORMAL)
            .expect("resolved signature");
        self.check_deprecated_signature(signature, node);
        let return_type = self.get_return_type_of_signature(signature);
        if tflags(self, return_type).intersects(TypeFlags::ANY) {
            return;
        }
        // if we fail to get a signature and return type here, we will have already reported a grammar error in `checkDecorators`.
        let decorator_signature = self.get_decorator_call_signature(node);
        let Some(decorator_signature) = decorator_signature else {
            return;
        };
        let Some(expected_return_type) = self
            .signature_arena
            .get(decorator_signature)
            .resolved_return_type
        else {
            return;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let head_message: &'static tsc_diagnostics::Message = match nodes[node]
            .parent
            .map(|p| nodes[p].kind)
        {
            Some(ast::Kind::ClassDeclaration) | Some(ast::Kind::ClassExpression) => {
                &tsc_diagnostics::Decorator_function_return_type_0_is_not_assignable_to_type_1
            }
            Some(ast::Kind::PropertyDeclaration) => {
                if !self.legacy_decorators {
                    &tsc_diagnostics::Decorator_function_return_type_0_is_not_assignable_to_type_1
                } else {
                    // falls through to KindParameter in Go
                    &tsc_diagnostics::Decorator_function_return_type_is_0_but_is_expected_to_be_void_or_any
                }
            }
            Some(ast::Kind::Parameter) => {
                &tsc_diagnostics::Decorator_function_return_type_is_0_but_is_expected_to_be_void_or_any
            }
            Some(ast::Kind::MethodDeclaration)
            | Some(ast::Kind::GetAccessor)
            | Some(ast::Kind::SetAccessor) => {
                &tsc_diagnostics::Decorator_function_return_type_0_is_not_assignable_to_type_1
            }
            _ => panic!("Unhandled case in checkDecorator"),
        };
        self.check_type_assignable_to(
            return_type,
            expected_return_type,
            nodes[node].expression(),
            Some(head_message),
        );
    }
}

/// `isInstantiatedModule` (checker.go) — free function.
fn is_instantiated_module(node: NodeId, preserve_const_enums: bool, nodes: &[ast::Node]) -> bool {
    let module_state = ast::get_module_instance_state(node, nodes);
    module_state == ast::ModuleInstanceState::Instantiated
        || preserve_const_enums && module_state == ast::ModuleInstanceState::ConstEnumOnly
}

/// `getFirstNonAmbientClassOrFunctionDeclaration` (checker.go) — free
/// function.
fn get_first_non_ambient_class_or_function_declaration(
    c: &mut Checker,
    symbol: SymbolId,
) -> Option<NodeId> {
    for declaration in sym_declarations(c, symbol) {
        let __program = c.program.clone().expect("program");
        let nodes = __program.nodes((declaration).file_index());
        if (ast::is_class_declaration(&nodes[declaration])
            || ast::is_function_declaration(&nodes[declaration])
                && ast::node_is_present(nodes[declaration].body(), &nodes))
            && !nodes[declaration].flags.intersects(ast::NodeFlags::AMBIENT)
        {
            return Some(declaration);
        }
    }
    None
}

/// `hasTypeJsonImportAttribute` (checker.go) — free function.
fn has_type_json_import_attribute(node: NodeId, nodes: &[ast::Node]) -> bool {
    let attributes = nodes[node].as_import_declaration().attributes;
    let Some(attributes) = attributes else {
        return false;
    };
    nodes[attributes]
        .as_import_attributes()
        .attributes
        .as_ref()
        .map(|l| l.nodes().to_vec())
        .unwrap_or_default()
        .iter()
        .any(|&attr| {
            nodes[attr]
                .name()
                .is_some_and(|n| &*nodes[n].text(nodes) == "type")
                && nodes[attr].as_import_attribute().value.is_some_and(|v| {
                    ast::is_string_literal_like(&nodes[v]) && &*nodes[v].text(nodes) == "json"
                })
        })
}

/// `isContainedByNamespace` (checker.go) — free function.
fn is_contained_by_namespace(node: NodeId, nodes: &[ast::Node]) -> bool {
    let mut container = nodes[node].parent;
    if !container.is_some_and(|c| ast::is_source_file(&nodes[c])) {
        container = container.and_then(|c| nodes[c].parent);
    }
    container.is_some_and(|c| {
        ast::is_module_declaration(&nodes[c]) && !ast::is_ambient_module(&nodes[c], nodes)
    })
}

/// `getVerbatimModuleSyntaxErrorMessage` (checker.go) — free function.
fn get_verbatim_module_syntax_error_message(
    node: NodeId,
    nodes: &[ast::Node],
) -> &'static tsc_diagnostics::Message {
    let source_file = ast::get_source_file_of_node(Some(node), nodes).expect("source file");
    let file_name = nodes[source_file].as_source_file().file_name();
    // Check if the file is .cts or .cjs (CommonJS-specific extensions)
    if tsc_tspath::file_extension_is_one_of(
        file_name.as_string(),
        &[tsc_tspath::EXTENSION_CTS, tsc_tspath::EXTENSION_CJS],
    ) {
        return &tsc_diagnostics::ECMAScript_imports_and_exports_cannot_be_written_in_a_CommonJS_file_under_verbatimModuleSyntax;
    }
    // For .ts, .tsx, .js, etc.
    &tsc_diagnostics::ECMAScript_imports_and_exports_cannot_be_written_in_a_CommonJS_file_under_verbatimModuleSyntax_Adjust_the_type_field_in_the_nearest_package_json_to_make_this_file_an_ECMAScript_module_or_adjust_your_verbatimModuleSyntax_module_and_moduleResolution_settings_in_TypeScript
}

/// `isNotOverload` (checker.go) — free function.
fn is_not_overload(node: &ast::Node, _nodes: &[ast::Node]) -> bool {
    !(ast::is_function_declaration(node) || ast::is_method_declaration(node))
        || node.body().is_some()
}

// ======== checker.go ~6296 — iteration types machinery ========

/// Clone the resolver bag without holding a `self` borrow. The resolvers
/// are assigned once in `initialize_iteration_resolvers` and never mutated
/// afterwards; cloning the `Rc` thunks frees callers to pass `&mut self`.
fn iter_resolver(
    r: &Option<Box<crate::checker_types::IterationTypesResolver>>,
) -> crate::checker_types::IterationTypesResolver {
    r.as_deref().expect("iteration types resolver").clone()
}

impl Checker {
    /// `(c *Checker) checkIteratedTypeOrElementType` (checker.go).
    pub(crate) fn check_iterated_type_or_element_type(
        &mut self,
        r#use: IterationUse,
        input_type: TypeId,
        sent_type: TypeId,
        error_node: Option<NodeId>,
    ) -> TypeId {
        if crate::utilities::is_type_any(&self.types, input_type) {
            return input_type;
        }
        let t = self.get_iterated_type_or_element_type(
            r#use, input_type, sent_type, error_node, true, /*checkAssignability*/
        );
        t.unwrap_or(self.any_type)
    }

    /// `(c *Checker) getIteratedTypeOrElementType` (checker.go).
    pub(crate) fn get_iterated_type_or_element_type(
        &mut self,
        r#use: IterationUse,
        input_type: TypeId,
        sent_type: TypeId,
        error_node: Option<NodeId>,
        check_assignability: bool,
    ) -> Option<TypeId> {
        let allow_async_iterables = r#use.contains(IterationUse::ALLOWS_ASYNC_ITERABLES_FLAG);
        if input_type == self.never_type {
            if let Some(error_node) = error_node {
                self.report_type_not_iterable_error(error_node, input_type, allow_async_iterables);
            }
            return None;
        }
        let iterable_exists = {
            let thunk = self
                .get_global_iterable_type
                .clone()
                .expect("getGlobalIterableType");
            thunk(self) != self.empty_generic_type
        };
        let possible_out_of_bounds = self.compiler_options.no_unchecked_indexed_access.is_true()
            && r#use.contains(IterationUse::POSSIBLY_OUT_OF_BOUNDS);
        if iterable_exists || allow_async_iterables {
            let iteration_types = self.get_iteration_types_of_iterable(
                input_type,
                r#use,
                if iterable_exists { error_node } else { None },
            );
            if check_assignability {
                if let Some(next_type) = iteration_types.next_type {
                    let diagnostic: Option<&'static tsc_diagnostics::Message> = if r#use
                        .contains(IterationUse::FOR_OF_FLAG)
                    {
                        Some(&tsc_diagnostics::Cannot_iterate_value_because_the_next_method_of_its_iterator_expects_type_1_but_for_of_will_always_send_0)
                    } else if r#use.contains(IterationUse::SPREAD_FLAG) {
                        Some(&tsc_diagnostics::Cannot_iterate_value_because_the_next_method_of_its_iterator_expects_type_1_but_array_spread_will_always_send_0)
                    } else if r#use.contains(IterationUse::DESTRUCTURING_FLAG) {
                        Some(&tsc_diagnostics::Cannot_iterate_value_because_the_next_method_of_its_iterator_expects_type_1_but_array_destructuring_will_always_send_0)
                    } else if r#use.contains(IterationUse::YIELD_STAR_FLAG) {
                        Some(&tsc_diagnostics::Cannot_delegate_iteration_to_value_because_the_next_method_of_its_iterator_expects_type_1_but_the_containing_generator_will_always_send_0)
                    } else {
                        None
                    };
                    if let Some(diagnostic) = diagnostic {
                        self.check_type_assignable_to(
                            sent_type,
                            next_type,
                            error_node,
                            Some(diagnostic),
                        );
                    }
                }
            }
            if iteration_types.yield_type.is_some() || iterable_exists {
                let yield_type = iteration_types.yield_type?;
                if possible_out_of_bounds {
                    return self.include_undefined_in_index_signature(Some(yield_type));
                }
                return Some(yield_type);
            }
        }
        let mut array_type = input_type;
        let mut has_string_constituent = false;
        // If strings are permitted, remove any string-like constituents from the array type.
        // This allows us to find other non-string element types from an array unioned with
        // a string.
        if r#use.contains(IterationUse::ALLOWS_STRING_INPUT_FLAG) {
            if tflags(self, array_type).intersects(TypeFlags::UNION) {
                // After we remove all types that are StringLike, we will know if there was a string constituent
                // based on whether the result of filter is a new array.
                let array_types = self.types.get_ref(array_type).types_rc();
                let filtered_types: Vec<TypeId> = array_types
                    .iter()
                    .copied()
                    .filter(|&t| !tflags(self, t).intersects(TypeFlags::STRING_LIKE))
                    .collect();
                if filtered_types.len() != array_types.len() {
                    array_type = self.get_union_type_ex(
                        &filtered_types,
                        crate::types::UnionReduction::Subtype,
                        None,
                        None,
                    );
                }
            } else if tflags(self, array_type).intersects(TypeFlags::STRING_LIKE) {
                array_type = self.never_type;
            }
            has_string_constituent = array_type != input_type;
            if has_string_constituent {
                // Now that we've removed all the StringLike types, if no constituents remain, then the entire
                // arrayOrStringType was a string.
                if tflags(self, array_type).intersects(TypeFlags::NEVER) {
                    if possible_out_of_bounds {
                        return self.include_undefined_in_index_signature(Some(self.string_type));
                    }
                    return Some(self.string_type);
                }
            }
        }
        if !self.is_array_like_type(array_type) {
            if let Some(error_node) = error_node {
                // Which error we report depends on whether we allow strings or if there was a
                // string constituent. For example, if the input type is number | string, we
                // want to say that number is not an array type. But if the input was just
                // number and string input is allowed, we want to say that number is not an
                // array type or a string type.
                let allows_strings = r#use.contains(IterationUse::ALLOWS_STRING_INPUT_FLAG)
                    && !has_string_constituent;
                let (default_diagnostic, maybe_missing_await) =
                    self.get_iteration_diagnostic_details(r#use, input_type, allows_strings);
                let arg = self.type_to_string(array_type);
                let suggest_await =
                    maybe_missing_await && self.get_awaited_type_of_promise(array_type).is_some();
                self.error_and_maybe_suggest_await(
                    error_node,
                    suggest_await,
                    default_diagnostic,
                    &[arg],
                );
            }
            if has_string_constituent {
                if possible_out_of_bounds {
                    return self.include_undefined_in_index_signature(Some(self.string_type));
                }
                return Some(self.string_type);
            }
            return None;
        }
        let array_element_type = self.get_index_type_of_type(array_type, self.number_type);
        if has_string_constituent && array_element_type.is_some() {
            let array_element_type = array_element_type.unwrap();
            // This is just an optimization for the case where arrayOrStringType is string | string[]
            if tflags(self, array_element_type).intersects(TypeFlags::STRING_LIKE)
                && !self.compiler_options.no_unchecked_indexed_access.is_true()
            {
                return Some(self.string_type);
            }
            if possible_out_of_bounds {
                return Some(self.get_union_type_ex(
                    &[array_element_type, self.string_type, self.undefined_type],
                    crate::types::UnionReduction::Subtype,
                    None,
                    None,
                ));
            }
            return Some(self.get_union_type_ex(
                &[array_element_type, self.string_type],
                crate::types::UnionReduction::Subtype,
                None,
                None,
            ));
        }
        if r#use.contains(IterationUse::POSSIBLY_OUT_OF_BOUNDS) {
            return self.include_undefined_in_index_signature(Some(
                array_element_type.unwrap_or(self.error_type),
            ));
        }
        array_element_type
    }

    /// `(c *Checker) getIterationTypeOfGeneratorFunctionReturnType` (checker.go).
    ///
    /// Gets the requested "iteration type" from a type that is either `Iterable`-like, `Iterator`-like,
    /// `IterableIterator`-like, or `Generator`-like (for a non-async generator); or `AsyncIterable`-like,
    /// `AsyncIterator`-like, `AsyncIterableIterator`-like, or `AsyncGenerator`-like (for an async generator).
    pub(crate) fn get_iteration_type_of_generator_function_return_type(
        &mut self,
        type_kind: IterationTypeKind,
        return_type: TypeId,
        is_async_generator: bool,
    ) -> Option<TypeId> {
        if crate::utilities::is_type_any(&self.types, return_type) {
            return None;
        }
        let iteration_types = self
            .get_iteration_types_of_generator_function_return_type(return_type, is_async_generator);
        iteration_types.get_type(type_kind)
    }

    /// `(c *Checker) getIterationTypesOfGeneratorFunctionReturnType` (checker.go).
    pub(crate) fn get_iteration_types_of_generator_function_return_type(
        &mut self,
        t: TypeId,
        is_async_generator: bool,
    ) -> IterationTypes {
        if crate::utilities::is_type_any(&self.types, t) {
            return IterationTypes::any(self.any_type);
        }
        let r#use = if is_async_generator {
            IterationUse::ASYNC_GENERATOR_RETURN_TYPE
        } else {
            IterationUse::GENERATOR_RETURN_TYPE
        };
        let resolver = if is_async_generator {
            &self.async_iteration_types_resolver
        } else {
            &self.sync_iteration_types_resolver
        };
        let r = iter_resolver(resolver);
        let result = self.get_iteration_types_of_iterable(t, r#use, None /*errorNode*/);
        if result.has_types() {
            return result;
        }
        self.get_iteration_types_of_iterator(
            t, &r, None, /*errorNode*/
            None, /*diagnosticOutput*/
        )
    }

    /// `(c *Checker) getIterationTypeOfIterable` (checker.go).
    ///
    /// Gets the requested "iteration type" from an `Iterable`-like or `AsyncIterable`-like type.
    pub(crate) fn get_iteration_type_of_iterable(
        &mut self,
        r#use: IterationUse,
        type_kind: IterationTypeKind,
        input_type: TypeId,
        error_node: Option<NodeId>,
    ) -> Option<TypeId> {
        if crate::utilities::is_type_any(&self.types, input_type) {
            return None;
        }
        let iteration_types = self.get_iteration_types_of_iterable(input_type, r#use, error_node);
        iteration_types.get_type(type_kind)
    }

    /// `(c *Checker) getIterationTypesOfIterable` (checker.go).
    ///
    /// Gets the *yield*, *return*, and *next* types from an `Iterable`-like or `AsyncIterable`-like type.
    pub(crate) fn get_iteration_types_of_iterable(
        &mut self,
        t: TypeId,
        r#use: IterationUse,
        error_node: Option<NodeId>,
    ) -> IterationTypes {
        let t = self.get_reduced_type(t);
        if crate::utilities::is_type_any(&self.types, t) {
            return IterationTypes::any(self.any_type);
        }
        let key = IterationTypesKey {
            type_id: t,
            use_: r#use & IterationUse::CACHE_FLAGS,
        };
        // If we are reporting errors and encounter a cached `noIterationTypes`, we should ignore the cached value and continue as if nothing was cached.
        // In addition, we should not cache any new results for this call.
        let mut no_cache = false;
        if let Some(cached) = self.iteration_types_cache.get(&key) {
            if error_node.is_none() || cached.has_types() {
                return *cached;
            }
            no_cache = true;
        }
        let result = self.get_iteration_types_of_iterable_worker(t, r#use, error_node, no_cache);
        if !no_cache {
            self.iteration_types_cache.insert(key, result);
        }
        result
    }

    /// `(c *Checker) getIterationTypesOfIterableWorker` (checker.go).
    pub(crate) fn get_iteration_types_of_iterable_worker(
        &mut self,
        t: TypeId,
        r#use: IterationUse,
        error_node: Option<NodeId>,
        no_cache: bool,
    ) -> IterationTypes {
        let _ = no_cache; // caching handled by the caller
        if tflags(self, t).intersects(TypeFlags::UNION) {
            let constituents = self.types.get_ref(t).types_rc();
            let mut all_iteration_types: Vec<IterationTypes> =
                Vec::with_capacity(constituents.len());
            for constituent in (constituents).iter().copied() {
                let iteration_types =
                    self.get_iteration_types_of_iterable_worker(constituent, r#use, None, no_cache);
                if !iteration_types.has_types() {
                    if let Some(error_node) = error_node {
                        self.add_deferred_diagnostic(Box::new(move |c: &mut Checker| {
                            c.report_type_not_iterable_error(
                                error_node,
                                t,
                                r#use.contains(IterationUse::ALLOWS_ASYNC_ITERABLES_FLAG),
                            );
                        }));
                    }
                    return IterationTypes::default();
                }
                all_iteration_types.push(iteration_types);
            }
            return self.combine_iteration_types(&all_iteration_types);
        }
        let mut diags: Vec<ast::diagnostic::DiagnosticRef> = Vec::new();
        if r#use.contains(IterationUse::ALLOWS_ASYNC_ITERABLES_FLAG) {
            let r = iter_resolver(&self.async_iteration_types_resolver);
            let iteration_types = self.get_iteration_types_of_iterable_fast(t, &r);
            if iteration_types.has_types() {
                if r#use.contains(IterationUse::FOR_OF_FLAG) {
                    return self.get_async_from_sync_iteration_types(iteration_types, error_node);
                }
                return iteration_types;
            }
            let iteration_types =
                self.get_iteration_types_of_iterable_slow(t, &r, error_node, Some(&mut diags));
            if iteration_types.has_types() {
                for d in diags.drain(..) {
                    self.add_diagnostic(&d);
                }
                return iteration_types;
            }
        }
        if r#use.contains(IterationUse::ALLOWS_SYNC_ITERABLES_FLAG) {
            let r = iter_resolver(&self.sync_iteration_types_resolver);
            let iteration_types = self.get_iteration_types_of_iterable_fast(t, &r);
            if iteration_types.has_types() {
                if r#use.contains(IterationUse::ALLOWS_ASYNC_ITERABLES_FLAG) {
                    return self.get_async_from_sync_iteration_types(iteration_types, error_node);
                }
                return iteration_types;
            }
            let iteration_types =
                self.get_iteration_types_of_iterable_slow(t, &r, error_node, Some(&mut diags));
            if iteration_types.has_types() {
                for d in diags.drain(..) {
                    self.add_diagnostic(&d);
                }
                if r#use.contains(IterationUse::ALLOWS_ASYNC_ITERABLES_FLAG) {
                    return self.get_async_from_sync_iteration_types(iteration_types, error_node);
                }
                return iteration_types;
            }
        }
        if let Some(error_node) = error_node {
            // We defer the diagnostic because TypeToString may attempt to resolve symbols that are already being
            // resolved, possibly causing circularities.
            self.add_deferred_diagnostic(Box::new(move |c: &mut Checker| {
                let diagnostic = c.report_type_not_iterable_error(
                    error_node,
                    t,
                    r#use.contains(IterationUse::ALLOWS_ASYNC_ITERABLES_FLAG),
                );
                for d in &diags {
                    ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(d.clone()));
                }
            }));
        }
        IterationTypes::default()
    }

    /// `(c *Checker) getIterationTypesOfIterableFast` (checker.go).
    pub(crate) fn get_iteration_types_of_iterable_fast(
        &mut self,
        t: TypeId,
        r: &IterationTypesResolver,
    ) -> IterationTypes {
        // As an optimization, if the type is an instantiation of the following global type, then
        // just grab its related type arguments:
        // - `Iterable<T, TReturn, TNext>` or `AsyncIterable<T, TReturn, TNext>`
        // - `IteratorObject<T, TReturn, TNext>` or `AsyncIteratorObject<T, TReturn, TNext>`
        // - `IterableIterator<T, TReturn, TNext>` or `AsyncIterableIterator<T, TReturn, TNext>`
        // - `Generator<T, TReturn, TNext>` or `AsyncGenerator<T, TReturn, TNext>`
        let g_iterable = r.get_global_iterable_type.clone().expect("thunk");
        let g_iterator_object = r.get_global_iterator_object_type.clone().expect("thunk");
        let g_iterable_iterator = r.get_global_iterable_iterator_type.clone().expect("thunk");
        let g_generator = r.get_global_generator_type.clone().expect("thunk");
        let g_iterable_t = g_iterable(self);
        let g_iterator_object_t = g_iterator_object(self);
        let g_iterable_iterator_t = g_iterable_iterator(self);
        let g_generator_t = g_generator(self);
        if self.is_reference_to_type(t, g_iterable_t)
            || self.is_reference_to_type(t, g_iterator_object_t)
            || self.is_reference_to_type(t, g_iterable_iterator_t)
            || self.is_reference_to_type(t, g_generator_t)
        {
            let type_arguments = self.get_type_arguments(t);
            let _resolve = r.resolve_iteration_type.clone().expect("thunk");
            return get_resolved_iteration_types(
                self,
                r,
                type_arguments[0],
                type_arguments[1],
                type_arguments[2],
            );
        }
        // As an optimization, if the type is an instantiation of one of the following global types, then
        // just grab the related type argument:
        // - `ArrayIterator<T>`
        // - `MapIterator<T>`
        // - `SetIterator<T>`
        // - `StringIterator<T>`
        // - `ReadableStreamAsyncIterator<T>`
        let g_builtin = r.get_global_builtin_iterator_types.clone().expect("thunk");
        let g_builtin_t = g_builtin(self);
        if self.is_reference_to_some_type(t, &g_builtin_t) {
            let resolve = r.resolve_iteration_type.clone().expect("thunk");
            let arg0 = self.get_type_arguments(t)[0];
            let return_type = self.get_builtin_iterator_return_type();
            return IterationTypes {
                yield_type: Some(resolve(self, arg0, None)),
                return_type: Some(resolve(self, return_type, None)),
                next_type: Some(self.unknown_type),
            };
        }
        IterationTypes::default()
    }

    /// `(c *Checker) isReferenceToType` (checker.go).
    pub(crate) fn is_reference_to_type(&mut self, t: TypeId, target: TypeId) -> bool {
        tobject_flags(self, t).intersects(ObjectFlags::REFERENCE)
            && self.types.get_ref(t).target() == Some(target)
    }

    /// `(c *Checker) isReferenceToSomeType` (checker.go).
    pub(crate) fn is_reference_to_some_type(&mut self, t: TypeId, targets: &[TypeId]) -> bool {
        tobject_flags(self, t).intersects(ObjectFlags::REFERENCE)
            && self
                .types_handle()
                .get_ref(t)
                .target()
                .is_some_and(|tt| targets.contains(&tt))
    }

    /// `(c *Checker) getBuiltinIteratorReturnType` (checker.go).
    pub(crate) fn get_builtin_iterator_return_type(&mut self) -> TypeId {
        tsc_core::core::if_else(
            self.strict_builtin_iterator_return,
            self.undefined_type,
            self.any_type,
        )
    }

    /// `(c *Checker) combineIterationTypes` (checker.go).
    pub(crate) fn combine_iteration_types(
        &mut self,
        iteration_types: &[IterationTypes],
    ) -> IterationTypes {
        IterationTypes {
            yield_type: self.get_iteration_type_union(iteration_types, |t| t.yield_type),
            return_type: self.get_iteration_type_union(iteration_types, |t| t.return_type),
            next_type: self.get_iteration_type_union(iteration_types, |t| t.next_type),
        }
    }

    /// `(c *Checker) getIterationTypeUnion` (checker.go).
    pub(crate) fn get_iteration_type_union(
        &mut self,
        iteration_types: &[IterationTypes],
        f: impl Fn(&IterationTypes) -> Option<TypeId>,
    ) -> Option<TypeId> {
        let types: Vec<TypeId> = iteration_types.iter().filter_map(|t| f(t)).collect();
        if types.is_empty() {
            return None;
        }
        Some(self.get_union_type(&types))
    }

    /// `(c *Checker) getAsyncFromSyncIterationTypes` (checker.go).
    pub(crate) fn get_async_from_sync_iteration_types(
        &mut self,
        iteration_types: IterationTypes,
        error_node: Option<NodeId>,
    ) -> IterationTypes {
        if !iteration_types.has_types()
            || (iteration_types.yield_type == Some(self.any_type)
                && iteration_types.return_type == Some(self.any_type)
                && iteration_types.next_type == Some(self.any_type))
        {
            return iteration_types;
        }
        // if we're requesting diagnostics, report errors for a missing `Awaited<T>`.
        if error_node.is_some() {
            {
                let thunk = self
                    .get_global_awaited_symbol
                    .clone()
                    .expect("getGlobalAwaitedSymbol");
                thunk(self);
            }
        }
        let yield_type = iteration_types
            .yield_type
            .and_then(|t| self.get_awaited_type_ex(t, error_node, None, &[]));
        let return_type = iteration_types
            .return_type
            .and_then(|t| self.get_awaited_type_ex(t, error_node, None, &[]));
        IterationTypes {
            yield_type: Some(yield_type.unwrap_or(self.any_type)),
            return_type: Some(return_type.unwrap_or(self.any_type)),
            next_type: iteration_types.next_type,
        }
    }

    /// `(c *Checker) getIterationTypesOfIterableSlow` (checker.go).
    ///
    /// Gets the *yield*, *return*, and *next* types of an `Iterable`-like or `AsyncIterable`-like
    /// type from its members.
    pub(crate) fn get_iteration_types_of_iterable_slow(
        &mut self,
        t: TypeId,
        r: &IterationTypesResolver,
        error_node: Option<NodeId>,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> IterationTypes {
        let mut diagnostic_output = diagnostic_output;
        let property_name = self.get_property_name_for_known_symbol_name(&r.iterator_symbol_name);
        let method = self.get_property_of_type(t, &property_name);
        if let Some(method) = method {
            if !sym_flags(self, method).intersects(ast::SymbolFlags::OPTIONAL) {
                let method_type = self.get_type_of_symbol(method);
                if crate::utilities::is_type_any(&self.types, method_type) {
                    return IterationTypes::any(self.any_type);
                }
                let all_signatures = self.get_signatures_of_type(method_type, SignatureKind::Call);
                let valid_signatures: Vec<SignatureId> = all_signatures
                    .iter()
                    .copied()
                    .filter(|&sig| self.get_min_argument_count(sig) == 0)
                    .collect();
                if !valid_signatures.is_empty() {
                    let return_types: Vec<TypeId> = valid_signatures
                        .iter()
                        .map(|&s| self.get_return_type_of_signature(s))
                        .collect();
                    let iterator_type = self.get_intersection_type(&return_types);
                    return self.get_iteration_types_of_iterator_worker(
                        iterator_type,
                        r,
                        error_node,
                        diagnostic_output,
                    );
                }
                if error_node.is_some() && !all_signatures.is_empty() {
                    let get_checked = r.get_global_iterable_type_checked.clone().expect("thunk");
                    let iterable_type_checked = get_checked(self);
                    self.check_type_assignable_to_ex(
                        t,
                        iterable_type_checked,
                        error_node,
                        None,
                        diagnostic_output.as_deref_mut(),
                    );
                }
            }
        }
        IterationTypes::default()
    }

    /// `(c *Checker) getIterationTypesOfIterator` (checker.go).
    ///
    /// Gets the *yield*, *return*, and *next* types from an `Iterator`-like or `AsyncIterator`-like type.
    pub(crate) fn get_iteration_types_of_iterator(
        &mut self,
        t: TypeId,
        r: &IterationTypesResolver,
        error_node: Option<NodeId>,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> IterationTypes {
        self.get_iteration_types_of_iterator_worker(t, r, error_node, diagnostic_output)
    }

    /// `(c *Checker) getIterationTypesOfIteratorWorker` (checker.go).
    pub(crate) fn get_iteration_types_of_iterator_worker(
        &mut self,
        t: TypeId,
        r: &IterationTypesResolver,
        error_node: Option<NodeId>,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> IterationTypes {
        if crate::utilities::is_type_any(&self.types, t) {
            return IterationTypes::any(self.any_type);
        }
        let iteration_types = self.get_iteration_types_of_iterator_fast(t, r);
        if iteration_types.has_types() {
            return iteration_types;
        }
        self.get_iteration_types_of_iterator_slow(t, r, error_node, diagnostic_output)
    }

    /// `(c *Checker) getIterationTypesOfIteratorFast` (checker.go).
    pub(crate) fn get_iteration_types_of_iterator_fast(
        &mut self,
        t: TypeId,
        r: &IterationTypesResolver,
    ) -> IterationTypes {
        // As an optimization, if the type is an instantiation of the following global type, then
        // just grab its related type arguments:
        // - `Iterable<T, TReturn, TNext>` or `AsyncIterable<T, TReturn, TNext>`
        // - `IteratorObject<T, TReturn, TNext>` or `AsyncIteratorObject<T, TReturn, TNext>`
        // - `IterableIterator<T, TReturn, TNext>` or `AsyncIterableIterator<T, TReturn, TNext>`
        // - `Generator<T, TReturn, TNext>` or `AsyncGenerator<T, TReturn, TNext>`
        let g_iterator = r.get_global_iterator_type.clone().expect("thunk");
        let g_iterator_object = r.get_global_iterator_object_type.clone().expect("thunk");
        let g_iterable_iterator = r.get_global_iterable_iterator_type.clone().expect("thunk");
        let g_generator = r.get_global_generator_type.clone().expect("thunk");
        let g_iterator_t = g_iterator(self);
        let g_iterator_object_t = g_iterator_object(self);
        let g_iterable_iterator_t = g_iterable_iterator(self);
        let g_generator_t = g_generator(self);
        if self.is_reference_to_type(t, g_iterator_t)
            || self.is_reference_to_type(t, g_iterator_object_t)
            || self.is_reference_to_type(t, g_iterable_iterator_t)
            || self.is_reference_to_type(t, g_generator_t)
        {
            let type_arguments = self.get_type_arguments(t);
            let _resolve = r.resolve_iteration_type.clone().expect("thunk");
            return get_resolved_iteration_types(
                self,
                r,
                type_arguments[0],
                type_arguments[1],
                type_arguments[2],
            );
        }
        // As an optimization, if the type is an instantiation of one of the following global types, then
        // just grab the related type argument:
        let g_builtin = r.get_global_builtin_iterator_types.clone().expect("thunk");
        let g_builtin_t = g_builtin(self);
        if self.is_reference_to_some_type(t, &g_builtin_t) {
            let resolve = r.resolve_iteration_type.clone().expect("thunk");
            let arg0 = self.get_type_arguments(t)[0];
            let return_type = self.get_builtin_iterator_return_type();
            return IterationTypes {
                yield_type: Some(resolve(self, arg0, None)),
                return_type: Some(resolve(self, return_type, None)),
                next_type: Some(self.unknown_type),
            };
        }
        IterationTypes::default()
    }

    /// `(c *Checker) getIterationTypesOfIteratorSlow` (checker.go).
    pub(crate) fn get_iteration_types_of_iterator_slow(
        &mut self,
        t: TypeId,
        r: &IterationTypesResolver,
        error_node: Option<NodeId>,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> IterationTypes {
        let mut diagnostic_output = diagnostic_output;
        let parts = [
            self.get_iteration_types_of_method(
                t,
                r,
                "next",
                error_node,
                diagnostic_output.as_deref_mut(),
            ),
            self.get_iteration_types_of_method(
                t,
                r,
                "return",
                error_node,
                diagnostic_output.as_deref_mut(),
            ),
            self.get_iteration_types_of_method(
                t,
                r,
                "throw",
                error_node,
                diagnostic_output.as_deref_mut(),
            ),
        ];
        self.combine_iteration_types(&parts)
    }

    /// `(c *Checker) getIterationTypesOfMethod` (checker.go).
    pub(crate) fn get_iteration_types_of_method(
        &mut self,
        t: TypeId,
        resolver: &IterationTypesResolver,
        method_name: &str,
        error_node: Option<NodeId>,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> IterationTypes {
        let mut diagnostic_output = diagnostic_output;
        let method = self.get_property_of_type(t, method_name);
        // Ignore 'return' or 'throw' if they are missing.
        if method.is_none() && method_name != "next" {
            return IterationTypes::default();
        }
        let mut method_type: Option<TypeId> = None;
        if let Some(method) = method {
            if !(method_name == "next"
                && sym_flags(self, method).intersects(ast::SymbolFlags::OPTIONAL))
            {
                if method_name == "next" {
                    method_type = Some(self.get_type_of_symbol(method));
                } else {
                    let method_sym_t = self.get_type_of_symbol(method);
                    method_type = Some(
                        self.get_type_with_facts(method_sym_t, TypeFacts::NE_UNDEFINED_OR_NULL),
                    );
                }
            }
        }
        if method_type.is_some_and(|t| crate::utilities::is_type_any(&self.types, t)) {
            return IterationTypes::any(self.any_type);
        }
        // Both async and non-async iterators *must* have a `next` method.
        let mut method_signatures: Vec<SignatureId> = Vec::new();
        if let Some(method_type) = method_type {
            method_signatures = self.get_signatures_of_type(method_type, SignatureKind::Call);
        }
        if method_signatures.is_empty() {
            if let Some(error_node) = error_node {
                let diagnostic: &'static tsc_diagnostics::Message = if method_name == "next" {
                    resolver
                        .must_have_a_next_method_diagnostic
                        .expect("diagnostic")
                } else {
                    resolver.must_be_a_method_diagnostic.expect("diagnostic")
                };
                let d = self.new_diagnostic_for_node(Some(error_node), diagnostic, &[method_name]);
                self.report_diagnostic(Some(d), diagnostic_output.as_deref_mut());
            }
            return IterationTypes::default();
        }
        // If the method signature comes exclusively from the global iterator or generator type,
        // create iteration types from its type arguments like `getIterationTypesOfIteratorFast`
        // does (so as to remove `undefined` from the next and return types). We arrive here when
        // a contextual type for a generator was not a direct reference to one of those global types,
        // but looking up `methodType` referred to one of them (and nothing else). E.g., in
        // `interface SpecialIterator extends Iterator<number> {}`, `SpecialIterator` is not a
        // reference to `Iterator`, but its `next` member derives exclusively from `Iterator`.
        if method_signatures.len() == 1
            && method_type.is_some_and(|mt| self.types.get_ref(mt).symbol.is_some())
        {
            let method_type = method_type.unwrap();
            let method_type_symbol = self.types.get_ref(method_type).symbol.unwrap();
            let get_global_generator_type =
                resolver.get_global_generator_type.clone().expect("thunk");
            let global_generator_type = get_global_generator_type(self);
            let get_global_iterator_type =
                resolver.get_global_iterator_type.clone().expect("thunk");
            let global_iterator_type = get_global_iterator_type(self);
            let global_generator_symbol = self.types.get_ref(global_generator_type)
                .symbol;
            let is_generator_method = global_generator_symbol.is_some_and(|s| {
                self.symbol_arena.borrow()[s.index()].members.get(method_name).copied()
                    == Some(method_type_symbol)
            });
            let global_iterator_symbol = self.types.get_ref(global_iterator_type)
                .symbol;
            let is_iterator_method = !is_generator_method
                && global_iterator_symbol.is_some_and(|s| {
                    self.symbol_arena.borrow()[s.index()].members.get(method_name).copied()
                        == Some(method_type_symbol)
                });
            if is_generator_method || is_iterator_method {
                let global = if is_generator_method {
                    global_generator_type
                } else {
                    global_iterator_type
                };
                let type_parameters: Vec<TypeId> = self
                    .types_handle()
                    .get(global)
                    .as_interface_type()
                    .map(|i| i.type_parameters().to_vec())
                    .unwrap_or_default();
                let __arena_method_mapper = self.types.clone();
                let method_mapper = __arena_method_mapper
                    .get(method_type)
                    .mapper()
                    .expect("mapper");
                let next_type = if method_name == "next" {
                    Some(crate::mapper::get_mapped_type(
                        self,
                        type_parameters[2],
                        method_mapper,
                    ))
                } else {
                    None
                };
                return IterationTypes {
                    yield_type: Some(crate::mapper::get_mapped_type(
                        self,
                        type_parameters[0],
                        method_mapper,
                    )),
                    return_type: Some(crate::mapper::get_mapped_type(
                        self,
                        type_parameters[1],
                        method_mapper,
                    )),
                    next_type,
                };
            }
        }
        // Extract the first parameter and return type of each signature.
        let mut method_parameter_types: Vec<TypeId> = Vec::new();
        let mut method_return_types: Vec<TypeId> = Vec::new();
        for &signature in &method_signatures {
            if method_name != "throw" && !self.signature_arena.get(signature).parameters.is_empty()
            {
                method_parameter_types.push(self.get_type_at_position(signature, 0));
            }
            method_return_types.push(self.get_return_type_of_signature(signature));
        }
        // Resolve the *next* or *return* type from the first parameter of a `next()` or
        // `return()` method, respectively.
        let mut return_types: Vec<TypeId> = Vec::new();
        let mut next_type: Option<TypeId> = None;
        if method_name != "throw" {
            let method_parameter_type = if !method_parameter_types.is_empty() {
                self.get_union_type(&method_parameter_types)
            } else {
                self.unknown_type
            };
            if method_name == "next" {
                // The value of `next(value)` is *not* awaited by async generators
                next_type = Some(method_parameter_type);
            } else if method_name == "return" {
                // The value of `return(value)` *is* awaited by async generators
                let resolve = resolver.resolve_iteration_type.clone().expect("thunk");
                let resolved = resolve(self, method_parameter_type, error_node);
                return_types.push(resolved);
            }
        }
        // Resolve the *yield* and *return* types from the return type of the method (i.e. `IteratorResult`)
        let method_return_type = if !method_return_types.is_empty() {
            self.get_intersection_type(&method_return_types)
        } else {
            self.never_type
        };
        let resolve = resolver.resolve_iteration_type.clone().expect("thunk");
        let resolved_method_return_type = resolve(self, method_return_type, error_node);
        let iteration_types =
            self.get_iteration_types_of_iterator_result(resolved_method_return_type);
        let yield_type;
        if !iteration_types.has_types() {
            if let Some(error_node) = error_node {
                let d = self.new_diagnostic_for_node(
                    Some(error_node),
                    resolver.must_have_a_value_diagnostic.expect("diagnostic"),
                    &[method_name],
                );
                self.report_diagnostic(Some(d), diagnostic_output.as_deref_mut());
            }
            yield_type = self.any_type;
            return_types.push(self.any_type);
        } else {
            yield_type = iteration_types.yield_type.unwrap_or(self.any_type);
            if let Some(rt) = iteration_types.return_type {
                return_types.push(rt);
            }
        }
        IterationTypes {
            yield_type: Some(yield_type),
            return_type: Some(self.get_union_type(&return_types)),
            next_type,
        }
    }

    /// `(c *Checker) getIterationTypesOfIteratorResult` (checker.go).
    ///
    /// Gets the *yield* and *return* types of an `IteratorResult`-like type.
    pub(crate) fn get_iteration_types_of_iterator_result(&mut self, t: TypeId) -> IterationTypes {
        if crate::utilities::is_type_any(&self.types, t) {
            return IterationTypes::any(self.any_type);
        }
        // As an optimization, if the type is an instantiation of one of the global `IteratorYieldResult<T>`
        // or `IteratorReturnResult<TReturn>` types, then just grab its type argument.
        let thunk = self
            .get_global_iterator_yield_result_type
            .clone()
            .expect("getGlobalIteratorYieldResultType");
        let yield_result_ty = thunk(self);
        if self.is_reference_to_type(t, yield_result_ty) {
            return IterationTypes {
                yield_type: Some(self.get_type_arguments(t)[0]),
                return_type: None,
                next_type: None,
            };
        }
        let thunk = self
            .get_global_iterator_return_result_type
            .clone()
            .expect("getGlobalIteratorReturnResultType");
        let return_result_ty = thunk(self);
        if self.is_reference_to_type(t, return_result_ty) {
            return IterationTypes {
                yield_type: None,
                return_type: Some(self.get_type_arguments(t)[0]),
                next_type: None,
            };
        }
        // Choose any constituents that can produce the requested iteration type.
        let yield_iterator_result = self.filter_type(t, &|c: &mut Checker, t: TypeId| {
            c.is_yield_iterator_result(t)
        });
        let mut yield_type: Option<TypeId> = None;
        if yield_iterator_result != self.never_type {
            yield_type = self.get_type_of_property_of_type(yield_iterator_result, "value");
        }
        let return_iterator_result = self.filter_type(t, &|c: &mut Checker, t: TypeId| {
            c.is_return_iterator_result(t)
        });
        let mut return_type: Option<TypeId> = None;
        if return_iterator_result != self.never_type {
            return_type = self.get_type_of_property_of_type(return_iterator_result, "value");
        }
        if yield_type.is_none() && return_type.is_none() {
            return IterationTypes::default();
        }
        // From https://tc39.github.io/ecma262/#sec-iteratorresult-interface
        // > ... If the iterator does not have a return value, `value` is `undefined`. In that case, the
        // > `value` property may be absent from the conforming object if it does not inherit an explicit
        // > `value` property.
        IterationTypes {
            yield_type,
            return_type: Some(return_type.unwrap_or(self.void_type)),
            next_type: None,
        }
    }

    /// `(c *Checker) isYieldIteratorResult` (checker.go).
    pub(crate) fn is_yield_iterator_result(&mut self, t: TypeId) -> bool {
        self.is_iterator_result(t, IterationTypeKind::Yield)
    }

    /// `(c *Checker) isReturnIteratorResult` (checker.go).
    pub(crate) fn is_return_iterator_result(&mut self, t: TypeId) -> bool {
        self.is_iterator_result(t, IterationTypeKind::Return)
    }

    /// `(c *Checker) isIteratorResult` (checker.go).
    pub(crate) fn is_iterator_result(&mut self, t: TypeId, kind: IterationTypeKind) -> bool {
        // From https://tc39.github.io/ecma262/#sec-iteratorresult-interface:
        // > [done] is the result status of an iterator `next` method call. If the end of the iterator was reached `done` is `true`.
        // > If the end was not reached `done` is `false` and a value is available.
        // > If a `done` property (either own or inherited) does not exist, it is consider to have the value `false`.
        let done_type = self
            .get_type_of_property_of_type(t, "done")
            .unwrap_or(self.false_type);
        self.is_type_assignable_to(
            if kind == IterationTypeKind::Yield {
                self.false_type
            } else {
                self.true_type
            },
            done_type,
        )
    }

    /// `(c *Checker) reportTypeNotIterableError` (checker.go).
    pub(crate) fn report_type_not_iterable_error(
        &mut self,
        error_node: NodeId,
        t: TypeId,
        allow_async_iterables: bool,
    ) -> ast::diagnostic::DiagnosticRef {
        let message: &'static tsc_diagnostics::Message = if allow_async_iterables {
            &tsc_diagnostics::Type_0_must_have_a_Symbol_asyncIterator_method_that_returns_an_async_iterator
        } else {
            &tsc_diagnostics::Type_0_must_have_a_Symbol_iterator_method_that_returns_an_iterator
        };
        let __program = self.program.clone().expect("program");
        let enodes = __program.nodes((error_node).file_index());
        let suggest_await = self.get_awaited_type_of_promise(t).is_some()
            || (!allow_async_iterables
                && enodes[error_node]
                    .parent
                    .is_some_and(|p| ast::is_for_of_statement(&enodes[p]))
                && enodes[error_node]
                    .parent
                    .and_then(|p| enodes[p].expression())
                    == Some(error_node)
                && {
                    let thunk = self
                        .get_global_async_iterable_type
                        .clone()
                        .expect("getGlobalAsyncIterableType");
                    thunk(self)
                } != self.empty_generic_type
                && {
                    let g_async_iter = self.get_global_async_iterable_type();
                    let created = self.create_type_from_generic_global_type(
                        g_async_iter,
                        &[self.any_type, self.any_type, self.any_type],
                    );
                    self.is_type_assignable_to(t, created)
                });
        let arg = self.type_to_string(t);
        self.error_and_maybe_suggest_await(error_node, suggest_await, message, &[arg])
            .expect("diagnostic")
    }

    /// `(c *Checker) getIterationDiagnosticDetails` (checker.go).
    pub(crate) fn get_iteration_diagnostic_details(
        &mut self,
        r#use: IterationUse,
        input_type: TypeId,
        allows_strings: bool,
    ) -> (&'static tsc_diagnostics::Message, bool) {
        let yield_type = self.get_iteration_type_of_iterable(
            r#use,
            IterationTypeKind::Yield,
            input_type,
            None, /*errorNode*/
        );
        if yield_type.is_some() {
            return (
                &tsc_diagnostics::Type_0_can_only_be_iterated_through_when_using_the_downlevelIteration_flag_or_with_a_target_of_es2015_or_higher,
                false,
            );
        }
        if self
            .types_handle()
            .get(input_type)
            .symbol
            .is_some_and(|s| is_es2015_or_later_iterable(&sym_name(self, s)))
        {
            return (
                &tsc_diagnostics::Type_0_can_only_be_iterated_through_when_using_the_downlevelIteration_flag_or_with_a_target_of_es2015_or_higher,
                true,
            );
        }
        if allows_strings {
            return (
                &tsc_diagnostics::Type_0_is_not_an_array_type_or_a_string_type,
                true,
            );
        }
        (&tsc_diagnostics::Type_0_is_not_an_array_type, true)
    }
}

impl IterationTypes {
    /// `IterationTypes_any` — Go composite literal `IterationTypes{anyType, anyType, anyType}`.
    pub(crate) fn any(any_type: TypeId) -> IterationTypes {
        IterationTypes {
            yield_type: Some(any_type),
            return_type: Some(any_type),
            next_type: Some(any_type),
        }
    }

    /// `(i IterationTypes) HasTypes` (checker.go).
    pub(crate) fn has_types(&self) -> bool {
        self.yield_type.is_some() || self.return_type.is_some() || self.next_type.is_some()
    }

    /// `(i IterationTypes) Get` (checker.go).
    pub(crate) fn get_type(&self, kind: IterationTypeKind) -> Option<TypeId> {
        match kind {
            IterationTypeKind::Yield => self.yield_type,
            IterationTypeKind::Return => self.return_type,
            IterationTypeKind::Next => self.next_type,
        }
    }
}

/// `getResolvedIterationTypes` — `(r *IterationTypesResolver)` method in Go.
fn get_resolved_iteration_types(
    c: &mut Checker,
    r: &IterationTypesResolver,
    yield_type: TypeId,
    return_type: TypeId,
    next_type: TypeId,
) -> IterationTypes {
    let resolve = r.resolve_iteration_type.clone().expect("thunk");
    let resolved_yield = resolve(c, yield_type, None);
    let resolved_return = resolve(c, return_type, None);
    IterationTypes {
        yield_type: Some(tsc_core::core::if_else(
            crate::utilities::is_type_any(&c.types, resolved_yield) || resolved_yield != yield_type,
            resolved_yield,
            resolved_yield,
        )),
        return_type: Some(resolved_return),
        next_type: Some(next_type),
    }
}

/// `isES2015OrLaterIterable` (checker.go) — free function.
fn is_es2015_or_later_iterable(n: &str) -> bool {
    matches!(
        n,
        "Float32Array"
            | "Float64Array"
            | "Int16Array"
            | "Int32Array"
            | "Int8Array"
            | "NodeList"
            | "Uint16Array"
            | "Uint32Array"
            | "Uint8Array"
            | "Uint8ClampedArray"
    )
}

// ======== checker.go ~6937 — alias symbol / declaration-space checking ========

impl Checker {
    /// `(c *Checker) checkAliasSymbol` (checker.go).
    pub(crate) fn check_alias_symbol(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut symbol = self.get_symbol_of_declaration(node).expect("alias symbol");
        let target = self.resolve_alias(symbol);
        if target == self.unknown_symbol {
            return;
        }
        // For external modules, `symbol` represents the local symbol for an alias.
        // This local symbol will merge any other local declarations (excluding other aliases)
        // and symbol.flags will contains combined representation for all merged declaration.
        // Based on symbol.flags we can compute a set of excluded meanings (meaning that resolved alias should not have,
        // otherwise it will conflict with some local declaration). Note that in addition to normal flags we include matching SymbolFlags.Export*
        // in order to prevent collisions with declarations that were exported from the current module (they still contribute to local names).
        let export_symbol = {
            let arena = self.symbol_arena.clone();
            arena.borrow()[symbol.index()]
                .export_symbol
                .unwrap_or(symbol)
        };
        symbol = self.get_merged_symbol(export_symbol);
        let target_flags = self.get_symbol_flags(target);
        // A type-only import/export will already have a grammar error in a JS file, so no need to issue more errors within
        if ast::is_in_js_file(Some(node), &nodes)
            && !target_flags.intersects(ast::SymbolFlags::VALUE)
            && !ast::is_type_only_import_or_export_declaration(node, &nodes)
        {
            let error_node = nodes[node].property_name_or_name().unwrap_or(node);
            debug_assert!(nodes[node].kind != ast::Kind::NamespaceExport);
            if ast::is_export_specifier(&nodes[node]) {
                let diag = self
                    .error(
                        Some(error_node),
                        &tsc_diagnostics::Types_cannot_appear_in_export_declarations_in_JavaScript_files,
                        &[] as &[String],
                    )
                    .expect("error returns a diagnostic");
                if let Some(source_symbol) = ast::get_source_file_of_node(Some(node), &nodes)
                    .and_then(|sf| nodes[sf].symbol())
                {
                    let export_name = nodes[error_node].text(&nodes).to_string();
                    if let Some(already_exported_symbol) = self.symbol_arena.borrow()
                        [source_symbol.index()]
                    .exports
                    .get(export_name.as_str())
                    .copied()
                    {
                        if already_exported_symbol == target {
                            let decls = sym_declarations(self, already_exported_symbol);
                            if let Some(exporting_declaration) = decls
                                .iter()
                                .copied()
                                .find(|&d| ast::is_js_type_alias_declaration(&nodes[d]))
                            {
                                let related = self.new_diagnostic_for_node(
                                    Some(exporting_declaration),
                                    &tsc_diagnostics::X_0_is_automatically_exported_here,
                                    &[sym_name(self, already_exported_symbol)],
                                );
                                ast::diagnostic::lock_diagnostic(&diag)
                                    .add_related_info(Some(related));
                            }
                        }
                    }
                }
            } else {
                let mut identifier_text = sym_name(self, symbol);
                if ast::is_identifier(&nodes[error_node]) {
                    identifier_text = nodes[error_node].text(&nodes).to_string();
                }
                let mut specifier_text = "...".to_string();
                if let Some(import_declaration) =
                    ast::find_ancestor(Some(node), &nodes, &mut |n, _ns| {
                        ast::is_import_or_import_equals_declaration(n)
                            || ast::is_variable_declaration(n)
                    })
                {
                    if let Some(module_specifier) =
                        crate::nodebuilderimpl::try_get_module_specifier_from_declaration(
                            import_declaration,
                            &nodes,
                        )
                    {
                        specifier_text = nodes[module_specifier].text(&nodes).to_string();
                    }
                }
                let mut import_text = format!("import(\"{}\")", specifier_text);
                if ast::is_import_specifier(&nodes[node]) {
                    import_text = format!("{}.{}", import_text, identifier_text);
                }
                self.error(
                    Some(error_node),
                    &tsc_diagnostics::X_0_is_a_type_and_cannot_be_imported_in_JavaScript_files_Use_1_in_a_JSDoc_type_annotation,
                    &[identifier_text, import_text],
                );
            }
            return;
        }
        let symbol_flags = sym_flags(self, symbol);
        let excluded_meanings = tsc_core::core::if_else(
            symbol_flags.intersects(ast::SymbolFlags::VALUE | ast::SymbolFlags::EXPORT_VALUE),
            ast::SymbolFlags::VALUE,
            ast::SymbolFlags::NONE,
        ) | tsc_core::core::if_else(
            symbol_flags.intersects(ast::SymbolFlags::TYPE),
            ast::SymbolFlags::TYPE,
            ast::SymbolFlags::NONE,
        ) | tsc_core::core::if_else(
            symbol_flags.intersects(ast::SymbolFlags::NAMESPACE),
            ast::SymbolFlags::NAMESPACE,
            ast::SymbolFlags::NONE,
        );
        if target_flags.intersects(excluded_meanings) {
            let message: &'static tsc_diagnostics::Message =
                if ast::is_export_specifier(&nodes[node]) {
                    &tsc_diagnostics::Export_declaration_conflicts_with_exported_declaration_of_0
                } else {
                    &tsc_diagnostics::Import_declaration_conflicts_with_local_declaration_of_0
                };
            let arg = self.symbol_to_string(symbol);
            self.error(Some(node), message, &[arg]);
        } else if !ast::is_export_specifier(&nodes[node]) {
            // Look at 'compilerOptions.isolatedModules' and not 'getIsolatedModules(...)' (which considers 'verbatimModuleSyntax')
            // here because 'verbatimModuleSyntax' will already have an error for importing a type without 'import type'.
            let appears_valuey_to_transpiler = self.compiler_options.isolated_modules.is_true()
                && ast::find_ancestor(Some(node), &nodes, &mut |n, ns| {
                    ast::is_type_only_import_or_export_declaration(n.id, ns)
                })
                .is_none();
            if appears_valuey_to_transpiler
                && symbol_flags.intersects(ast::SymbolFlags::VALUE | ast::SymbolFlags::EXPORT_VALUE)
            {
                let __h10966_25 = self.symbol_to_string(symbol);

                self.error(
                    Some(node),
                    &tsc_diagnostics::Import_0_conflicts_with_local_value_so_must_be_declared_with_a_type_only_import_when_isolatedModules_is_enabled,
                    &[

                        __h10966_25,
                        self.get_isolated_modules_like_flag_name(),
                    ],
                );
            }
        }
        if self.compiler_options.get_isolated_modules()
            && !ast::is_type_only_import_or_export_declaration(node, &nodes)
            && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
        {
            let type_only_alias = self.get_type_only_alias_declaration(symbol);
            let is_type = !target_flags.intersects(ast::SymbolFlags::VALUE);
            if is_type || type_only_alias.is_some() {
                match nodes[node].kind {
                    ast::Kind::ImportClause
                    | ast::Kind::ImportSpecifier
                    | ast::Kind::ImportEqualsDeclaration => {
                        if self.compiler_options.verbatim_module_syntax.is_true() {
                            debug_assert!(
                                nodes[node].name().is_some(),
                                "An ImportClause with a symbol should have a name"
                            );
                            let message: &'static tsc_diagnostics::Message = if self
                                .compiler_options
                                .verbatim_module_syntax
                                .is_true()
                                && ast::is_internal_module_import_equals_declaration(
                                    &nodes[node],
                                    &nodes,
                                ) {
                                &tsc_diagnostics::An_import_alias_cannot_resolve_to_a_type_or_type_only_declaration_when_verbatimModuleSyntax_is_enabled
                            } else if is_type {
                                &tsc_diagnostics::X_0_is_a_type_and_must_be_imported_using_a_type_only_import_when_verbatimModuleSyntax_is_enabled
                            } else {
                                &tsc_diagnostics::X_0_resolves_to_a_type_only_declaration_and_must_be_imported_using_a_type_only_import_when_verbatimModuleSyntax_is_enabled
                            };
                            let name = nodes[node]
                                .property_name_or_name()
                                .map(|n| nodes[n].text(&nodes).to_string())
                                .unwrap_or_default();
                            let d = self
                                .error(Some(node), message, &[name.clone()])
                                .expect("error returns a diagnostic");
                            self.add_type_only_declaration_related_info(
                                d,
                                if is_type { None } else { type_only_alias },
                                &name,
                            );
                        }
                        if is_type
                            && nodes[node].kind == ast::Kind::ImportEqualsDeclaration
                            && ast::has_modifier(&nodes[node], ast::ModifierFlags::EXPORT)
                        {
                            self.error(
                                Some(node),
                                &tsc_diagnostics::Cannot_use_export_import_on_a_type_or_type_only_namespace_when_0_is_enabled,
                                &[self.get_isolated_modules_like_flag_name()],
                            );
                        }
                    }
                    ast::Kind::ExportSpecifier => {
                        // Don't allow re-exporting an export that will be elided when `--isolatedModules` is set.
                        // The exception is that `import type { A } from './a'; export { A }` is allowed
                        // because single-file analysis can determine that the export should be dropped.
                        // PORT: `type_only_alias` can belong to another
                        // file's arena — indexing it into `nodes` would walk
                        // the wrong parents. file_index equality is the same
                        // test Go does via GetSourceFileOfNode.
                        if self.compiler_options.verbatim_module_syntax.is_true()
                            || type_only_alias.is_none_or(|a| a.file_index() != node.file_index())
                        {
                            let name = nodes[node]
                                .property_name_or_name()
                                .map(|n| nodes[n].text(&nodes).to_string())
                                .unwrap_or_default();
                            let diagnostic = if is_type {
                                self.error(
                                    Some(node),
                                    &tsc_diagnostics::Re_exporting_a_type_when_0_is_enabled_requires_using_export_type,
                                    &[self.get_isolated_modules_like_flag_name()],
                                )
                            } else {
                                self.error(
                                    Some(node),
                                    &tsc_diagnostics::X_0_resolves_to_a_type_only_declaration_and_must_be_re_exported_using_a_type_only_re_export_when_1_is_enabled,
                                    &[
                                        name.clone(),
                                        self.get_isolated_modules_like_flag_name(),
                                    ],
                                )
                            }
                            .expect("error returns a diagnostic");
                            self.add_type_only_declaration_related_info(
                                diagnostic,
                                if is_type { None } else { type_only_alias },
                                &name,
                            );
                        }
                    }
                    _ => {}
                }
            }
            if self.compiler_options.verbatim_module_syntax.is_true()
                && !ast::is_import_equals_declaration(&nodes[node])
                && !ast::is_in_js_file(Some(node), &nodes)
                && self
                    .program
                    .as_ref()
                    .expect("program")
                    .get_emit_module_format_of_file(
                        nodes[ast::get_source_file_of_node(Some(node), &nodes)
                            .expect("source file")]
                        .as_source_file(),
                    )
                    == tsc_core::options_generated::ModuleKind::CommonJS
            {
                self.error(
                    Some(node),
                    get_verbatim_module_syntax_error_message(node, &nodes),
                    &[],
                );
            } else if self.module_kind == tsc_core::options_generated::ModuleKind::Preserve
                && !ast::is_import_equals_declaration(&nodes[node])
                && !ast::is_variable_declaration(&nodes[node])
                && !ast::is_binding_element(&nodes[node])
                && self
                    .program
                    .as_ref()
                    .expect("program")
                    .get_emit_module_format_of_file(
                        nodes[ast::get_source_file_of_node(Some(node), &nodes)
                            .expect("source file")]
                        .as_source_file(),
                    )
                    == tsc_core::options_generated::ModuleKind::CommonJS
            {
                // In `--module preserve`, ESM input syntax emits ESM output syntax, but there will be times
                // when we look at the `impliedNodeFormat` of this file and decide it's CommonJS (i.e., currently,
                // only if the file extension is .cjs/.cts). To avoid that inconsistency, we disallow ESM syntax
                // in files that are unambiguously CommonJS in this mode.
                self.error(
                    Some(node),
                    &tsc_diagnostics::ECMAScript_module_syntax_is_not_allowed_in_a_CommonJS_module_when_module_is_set_to_preserve,
                    &[],
                );
            }
            if self.compiler_options.verbatim_module_syntax.is_true()
                && !ast::is_type_only_import_or_export_declaration(node, &nodes)
                && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
                && target_flags.intersects(ast::SymbolFlags::CONST_ENUM)
            {
                let const_enum_declaration = sym_value_declaration(self, target);
                if let Some(const_enum_declaration) = const_enum_declaration {
                    if nodes[const_enum_declaration]
                        .flags
                        .intersects(ast::NodeFlags::AMBIENT)
                    {
                        let sf = ast::get_source_file_of_node(Some(const_enum_declaration), &nodes)
                            .expect("source file");
                        let redirect = self
                            .program
                            .as_ref()
                            .expect("program")
                            .get_project_reference_from_output_dts(
                                nodes[sf].as_source_file().path_key(),
                            );
                        if redirect.is_none_or(|r| {
                            !r.resolved
                                .compiler_options()
                                .is_some_and(|o| o.should_preserve_const_enums())
                        }) {
                            self.error(
                                Some(node),
                                &tsc_diagnostics::Cannot_access_ambient_const_enums_when_0_is_enabled,
                                &[self.get_isolated_modules_like_flag_name()],
                            );
                        }
                    }
                }
            }
        }
        if ast::is_import_specifier(&nodes[node]) {
            let target_symbol = self.resolve_alias_with_deprecation_check(symbol, node);
            if self.is_deprecated_symbol(target_symbol)
                && !sym_declarations(self, target_symbol).is_empty()
            {
                self.add_deprecated_suggestion(
                    node,
                    &sym_declarations(self, target_symbol),
                    &sym_name(self, target_symbol),
                );
            }
        }
    }

    /// `(c *Checker) areDeclarationFlagsIdentical` (checker.go).
    pub(crate) fn are_declaration_flags_identical(&mut self, left: NodeId, right: NodeId) -> bool {
        // `left`/`right` may live in different file arenas (Go compares raw
        // node pointers across files) — fetch each arena by its own id.
        let __program = self.program.clone().expect("program");
        let left_nodes = __program.nodes((left).file_index());
        let right_nodes = __program.nodes((right).file_index());
        if (ast::is_parameter_declaration(&left_nodes[left])
            && ast::is_variable_declaration(&right_nodes[right]))
            || (ast::is_variable_declaration(&left_nodes[left])
                && ast::is_parameter_declaration(&right_nodes[right]))
        {
            // Differences in optionality between parameters and variables are allowed.
            return true;
        }
        if crate::utilities::is_optional_declaration(&left_nodes[left], &left_nodes)
            != crate::utilities::is_optional_declaration(&right_nodes[right], &right_nodes)
        {
            return false;
        }
        let interesting_flags = ast::ModifierFlags::PRIVATE
            | ast::ModifierFlags::PROTECTED
            | ast::ModifierFlags::ASYNC
            | ast::ModifierFlags::ABSTRACT
            | ast::ModifierFlags::READONLY
            | ast::ModifierFlags::STATIC;
        crate::utilities::get_selected_modifier_flags(&left_nodes[left], interesting_flags)
            == crate::utilities::get_selected_modifier_flags(&right_nodes[right], interesting_flags)
    }

    /// `(c *Checker) checkTypeAliasDeclaration` (checker.go).
    pub(crate) fn check_type_alias_declaration(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Grammar checking
        self.check_grammar_modifiers(node);
        self.check_type_name_is_reserved(
            nodes[node].name().expect("type alias name"),
            &tsc_diagnostics::Type_alias_name_cannot_be_0,
        );
        if !crate::utilities::container_allows_block_scoped_variable(
            nodes[node].parent.expect("parent"),
            &nodes,
        ) {
            self.grammar_error_on_node(
                node,
                &tsc_diagnostics::X_0_declarations_can_only_be_declared_inside_a_block,
                &["type".to_string()],
            );
        }
        self.check_exports_on_merged_declarations(node);

        let type_node = nodes[node].type_();
        let type_parameters: Vec<NodeId> = nodes[node]
            .type_parameters()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        self.check_type_parameters(&type_parameters);
        if let Some(type_node) = type_node {
            if nodes[type_node].kind == ast::Kind::IntrinsicKeyword {
                let name_text = nodes[nodes[node].name().unwrap()].text(&nodes).to_string();
                if !((type_parameters.is_empty() && name_text == "BuiltinIteratorReturn")
                    || (type_parameters.len() == 1
                        && crate::checker_types::intrinsic_type_kind(&name_text).is_some_and(
                            |k| k != crate::checker_types::IntrinsicTypeKind::Unknown,
                        )))
                {
                    self.error(
                        Some(type_node),
                        &tsc_diagnostics::The_intrinsic_keyword_can_only_be_used_to_declare_compiler_provided_intrinsic_types,
                        &[],
                    );
                }
                // The `intrinsic` keyword is a leaf type node with no child nodes to check,
                // so skipping the checkSourceElement below visits nothing.
                return;
            }
        }
        self.check_source_element(type_node);
        self.register_for_unused_identifiers_check(node);
    }

    /// `(c *Checker) checkTypeNameIsReserved` (checker.go).
    pub(crate) fn check_type_name_is_reserved(
        &mut self,
        name: NodeId,
        message: &'static tsc_diagnostics::Message,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((name).file_index());
        // TS 1.0 spec (April 2014): 3.6.1
        // The predefined type keywords are reserved and cannot be used as names of user defined types.
        let text = nodes[name].text(&nodes).to_string();
        match text.as_str() {
            "any" | "unknown" | "never" | "number" | "bigint" | "boolean" | "string" | "symbol"
            | "void" | "object" | "undefined" => {
                self.error(Some(name), message, &[text]);
            }
            _ => {}
        }
    }

    /// `(c *Checker) checkExportsOnMergedDeclarations` (checker.go).
    pub(crate) fn check_exports_on_merged_declarations(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // If localSymbol is defined on node then node itself is exported - check is required.
        let mut symbol = nodes[node].local_symbol();
        if symbol.is_none() {
            // Local symbol is undefined => this declaration is non-exported.
            // However, symbol might contain other declarations that are exported.
            symbol = self.get_symbol_of_declaration(node);
            if symbol.is_none_or(|s| {
                self.symbol_arena.borrow()[s.index()]
                    .export_symbol
                    .is_none()
            }) {
                // This is a pure local symbol (all declarations are non-exported) - no need to check anything.
                return;
            }
        }
        let symbol = symbol.expect("merged declaration symbol");
        let declarations = sym_declarations(self, symbol);
        if declarations.len() < 2 || self.merged_exports_checked.has(&symbol) {
            return;
        }
        self.merged_exports_checked.add(symbol);
        let mut exported_declaration_spaces = DeclarationSpaces::NONE;
        let mut non_exported_declaration_spaces = DeclarationSpaces::NONE;
        let mut default_exported_declaration_spaces = DeclarationSpaces::NONE;
        for &d in &declarations {
            let declaration_spaces = self.get_declaration_spaces(d);
            let effective_declaration_flags = self.get_effective_declaration_flags(
                d,
                ast::ModifierFlags::EXPORT | ast::ModifierFlags::DEFAULT,
            );
            if effective_declaration_flags.intersects(ast::ModifierFlags::EXPORT) {
                if effective_declaration_flags.intersects(ast::ModifierFlags::DEFAULT) {
                    default_exported_declaration_spaces |= declaration_spaces;
                } else {
                    exported_declaration_spaces |= declaration_spaces;
                }
            } else {
                non_exported_declaration_spaces |= declaration_spaces;
            }
        }
        // Spaces for anything not declared a 'default export'.
        let non_default_exported_declaration_spaces =
            exported_declaration_spaces | non_exported_declaration_spaces;
        let common_declaration_spaces_for_exports_and_locals =
            exported_declaration_spaces & non_exported_declaration_spaces;
        let common_declaration_spaces_for_default_and_non_default =
            default_exported_declaration_spaces & non_default_exported_declaration_spaces;
        if common_declaration_spaces_for_exports_and_locals != DeclarationSpaces::NONE
            || common_declaration_spaces_for_default_and_non_default != DeclarationSpaces::NONE
        {
            // declaration spaces for exported and non-exported declarations intersect
            for &d in &declarations {
                let declaration_spaces = self.get_declaration_spaces(d);
                let name = ast::get_name_of_declaration(Some(d), &nodes);
                // Only error on the declarations that contributed to the intersecting spaces.
                if declaration_spaces
                    .intersects(common_declaration_spaces_for_default_and_non_default)
                {
                    self.error(
                        name,
                        &tsc_diagnostics::Merged_declaration_0_cannot_include_a_default_export_declaration_Consider_adding_a_separate_export_default_0_declaration_instead,
                        &[tsc_scanner::utilities::declaration_name_to_string(name, &nodes)],
                    );
                } else if declaration_spaces
                    .intersects(common_declaration_spaces_for_exports_and_locals)
                {
                    self.error(
                        name,
                        &tsc_diagnostics::Individual_declarations_in_merged_declaration_0_must_be_all_exported_or_all_local,
                        &[tsc_scanner::utilities::declaration_name_to_string(name, &nodes)],
                    );
                }
            }
        }
    }

    /// `(c *Checker) getDeclarationSpaces` (checker.go).
    pub(crate) fn get_declaration_spaces(&mut self, node: NodeId) -> DeclarationSpaces {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::InterfaceDeclaration
            | ast::Kind::TypeAliasDeclaration
            | ast::Kind::JSTypeAliasDeclaration
            | ast::Kind::JSDocTypedefTag
            | ast::Kind::JSDocCallbackTag => DeclarationSpaces::EXPORT_TYPE,
            ast::Kind::ModuleDeclaration => {
                if ast::is_ambient_module(&nodes[node], &nodes)
                    || ast::get_module_instance_state(node, &nodes)
                        != ast::ModuleInstanceState::NonInstantiated
                {
                    DeclarationSpaces::EXPORT_NAMESPACE | DeclarationSpaces::EXPORT_VALUE
                } else {
                    DeclarationSpaces::EXPORT_NAMESPACE
                }
            }
            ast::Kind::ClassDeclaration | ast::Kind::EnumDeclaration | ast::Kind::EnumMember => {
                DeclarationSpaces::EXPORT_TYPE | DeclarationSpaces::EXPORT_VALUE
            }
            ast::Kind::SourceFile => {
                DeclarationSpaces::EXPORT_TYPE
                    | DeclarationSpaces::EXPORT_VALUE
                    | DeclarationSpaces::EXPORT_NAMESPACE
            }
            ast::Kind::ExportAssignment | ast::Kind::BinaryExpression => {
                let expression = if ast::is_export_assignment(&nodes[node]) {
                    nodes[node].expression()
                } else {
                    nodes[node].as_binary_expression().right
                };
                // Export assigned entity name expressions act as aliases and should fall through, otherwise they export values.
                let export_symbol = self.get_symbol_of_declaration(node).expect("export symbol");
                if !expression.is_some_and(|e| ast::is_entity_name_expression(&nodes[e], &nodes))
                    || !sym_flags(self, export_symbol).intersects(ast::SymbolFlags::ALIAS)
                {
                    return DeclarationSpaces::EXPORT_VALUE;
                }
                // The below options all declare an Alias, which is allowed to merge with other values within the importing module.
                self.get_declaration_spaces_of_alias_target(node, &nodes)
            }
            ast::Kind::ImportEqualsDeclaration
            | ast::Kind::NamespaceImport
            | ast::Kind::ImportClause => self.get_declaration_spaces_of_alias_target(node, &nodes),
            ast::Kind::VariableDeclaration
            | ast::Kind::BindingElement
            | ast::Kind::FunctionDeclaration
            | ast::Kind::ImportSpecifier => DeclarationSpaces::EXPORT_VALUE,
            ast::Kind::MethodSignature | ast::Kind::PropertySignature => {
                DeclarationSpaces::EXPORT_TYPE
            }
            _ => panic!(
                "Unhandled case in getDeclarationSpaces: {}",
                nodes[node].kind_string()
            ),
        }
    }

    /// Fallthrough shared by `getDeclarationSpaces`'s ExportAssignment/BinaryExpression
    /// and ImportEqualsDeclaration/NamespaceImport/ImportClause cases.
    fn get_declaration_spaces_of_alias_target(
        &mut self,
        node: NodeId,
        nodes: &[ast::Node],
    ) -> DeclarationSpaces {
        let _ = nodes;
        let mut result = DeclarationSpaces::NONE;
        let symbol = self.get_symbol_of_declaration(node).expect("alias symbol");
        let target = self.resolve_alias(symbol);
        {
            let target_declarations = sym_declarations(self, target);
            for d in target_declarations {
                result |= self.get_declaration_spaces(d);
            }
        }
        result
    }

    /// `(c *Checker) checkTypeParameters` (checker.go).
    pub(crate) fn check_type_parameters(&mut self, type_parameter_declarations: &[NodeId]) {
        let mut seen_default = false;
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes(
            (if let Some(&n) = type_parameter_declarations.first() {
                n
            } else {
                return;
            })
            .file_index(),
        );
        for (i, &node) in type_parameter_declarations.iter().enumerate() {
            self.check_type_parameter(node);
            let default_type_node = nodes[node].as_type_parameter_declaration().default_type;
            if let Some(default_type_node) = default_type_node {
                seen_default = true;
                self.check_type_parameters_not_referenced(
                    default_type_node,
                    type_parameter_declarations,
                    i,
                );
            } else if seen_default {
                self.error(
                    Some(node),
                    &tsc_diagnostics::Required_type_parameters_may_not_follow_optional_type_parameters,
                    &[],
                );
            }
            for j in 0..i {
                if nodes[type_parameter_declarations[j]].symbol() == nodes[node].symbol() {
                    let name = nodes[node].name();
                    self.error(
                        name,
                        &tsc_diagnostics::Duplicate_identifier_0,
                        &[tsc_scanner::utilities::declaration_name_to_string(
                            name, &nodes,
                        )],
                    );
                }
            }
        }
    }

    /// `(c *Checker) checkTypeParametersNotReferenced` (checker.go).
    ///
    /// Check that type parameter defaults only reference previously declared type parameters.
    pub(crate) fn check_type_parameters_not_referenced(
        &mut self,
        root: NodeId,
        type_parameters: &[NodeId],
        index: usize,
    ) {
        // Iterative DFS so we can call `&mut self` methods without running
        // afoul of the `for_each_child` visitor borrow rules.
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((root).file_index());
        let mut stack: Vec<NodeId> = vec![root];
        while let Some(node) = stack.pop() {
            if ast::is_type_reference_node(&nodes[node]) {
                let t = self.get_type_from_type_reference(node);
                if tflags(self, t).intersects(TypeFlags::TYPE_PARAMETER) {
                    for i in index..type_parameters.len() {
                        let tp_symbol = self
                            .get_symbol_of_declaration(type_parameters[i])
                            .unwrap_or(SymbolId::NONE);
                        if self.types.get_ref(t).symbol() == Some(tp_symbol) {
                            self.error(
                                Some(node),
                                &tsc_diagnostics::Type_parameter_defaults_can_only_reference_previously_declared_type_parameters,
                                &[],
                            );
                        }
                    }
                }
            }
            let mut children: Vec<NodeId> = Vec::new();
            nodes[node].for_each_child(&nodes, &mut |child| {
                children.push(child);
                false
            });
            for child in children.into_iter().rev() {
                stack.push(child);
            }
        }
    }

    /// `(c *Checker) registerForUnusedIdentifiersCheck` (checker.go).
    pub(crate) fn register_for_unused_identifiers_check(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let source_file = ast::get_source_file_of_node(Some(node), &nodes);
        if let Some(source_file) = source_file {
            self.source_file_links
                .get(source_file)
                .identifier_check_nodes
                .push(node);
        }
    }

    /// `(c *Checker) checkUnusedIdentifiers` (checker.go).
    pub(crate) fn check_unused_identifiers(&mut self, potentially_unused_identifiers: &[NodeId]) {
        for &node in potentially_unused_identifiers {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            match nodes[node].kind {
                ast::Kind::ClassDeclaration | ast::Kind::ClassExpression => {
                    self.check_unused_class_members(node);
                    self.check_unused_type_parameters(node);
                }
                ast::Kind::SourceFile
                | ast::Kind::ModuleDeclaration
                | ast::Kind::Block
                | ast::Kind::CaseBlock
                | ast::Kind::ForStatement
                | ast::Kind::ForInStatement
                | ast::Kind::ForOfStatement
                | ast::Kind::ClassStaticBlockDeclaration => {
                    self.check_unused_locals_and_parameters(node);
                }
                ast::Kind::Constructor
                | ast::Kind::FunctionExpression
                | ast::Kind::FunctionDeclaration
                | ast::Kind::ArrowFunction
                | ast::Kind::MethodDeclaration
                | ast::Kind::GetAccessor
                | ast::Kind::SetAccessor => {
                    // Only report unused parameters on the implementation, not overloads.
                    if nodes[node].body().is_some() {
                        self.check_unused_locals_and_parameters(node);
                    }
                    self.check_unused_type_parameters(node);
                }
                ast::Kind::MethodSignature
                | ast::Kind::CallSignature
                | ast::Kind::ConstructSignature
                | ast::Kind::FunctionType
                | ast::Kind::ConstructorType
                | ast::Kind::TypeAliasDeclaration
                | ast::Kind::JSTypeAliasDeclaration
                | ast::Kind::InterfaceDeclaration => {
                    self.check_unused_type_parameters(node);
                }
                ast::Kind::InferType => {
                    self.check_unused_infer_type_parameter(node);
                }
                _ => panic!("Unhandled case in checkUnusedIdentifiers"),
            }
        }
    }

    /// `(c *Checker) isReferenced` (checker.go).
    pub(crate) fn is_referenced(&mut self, symbol: SymbolId) -> bool {
        self.symbol_reference_links.get(symbol).reference_kinds != ast::SymbolFlags::NONE
    }

    /// `(c *Checker) reportUnusedVariable` (checker.go).
    pub(crate) fn report_unused_variable(
        &mut self,
        location: NodeId,
        diagnostic: ast::diagnostic::DiagnosticRef,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((location).file_index());
        let mut location = location;
        while ast::is_binding_element(&nodes[location]) || ast::is_binding_pattern(&nodes[location])
        {
            location = nodes[location].parent.expect("binding parent");
        }
        let kind = if ast::is_parameter_declaration(&nodes[location]) {
            UnusedKind::Parameter
        } else {
            UnusedKind::Local
        };
        self.report_unused(location, kind, diagnostic);
    }

    /// `(c *Checker) reportUnused` (checker.go).
    pub(crate) fn report_unused(
        &mut self,
        location: NodeId,
        kind: UnusedKind,
        diagnostic: ast::diagnostic::DiagnosticRef,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((location).file_index());
        if !nodes[location].flags.intersects(
            ast::NodeFlags::AMBIENT | ast::NodeFlags::THIS_NODE_OR_ANY_SUB_NODES_HAS_ERROR,
        ) {
            let is_error = self.unused_is_error(kind);
            if is_error {
                self.add_diagnostic(&diagnostic);
            } else {
                ast::diagnostic::lock_diagnostic(&diagnostic)
                    .set_category(tsc_diagnostics::Category::Suggestion);
                self.add_suggestion_diagnostic(&diagnostic);
            }
        }
    }

    /// `(c *Checker) unusedIsError` (checker.go).
    pub(crate) fn unused_is_error(&self, kind: UnusedKind) -> bool {
        match kind {
            UnusedKind::Local => self.compiler_options.no_unused_locals.is_true(),
            UnusedKind::Parameter => self.compiler_options.no_unused_parameters.is_true(),
            _ => panic!("Unhandled case in unusedIsError"),
        }
    }

    /// `(c *Checker) checkUnusedClassMembers` (checker.go).
    pub(crate) fn check_unused_class_members(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let members: Vec<NodeId> = nodes[node]
            .members()
            .map(|m| m.to_vec())
            .unwrap_or_default();
        for member in members {
            match nodes[member].kind {
                ast::Kind::MethodDeclaration
                | ast::Kind::PropertyDeclaration
                | ast::Kind::GetAccessor
                | ast::Kind::SetAccessor => {
                    if ast::is_set_accessor_declaration(&nodes[member])
                        && nodes[member].symbol().is_some_and(|s| {
                            sym_flags(self, s).intersects(ast::SymbolFlags::GET_ACCESSOR)
                        })
                    {
                        continue; // Already would have reported an error on the getter.
                    }
                    let symbol = self.get_symbol_of_declaration(member);
                    let symbol = match symbol {
                        Some(s) => s,
                        None => continue,
                    };
                    if !self.is_referenced(symbol)
                        && (ast::has_modifier(&nodes[member], ast::ModifierFlags::PRIVATE)
                            || nodes[member]
                                .name()
                                .is_some_and(|n| ast::is_private_identifier(&nodes[n])))
                        && !nodes[member].flags.intersects(ast::NodeFlags::AMBIENT)
                    {
                        let name = nodes[member].name();
                        let sym_name = self.symbol_to_string(symbol);
                        let diag = self.new_diagnostic_for_node(
                            name,
                            &tsc_diagnostics::X_0_is_declared_but_its_value_is_never_read,
                            &[sym_name],
                        );
                        self.report_unused(member, UnusedKind::Local, diag);
                    }
                }
                ast::Kind::Constructor => {
                    let params: Vec<NodeId> = nodes[member]
                        .parameters()
                        .map(|l| l.to_vec())
                        .unwrap_or_default();
                    for parameter in params {
                        if let Some(symbol) = nodes[parameter].symbol() {
                            if !self.is_referenced(symbol)
                                && ast::has_syntactic_modifier(
                                    &nodes[parameter],
                                    ast::ModifierFlags::PRIVATE,
                                )
                            {
                                let name = nodes[parameter].name();
                                let diag = self.new_diagnostic_for_node(
                                    name,
                                    &tsc_diagnostics::Property_0_is_declared_but_its_value_is_never_read,
                                    &[sym_name(self, symbol)],
                                );
                                self.report_unused(parameter, UnusedKind::Local, diag);
                            }
                        }
                    }
                }
                ast::Kind::IndexSignature
                | ast::Kind::SemicolonClassElement
                | ast::Kind::ClassStaticBlockDeclaration
                | ast::Kind::JSTypeAliasDeclaration => {
                    // Can't be private
                }
                _ => panic!("Unhandled case in checkUnusedClassMembers"),
            }
        }
    }

    /// `(c *Checker) checkUnusedLocalsAndParameters` (checker.go).
    pub(crate) fn check_unused_locals_and_parameters(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut variable_parents: Vec<NodeId> = Vec::new();
        let mut import_clauses: Vec<(NodeId, Vec<NodeId>)> = Vec::new();
        let locals: Vec<SymbolId> = nodes[node]
            .locals()
            .map(|l| l.entries().map(|(_, &s)| s).collect())
            .unwrap_or_default();
        for local in locals {
            let reference_kinds = self.symbol_reference_links.get(local).reference_kinds;
            let local_flags = sym_flags(self, local);
            let export_symbol = self.symbol_arena.borrow()[local.index()].export_symbol;
            if (local_flags.intersects(ast::SymbolFlags::TYPE_PARAMETER)
                && (!local_flags.intersects(ast::SymbolFlags::VARIABLE)
                    || reference_kinds.intersects(ast::SymbolFlags::VARIABLE)))
                || (!local_flags.intersects(ast::SymbolFlags::TYPE_PARAMETER)
                    && (reference_kinds != ast::SymbolFlags::NONE
                        || export_symbol.is_some()
                        || local_flags.intersects(ast::SymbolFlags::MODULE_EXPORTS)))
            {
                continue;
            }
            for declaration in sym_declarations(self, local) {
                if ast::is_variable_declaration(&nodes[declaration])
                    || ast::is_parameter_declaration(&nodes[declaration])
                    || ast::is_binding_element(&nodes[declaration])
                {
                    let root = ast::get_root_declaration(declaration, &nodes);
                    let parent = nodes[root].parent.expect("root parent");
                    if !variable_parents.contains(&parent) {
                        variable_parents.push(parent);
                    }
                } else if ast::is_import_clause(&nodes[declaration])
                    || ast::is_import_specifier(&nodes[declaration])
                    || ast::is_namespace_import(&nodes[declaration])
                {
                    if !nodes[declaration].name().is_some_and(|n| {
                        is_identifier_that_starts_with_underscore(&nodes[n], &nodes)
                    }) {
                        let import_clause = import_clause_from_imported(declaration, &nodes);
                        if let Some(entry) =
                            import_clauses.iter_mut().find(|(k, _)| *k == import_clause)
                        {
                            entry.1.push(declaration);
                        } else {
                            import_clauses.push((import_clause, vec![declaration]));
                        }
                    }
                } else {
                    if !ast::is_type_parameter_declaration(&nodes[declaration])
                        && !ast::is_ambient_module(&nodes[declaration], &nodes)
                    {
                        self.report_unused_local(declaration, sym_name(self, local));
                    }
                }
            }
        }
        for declaration in variable_parents {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((declaration).file_index());
            if ast::is_variable_declaration_list(&nodes[declaration]) {
                self.report_unused_variables(declaration);
            } else {
                self.report_unused_parameters(declaration);
            }
        }
        for (declaration, unuseds) in import_clauses {
            self.report_unused_imports(declaration, &unuseds);
        }
    }

    /// `(c *Checker) reportUnusedLocal` (checker.go).
    pub(crate) fn report_unused_local(&mut self, node: NodeId, name: String) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let message: &'static tsc_diagnostics::Message = if ast::is_type_declaration(node, &nodes) {
            &tsc_diagnostics::X_0_is_declared_but_never_used
        } else {
            &tsc_diagnostics::X_0_is_declared_but_its_value_is_never_read
        };
        let diag =
            self.new_diagnostic_for_node(nodes[node].name().or(Some(node)), message, &[name]);
        self.report_unused(node, UnusedKind::Local, diag);
    }

    /// `(c *Checker) reportUnusedVariables` (checker.go).
    pub(crate) fn report_unused_variables(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let declarations: Vec<NodeId> = nodes[node]
            .as_variable_declaration_list()
            .declarations
            .as_ref()
            .map(|l| l.nodes.to_vec())
            .unwrap_or_default();
        if declarations.len() > 1
            && declarations
                .iter()
                .all(|&d| self.is_unreferenced_variable_declaration(d))
        {
            let diag = self.new_diagnostic_for_node::<String>(
                Some(node),
                &tsc_diagnostics::All_variables_are_unused,
                &[],
            );
            self.report_unused_variable(node, diag);
        } else {
            self.report_unused_variable_declarations(&declarations);
        }
    }

    /// `(c *Checker) reportUnusedParameters` (checker.go).
    pub(crate) fn report_unused_parameters(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let params: Vec<NodeId> = nodes[node]
            .parameters()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        self.report_unused_variable_declarations(&params);
    }

    /// `(c *Checker) reportUnusedBindingElements` (checker.go).
    pub(crate) fn report_unused_binding_elements(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let declarations: Vec<NodeId> = nodes[node]
            .elements()
            .map(|e| e.to_vec())
            .unwrap_or_default();
        if declarations.len() > 1
            && declarations
                .iter()
                .all(|&d| self.is_unreferenced_variable_declaration(d))
        {
            let diag = self.new_diagnostic_for_node::<&str>(
                Some(node),
                &tsc_diagnostics::All_destructured_elements_are_unused,
                &[],
            );
            self.report_unused_variable(node, diag);
        } else {
            self.report_unused_variable_declarations(&declarations);
        }
    }

    /// `(c *Checker) reportUnusedVariableDeclarations` (checker.go).
    pub(crate) fn report_unused_variable_declarations(&mut self, declarations: &[NodeId]) {
        for &declaration in declarations {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((declaration).file_index());
            if let Some(name) = nodes[declaration].name() {
                let parent = nodes[declaration].parent;
                if parent.is_some_and(|p| {
                    ast::is_parameter_property_declaration(&nodes[declaration], &nodes[p])
                }) || ast::is_this_parameter(&nodes[declaration], &nodes)
                {
                    continue;
                }
                if ast::is_binding_pattern(&nodes[name]) {
                    self.report_unused_binding_elements(name);
                } else if self.is_unreferenced_variable_declaration(declaration) {
                    let text = nodes[name].text(&nodes).to_string();
                    let diag = self.new_diagnostic_for_node(
                        Some(name),
                        &tsc_diagnostics::X_0_is_declared_but_its_value_is_never_read,
                        &[text],
                    );
                    self.report_unused_variable(declaration, diag);
                }
            }
        }
    }

    /// `(c *Checker) isUnreferencedVariableDeclaration` (checker.go).
    pub(crate) fn is_unreferenced_variable_declaration(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let name = match nodes[node].name() {
            Some(n) => n,
            None => return true,
        };
        if ast::is_binding_pattern(&nodes[name]) {
            return nodes[name]
                .elements()
                .map(|e| e.to_vec())
                .unwrap_or_default()
                .iter()
                .all(|&d| self.is_unreferenced_variable_declaration(d));
        }
        let __h11878_17 = self.get_symbol_of_declaration(node);

        if self
            .symbol_reference_links
            .get(__h11878_17.unwrap_or(SymbolId::NONE))
            .reference_kinds
            .intersects(ast::SymbolFlags::VARIABLE)
        {
            return false;
        }
        if ast::is_binding_element(&nodes[node])
            && nodes[node]
                .parent
                .is_some_and(|p| ast::is_object_binding_pattern(&nodes[p]))
        {
            // In `{ a, ...b }, `a` is considered used since it removes a property from `b`. `b` may still be unused though.
            let parent = nodes[node].parent.unwrap();
            let last_element = nodes[parent].elements().and_then(|e| e.last().copied());
            if last_element.is_some_and(|le| node != le)
                && last_element
                    .is_some_and(|le| crate::utilities::has_dot_dot_dot_token(&nodes[le], &nodes))
            {
                return false;
            }
        }
        if (ast::is_parameter_declaration(&nodes[node])
            || (ast::is_variable_declaration(&nodes[node])
                && (nodes[node]
                    .parent
                    .and_then(|p| nodes[p].parent)
                    .is_some_and(|gp| ast::is_for_in_or_of_statement(Some(gp), &nodes))
                    || self
                        .get_combined_node_flags_cached(node)
                        .intersects(ast::NodeFlags::USING)))
            || (ast::is_binding_element(&nodes[node])
                && !(nodes[node]
                    .parent
                    .is_some_and(|p| ast::is_object_binding_pattern(&nodes[p]))
                    && nodes[node].property_name().is_none())))
            && is_identifier_that_starts_with_underscore(&nodes[name], &nodes)
        {
            return false;
        }
        true
    }

    /// `(c *Checker) reportUnusedImports` (checker.go).
    pub(crate) fn report_unused_imports(&mut self, node: NodeId, unuseds: &[NodeId]) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut declaration_count = tsc_core::core::if_else(nodes[node].name().is_some(), 1, 0);
        let named_bindings = nodes[node].as_import_clause().named_bindings;
        if let Some(named_bindings) = named_bindings {
            if ast::is_namespace_import(&nodes[named_bindings]) {
                declaration_count += 1;
            } else {
                declaration_count += nodes[named_bindings]
                    .elements()
                    .map(|e| e.len())
                    .unwrap_or(0);
            }
        }
        if declaration_count > 1 && declaration_count == unuseds.len() {
            let parent = nodes[node].parent;
            let diag = self.new_diagnostic_for_node::<&str>(
                parent,
                &tsc_diagnostics::All_imports_in_import_declaration_are_unused,
                &[],
            );
            self.report_unused(node, UnusedKind::Local, diag);
        } else {
            for &unused in unuseds {
                let name = nodes[unused]
                    .name()
                    .map(|n| nodes[n].text(&nodes).to_string())
                    .unwrap_or_default();
                self.report_unused_local(unused, name);
            }
        }
    }

    /// `(c *Checker) checkUnusedInferTypeParameter` (checker.go).
    pub(crate) fn check_unused_infer_type_parameter(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let type_parameter = nodes[node]
            .as_infer_type_node()
            .type_parameter
            .expect("infer type parameter");
        if self.is_unreferenced_type_parameter(type_parameter) {
            let name = nodes[type_parameter].name();
            let text = name
                .map(|n| nodes[n].text(&nodes).to_string())
                .unwrap_or_default();
            let diag = self.new_diagnostic_for_node(
                name,
                &tsc_diagnostics::X_0_is_declared_but_never_used,
                &[text],
            );
            self.report_unused(node, UnusedKind::Parameter, diag);
        }
    }

    /// `(c *Checker) checkUnusedTypeParameters` (checker.go).
    pub(crate) fn check_unused_type_parameters(&mut self, node: NodeId) {
        let symbol = self.get_symbol_of_declaration(node);
        if !symbol.is_some_and(|s| {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            crate::utilities::all_declarations_in_same_source_file(
                &self.symbol_arena.borrow()[s.index()],
                &nodes,
            )
        }) {
            return;
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let type_parameter_list: Vec<NodeId> = nodes[node]
            .type_parameter_list()
            .map(|l| l.nodes.to_vec())
            .unwrap_or_default();
        if type_parameter_list.is_empty() {
            return;
        }
        if type_parameter_list.len() > 1
            && type_parameter_list
                .iter()
                .all(|&tp| self.is_unreferenced_type_parameter(tp))
        {
            let file = ast::get_source_file_of_node(Some(node), &nodes).expect("source file");
            let loc = crate::utilities::range_of_type_parameters(
                nodes[file].as_source_file(),
                nodes[node].type_parameter_list().unwrap(),
                &nodes,
            );
            let diag = ast::diagnostic::new_diagnostic(
                Some(ast::diagnostic::DiagnosticFile::from_node(file, &nodes)),
                loc,
                &tsc_diagnostics::All_type_parameters_are_unused,
                &[] as &[String],
            );
            self.report_unused(node, UnusedKind::Parameter, diag);
        } else {
            for &type_parameter in &type_parameter_list {
                if self.is_unreferenced_type_parameter(type_parameter) {
                    let name = nodes[type_parameter].name();
                    let text = name
                        .map(|n| nodes[n].text(&nodes).to_string())
                        .unwrap_or_default();
                    let diag = self.new_diagnostic_for_node(
                        Some(type_parameter),
                        &tsc_diagnostics::X_0_is_declared_but_never_used,
                        &[text],
                    );
                    self.report_unused(node, UnusedKind::Parameter, diag);
                }
            }
        }
    }

    /// `(c *Checker) isUnreferencedTypeParameter` (checker.go).
    pub(crate) fn is_unreferenced_type_parameter(&mut self, type_parameter: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((type_parameter).file_index());
        let symbol = nodes[type_parameter].symbol().unwrap_or(SymbolId::NONE);
        let merged = self.get_merged_symbol(symbol);
        !self
            .symbol_reference_links
            .get(merged)
            .reference_kinds
            .intersects(ast::SymbolFlags::TYPE_PARAMETER)
            && !nodes[type_parameter]
                .name()
                .is_some_and(|n| is_identifier_that_starts_with_underscore(&nodes[n], &nodes))
    }

    /// `(c *Checker) checkUnusedRenamedBindingElements` (checker.go).
    pub(crate) fn check_unused_renamed_binding_elements(&mut self) {
        let nodes_list: Vec<NodeId> = self.renamed_binding_elements_in_types.clone();
        for node in nodes_list {
            let symbol = self
                .get_symbol_of_declaration(node)
                .unwrap_or(SymbolId::NONE);
            if self.symbol_reference_links.get(symbol).reference_kinds == ast::SymbolFlags::NONE {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((node).file_index());
                let wrapping_declaration = ast::walk_up_binding_elements_and_patterns(node, &nodes);
                debug_assert!(
                    wrapping_declaration
                        .is_some_and(|w| { ast::is_part_of_parameter_declaration(w, &nodes) }),
                    "Only parameter declaration should be checked here"
                );
                let name = nodes[node].name();
                let property_name = nodes[node].property_name();
                let diagnostic = self.new_diagnostic_for_node(
                    name,
                    &tsc_diagnostics::X_0_is_an_unused_renaming_of_1_Did_you_intend_to_use_it_as_a_type_annotation,
                    &[
                        tsc_scanner::utilities::declaration_name_to_string(name, &nodes),
                        tsc_scanner::utilities::declaration_name_to_string(property_name, &nodes),
                    ],
                );
                if let Some(wrapping_declaration) = wrapping_declaration {
                    if nodes[wrapping_declaration].type_().is_none() {
                        // entire parameter does not have type annotation, suggest adding an annotation
                        let wrapping_file =
                            ast::get_source_file_of_node(Some(wrapping_declaration), &nodes)
                                .expect("source file");
                        let end = nodes[wrapping_declaration].end();
                        let related = ast::diagnostic::new_diagnostic(
                            Some(ast::diagnostic::DiagnosticFile::from_node(
                                wrapping_file,
                                &nodes,
                            )),
                            tsc_core::text::TextRange::new(end, end),
                            &tsc_diagnostics::We_can_only_write_a_type_for_0_by_adding_a_type_for_the_entire_parameter_here,
                            &[tsc_scanner::utilities::declaration_name_to_string(
                                property_name,
                                &nodes,
                            )],
                        );
                        ast::diagnostic::lock_diagnostic(&diagnostic)
                            .add_related_info(Some(related));
                    }
                }
                self.add_diagnostic(&diagnostic);
            }
        }
    }

    /// `(c *Checker) checkExpressionStatement` (checker.go).
    pub(crate) fn check_expression_statement(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Grammar checking
        self.check_grammar_statement_in_ambient_context(node);
        if let Some(expression) = nodes[node].expression() {
            self.check_expression(expression);
        }
    }
}

/// `isIdentifierThatStartsWithUnderscore` (checker.go) — free function.
fn is_identifier_that_starts_with_underscore(node: &ast::Node, nodes: &[ast::Node]) -> bool {
    ast::is_identifier(node) && node.text(nodes).starts_with('_')
}

/// `importClauseFromImported` (checker.go) — free function.
fn import_clause_from_imported(node: NodeId, nodes: &[ast::Node]) -> NodeId {
    match nodes[node].kind {
        ast::Kind::ImportClause => node,
        ast::Kind::NamespaceImport => nodes[node].parent.expect("namespace import parent"),
        _ => nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .expect("import specifier grandparent"),
    }
}

// ======== checker.go ~7539 — expression checking ========

impl Checker {
    /// `(c *Checker) getTypeOfExpression` (checker.go).
    ///
    /// Returns the type of an expression. Unlike checkExpression, this function is simply concerned
    /// with computing the type and may not fully check all contained sub-expressions for errors.
    pub(crate) fn get_type_of_expression(&mut self, node: NodeId) -> TypeId {
        // Don't bother caching types that require no flow analysis and are quick to compute.
        if let Some(quick_type) = self.get_quick_type_of_expression(node) {
            return quick_type;
        }
        // If a type has been cached for the node, return it.
        if let Some(&cached_type) = self.flow_type_cache.get(&node) {
            return cached_type;
        }
        let start_invocation_count = self.flow_invocation_count;
        let t = self.check_expression_ex(node, CheckMode::TYPE_ONLY);
        // If control flow analysis was required to determine the type, it is worth caching.
        if self.flow_invocation_count != start_invocation_count {
            self.flow_type_cache.insert(node, t);
        }
        t
    }

    /// `(c *Checker) getQuickTypeOfExpression` (checker.go).
    ///
    /// Returns the type of an expression. Unlike checkExpression, this function is simply concerned
    /// with computing the type and may not fully check all contained sub-expressions for errors.
    pub(crate) fn get_quick_type_of_expression(&mut self, node: NodeId) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let expr = ast::skip_parentheses(node, &nodes);
        if ast::is_await_expression(&nodes[expr]) {
            let t = self.get_quick_type_of_expression(nodes[expr].expression()?);
            return t.and_then(|t| self.get_awaited_type(t));
        }
        // Optimize for the common case of a call to a function with a single non-generic call
        // signature where we can just fetch the return type without checking the arguments.
        if ast::is_call_expression(&nodes[expr])
            && nodes[expr]
                .expression()
                .is_some_and(|e| nodes[e].kind != ast::Kind::SuperKeyword)
            && !ast::is_require_call(
                &nodes[expr],
                true, /*requireStringLiteralLikeArgument*/
                &nodes,
            )
            && !self.is_symbol_or_symbol_for_call(expr)
            && !ast::is_import_call(&nodes[expr], &nodes)
        {
            if crate::utilities::is_call_chain(&nodes[expr]) {
                return self.get_return_type_of_single_non_generic_signature_of_call_chain(expr);
            }
            let func_type = self.check_non_null_expression(nodes[expr].expression().unwrap());
            return self
                .get_return_type_of_single_non_generic_signature(func_type, SignatureKind::Call);
        }
        if ast::is_new_expression(&nodes[expr]) {
            let func_type = self.check_non_null_expression(nodes[expr].expression().unwrap());
            return self.get_return_type_of_single_non_generic_signature(
                func_type,
                SignatureKind::Construct,
            );
        }
        if ast::is_assertion_expression(&nodes[expr])
            && !ast::is_const_type_reference(&nodes[nodes[expr].type_()?], &nodes)
        {
            return Some(self.get_type_from_type_node(nodes[expr].type_()?));
        }
        if ast::is_literal_expression(&nodes[node]) || ast::is_boolean_literal(&nodes[node]) {
            return Some(self.check_expression(node));
        }
        None
    }

    /// `(c *Checker) getReturnTypeOfSingleNonGenericSignature` (checker.go).
    pub(crate) fn get_return_type_of_single_non_generic_signature(
        &mut self,
        func_type: TypeId,
        kind: SignatureKind,
    ) -> Option<TypeId> {
        let signature = self.get_single_signature(func_type, kind, true /*allowMembers*/);
        if let Some(signature) = signature {
            if self
                .signature_arena
                .get(signature)
                .type_parameters
                .is_empty()
            {
                return Some(self.get_return_type_of_signature(signature));
            }
        }
        None
    }

    /// `(c *Checker) getReturnTypeOfSingleNonGenericSignatureOfCallChain` (checker.go).
    pub(crate) fn get_return_type_of_single_non_generic_signature_of_call_chain(
        &mut self,
        expr: NodeId,
    ) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((expr).file_index());
        let expression = nodes[expr].expression()?;
        let func_type = self.check_expression(expression);
        let non_optional_type = self.get_optional_expression_type(func_type, expression);
        let return_type =
            self.get_return_type_of_single_non_generic_signature(func_type, SignatureKind::Call);
        if let Some(return_type) = return_type {
            return Some(self.propagate_optional_type_marker(
                return_type,
                expr,
                non_optional_type != func_type,
            ));
        }
        None
    }

    /// `(c *Checker) checkNonNullExpression` (checker.go).
    pub(crate) fn check_non_null_expression(&mut self, node: NodeId) -> TypeId {
        let t = self.check_expression(node);
        self.check_non_null_type(t, node)
    }

    /// `(c *Checker) checkNonNullType` (checker.go).
    pub(crate) fn check_non_null_type(&mut self, t: TypeId, node: NodeId) -> TypeId {
        self.check_non_null_type_with_reporter(t, node, |c, node, facts| {
            c.report_object_possibly_null_or_undefined_error(node, facts)
        })
    }

    /// `(c *Checker) checkNonNullTypeWithReporter` (checker.go).
    pub(crate) fn check_non_null_type_with_reporter(
        &mut self,
        t: TypeId,
        node: NodeId,
        report_error: impl FnOnce(&mut Checker, NodeId, TypeFacts),
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if self.strict_null_checks && tflags(self, t).intersects(TypeFlags::UNKNOWN) {
            if ast::is_entity_name_expression(&nodes[node], &nodes) {
                let node_text = ast::entity_name_to_string(node, &nodes, None);
                if node_text.len() < 100 {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::X_0_is_of_type_unknown,
                        &[node_text],
                    );
                    return self.error_type;
                }
            }
            self.error(Some(node), &tsc_diagnostics::Object_is_of_type_unknown, &[]);
            return self.error_type;
        }
        let facts = self.get_type_facts(t, TypeFacts::IS_UNDEFINED_OR_NULL);
        if facts.intersects(TypeFacts::IS_UNDEFINED_OR_NULL) {
            report_error(self, node, facts);
            let non_nullable = self.get_non_nullable_type(t);
            if tflags(self, non_nullable).intersects(TypeFlags::NULLABLE | TypeFlags::NEVER) {
                return self.error_type;
            }
            return non_nullable;
        }
        t
    }

    /// `(c *Checker) checkNonNullNonVoidType` (checker.go).
    pub(crate) fn check_non_null_non_void_type(&mut self, t: TypeId, node: NodeId) -> TypeId {
        let non_null_type = self.check_non_null_type(t, node);
        if tflags(self, non_null_type).intersects(TypeFlags::VOID) {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            if ast::is_entity_name_expression(&nodes[node], &nodes) {
                let node_text = ast::entity_name_to_string(node, &nodes, None);
                if ast::is_identifier(&nodes[node]) && node_text == "undefined" {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::The_value_0_cannot_be_used_here,
                        &[node_text],
                    );
                    return non_null_type;
                }
                if node_text.len() < 100 {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::X_0_is_possibly_undefined,
                        &[node_text],
                    );
                    return non_null_type;
                }
            }
            self.error(
                Some(node),
                &tsc_diagnostics::Object_is_possibly_undefined,
                &[],
            );
        }
        non_null_type
    }

    /// `(c *Checker) reportObjectPossiblyNullOrUndefinedError` (checker.go).
    pub(crate) fn report_object_possibly_null_or_undefined_error(
        &mut self,
        node: NodeId,
        facts: TypeFacts,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut node_text = String::new();
        if ast::is_entity_name_expression(&nodes[node], &nodes) {
            node_text = ast::entity_name_to_string(node, &nodes, None);
        }
        if nodes[node].kind == ast::Kind::NullKeyword {
            self.error(
                Some(node),
                &tsc_diagnostics::The_value_0_cannot_be_used_here,
                &["null".to_string()],
            );
            return;
        }
        if !node_text.is_empty() && node_text.len() < 100 {
            if ast::is_identifier(&nodes[node]) && node_text == "undefined" {
                self.error(
                    Some(node),
                    &tsc_diagnostics::The_value_0_cannot_be_used_here,
                    &["undefined".to_string()],
                );
                return;
            }
            self.error(
                Some(node),
                tsc_core::core::if_else(
                    facts.intersects(TypeFacts::IS_UNDEFINED),
                    tsc_core::core::if_else(
                        facts.intersects(TypeFacts::IS_NULL),
                        &tsc_diagnostics::X_0_is_possibly_null_or_undefined,
                        &tsc_diagnostics::X_0_is_possibly_undefined,
                    ),
                    &tsc_diagnostics::X_0_is_possibly_null,
                ),
                &[node_text],
            );
        } else {
            self.error(
                Some(node),
                tsc_core::core::if_else(
                    facts.intersects(TypeFacts::IS_UNDEFINED),
                    tsc_core::core::if_else(
                        facts.intersects(TypeFacts::IS_NULL),
                        &tsc_diagnostics::Object_is_possibly_null_or_undefined,
                        &tsc_diagnostics::Object_is_possibly_undefined,
                    ),
                    &tsc_diagnostics::Object_is_possibly_null,
                ),
                &[] as &[String],
            );
        }
    }

    /// `(c *Checker) checkExpressionWithContextualType` (checker.go).
    pub(crate) fn check_expression_with_contextual_type(
        &mut self,
        node: NodeId,
        contextual_type: TypeId,
        inference_context: Option<InferenceContextId>,
        check_mode: CheckMode,
    ) -> TypeId {
        let context_node = self.get_context_node(node);
        self.push_contextual_type(context_node, Some(contextual_type), false /*isCache*/);
        self.push_inference_context(context_node, inference_context);
        let mut t = self.check_expression_ex(
            node,
            check_mode
                | CheckMode::CONTEXTUAL
                | if inference_context.is_some() {
                    CheckMode::INFERENTIAL
                } else {
                    CheckMode::NORMAL
                },
        );
        // In CheckMode.Inferential we collect intra-expression inference sites to process before fixing any type
        // parameters. This information is no longer needed after the call to checkExpression.
        if let Some(context_id) = inference_context {
            if !self.inference_contexts[context_id.index()]
                .intra_expression_inference_sites
                .is_empty()
            {
                self.inference_contexts[context_id.index()]
                    .intra_expression_inference_sites
                    .clear();
            }
        }
        let __h12423_17 =
            self.instantiate_contextual_type(Some(contextual_type), node, ContextFlags::NONE);

        // We strip literal freshness when an appropriate contextual type is present such that contextually typed
        // literals always preserve their literal types (otherwise they might widen during type inference). An alternative
        // here would be to not mark contextually typed literals as fresh in the first place.
        if self.maybe_type_of_kind(t, TypeFlags::LITERAL)
            && self.is_literal_of_contextual_type(t, __h12423_17)
        {
            t = self.get_regular_type_of_literal_type(t);
        }
        self.pop_inference_context();
        self.pop_contextual_type();
        t
    }

    /// `(c *Checker) getContextNode` (checker.go).
    pub(crate) fn get_context_node(&self, node: NodeId) -> NodeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if ast::is_jsx_attributes(&nodes[node])
            && !nodes[node]
                .parent
                .is_some_and(|p| ast::is_jsx_self_closing_element(&nodes[p]))
        {
            // Needs to be the root JsxElement, so it encompasses the attributes _and_ the children (which are essentially part of the attributes)
            return nodes[node]
                .parent
                .and_then(|p| nodes[p].parent)
                .expect("jsx element");
        }
        node
    }

    /// `(c *Checker) checkExpressionCached` (checker.go).
    pub(crate) fn check_expression_cached(&mut self, node: NodeId) -> TypeId {
        self.check_expression_cached_ex(node, CheckMode::NORMAL)
    }

    /// `(c *Checker) checkExpressionCachedEx` (checker.go).
    pub(crate) fn check_expression_cached_ex(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        if check_mode != CheckMode::NORMAL {
            return self.check_expression_ex(node, check_mode);
        }
        if let Some(t) = self.type_node_links.get(node).resolved_type {
            return t;
        }
        // When computing a type that we're going to cache, we need to ignore any ongoing control flow
        // analysis because variables may have transient types in indeterminable states. Moving flowLoopStart
        // to the top of the stack ensures all transient types are computed from a known point.
        let save_flow_loop_stack = std::mem::take(&mut self.flow_loop_stack);
        let save_flow_type_cache = std::mem::take(&mut self.flow_type_cache);
        let t = self.check_expression_ex(node, check_mode);
        self.type_node_links.get(node).resolved_type = Some(t);
        self.flow_type_cache = save_flow_type_cache;
        self.flow_loop_stack = save_flow_loop_stack;
        t
    }

    /// `(c *Checker) getContextFreeTypeOfExpression` (checker.go).
    ///
    /// Returns the type of an expression. Unlike checkExpression, this function is simply concerned
    /// with computing the type and may not fully check all contained sub-expressions for errors.
    /// It is intended for uses where you know there is no contextual type,
    /// and requesting the contextual type might cause a circularity or other bad behaviour.
    /// It sets the contextual type of the node to any before calling getTypeOfExpression.
    pub(crate) fn get_context_free_type_of_expression(&mut self, node: NodeId) -> TypeId {
        if let Some(&cached) = self.context_free_types.get(&node) {
            return cached;
        }
        self.push_contextual_type(node, Some(self.any_type), false /*isCache*/);
        let t = self.check_expression_ex(node, CheckMode::SKIP_CONTEXT_SENSITIVE);
        self.context_free_types.insert(node, t);
        self.pop_contextual_type();
        t
    }

    /// `(c *Checker) checkExpression` (checker.go).
    pub(crate) fn check_expression(&mut self, node: NodeId) -> TypeId {
        self.check_expression_ex(node, CheckMode::NORMAL)
    }

    /// `(c *Checker) checkExpressionEx` (checker.go).
    pub(crate) fn check_expression_ex(&mut self, node: NodeId, check_mode: CheckMode) -> TypeId {
        // `if tr := c.tracer; tr != nil { defer tr.Push(...)() }`
        let trace_pop: Option<Box<dyn FnOnce()>> = self.tracer.as_ref().map(|tr| {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            let mut args = tsc_tracing::TraceArgs::default();
            args.insert(
                "kind".into(),
                serde_json::Value::from(nodes[node].kind_value()),
            );
            args.insert("pos".into(), serde_json::Value::from(nodes[node].pos()));
            args.insert("end".into(), serde_json::Value::from(nodes[node].end()));
            if let Some(sf) = ast::get_source_file_of_node(Some(node), &nodes) {
                args.insert(
                    "path".into(),
                    serde_json::Value::from(nodes[sf].as_source_file().file_name().to_string()),
                );
            }
            tr.push(
                tsc_tracing::PHASE_CHECK,
                "checkExpression",
                &mut args,
                false,
            )
        });
        let save_current_node = self.current_node;
        self.current_node = Some(node);
        self.instantiation_count = 0;
        let uninstantiated_type = self.check_expression_worker(node, check_mode);
        let t = self.instantiate_type_with_single_generic_call_signature(
            node,
            uninstantiated_type,
            check_mode,
        );
        if crate::utilities::is_const_enum_object_type(self, t) {
            self.check_const_enum_access(node, t);
        }
        self.current_node = save_current_node;
        if let Some(pop) = trace_pop {
            pop();
        }
        t
    }

    /// `(c *Checker) checkConstEnumAccess` (checker.go).
    pub(crate) fn check_const_enum_access(&mut self, node: NodeId, t: TypeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // enum object type for const enums are only permitted in:
        // - 'left' in property access
        // - 'object' in indexed access
        // - target in rhs of import statement
        let parent = nodes[node].parent;
        let ok = parent.is_some_and(|p| {
            ast::is_property_access_expression(&nodes[p]) && nodes[p].expression() == Some(node)
        }) || parent.is_some_and(|p| {
            ast::is_element_access_expression(&nodes[p]) && nodes[p].expression() == Some(node)
        }) || ((ast::is_identifier(&nodes[node]) || ast::is_qualified_name(&nodes[node]))
            && crate::utilities::is_in_right_side_of_import_or_export_assignment(node, &nodes)
            || parent.is_some_and(|p| {
                ast::is_type_query_node(&nodes[p])
                    && nodes[p].as_type_query_node().expr_name == Some(node)
            }))
            || parent.is_some_and(|p| ast::is_export_specifier(&nodes[p])); // We allow reexporting const enums
        if !ok {
            self.error(
                Some(node),
                &tsc_diagnostics::X_const_enums_can_only_be_used_in_property_or_index_access_expressions_or_the_right_hand_side_of_an_import_declaration_or_export_assignment_or_type_query,
                &[],
            );
        }
        // --verbatimModuleSyntax only gets checked here when the enum usage does not
        // resolve to an import, because imports of ambient const enums get checked
        // separately in `checkAliasSymbol`.
        if self.compiler_options.isolated_modules.is_true()
            || (self.compiler_options.verbatim_module_syntax.is_true()
                && ok
                && call_resolve_name(
                    self,
                    Some(node),
                    &nodes[ast::get_first_identifier(node, &nodes)]
                        .text(&nodes)
                        .to_string(),
                    ast::SymbolFlags::ALIAS,
                    None,
                    false,
                    true,
                )
                .is_none())
        {
            debug_assert!(
                self.types_handle()
                    .get(t)
                    .symbol()
                    .is_some_and(|s| sym_flags(self, s).intersects(ast::SymbolFlags::CONST_ENUM))
            );
            let const_enum_symbol = self.types.get_ref(t)
                .symbol()
                .expect("const enum symbol");
            if let Some(const_enum_declaration) = sym_value_declaration(self, const_enum_symbol) {
                let sf = ast::get_source_file_of_node(Some(const_enum_declaration), &nodes)
                    .expect("source file");
                let redirect = self
                    .program
                    .as_ref()
                    .expect("program")
                    .get_project_reference_from_output_dts(nodes[sf].as_source_file().path_key());
                if nodes[const_enum_declaration]
                    .flags
                    .intersects(ast::NodeFlags::AMBIENT)
                    && !ast::is_valid_type_only_alias_use_site(node, &nodes)
                    && redirect.is_none_or(|r| {
                        !r.resolved
                            .compiler_options()
                            .is_some_and(|o| o.should_preserve_const_enums())
                    })
                {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Cannot_access_ambient_const_enums_when_0_is_enabled,
                        &[self.get_isolated_modules_like_flag_name()],
                    );
                }
            }
        }
    }

    /// `(c *Checker) instantiateTypeWithSingleGenericCallSignature` (checker.go).
    pub(crate) fn instantiate_type_with_single_generic_call_signature(
        &mut self,
        node: NodeId,
        t: TypeId,
        check_mode: CheckMode,
    ) -> TypeId {
        if !check_mode.intersects(CheckMode::INFERENTIAL | CheckMode::SKIP_GENERIC_FUNCTIONS) {
            return t;
        }
        let call_signature =
            self.get_single_signature(t, SignatureKind::Call, true /*allowMembers*/);
        let construct_signature =
            self.get_single_signature(t, SignatureKind::Construct, true /*allowMembers*/);
        let signature = call_signature.or(construct_signature);
        let signature = match signature {
            Some(s) if !self.signature_arena.get(s).type_parameters.is_empty() => s,
            _ => return t,
        };
        let contextual_type =
            self.get_apparent_type_of_contextual_type(node, ContextFlags::NO_CONSTRAINTS);
        let contextual_type = match contextual_type {
            Some(t) => t,
            None => return t,
        };
        let __h12652_13 = self.get_non_nullable_type(contextual_type);
        let contextual_signature = self.get_single_signature(
            __h12652_13,
            if call_signature.is_some() {
                SignatureKind::Call
            } else {
                SignatureKind::Construct
            },
            false, /*allowMembers*/
        );
        let contextual_signature = match contextual_signature {
            Some(s) if self.signature_arena.get(s).type_parameters.is_empty() => s,
            _ => return t,
        };
        if check_mode.intersects(CheckMode::SKIP_GENERIC_FUNCTIONS) {
            self.skipped_generic_function(node, check_mode);
            return self.any_function_type;
        }
        let context = self.get_inference_context(node);
        let context = match context {
            Some(c) => c,
            None => return t,
        };
        // We have an expression that is an argument of a generic function for which we are performing
        // type argument inference. The expression is of a function type with a single generic call
        // signature and a contextual function type with a single non-generic call signature. Now check
        // if the outer function returns a function type with a single non-generic call signature and
        // if some of the outer function type parameters have no inferences so far. If so, we can
        // potentially add inferred type parameters to the outer function return type.
        let mut return_signature: Option<SignatureId> = None;
        if let Some(sig) = self.inference_contexts[context.index()].signature {
            let return_type = self.get_return_type_of_signature(sig);
            if !tflags(self, return_type).intersects(TypeFlags::NEVER) {
                return_signature = self.get_single_call_or_construct_signature(return_type);
            }
        }
        if let Some(return_signature) = return_signature {
            if self
                .signature_arena
                .get(return_signature)
                .type_parameters
                .is_empty()
                && !self.inference_contexts[context.index()]
                    .inferences
                    .iter()
                    .all(crate::inference::has_inference_candidates)
            {
                // Instantiate the signature with its own type parameters as type arguments, possibly
                // renaming the type parameters to ensure they have unique names.
                let type_parameters = self.signature_arena.get(signature).type_parameters.clone();
                let unique_type_parameters =
                    self.get_unique_type_parameters(context, &type_parameters);
                let instantiated_signature = self
                    .get_signature_instantiation_without_filling_in_type_arguments(
                        signature,
                        &unique_type_parameters,
                    );
                // Infer from the parameters of the instantiated signature to the parameters of the
                // contextual signature starting with an empty set of inference candidates.
                let mut inferences: Vec<InferenceInfo> = self.inference_contexts[context.index()]
                    .inferences
                    .iter()
                    .map(|info| crate::inference::new_inference_info(info.type_parameter))
                    .collect();
                self.apply_to_parameter_types(
                    instantiated_signature,
                    contextual_signature,
                    |c: &mut Checker, source: TypeId, target: TypeId| {
                        c.infer_types(
                            &mut inferences,
                            source,
                            target,
                            InferencePriority::NONE_PRIORITY,
                            true, /*contravariant*/
                        );
                    },
                );
                if inferences
                    .iter()
                    .any(crate::inference::has_inference_candidates)
                {
                    // We have inference candidates, indicating that one or more type parameters are referenced
                    // in the parameter types of the contextual signature. Now also infer from the return type.
                    self.apply_to_return_types(
                        instantiated_signature,
                        contextual_signature,
                        |c: &mut Checker, source: TypeId, target: TypeId| {
                            c.infer_types(
                                &mut inferences,
                                source,
                                target,
                                InferencePriority::NONE_PRIORITY,
                                false,
                            );
                        },
                    );
                    // If the type parameters for which we produced candidates do not have any inferences yet,
                    // we adopt the new inference candidates and add the type parameters of the expression type
                    // to the set of inferred type parameters for the outer function return type.
                    if !crate::inference::has_overlapping_inferences(
                        &self.inference_contexts[context.index()].inferences,
                        &inferences,
                    ) {
                        let mut target_inferences = std::mem::take(
                            &mut self.inference_contexts[context.index()].inferences,
                        );
                        self.merge_inferences(&mut target_inferences, &inferences);
                        self.inference_contexts[context.index()].inferences = target_inferences;
                        self.inference_contexts[context.index()]
                            .inferred_type_parameters
                            .extend_from_slice(&unique_type_parameters);
                        return self.get_or_create_type_from_signature(instantiated_signature);
                    }
                }
            }
        }
        let __h12770_48 = self.instantiate_signature_in_context_of(
            signature,
            contextual_signature,
            Some(context),
            None,
        );

        // TODO: The signature may reference any outer inference contexts, but we map pop off and then apply new inference contexts,
        // and thus get different inferred types. That this is cached on the *first* such attempt is not currently an issue, since expression
        // types *also* get cached on the first pass. If we ever properly speculate, though, the cached "isolatedSignatureType" signature
        // field absolutely needs to be included in the list of speculative caches.
        self.get_or_create_type_from_signature(__h12770_48)
    }

    /// `(c *Checker) getOuterInferenceTypeParameters` (checker.go).
    pub(crate) fn get_outer_inference_type_parameters(&self) -> Vec<TypeId> {
        let mut result: Vec<TypeId> = Vec::new();
        for info in &self.inference_context_infos {
            if let Some(context) = info.context {
                for inference in &self.inference_contexts[context.index()].inferences {
                    if let Some(tp) = inference.type_parameter {
                        result.push(tp);
                    }
                }
            }
        }
        result
    }

    /// `(c *Checker) getUniqueTypeParameters` (checker.go).
    pub(crate) fn get_unique_type_parameters(
        &mut self,
        context: InferenceContextId,
        type_parameters: &[TypeId],
    ) -> Vec<TypeId> {
        let mut old_type_parameters: Vec<TypeId> = Vec::new();
        let mut new_type_parameters: Vec<TypeId> = Vec::new();
        let mut result: Vec<TypeId> = Vec::with_capacity(type_parameters.len());
        for &tp in type_parameters {
            let name = sym_name(
                self,
                self.types_handle()
                    .get(tp)
                    .symbol()
                    .expect("type parameter symbol"),
            );
            let inferred = self.inference_contexts[context.index()]
                .inferred_type_parameters
                .clone();
            if has_type_parameter_by_name(self, &inferred, &name)
                || has_type_parameter_by_name(self, &result, &name)
            {
                let mut all: Vec<TypeId> = inferred.clone();
                all.extend_from_slice(&result);
                let new_name = get_unique_type_parameter_name(self, &all, &name);
                let symbol = self.new_symbol(ast::SymbolFlags::TYPE_PARAMETER, &new_name);
                let new_type_parameter = self.new_type_parameter(Some(symbol));
                self.types_handle()
                    .get_mut(new_type_parameter)
                    .as_type_parameter_mut()
                    .target = Some(tp);
                old_type_parameters.push(tp);
                new_type_parameters.push(new_type_parameter);
                result.push(new_type_parameter);
            } else {
                result.push(tp);
            }
        }
        if !new_type_parameters.is_empty() {
            let mapper = crate::mapper::new_type_mapper(
                self,
                old_type_parameters,
                new_type_parameters.clone(),
            );
            for &tp in &new_type_parameters {
                self.types_handle()
                    .get_mut(tp)
                    .as_type_parameter_mut()
                    .mapper = Some(mapper);
            }
        }
        result
    }

    /// `(c *Checker) checkExpressionWorker` (checker.go).
    pub(crate) fn check_expression_worker(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::Identifier => self.check_identifier(node, check_mode),
            ast::Kind::PrivateIdentifier => self.check_private_identifier_expression(node),
            ast::Kind::ThisKeyword => self.check_this_expression(node),
            ast::Kind::SuperKeyword => self.check_super_expression(node),
            ast::Kind::NullKeyword => self.null_widening_type,
            ast::Kind::StringLiteral | ast::Kind::NoSubstitutionTemplateLiteral => {
                if self.is_skip_direct_inference_node(node) {
                    return self.blocked_string_type;
                }
                let lit = self.get_string_literal_type(&nodes[node].text(&nodes));
                self.get_fresh_type_of_literal_type(lit)
            }
            ast::Kind::NumericLiteral => {
                self.check_grammar_numeric_literal(node);
                let lit =
                    self.get_number_literal_type(tsc_jsnum::from_string(&nodes[node].text(&nodes)));
                self.get_fresh_type_of_literal_type(lit)
            }
            ast::Kind::BigIntLiteral => {
                self.check_grammar_big_int_literal(node);
                let lit = self.get_big_int_literal_type(tsc_jsnum::new_pseudo_big_int(
                    &tsc_jsnum::parse_pseudo_big_int(&nodes[node].text(&nodes)),
                    false, /*negative*/
                ));
                self.get_fresh_type_of_literal_type(lit)
            }
            ast::Kind::TrueKeyword => self.true_type,
            ast::Kind::FalseKeyword => self.false_type,
            ast::Kind::TemplateExpression => self.check_template_expression(node),
            ast::Kind::RegularExpressionLiteral => self.check_regular_expression_literal(node),
            ast::Kind::ArrayLiteralExpression => self.check_array_literal(node, check_mode),
            ast::Kind::ObjectLiteralExpression => self.check_object_literal(node, check_mode),
            ast::Kind::PropertyAccessExpression => {
                self.check_property_access_expression(node, check_mode, false /*writeOnly*/)
            }
            ast::Kind::QualifiedName => self.check_qualified_name(node, check_mode),
            ast::Kind::ElementAccessExpression => self.check_indexed_access(node, check_mode),
            ast::Kind::CallExpression => {
                if ast::is_import_call(&nodes[node], &nodes) {
                    return self.check_import_call_expression(node);
                }
                self.check_call_expression(node, check_mode)
            }
            ast::Kind::NewExpression => self.check_call_expression(node, check_mode),
            ast::Kind::TaggedTemplateExpression => self.check_tagged_template_expression(node),
            ast::Kind::ParenthesizedExpression => {
                self.check_parenthesized_expression(node, check_mode)
            }
            ast::Kind::ClassExpression => self.check_class_expression(node),
            ast::Kind::FunctionExpression | ast::Kind::ArrowFunction => {
                self.check_function_expression_or_object_literal_method(node, check_mode)
            }
            ast::Kind::TypeAssertionExpression | ast::Kind::AsExpression => {
                self.check_assertion(node, check_mode)
            }
            ast::Kind::TypeOfExpression => self.check_type_of_expression(node),
            ast::Kind::NonNullExpression => self.check_non_null_assertion(node),
            ast::Kind::ExpressionWithTypeArguments => {
                self.check_expression_with_type_arguments(node)
            }
            ast::Kind::SatisfiesExpression => self.check_satisfies_expression(node),
            ast::Kind::MetaProperty => self.check_meta_property(node),
            ast::Kind::DeleteExpression => self.check_delete_expression(node),
            ast::Kind::VoidExpression => self.check_void_expression(node),
            ast::Kind::AwaitExpression => self.check_await_expression(node),
            ast::Kind::PrefixUnaryExpression => self.check_prefix_unary_expression(node),
            ast::Kind::PostfixUnaryExpression => self.check_postfix_unary_expression(node),
            ast::Kind::BinaryExpression => self.check_binary_expression(node, check_mode),
            ast::Kind::ConditionalExpression => self.check_conditional_expression(node, check_mode),
            ast::Kind::SpreadElement => self.check_spread_expression(node, check_mode),
            ast::Kind::OmittedExpression => self.undefined_widening_type,
            ast::Kind::YieldExpression => self.check_yield_expression(node),
            ast::Kind::SyntheticExpression => self.check_synthetic_expression(node),
            ast::Kind::JsxExpression => self.check_jsx_expression(node, check_mode),
            ast::Kind::JsxElement => self.check_jsx_element(node, check_mode),
            ast::Kind::JsxSelfClosingElement => {
                self.check_jsx_self_closing_element(node, check_mode)
            }
            ast::Kind::JsxFragment => self.check_jsx_fragment(node),
            ast::Kind::JsxAttributes => self.check_jsx_attributes(node, check_mode),
            ast::Kind::JsxOpeningElement => {
                panic!("Should never directly check a JsxOpeningElement")
            }
            _ => self.error_type,
        }
    }

    /// `(c *Checker) checkPrivateIdentifierExpression` (checker.go).
    pub(crate) fn check_private_identifier_expression(&mut self, node: NodeId) -> TypeId {
        self.check_grammar_private_identifier_expression(node);
        let symbol = self.get_symbol_for_private_identifier_expression(node);
        if let Some(symbol) = symbol {
            self.mark_property_as_referenced(
                symbol, None,  /*nodeForCheckWriteOnly*/
                false, /*isSelfTypeAccess*/
            );
        }
        self.any_type
    }

    /// `(c *Checker) getSymbolForPrivateIdentifierExpression` (checker.go).
    pub(crate) fn get_symbol_for_private_identifier_expression(
        &mut self,
        node: NodeId,
    ) -> Option<SymbolId> {
        if self.symbol_node_links.get(node).resolved_symbol.is_none() {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            let text = nodes[node].text(&nodes).to_string();
            let symbol = self.lookup_symbol_for_private_identifier_declaration(&text, node);
            self.symbol_node_links.get(node).resolved_symbol = symbol;
        }
        self.symbol_node_links.get(node).resolved_symbol
    }

    /// `(c *Checker) checkSuperExpression` (checker.go).
    pub(crate) fn check_super_expression(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let is_call_expression = nodes[node].parent.is_some_and(|p| {
            ast::is_call_expression(&nodes[p]) && nodes[p].expression() == Some(node)
        });
        let immediate_container =
            ast::get_super_container(node, &nodes, true /*stopOnFunctions*/);
        let mut container = immediate_container;

        // adjust the container reference in case if super is used inside arrow functions with arbitrarily deep nesting
        if !is_call_expression {
            while let Some(c) = container {
                if !ast::is_arrow_function(&nodes[c]) {
                    break;
                }
                container = ast::get_super_container(c, &nodes, true /*stopOnFunctions*/);
            }
        }

        let is_legal_usage_of_super_expression = |container: Option<NodeId>| -> bool {
            let container = match container {
                Some(c) => c,
                None => return false,
            };
            if is_call_expression {
                // TS 1.0 SPEC (April 2014): 4.8.1
                // Super calls are only permitted in constructors of derived classes
                return ast::is_constructor_declaration(&nodes[container]);
            }
            // TS 1.0 SPEC (April 2014)
            // 'super' property access is allowed
            // - In a constructor, instance member function, instance member accessor, or instance member variable initializer where this references a derived class instance
            // - In a static member function or static member accessor

            // topmost container must be something that is directly nested in the class declaration\object literal expression
            let container_parent = nodes[container].parent;
            if ast::is_class_like(container_parent, &nodes)
                || container_parent.is_some_and(|p| ast::is_object_literal_expression(&nodes[p]))
            {
                if ast::is_static(&nodes[container]) {
                    return ast::node_kind_is(
                        &nodes[container],
                        &[
                            ast::Kind::MethodDeclaration,
                            ast::Kind::MethodSignature,
                            ast::Kind::GetAccessor,
                            ast::Kind::SetAccessor,
                            ast::Kind::PropertyDeclaration,
                            ast::Kind::ClassStaticBlockDeclaration,
                        ],
                    );
                }
                return ast::node_kind_is(
                    &nodes[container],
                    &[
                        ast::Kind::MethodDeclaration,
                        ast::Kind::MethodSignature,
                        ast::Kind::GetAccessor,
                        ast::Kind::SetAccessor,
                        ast::Kind::PropertyDeclaration,
                        ast::Kind::PropertySignature,
                        ast::Kind::Constructor,
                    ],
                );
            }
            false
        };

        if container.is_none() || !is_legal_usage_of_super_expression(container) {
            // issue more specific error if super is used in computed property name
            // class A { foo() { return "1" }}
            // class B {
            //     [super.foo()]() {}
            // }
            let current = ast::find_ancestor_or_quit(Some(node), &nodes, &mut |n, _ns| {
                if Some(n.id) == container {
                    return ast::FindAncestorResult::Quit;
                }
                if ast::is_computed_property_name(n) {
                    return ast::FindAncestorResult::True;
                }
                ast::FindAncestorResult::False
            });
            if let Some(current) = current {
                if ast::is_computed_property_name(&nodes[current]) {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::X_super_cannot_be_referenced_in_a_computed_property_name,
                        &[],
                    );
                    return self.error_type;
                }
            }
            if is_call_expression {
                self.error(
                    Some(node),
                    &tsc_diagnostics::Super_calls_are_not_permitted_outside_constructors_or_in_nested_functions_inside_constructors,
                    &[],
                );
            } else if container.is_none()
                || container.and_then(|c| nodes[c].parent).is_none()
                || !(container.and_then(|c| nodes[c].parent).is_some_and(|p| {
                    ast::is_class_like(Some(p), &nodes)
                        || ast::is_object_literal_expression(&nodes[p])
                }))
            {
                self.error(
                    Some(node),
                    &tsc_diagnostics::X_super_can_only_be_referenced_in_members_of_derived_classes_or_object_literal_expressions,
                    &[],
                );
            } else {
                self.error(
                    Some(node),
                    &tsc_diagnostics::X_super_property_access_is_permitted_only_in_a_constructor_member_function_or_member_accessor_of_a_derived_class,
                    &[],
                );
            }
            return self.error_type;
        }
        let container = container.unwrap();
        if !is_call_expression
            && immediate_container.is_some_and(|c| ast::is_constructor_declaration(&nodes[c]))
        {
            self.check_this_before_super(
                node,
                container,
                &tsc_diagnostics::X_super_must_be_called_before_accessing_a_property_of_super_in_the_constructor_of_a_derived_class,
            );
        }
        let container_parent = nodes[container].parent.expect("container parent");
        if nodes[container_parent].kind == ast::Kind::ObjectLiteralExpression {
            // for object literal assume that type of 'super' is 'any'
            return self.any_type;
        }
        // at this point the only legal case for parent is ClassLikeDeclaration
        let class_like_declaration = container_parent;
        if ast::get_class_extends_heritage_element(&nodes[class_like_declaration], &nodes).is_none()
        {
            self.error(
                Some(node),
                &tsc_diagnostics::X_super_can_only_be_referenced_in_a_derived_class,
                &[],
            );
            return self.error_type;
        }
        if self.class_declaration_extends_null(class_like_declaration) {
            if is_call_expression {
                return self.error_type;
            }
            return self.null_widening_type;
        }
        let __h13117_13 = self.get_symbol_of_declaration(class_like_declaration);

        let class_type = self.get_declared_type_of_symbol(__h13117_13.expect("class symbol"));
        let base_class_type = self.get_base_types(class_type).first().copied();
        let base_class_type = match base_class_type {
            Some(t) => t,
            None => return self.error_type,
        };
        if ast::is_constructor_declaration(&nodes[container])
            && self.is_in_constructor_argument_initializer(node, container)
        {
            // issue custom error message for super property access in constructor arguments (to be aligned with old compiler)
            self.error(
                Some(node),
                &tsc_diagnostics::X_super_cannot_be_referenced_in_constructor_arguments,
                &[],
            );
            return self.error_type;
        }
        if ast::is_static(&nodes[container]) || is_call_expression {
            if !is_call_expression
                && self.language_version <= tsc_core::options_generated::ScriptTarget::ES2021
                && (ast::is_property_declaration(&nodes[container])
                    || ast::is_class_static_block_declaration(&nodes[container]))
            {
                // for `super.x` or `super[x]` in a static initializer, mark all enclosing
                // block scope containers so that we can report potential collisions with
                // `Reflect`.
                let mut current =
                    ast::get_enclosing_block_scope_container(nodes[node].parent.unwrap(), &nodes);
                while let Some(c) = current {
                    if !ast::is_source_file(&nodes[c])
                        || ast::is_external_or_commonjs_module(nodes[c].as_source_file())
                    {
                        self.node_links.get(c).flags |=
                            NodeCheckFlags::CONTAINS_SUPER_PROPERTY_IN_STATIC_INITIALIZER;
                    }
                    current = ast::get_enclosing_block_scope_container(c, &nodes);
                }
            }
            return self.get_base_constructor_type_of_class(class_type);
        }
        let __arena___guard_this_type = self.types.clone();
        let __guard_this_type = __arena___guard_this_type.get(class_type).clone();
        let this_type = __guard_this_type
            .as_interface_type()
            .and_then(|i| i.this_type);
        self.get_type_with_this_argument(base_class_type, this_type, false)
    }

    /// `(c *Checker) isInConstructorArgumentInitializer` (checker.go).
    pub(crate) fn is_in_constructor_argument_initializer(
        &mut self,
        node: NodeId,
        constructor_decl: NodeId,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        ast::find_ancestor_or_quit(Some(node), &nodes, &mut |n, ns| {
            if ast::is_function_like_declaration(Some(n.id), ns) {
                return ast::FindAncestorResult::Quit;
            }
            if ast::is_parameter_declaration(n) && n.parent == Some(constructor_decl) {
                return ast::FindAncestorResult::True;
            }
            ast::FindAncestorResult::False
        })
        .is_some()
    }

    /// `(c *Checker) checkTemplateExpression` (checker.go).
    pub(crate) fn check_template_expression(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let template = nodes[node].as_template_expression();
        let spans: Vec<NodeId> = template
            .template_spans
            .as_ref()
            .map(|l| l.nodes.to_vec())
            .unwrap_or_default();
        let head = template.head.expect("template head");
        let length = spans.len();
        let mut texts: Vec<String> = vec![String::new(); length + 1];
        let mut types: Vec<TypeId> = vec![self.error_type; length];
        texts[0] = nodes[head].text(&nodes).to_string();
        for (i, span) in spans.iter().copied().enumerate() {
            let span_expr = nodes[span].expression().expect("span expression");
            let t = self.check_expression(span_expr);
            if self.maybe_type_of_kind_considering_base_constraint(t, TypeFlags::ES_SYMBOL_LIKE) {
                self.error(
                    Some(span_expr),
                    &tsc_diagnostics::Implicit_conversion_of_a_symbol_to_a_string_will_fail_at_runtime_Consider_wrapping_this_expression_in_String,
                    &[],
                );
            }
            if let Some(literal) = nodes[span].as_template_span().literal {
                texts[i + 1] = nodes[literal].text(&nodes).to_string();
            }
            types[i] = tsc_core::core::if_else(
                self.is_type_assignable_to(t, self.template_constraint_type),
                t,
                self.string_type,
            );
        }
        let mut evaluated: Option<tsc_evaluator::Value> = None;
        if !nodes[node]
            .parent
            .is_some_and(|p| ast::is_tagged_template_expression(&nodes[p]))
        {
            evaluated = self.evaluate_call(node, Some(node), &nodes).value;
        }
        if let Some(tsc_evaluator::Value::String(s)) = evaluated {
            let __h13224_56 = self.get_string_literal_type(&s);

            return self.get_fresh_type_of_literal_type(__h13224_56);
        }
        let __h13230_17 = self.get_contextual_type(node, ContextFlags::NONE);

        if self.is_const_context(node)
            || self.is_template_literal_context(node)
            || crate::checker_d::some_type(
                self,
                __h13230_17.unwrap_or(self.unknown_type),
                |c: &mut Checker, t: TypeId| c.is_template_literal_contextual_type(t),
            )
        {
            return self.get_template_literal_type(&texts, &types);
        }
        self.string_type
    }
}

/// `hasTypeParameterByName` (checker.go) — free function.
fn has_type_parameter_by_name(c: &Checker, type_parameters: &[TypeId], name: &str) -> bool {
    type_parameters.iter().any(|&tp| {
        c.types_handle()
            .get(tp)
            .symbol()
            .is_some_and(|s| sym_name(c, s) == name)
    })
}

/// `getUniqueTypeParameterName` (checker.go) — free function.
fn get_unique_type_parameter_name(
    c: &Checker,
    type_parameters: &[TypeId],
    base_name: &str,
) -> String {
    let mut base_name = base_name.to_string();
    while base_name.len() > 1
        && base_name
            .chars()
            .last()
            .is_some_and(|ch| ch.is_ascii_digit())
    {
        base_name.pop();
    }
    let mut index = 1;
    loop {
        let augmented_name = format!("{}{}", base_name, index);
        if !has_type_parameter_by_name(c, type_parameters, &augmented_name) {
            return augmented_name;
        }
        index += 1;
    }
}

// === CONTINUE ===
