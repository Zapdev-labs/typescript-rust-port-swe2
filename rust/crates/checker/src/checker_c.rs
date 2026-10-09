// Ported from tsc/internal/checker/checker.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — lines 16295..=24557
// (`getSuggestedSymbolForNonexistentModule` through `computeConstantEnumMemberValue`,
// the function preceding `evaluateEntity`).
//
// Scope of this file (per the checker.go ownership map):
//   - Symbol/module export resolution: getExportsOfSymbol,
//     getResolvedMembersOrExportsOfSymbol, late binding (lateBindMember,
//     lateBindIndexSignature, addDeclarationToLateBoundSymbol),
//     getExportsOfModule(+Worker), extendExportSymbols, alias resolution
//     (ResolveAlias/resolveAlias/resolveIndirectionAlias/tryResolveAlias/
//     resolveAliasWithDeprecationCheck), getSymbolFlags(Ex),
//     getDeclarationOfAliasSymbol.
//   - The getTypeOfSymbol family and the variable/parameter/property type
//     resolution workers it drives, including binding-pattern padding,
//     assignment-declaration widening and the WideningContext machinery.
//   - Constraints (getConstraintOfType*, getInferredTypeParameterConstraint),
//     the remaining `keyBuilder`/`get*Key` hash helpers not already ported in
//     checker_types.rs, and type-resolution stack bookkeeping.
//   - Property/signature/index-info materialization:
//     getProperty(ies)OfType, resolveStructuredTypeMembers and the
//     class/interface/object/union/intersection/mapped resolvers,
//     signature instantiation, getTypeWithThisArgument, apparent/reduced
//     types.
//   - Type instantiation: instantiateType(WithAlias), instantiateTypeWorker,
//     getObjectTypeInstantiation, conditional/mapped/reverse-mapped
//     instantiation, instantiateSymbols/Signatures/IndexInfos/List.
//   - getTypeFromTypeNode and friends (type references, aliases, tuple
//     normalization) plus the declared-type getters and enum member value
//     computation ending just before evaluateEntity.
//
// PORT notes:
// - `*ast.Node` → `NodeId`/`Option<NodeId>`; node payload access goes through
//   `self.program_nodes(id)` (the per-file `Vec<ast::Node>` arena).
// - `*ast.Symbol` → `SymbolId`; fields read/mutated through
//   `self.symbol_arena.borrow()[s.index()]` / `borrow_mut()`.
// - `*Type` → `TypeId`; `self.types.get(t)` / `get_mut(t)` guards.
//   `*Signature` → `SignatureId` (`self.signature_arena`),
//   `*IndexInfo` → `IndexInfoId` (`self.index_info_arena`),
//   `*TypeMapper` → `TypeMapperId` (`self.type_mappers`),
//   `*InferenceContext` → `InferenceContextId` (`self.inference_contexts`).
// - `ast.SymbolTable` → `tsc_ast::SymbolTable` (insertion-ordered). Go's
//   `nil` symbol-table sentinel on the members/exports links is represented
//   by an empty `SymbolTable`; the resolution functions are idempotent so an
//   empty-but-resolved table recomputes to itself — noted where it matters.
// - Method calls on sibling-owned ranges (`checker_a.rs`, `checker_b.rs`,
//   `checker_d.rs`, `relater.rs`, `flow.rs`, `inference.rs`,
//   `utilities.rs`, `jsx.go` owner, etc.) are invoked as
//   `self.<snake_case>(...)` / `crate::<module>::<snake_case>(...)` and are
//   expected `E0599`/`unresolved` until those files land — see the report.

use std::cell::{Ref, RefCell, RefMut};
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, HasFileName, NodeId, SymbolId, SymbolTable};
use tsc_collections::{OrderedMap, OrderedSet, Set};
use tsc_core::core as core;
use tsc_core::options_generated::{ModuleKind, ModuleResolutionKind, ScriptTarget};
use tsc_core::tristate::Tristate;
use tsc_evaluator as evaluator;
use tsc_jsnum::PseudoBigInt;

use crate::checker_core::{
    CacheHashKey, CheckMode, Checker, InferenceContextId, InferenceFlags, InferencePriority,
    WideningKind, is_tuple_type,
};
use crate::checker_types::{
    self, ExportCollision, ExportCollisionTable, InheritanceInfo, IterationTypeKind,
    ThisAssignmentDeclarationKind, TupleNormalizer, TypeResolution, TypeSystemEntity,
    TypeSystemPropertyName, WideningContext, get_alias_key, get_indexed_access_key,
    get_intersection_key, get_template_type_key, get_tuple_key, get_type_alias_instantiation_key,
    get_type_instantiation_key, get_type_list_key, get_union_key,
    is_non_deferred_type_reference, is_type_reference_with_generic_arguments,
};
use crate::mapper::{
    TypeMapperData, TypeMapperId, TypeMapperKind, append_type_mapping, get_mapped_type,
    merge_type_mappers, new_array_type_mapper, new_composite_type_mapper,
    new_deferred_type_mapper, new_function_type_mapper, new_merged_type_mapper,
    new_simple_type_mapper, new_type_mapper, prepend_type_mapping,
};
use crate::relater::RelationComparisonResult;
use crate::types::{
    AccessFlags, ConditionalRoot, ConditionalType, ElementFlags, IndexFlags, IndexInfo,
    IndexInfoId, InterfaceType, IntersectionFlags, IntersectionType, MappedType,
    MembersOrExportsResolutionKind, NodeCheckFlags, ObjectFlags, Signature, SignatureFlags,
    SignatureId, SignatureKind, StructuredType, TupleElementInfo, TupleType, Type, TypeAlias,
    TypeData, TypeFlags, TypeId, TypeParameter, TypePredicate, TypePredicateKind, UnionType,
};

impl Checker {
    // PORT: symbol arena accessors — `symbol.Field` reads/writes in Go.
    // `pub(crate)` so sibling checker files can share the idiom.
    /// `symbol.Field` — short read borrow of the symbol arena.
    #[inline]
    pub(crate) fn sym(&self, s: SymbolId) -> Ref<'_, ast::Symbol> {
        Ref::map(self.symbol_arena.borrow(), |a| &a[s.index()])
    }

    /// `symbol.Field = v` — short write borrow of the symbol arena.
    #[inline]
    pub(crate) fn sym_mut(&self, s: SymbolId) -> RefMut<'_, ast::Symbol> {
        RefMut::map(self.symbol_arena.borrow_mut(), |a| &mut a[s.index()])
    }

    /// `(k CacheHashKey) IsZero` (checker.go) — `impl` on the `ast::Uint128`
    /// alias is not allowed (foreign type), so it is a crate-private helper.

    /// `(c *Checker) getSuggestedSymbolForNonexistentModule` (checker.go).
    pub(crate) fn get_suggested_symbol_for_nonexistent_module(
        &mut self,
        name: NodeId,
        target_module: SymbolId,
    ) -> Option<SymbolId> {
        let nodes = self.program_nodes(name);
        let name_text = nodes[name].text(&nodes).into_owned();
        let exports = self.get_exports_of_module(target_module);
        let candidates: Vec<SymbolId> = exports.values().copied().collect();
        self.get_spelling_suggestion_for_name(
            &name_text,
            candidates,
            ast::SymbolFlags::MODULE_MEMBER,
        )
    }

    /// `(c *Checker) getFullyQualifiedName` (checker.go).
    pub(crate) fn get_fully_qualified_name(
        &mut self,
        symbol: SymbolId,
        containing_location: Option<NodeId>,
    ) -> String {
        if let Some(parent) = self.sym(symbol).parent {
            return format!(
                "{}.{}",
                self.get_fully_qualified_name(parent, containing_location),
                self.symbol_to_string(symbol)
            );
        }
        self.symbol_to_string_ex(
            symbol,
            containing_location,
            ast::SymbolFlags::ALL,
            crate::types::SymbolFormatFlags::DO_NOT_INCLUDE_SYMBOL_CHAIN
                | crate::types::SymbolFormatFlags::ALLOW_ANY_NODE_KIND,
        )
    }

    /// `(c *Checker) getExportsOfSymbol` (checker.go).
    pub(crate) fn get_exports_of_symbol(&mut self, symbol: SymbolId) -> SymbolTable {
        let flags = self.sym(symbol).flags;
        if flags.intersects(ast::SymbolFlags::LATE_BINDING_CONTAINER) {
            return self.get_resolved_members_or_exports_of_symbol(
                symbol,
                MembersOrExportsResolutionKind::ResolvedExports,
            );
        }
        if flags.intersects(ast::SymbolFlags::MODULE) {
            return self.get_exports_of_module(symbol);
        }
        self.sym(symbol).exports.clone()
    }

    /// `(c *Checker) getResolvedMembersOrExportsOfSymbol` (checker.go).
    ///
    /// PORT: Go keys `links[resolutionKind]` nil-ness; here an empty
    /// `SymbolTable` doubles as the uncomputed sentinel. The resolution is
    /// idempotent for the empty case (an empty result could not have
    /// populated late-bound members or reported diagnostics), so recompute
    /// produces the same table.
    pub(crate) fn get_resolved_members_or_exports_of_symbol(
        &mut self,
        symbol: SymbolId,
        resolution_kind: MembersOrExportsResolutionKind,
    ) -> SymbolTable {
        let kind_index = resolution_kind as usize;
        if self.members_and_exports_links.get(symbol).0[kind_index].is_empty() {
            let is_static = resolution_kind == MembersOrExportsResolutionKind::ResolvedExports;
            let flags = self.sym(symbol).flags;
            let mut early_symbols = if !is_static {
                self.sym(symbol).members.clone()
            } else if flags.intersects(ast::SymbolFlags::MODULE) {
                let (exports, _) = self.get_exports_of_module_worker(symbol);
                exports
            } else {
                self.sym(symbol).exports.clone()
            };
            self.members_and_exports_links.get(symbol).0[kind_index] = early_symbols.clone();
            // fill in any as-yet-unresolved late-bound members.
            let mut late_symbols: SymbolTable = SymbolTable::new();
            let declarations = self.sym(symbol).declarations.clone();
            for decl in declarations {
                let nodes = self.program_nodes(decl);
                for member in crate::utilities::get_members_of_declaration(&nodes[decl]) {
                    if is_static == ast::has_static_modifier(&nodes[member]) {
                        if self.has_late_bindable_name(member) {
                            self.late_bind_member(
                                symbol,
                                &early_symbols,
                                &mut late_symbols,
                                member,
                            );
                        } else if self.has_late_bindable_index_signature(member) {
                            self.late_bind_index_signature(
                                symbol,
                                &early_symbols,
                                &mut late_symbols,
                                member,
                            );
                        }
                    }
                }
            }
            if is_static {
                let assignment_symbol = self
                    .sym(symbol)
                    .exports
                    .get(ast::INTERNAL_SYMBOL_NAME_ASSIGNMENT_DECLARATION)
                    .copied();
                if let Some(assignment_symbol) = assignment_symbol {
                    let members = self.sym(assignment_symbol).declarations.clone();
                    for member in members {
                        if self.has_late_bindable_name(member) {
                            self.late_bind_member(
                                symbol,
                                &early_symbols,
                                &mut late_symbols,
                                member,
                            );
                        }
                    }
                }
            }
            let combined = self.combine_symbol_tables(
                std::mem::take(&mut early_symbols),
                std::mem::take(&mut late_symbols),
            );
            self.members_and_exports_links.get(symbol).0[kind_index] = combined;
        }
        self.members_and_exports_links.get(symbol).0[kind_index].clone()
    }

    /// `(c *Checker) lateBindMember` (checker.go) — performs the same function
    /// for late-bound members that `declareSymbol` in binder.ts performs for
    /// early-bound members. `earlySymbols` is read-only, `lateSymbols` gains
    /// entries.
    pub(crate) fn late_bind_member(
        &mut self,
        parent: SymbolId,
        early_symbols: &SymbolTable,
        late_symbols: &mut SymbolTable,
        decl: NodeId,
    ) -> Option<SymbolId> {
        let nodes = self.program_nodes(decl);
        debug_assert!(
            nodes[decl].symbol().is_some(),
            "The member is expected to have a symbol."
        );
        if self.symbol_node_links.get(decl).resolved_symbol.is_none() {
            // In the event we attempt to resolve the late-bound name of this
            // member recursively, fall back to the early-bound name of this
            // member.
            self.symbol_node_links.get(decl).resolved_symbol = nodes[decl].symbol();
            let decl_name = if ast::is_binary_expression(&nodes[decl]) {
                Some(nodes[decl].as_binary_expression().left)
            } else {
                nodes[decl].name()
            };
            let t = if let Some(dn) = decl_name
                && ast::is_element_access_expression(&nodes[dn])
            {
                let argument_expression =
                    nodes[dn].as_element_access_expression().argument_expression;
                self.check_expression_cached(argument_expression)
            } else {
                self.check_computed_property_name(decl_name.expect("declName"))
            };
            if crate::utilities::is_type_usable_as_property_name(&self.types, t) {
                let member_name =
                    crate::utilities::get_property_name_from_type(&self.types, t);
                let symbol_flags = self.sym(nodes[decl].symbol().unwrap()).flags;
                // Get or add a late-bound symbol for the member. This allows
                // us to merge late-bound accessor declarations.
                let mut late_symbol = match late_symbols.get(&member_name).copied() {
                    Some(s) => s,
                    None => {
                        let s = self.new_symbol_ex(
                            ast::SymbolFlags::NONE,
                            &member_name,
                            ast::checkflags::CheckFlags::LATE,
                        );
                        late_symbols.set(member_name.clone(), s);
                        s
                    }
                };
                // Report an error if there's a symbol declaration with the
                // same name and conflicting flags.
                let early_symbol = early_symbols.get(&member_name).copied();
                if self
                    .sym(late_symbol)
                    .flags
                    .intersects(crate::checker_b::get_excluded_symbol_flags(symbol_flags))
                {
                    // If we have an existing early-bound member, combine its
                    // declarations so that we can report an error at each
                    // declaration.
                    let declarations = if let Some(early_symbol) = early_symbol {
                        let mut d = self.sym(early_symbol).declarations.clone();
                        d.extend(self.sym(late_symbol).declarations.iter().copied());
                        d
                    } else {
                        self.sym(late_symbol).declarations.clone()
                    };
                    let mut name = member_name.clone();
                    if self
                        .types
                        .get(t)
                        .flags
                        .intersects(TypeFlags::UNIQUE_ES_SYMBOL)
                    {
                        name = tsc_scanner::utilities::declaration_name_to_string(
                            decl_name, &nodes,
                        );
                    }
                    for d in declarations {
                        self.error(
                            ast::get_name_of_declaration(Some(d), &nodes).or(Some(d)),
                            &tsc_diagnostics::Duplicate_identifier_0,
                            &[name.clone()],
                        );
                    }
                    self.error(
                        decl_name.or(Some(decl)),
                        &tsc_diagnostics::Duplicate_identifier_0,
                        &[name],
                    );
                    let late_flags = self.sym(late_symbol).flags;
                    if late_flags.intersects(ast::SymbolFlags::ACCESSOR)
                        && late_flags & ast::SymbolFlags::ACCESSOR
                            != symbol_flags & ast::SymbolFlags::ACCESSOR
                    {
                        self.sym_mut(late_symbol)
                            .flags
                            .insert(ast::SymbolFlags::ACCESSOR);
                    }
                    late_symbol = self.new_symbol_ex(
                        ast::SymbolFlags::NONE,
                        &member_name,
                        ast::checkflags::CheckFlags::LATE,
                    );
                }
                self.value_symbol_links.get(late_symbol).name_type = Some(t);
                self.add_declaration_to_late_bound_symbol(late_symbol, decl, symbol_flags);
                if self.sym(late_symbol).parent.is_none() {
                    self.sym_mut(late_symbol).parent = Some(parent);
                }
                self.symbol_node_links.get(decl).resolved_symbol = Some(late_symbol);
            }
        }
        self.symbol_node_links.get(decl).resolved_symbol
    }

    /// `(c *Checker) lateBindIndexSignature` (checker.go).
    pub(crate) fn late_bind_index_signature(
        &mut self,
        parent: SymbolId,
        early_symbols: &SymbolTable,
        late_symbols: &mut SymbolTable,
        decl: NodeId,
    ) {
        // First, late bind the index symbol itself, if needed
        let index_symbol = match late_symbols.get(ast::INTERNAL_SYMBOL_NAME_INDEX).copied() {
            Some(s) => s,
            None => {
                let early = early_symbols.get(ast::INTERNAL_SYMBOL_NAME_INDEX).copied();
                let index_symbol = match early {
                    None => self.new_symbol_ex(
                        ast::SymbolFlags::NONE,
                        ast::INTERNAL_SYMBOL_NAME_INDEX,
                        ast::checkflags::CheckFlags::LATE,
                    ),
                    Some(early) => {
                        let index_symbol = self.clone_symbol(early);
                        self.sym_mut(index_symbol)
                            .check_flags
                            .insert(ast::checkflags::CheckFlags::LATE);
                        index_symbol
                    }
                };
                late_symbols.set(ast::INTERNAL_SYMBOL_NAME_INDEX.to_string(), index_symbol);
                index_symbol
            }
        };
        // Then just add the computed name as a late bound declaration
        // (note: unlike `addDeclarationToLateBoundSymbol` we do not set up a
        // `.lateSymbol` on `decl`'s links, since that would point at an index
        // symbol and not a single property symbol, like most consumers would
        // expect)
        let nodes = self.program_nodes(decl);
        let decl_symbol_flags = self.sym(nodes[decl].symbol().unwrap()).flags;
        if self.sym(index_symbol).declarations.is_empty()
            || !decl_symbol_flags.intersects(ast::SymbolFlags::REPLACEABLE_BY_METHOD)
        {
            self.sym_mut(index_symbol).declarations.push(decl);
        }
        let _ = parent;
    }

    /// `(c *Checker) addDeclarationToLateBoundSymbol` (checker.go) — performs
    /// the same function for late-bound members that `addDeclarationToSymbol`
    /// in binder.ts performs for early-bound members.
    pub(crate) fn add_declaration_to_late_bound_symbol(
        &mut self,
        symbol: SymbolId,
        member: NodeId,
        symbol_flags: ast::SymbolFlags,
    ) {
        debug_assert!(
            self.sym(symbol)
                .check_flags
                .intersects(ast::checkflags::CheckFlags::LATE),
            "Expected a late-bound symbol."
        );
        let nodes = self.program_nodes(member);
        let member_symbol = nodes[member].symbol().unwrap();
        self.late_bound_links.get(member_symbol).late_symbol = Some(symbol);
        if self.sym(symbol).declarations.is_empty()
            || !self
                .sym(member_symbol)
                .flags
                .intersects(ast::SymbolFlags::REPLACEABLE_BY_METHOD)
        {
            self.sym_mut(symbol).flags.insert(symbol_flags);
            self.sym_mut(symbol).declarations.push(member);
        } else if self
            .sym(symbol)
            .flags
            .intersects(ast::SymbolFlags::REPLACEABLE_BY_METHOD)
            && self
                .sym(member_symbol)
                .flags
                .intersects(ast::SymbolFlags::METHOD)
        {
            // Remove all replacable-by-method members, along with their flags.
            let mut declarations: Vec<NodeId> = self
                .sym(symbol)
                .declarations
                .iter()
                .copied()
                .filter(|&d| is_not_replacable_by_method(self, d))
                .collect();
            declarations.push(member);
            let old_flags = self.sym(symbol).flags;
            self.sym_mut(symbol).declarations = declarations;
            self.sym_mut(symbol).flags = ast::SymbolFlags::TRANSIENT;
            let decls = self.sym(symbol).declarations.clone();
            for d in decls {
                let d_nodes = self.program_nodes(d);
                let d_flags = self.sym(d_nodes[d].symbol().unwrap()).flags;
                self.sym_mut(symbol).flags.insert(d_flags);
            }
            if old_flags.intersects(ast::SymbolFlags::ACCESSOR) {
                self.sym_mut(symbol)
                    .flags
                    .insert(ast::SymbolFlags::ACCESSOR);
            }
        }
        if symbol_flags.intersects(ast::SymbolFlags::VALUE) {
            let nodes = self.program_nodes(member);
            tsc_binder::set_value_declaration(
                &mut self.symbol_arena.borrow_mut(),
                symbol,
                member,
                &nodes,
            );
        }
    }

    /// `(c *Checker) getMembersOfSymbol` (checker.go) — gets a SymbolTable
    /// containing both the early- and late-bound members of a symbol.
    pub(crate) fn get_members_of_symbol(&mut self, symbol: SymbolId) -> SymbolTable {
        if self
            .sym(symbol)
            .flags
            .intersects(ast::SymbolFlags::LATE_BINDING_CONTAINER)
        {
            return self.get_resolved_members_or_exports_of_symbol(
                symbol,
                MembersOrExportsResolutionKind::ResolvedMembers,
            );
        }
        self.sym(symbol).members.clone()
    }

    /// `(c *Checker) getExportsOfModule` (checker.go).
    ///
    /// PORT: `resolvedExports == nil` → empty-table sentinel (see
    /// `get_resolved_members_or_exports_of_symbol`). A computed-but-empty
    /// result recomputes; `getExportsOfModuleWorker` is side-effect free on
    /// diagnostics when its result is empty.
    pub(crate) fn get_exports_of_module(&mut self, module_symbol: SymbolId) -> SymbolTable {
        if self
            .module_symbol_links
            .get(module_symbol)
            .resolved_exports
            .is_empty()
        {
            let (exports, type_only_export_star_map) =
                self.get_exports_of_module_worker(module_symbol);
            let links = self.module_symbol_links.get(module_symbol);
            links.resolved_exports = exports;
            links.type_only_export_star_map = type_only_export_star_map;
        }
        self.module_symbol_links
            .get(module_symbol)
            .resolved_exports
            .clone()
    }

    /// `(c *Checker) getExportsOfModuleWorker` (checker.go).
    ///
    /// PORT: `map[string]*ast.Node` → `SymbolTable` storing
    /// `SymbolId(node.0 as u32)` re-punned NodeIds — the
    /// `ModuleSymbolLinks.typeOnlyExportStarMap` field is declared
    /// `tsc_ast::SymbolTable` (see types.rs PORT note); readers must decode
    /// with `NodeId(v.0 as u64)`.
    pub(crate) fn get_exports_of_module_worker(
        &mut self,
        module_symbol: SymbolId,
    ) -> (SymbolTable, SymbolTable) {
        let mut visited_symbols: Vec<SymbolId> = Vec::new();
        let mut non_type_only_names: Set<String> =
            Set::with_size_hint(self.sym(module_symbol).exports.size());
        // The ES6 spec permits export * declarations in a module to circularly
        // reference the module itself.
        let mut type_only_export_star_map: SymbolTable = SymbolTable::new();
        #[allow(clippy::too_many_arguments)]
        fn visit(
            c: &mut Checker,
            visited_symbols: &mut Vec<SymbolId>,
            non_type_only_names: &mut Set<String>,
            type_only_export_star_map: &mut SymbolTable,
            symbol: Option<SymbolId>,
            export_star: Option<NodeId>,
            is_type_only: bool,
        ) -> Option<SymbolTable> {
            if !is_type_only
                && let Some(symbol) = symbol
            {
                // Add non-type-only names before checking if we've visited
                // this module, because we might have visited it via an
                // 'export type *', and visiting again with 'export *' will
                // override the type-onlyness of its exports.
                for name in c.sym(symbol).exports.keys() {
                    non_type_only_names.add(name.clone());
                }
            }
            let Some(symbol) = symbol else {
                return None;
            };
            if visited_symbols.contains(&symbol) {
                return None;
            }
            visited_symbols.push(symbol);
            let mut symbols = c.sym(symbol).exports.clone();
            // All export * declarations are collected in an __export symbol
            // by the binder
            let export_stars = c
                .sym(symbol)
                .exports
                .get(ast::INTERNAL_SYMBOL_NAME_EXPORT_STAR)
                .copied();
            if let Some(export_stars) = export_stars {
                let mut nested_symbols = SymbolTable::new();
                let mut lookup_table = ExportCollisionTable::default();
                let star_declarations = c.sym(export_stars).declarations.clone();
                for node in star_declarations {
                    let nodes = c.program_nodes(node);
                    let module_specifier = nodes[node].module_specifier();
                    let attributes_type = c.get_type_from_import_attributes(
                        ast::get_import_attributes(&nodes[node]),
                    );
                    let resolved_module = c.resolve_external_module_name(
                        node,
                        module_specifier,
                        false, /*ignoreErrors*/
                        attributes_type,
                    );
                    let exported_symbols = visit(
                        c,
                        visited_symbols,
                        non_type_only_names,
                        type_only_export_star_map,
                        resolved_module,
                        Some(node),
                        is_type_only || nodes[node].is_type_only(),
                    );
                    c.extend_export_symbols(
                        &mut nested_symbols,
                        exported_symbols.as_ref(),
                        Some(&mut lookup_table),
                        Some(node),
                    );
                }
                for (id, s) in lookup_table.iter() {
                    // It's not an error if the file with multiple `export *`s
                    // with duplicate names exports a member with that name
                    // itself
                    if id == ast::INTERNAL_SYMBOL_NAME_EXPORT_STAR
                        || s.exports_with_duplicate.is_empty()
                        || symbols.get(id).is_some()
                    {
                        continue;
                    }
                    for &node in &s.exports_with_duplicate {
                        let diagnostic = crate::checker_b::create_diagnostic_for_node(
                            Some(node),
                            &c.program_nodes(node),
                            &tsc_diagnostics::Module_0_has_already_exported_a_member_named_1_Consider_explicitly_re_exporting_to_resolve_the_ambiguity,
                            &[s.specifier_text.clone(), id.clone()],
                        );
                        c.add_diagnostic(&diagnostic);
                    }
                }
                c.extend_export_symbols(&mut symbols, Some(&nested_symbols), None, None);
            }
            if let Some(export_star) = export_star {
                let nodes = c.program_nodes(export_star);
                if nodes[export_star].is_type_only() {
                    for name in symbols.keys() {
                        type_only_export_star_map
                            .set(name.clone(), SymbolId(export_star.0 as u32));
                    }
                }
            }
            Some(symbols)
        }
        let mut original_module: Option<SymbolId> = None;
        let export_equals = self
            .sym(module_symbol)
            .exports
            .get(ast::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
            .copied();
        // Go: `c.resolveSymbolEx(moduleSymbol.Exports[ExportEquals], false) !=
        // nil` — `resolveSymbolEx` returns a non-NONE id for any non-NONE
        // input, so the Option guard carries the nil check.
        if let Some(export_equals) = export_equals {
            self.resolve_symbol_ex(export_equals, false /*dontResolveAlias*/);
            original_module = Some(module_symbol);
        }
        // A module defined by an 'export=' consists of one export that needs
        // to be resolved
        let module_symbol = self.resolve_external_module_symbol(module_symbol, false);
        let mut exports =
            visit(self, &mut visited_symbols, &mut non_type_only_names, &mut type_only_export_star_map, module_symbol, None, false)
                .unwrap_or_default();
        // A CommonJS module defined by an 'export=' might also export
        // typedefs, stored on the original module
        if let Some(original_module) = original_module
            && self.sym(original_module).exports.size() > 1
        {
            let original_exports = self.sym(original_module).exports.clone();
            for symbol in original_exports.values().copied() {
                let name = self.sym(symbol).name.clone();
                if name == ast::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
                    || name == ast::INTERNAL_SYMBOL_NAME_EXPORT_STAR
                {
                    continue;
                }
                let flags = self.get_symbol_flags(symbol);
                if flags.intersects(ast::SymbolFlags::TYPE | ast::SymbolFlags::NAMESPACE)
                    && !flags.intersects(ast::SymbolFlags::VALUE)
                    && exports.get(&name).is_none()
                {
                    exports.set(name, symbol);
                }
            }
        }
        for name in non_type_only_names.keys() {
            type_only_export_star_map.delete(name);
        }
        (exports, type_only_export_star_map)
    }

    /// `(c *Checker) extendExportSymbols` (checker.go) — extends one symbol
    /// table with another while collecting name-collision information into
    /// `lookupTable` for error message generation. Not passing `lookupTable`
    /// and `exportNode` disables collection.
    pub(crate) fn extend_export_symbols(
        &mut self,
        target: &mut SymbolTable,
        source: Option<&SymbolTable>,
        mut lookup_table: Option<&mut ExportCollisionTable>,
        export_node: Option<NodeId>,
    ) {
        let Some(source) = source else {
            return;
        };
        let collect = lookup_table.is_some() && export_node.is_some();
        let specifier_text = if collect {
            let nodes = self.program_nodes(export_node.unwrap());
            nodes[export_node.unwrap()]
                .module_specifier()
                .map(|ms| tsc_scanner::utilities::get_text_of_node(ms, &nodes))
        } else {
            None
        };
        let source: Vec<(String, SymbolId)> = source
            .entries()
            .map(|(k, &v)| (k.clone(), v))
            .collect();
        for (id, source_symbol) in source {
            if id == ast::INTERNAL_SYMBOL_NAME_DEFAULT {
                continue;
            }
            let target_symbol = target.get(&id).copied();
            if target_symbol.is_none() {
                target.set(id.clone(), source_symbol);
                if let (Some(table), Some(text)) = (lookup_table.as_deref_mut(), &specifier_text) {
                    table.insert(
                        id,
                        ExportCollision {
                            specifier_text: text.clone(),
                            exports_with_duplicate: Vec::new(),
                        },
                    );
                }
            } else if let Some(table) = lookup_table.as_deref_mut()
                && let Some(export_node) = export_node
            {
                let resolved_target = self.resolve_symbol(target_symbol.unwrap());
                let resolved_source = self.resolve_symbol(source_symbol);
                if resolved_target != resolved_source {
                    let s = table.get_mut(&id);
                    if let Some(s) = s {
                        s.exports_with_duplicate.push(export_node);
                    }
                }
            }
        }
    }

    /// `(c *Checker) ResolveAlias` (checker.go) — exported.
    pub fn resolve_alias_public(&mut self, symbol: Option<SymbolId>) -> (Option<SymbolId>, bool) {
        let Some(symbol) = symbol else {
            return (None, false);
        };
        let resolved = self.resolve_alias(symbol);
        (Some(resolved), resolved != self.unknown_symbol)
    }

    /// `(c *Checker) resolveAlias` (checker.go) — resolves an alias symbol to
    /// the first target symbol in the resolution chain that includes some
    /// other meaning. Panics if the argument is not a symbol with an alias
    /// meaning, mirroring Go.
    pub(crate) fn resolve_alias(&mut self, symbol: SymbolId) -> SymbolId {
        if !self
            .sym(symbol)
            .flags
            .intersects(ast::SymbolFlags::ALIAS)
        {
            panic!("Should only get alias here")
        }
        if self
            .alias_symbol_links
            .get(symbol)
            .alias_target
            .is_none()
        {
            if !self.push_type_resolution(
                TypeSystemEntity::Symbol(symbol),
                TypeSystemPropertyName::AliasTarget,
            ) {
                return self.unknown_symbol;
            }
            let node = match self.get_declaration_of_alias_symbol(symbol) {
                Some(node) => node,
                None => panic!(
                    "Unexpected nil in resolveAlias for symbol: {}",
                    self.symbol_to_string(symbol)
                ),
            };
            let mut target = self.get_target_of_alias_declaration(node);
            let is_non_local = {
                let arena = self.symbol_arena.borrow();
                ast::is_non_local_alias(
                    target.map(|t| &arena[t.index()]),
                    ast::SymbolFlags::VALUE
                        | ast::SymbolFlags::TYPE
                        | ast::SymbolFlags::NAMESPACE,
                )
            };
            if is_non_local {
                // When the target is a pure alias, we transitively resolve and
                // propagate any typeOnlyDeclaration
                target = Some(self.resolve_indirection_alias(symbol, target.unwrap()));
            }
            self.alias_symbol_links.get(symbol).alias_target =
                Some(target.unwrap_or(self.unknown_symbol));
            if !self.pop_type_resolution() {
                let arg = self.symbol_to_string(symbol);
                self.error(
                    Some(node),
                    &tsc_diagnostics::Circular_definition_of_import_alias_0,
                    &[arg],
                );
                self.alias_symbol_links.get(symbol).alias_target = Some(self.unknown_symbol);
            }
        }
        self.alias_symbol_links
            .get(symbol)
            .alias_target
            .unwrap()
    }

    /// `(c *Checker) resolveIndirectionAlias` (checker.go).
    pub(crate) fn resolve_indirection_alias(
        &mut self,
        source: SymbolId,
        target: SymbolId,
    ) -> SymbolId {
        let result = self.get_merged_symbol(self.resolve_alias(target));
        let target_type_only = self
            .alias_symbol_links
            .get(target)
            .type_only_declaration;
        if target_type_only.is_some()
            && self
                .alias_symbol_links
                .get(source)
                .type_only_declaration
                .is_none()
        {
            self.alias_symbol_links.get(source).type_only_declaration = target_type_only;
        }
        result
    }

    /// `(c *Checker) tryResolveAlias` (checker.go).
    pub(crate) fn try_resolve_alias(&mut self, symbol: SymbolId) -> Option<SymbolId> {
        if self
            .alias_symbol_links
            .get(symbol)
            .alias_target
            .is_some()
            || self.find_resolution_cycle_start_index(
                TypeSystemEntity::Symbol(symbol),
                TypeSystemPropertyName::AliasTarget,
            ) < 0
        {
            return Some(self.resolve_alias(symbol));
        }
        None
    }

    /// `(c *Checker) resolveAliasWithDeprecationCheck` (checker.go).
    pub(crate) fn resolve_alias_with_deprecation_check(
        &mut self,
        symbol: SymbolId,
        location: NodeId,
    ) -> SymbolId {
        if !self.sym(symbol).flags.intersects(ast::SymbolFlags::ALIAS)
            || self.is_deprecated_symbol(symbol)
            || self.get_declaration_of_alias_symbol(symbol).is_none()
        {
            return symbol;
        }
        let target_symbol = self.resolve_alias(symbol);
        if target_symbol == self.unknown_symbol {
            return target_symbol;
        }
        let mut symbol = symbol;
        while self.sym(symbol).flags.intersects(ast::SymbolFlags::ALIAS) {
            let target = self.get_immediate_aliased_symbol(symbol);
            if let Some(target) = target {
                if target == target_symbol {
                    break;
                }
                if !self.sym(target).declarations.is_empty() {
                    if self.is_deprecated_symbol(target) {
                        let declarations = self.sym(target).declarations.clone();
                        let name = self.sym(target).name.clone();
                        self.add_deprecated_suggestion(location, &declarations, &name);
                        break;
                    } else {
                        if symbol == target_symbol {
                            break;
                        }
                        symbol = target;
                    }
                }
            } else {
                break;
            }
        }
        target_symbol
    }

    /// `(c *Checker) getSymbolFlags` (checker.go) — gets combined flags of a
    /// `symbol` and all alias targets it resolves to.
    pub(crate) fn get_symbol_flags(&mut self, symbol: SymbolId) -> ast::SymbolFlags {
        self.get_symbol_flags_ex(symbol, false, false)
    }

    /// `(c *Checker) getSymbolFlagsEx` (checker.go).
    pub(crate) fn get_symbol_flags_ex(
        &mut self,
        symbol: SymbolId,
        exclude_type_only_meanings: bool,
        exclude_local_meanings: bool,
    ) -> ast::SymbolFlags {
        let mut seen_symbols: Set<SymbolId> = Set::new();
        let mut flags = if !exclude_local_meanings {
            self.sym(symbol).flags
        } else {
            ast::SymbolFlags::NONE
        };
        let mut symbol = symbol;
        while self.sym(symbol).flags.intersects(ast::SymbolFlags::ALIAS) {
            if exclude_type_only_meanings
                && self.get_type_only_alias_declaration(symbol).is_some()
            {
                break;
            }
            let target = self
                .get_export_symbol_of_value_symbol_if_exported(Some(self.resolve_alias(symbol)));
            let Some(target) = target else {
                break;
            };
            if target == self.unknown_symbol {
                return ast::SymbolFlags::ALL;
            }
            if self.sym(target).flags.intersects(ast::SymbolFlags::ALIAS) {
                // Optimization - try to avoid creating or adding to
                // `seenSymbols` if possible
                if target == symbol || seen_symbols.has(&target) {
                    break;
                }
                if seen_symbols.is_empty() {
                    seen_symbols.add(symbol);
                }
                seen_symbols.add(target);
            }
            flags |= self.sym(target).flags;
            symbol = target;
        }
        flags
    }

    /// `(c *Checker) getDeclarationOfAliasSymbol` (checker.go).
    pub(crate) fn get_declaration_of_alias_symbol(&mut self, symbol: SymbolId) -> Option<NodeId> {
        // `core.FindLast(symbol.Declarations, ast.IsAliasSymbolDeclaration)` —
        // declarations may span files, so each gets its own node arena.
        let declarations = self.sym(symbol).declarations.clone();
        for &d in declarations.iter().rev() {
            let nodes = self.program_nodes(d);
            if ast::is_alias_symbol_declaration(d, &nodes) {
                return Some(d);
            }
        }
        None
    }

    /// `(c *Checker) getTypeOfSymbolWithDeferredType` (checker.go).
    pub(crate) fn get_type_of_symbol_with_deferred_type(&mut self, symbol: SymbolId) -> TypeId {
        if self.value_symbol_links.get(symbol).resolved_type.is_none() {
            let (parent, constituents) = {
                let deferred = self.deferred_symbol_links.get(symbol);
                (deferred.parent, deferred.constituents.clone())
            };
            let resolved = if self
                .types
                .get(parent.expect("deferred parent"))
                .flags
                .intersects(TypeFlags::UNION)
            {
                self.get_union_type(&constituents)
            } else {
                self.get_intersection_type(&constituents)
            };
            self.value_symbol_links.get(symbol).resolved_type = Some(resolved);
        }
        self.value_symbol_links.get(symbol).resolved_type.unwrap()
    }

    /// `(c *Checker) getWriteTypeOfSymbolWithDeferredType` (checker.go).
    pub(crate) fn get_write_type_of_symbol_with_deferred_type(
        &mut self,
        symbol: SymbolId,
    ) -> TypeId {
        if self.value_symbol_links.get(symbol).write_type.is_none() {
            let (parent, write_constituents) = {
                let deferred = self.deferred_symbol_links.get(symbol);
                (deferred.parent, deferred.write_constituents.clone())
            };
            let write_type = if !write_constituents.is_empty() {
                if self
                    .types
                    .get(parent.expect("deferred parent"))
                    .flags
                    .intersects(TypeFlags::UNION)
                {
                    self.get_union_type(&write_constituents)
                } else {
                    self.get_intersection_type(&write_constituents)
                }
            } else {
                self.get_type_of_symbol_with_deferred_type(symbol)
            };
            self.value_symbol_links.get(symbol).write_type = Some(write_type);
        }
        self.value_symbol_links.get(symbol).write_type.unwrap()
    }

    /// `(c *Checker) getWriteTypeOfSymbol` (checker.go) — distinct write
    /// types come only from set accessors, but synthetic union and
    /// intersection properties deriving from set accessors will either
    /// pre-compute or defer the union or intersection of the writeTypes of
    /// their constituents.
    pub(crate) fn get_write_type_of_symbol(&mut self, symbol: SymbolId) -> TypeId {
        let check_flags = self.sym(symbol).check_flags;
        if check_flags.intersects(ast::checkflags::CheckFlags::SYNTHETIC_PROPERTY) {
            if check_flags.intersects(ast::checkflags::CheckFlags::DEFERRED_TYPE) {
                return self.get_write_type_of_symbol_with_deferred_type(symbol);
            }
            let links = self.value_symbol_links.get(symbol);
            return links.write_type.or(links.resolved_type).unwrap();
        }
        let flags = self.sym(symbol).flags;
        if flags.intersects(ast::SymbolFlags::PROPERTY) {
            return self.remove_missing_type(
                self.get_type_of_symbol(symbol),
                flags.intersects(ast::SymbolFlags::OPTIONAL),
            );
        }
        if flags.intersects(ast::SymbolFlags::ACCESSOR) {
            if check_flags.intersects(ast::checkflags::CheckFlags::INSTANTIATED) {
                return self.get_write_type_of_instantiated_symbol(symbol);
            }
            return self.get_write_type_of_accessors(symbol);
        }
        self.get_type_of_symbol(symbol)
    }

    /// `(c *Checker) GetTypeOfSymbolAtLocation` (checker.go) — exported.
    /// `location` is nil-able in Go (`Option<NodeId>`).
    pub fn get_type_of_symbol_at_location(
        &mut self,
        symbol: SymbolId,
        location: Option<NodeId>,
    ) -> TypeId {
        let symbol = self
            .get_export_symbol_of_value_symbol_if_exported(Some(symbol))
            .unwrap_or(self.unknown_symbol);
        if let Some(location) = location {
            let nodes = self.program_nodes(location);
            // If we have an identifier or a property access at the given
            // location, if the location is a dotted name expression, and if
            // the location is not an assignment target, obtain the type of
            // the expression (which will reflect control flow analysis). If
            // the expression indeed resolved to the given symbol, return the
            // narrowed type.
            let mut location = location;
            if (ast::is_identifier(&nodes[location])
                || ast::is_private_identifier(&nodes[location]))
                && !(ast::is_jsx_tag_name(location, &nodes)
                    || nodes[location]
                        .parent
                        .is_some_and(|p| ast::is_jsx_attribute(&nodes[p]))
                    || nodes[location]
                        .parent
                        .is_some_and(|p| ast::is_jsx_namespaced_name(&nodes[p])))
            {
                if ast::is_right_side_of_qualified_name_or_property_access(location, &nodes) {
                    location = nodes[location].parent.unwrap();
                }
                if ast::is_expression_node(location, &nodes)
                    && (!ast::is_assignment_target(location, &nodes)
                        || ast::is_write_access(&nodes[location]))
                {
                    let t = if ast::is_write_access(&nodes[location])
                        && nodes[location].kind == ast::Kind::PropertyAccessExpression
                    {
                        self.check_property_access_expression(
                            location,
                            CheckMode::NORMAL,
                            true, /*writeOnly*/
                        )
                    } else {
                        self.get_type_of_expression(location)
                    };
                    if self.get_export_symbol_of_value_symbol_if_exported(
                        self.symbol_node_links.get(location).resolved_symbol,
                    ) == Some(symbol)
                    {
                        return self.remove_optional_type_marker(t);
                    }
                }
            }
            if ast::is_declaration_name(location, &nodes)
                && nodes[location]
                    .parent
                    .is_some_and(|p| ast::is_set_accessor_declaration(&nodes[p]))
            {
                let parent = nodes[location].parent.unwrap();
                if self.get_annotated_accessor_type_node(parent).is_some() {
                    return self.get_write_type_of_accessors(nodes[parent].symbol().unwrap());
                }
            }
            // The location isn't a reference to the given symbol, meaning
            // we're being asked a hypothetical question of what type the
            // symbol would have if there was a reference to it at the given
            // location. Since we have no control flow information for the
            // hypothetical reference (control flow information is created and
            // attached by the binder), we simply return the declared type of
            // the symbol.
            if crate::utilities::is_right_side_of_access_expression(location, &nodes)
                && nodes[location]
                    .parent
                    .is_some_and(|p| ast::is_write_access(&nodes[p]))
            {
                return self.get_write_type_of_symbol(symbol);
            }
        }
        self.get_non_missing_type_of_symbol(symbol)
    }

    /// `(c *Checker) getTypeOfSymbol` (checker.go).
    ///
    /// NOTE: this is the real implementation; a `PORT(deferred)` placeholder
    /// of the same name previously lived in `checker_core.rs` and was removed
    /// when this body landed (see PORTING-NOTES).
    pub fn get_type_of_symbol(&mut self, symbol: SymbolId) -> TypeId {
        let check_flags = self.sym(symbol).check_flags;
        if check_flags.intersects(ast::checkflags::CheckFlags::DEFERRED_TYPE) {
            return self.get_type_of_symbol_with_deferred_type(symbol);
        }
        if check_flags.intersects(ast::checkflags::CheckFlags::INSTANTIATED) {
            return self.get_type_of_instantiated_symbol(symbol);
        }
        if check_flags.intersects(ast::checkflags::CheckFlags::MAPPED) {
            return self.get_type_of_mapped_symbol(symbol);
        }
        if check_flags.intersects(ast::checkflags::CheckFlags::REVERSE_MAPPED) {
            return self.get_type_of_reverse_mapped_symbol(symbol);
        }
        let flags = self.sym(symbol).flags;
        if flags.intersects(ast::SymbolFlags::ACCESSOR) {
            return self.get_type_of_accessors(symbol);
        }
        if flags.intersects(ast::SymbolFlags::VARIABLE | ast::SymbolFlags::PROPERTY) {
            return self.get_type_of_variable_or_parameter_or_property(symbol);
        }
        if flags.intersects(
            ast::SymbolFlags::FUNCTION
                | ast::SymbolFlags::METHOD
                | ast::SymbolFlags::CLASS
                | ast::SymbolFlags::ENUM
                | ast::SymbolFlags::VALUE_MODULE,
        ) {
            return self.get_type_of_func_class_enum_module(symbol);
        }
        if flags.intersects(ast::SymbolFlags::ENUM_MEMBER) {
            return self.get_type_of_enum_member(symbol);
        }
        if flags.intersects(ast::SymbolFlags::ALIAS) {
            return self.get_type_of_alias(symbol);
        }
        self.error_type
    }

    /// `(c *Checker) getNonMissingTypeOfSymbol` (checker.go).
    pub(crate) fn get_non_missing_type_of_symbol(&mut self, symbol: SymbolId) -> TypeId {
        let is_optional = self
            .sym(symbol)
            .flags
            .intersects(ast::SymbolFlags::OPTIONAL);
        self.remove_missing_type(self.get_type_of_symbol(symbol), is_optional)
    }

    /// `(c *Checker) getTypeOfInstantiatedSymbol` (checker.go).
    pub(crate) fn get_type_of_instantiated_symbol(&mut self, symbol: SymbolId) -> TypeId {
        if self.value_symbol_links.get(symbol).resolved_type.is_none() {
            let (target, mapper) = {
                let links = self.value_symbol_links.get(symbol);
                (links.target, links.mapper)
            };
            let resolved =
                self.instantiate_type(self.get_type_of_symbol(target.unwrap()), mapper);
            self.value_symbol_links.get(symbol).resolved_type = Some(resolved);
        }
        self.value_symbol_links.get(symbol).resolved_type.unwrap()
    }

    /// `(c *Checker) getWriteTypeOfInstantiatedSymbol` (checker.go).
    pub(crate) fn get_write_type_of_instantiated_symbol(&mut self, symbol: SymbolId) -> TypeId {
        if self.value_symbol_links.get(symbol).write_type.is_none() {
            let (target, mapper) = {
                let links = self.value_symbol_links.get(symbol);
                (links.target, links.mapper)
            };
            let write_type =
                self.instantiate_type(self.get_write_type_of_symbol(target.unwrap()), mapper);
            self.value_symbol_links.get(symbol).write_type = Some(write_type);
        }
        self.value_symbol_links.get(symbol).write_type.unwrap()
    }

    /// `(c *Checker) getTypeOfVariableOrParameterOrProperty` (checker.go).
    pub(crate) fn get_type_of_variable_or_parameter_or_property(
        &mut self,
        symbol: SymbolId,
    ) -> TypeId {
        if self.value_symbol_links.get(symbol).resolved_type.is_none() {
            let t = self.get_type_of_variable_or_parameter_or_property_worker(symbol);
            // For a contextually typed parameter it is possible that a type
            // has already been assigned (in
            // assignTypeToParameterAndFixTypeParameters), and we want to
            // preserve this type. In fact, we need to _prefer_ that type, but
            // it won't be assigned until contextual typing is complete, so we
            // need to defer in cases where contextual typing may take place.
            if self.value_symbol_links.get(symbol).resolved_type.is_none()
                && !self.is_parameter_of_context_sensitive_signature(symbol)
            {
                self.value_symbol_links.get(symbol).resolved_type = Some(t);
            }
            return t;
        }
        self.value_symbol_links.get(symbol).resolved_type.unwrap()
    }

    /// `(c *Checker) isParameterOfContextSensitiveSignature` (checker.go).
    pub(crate) fn is_parameter_of_context_sensitive_signature(&mut self, symbol: SymbolId) -> bool {
        let Some(decl) = self.sym(symbol).value_declaration else {
            return false;
        };
        let nodes = self.program_nodes(decl);
        let decl = if ast::is_binding_element(&nodes[decl]) {
            ast::walk_up_binding_elements_and_patterns(decl, &nodes).unwrap_or(decl)
        } else {
            decl
        };
        if ast::is_parameter_declaration(&nodes[decl]) {
            return self.is_context_sensitive_function_or_object_literal_method(
                nodes[decl].parent.expect("parameter parent"),
            );
        }
        false
    }

    /// `(c *Checker) getTypeOfVariableOrParameterOrPropertyWorker`
    /// (checker.go).
    pub(crate) fn get_type_of_variable_or_parameter_or_property_worker(
        &mut self,
        symbol: SymbolId,
    ) -> TypeId {
        // Handle prototype property
        if self
            .sym(symbol)
            .flags
            .intersects(ast::SymbolFlags::PROTOTYPE)
        {
            return self.get_type_of_prototype_property(symbol);
        }
        // CommonsJS require and module both have type any.
        if symbol == self.require_symbol {
            return self.any_type;
        }
        let declaration = self
            .sym(symbol)
            .value_declaration
            .expect("symbol.ValueDeclaration");
        let nodes = self.program_nodes(declaration);
        if ast::is_source_file(&nodes[declaration])
            && ast::is_json_source_file(nodes[declaration].as_source_file())
        {
            let statements = nodes[declaration].statements().unwrap_or(&[]).to_vec();
            if statements.is_empty() {
                return self.empty_object_type;
            }
            let expr = nodes[statements[0]].expression().expect("expr statement");
            return self.get_widened_type(
                self.get_widened_literal_type(self.check_expression(expr)),
            );
        }
        // Handle variable, parameter or property
        if !self.push_type_resolution(
            TypeSystemEntity::Symbol(symbol),
            TypeSystemPropertyName::Type,
        ) {
            return self.report_circularity_error(symbol);
        }
        if self
            .sym(symbol)
            .flags
            .intersects(ast::SymbolFlags::MODULE_EXPORTS)
        {
            if self.sym(symbol).name == "exports" {
                let decl_symbol = nodes[declaration].symbol().unwrap();
                return self.get_type_of_symbol(
                    self.resolve_external_module_symbol(decl_symbol, false)
                        .expect("resolved external module"),
                );
            }
            let members = self.sym(symbol).members.clone();
            return self.new_anonymous_type(Some(symbol), members, &[], &[], &[]);
        }
        let result = match nodes[declaration].kind {
            ast::Kind::Parameter
            | ast::Kind::PropertyDeclaration
            | ast::Kind::PropertySignature
            | ast::Kind::VariableDeclaration
            | ast::Kind::BindingElement => {
                // only report diagnostics for context-insensitive parameters
                // - context-sensitive ones may have their type fixed to
                // something else
                self.get_widened_type_for_variable_like_declaration(
                    declaration,
                    !self.is_parameter_of_context_sensitive_signature(symbol),
                )
            }
            ast::Kind::PropertyAssignment => {
                self.check_property_assignment(declaration, CheckMode::NORMAL)
            }
            ast::Kind::ShorthandPropertyAssignment => self.check_shorthand_property_assignment(
                declaration,
                true, /*inDestructuringPattern*/
                CheckMode::NORMAL,
            ),
            ast::Kind::MethodDeclaration => {
                self.check_object_literal_method(declaration, CheckMode::NORMAL)
            }
            ast::Kind::ExportAssignment => {
                if nodes[declaration].type_().is_some() {
                    self.get_type_from_type_node(nodes[declaration].type_().unwrap())
                } else {
                    let expr = nodes[declaration].expression().expect("export expr");
                    let t = self.check_expression_cached(expr);
                    self.widen_type_for_variable_like_declaration(t, declaration, false)
                }
            }
            ast::Kind::BinaryExpression | ast::Kind::CallExpression => {
                self.get_widened_type_for_assignment_declaration(symbol)
            }
            ast::Kind::JsxAttribute => self.check_jsx_attribute(declaration, CheckMode::NORMAL),
            ast::Kind::EnumMember => self.get_type_of_enum_member(symbol),
            _ => panic!(
                "Unhandled case in getTypeOfVariableOrParameterOrPropertyWorker: {}",
                nodes[declaration].kind_string()
            ),
        };
        if !self.pop_type_resolution() {
            return self.report_circularity_error(symbol);
        }
        result
    }

    /// `(c *Checker) getWidenedTypeForVariableLikeDeclaration` (checker.go) —
    /// returns the type associated with a variable, parameter, or property
    /// declaration.
    pub(crate) fn get_widened_type_for_variable_like_declaration(
        &mut self,
        declaration: NodeId,
        report_errors: bool,
    ) -> TypeId {
        let t =
            self.get_type_for_variable_like_declaration(declaration, true, CheckMode::NORMAL);
        self.widen_type_for_variable_like_declaration(t, declaration, report_errors)
    }

    /// `(c *Checker) getTypeForVariableLikeDeclaration` (checker.go) —
    /// returns the inferred type for a variable, parameter, or property
    /// declaration. Returns `None` for Go's nil results.
    pub(crate) fn get_type_for_variable_like_declaration(
        &mut self,
        declaration: NodeId,
        include_optionality: bool,
        check_mode: CheckMode,
    ) -> Option<TypeId> {
        let nodes = self.program_nodes(declaration);
        // A variable declared in a for..in statement is of type string, or of
        // type keyof T when the right hand expression is of a type parameter
        // type.
        if ast::is_variable_declaration(&nodes[declaration]) {
            let grand_parent =
                nodes[declaration].parent.and_then(|p| nodes[p].parent);
            let grand_parent = grand_parent.expect("for variable grandparent");
            match nodes[grand_parent].kind {
                ast::Kind::ForInStatement => {
                    let expr = nodes[grand_parent].expression().unwrap();
                    let index_type = self.get_index_type(
                        self.get_non_nullable_type_if_needed(
                            self.check_expression_ex(expr, check_mode),
                        ),
                    );
                    if self
                        .types
                        .get(index_type)
                        .flags
                        .intersects(TypeFlags::TYPE_PARAMETER | TypeFlags::INDEX)
                    {
                        return Some(self.get_extract_string_type(index_type));
                    }
                    return Some(self.string_type);
                }
                ast::Kind::ForOfStatement => {
                    // checkRightHandSideOfForOf will return undefined if the
                    // for-of expression type was missing properties/signatures
                    // required to get its iteratedType (like
                    // [Symbol.iterator] or next). This may be because we
                    // accessed properties from anyType, or it may have led to
                    // an error inside getElementTypeOfIterable.
                    return Some(self.check_right_hand_side_of_for_of(grand_parent));
                }
                _ => {}
            }
        } else if ast::is_binding_element(&nodes[declaration]) {
            return Some(self.get_type_for_binding_element(declaration));
        }
        let is_property = (ast::is_property_declaration(&nodes[declaration])
            && !ast::has_accessor_modifier(&nodes[declaration]))
            || ast::is_property_signature_declaration(&nodes[declaration]);
        let is_optional =
            include_optionality && crate::utilities::is_optional_declaration(&nodes[declaration]);
        // Use type from type annotation if one is present
        let declared_type = self.try_get_type_from_type_node(declaration);
        if ast::is_catch_clause_variable_declaration_or_binding_element(declaration, &nodes) {
            if let Some(declared_type) = declared_type {
                // If the catch clause is explicitly annotated with any or
                // unknown, accept it, otherwise error.
                if self
                    .types
                    .get(declared_type)
                    .flags
                    .intersects(TypeFlags::ANY_OR_UNKNOWN)
                {
                    return Some(declared_type);
                }
                return Some(self.error_type);
            }
            // If the catch clause is not explicitly annotated, treat it as
            // though it were explicitly annotated with unknown or any,
            // depending on useUnknownInCatchVariables.
            if self.use_unknown_in_catch_variables {
                return Some(self.unknown_type);
            } else {
                return Some(self.any_type);
            }
        }
        if let Some(declared_type) = declared_type {
            return Some(self.add_optionality_ex(declared_type, is_property, is_optional));
        }
        if self.no_implicit_any
            && ast::is_variable_declaration(&nodes[declaration])
            && !nodes[declaration].name().is_some_and(|n| ast::is_binding_pattern(&nodes[n]))
            && !self
                .get_combined_modifier_flags_cached(declaration)
                .intersects(ast::ModifierFlags::EXPORT)
            && !nodes[declaration]
                .flags
                .intersects(ast::NodeFlags::AMBIENT)
        {
            // If --noImplicitAny is on or the declaration is in a Javascript
            // file, use control flow tracked 'any' type for non-ambient,
            // non-exported var or let variables with no initializer or a
            // 'null' or 'undefined' initializer.
            let initializer = nodes[declaration].initializer();
            if !self
                .get_combined_node_flags_cached(declaration)
                .intersects(ast::NodeFlags::CONSTANT)
                && (initializer.is_none()
                    || self.is_null_or_undefined(initializer.unwrap()))
            {
                return Some(self.auto_type);
            }
            // Use control flow tracked 'any[]' type for non-ambient,
            // non-exported variables with an empty array literal initializer.
            if let Some(initializer) = initializer
                && ast::is_empty_array_literal(&nodes[initializer])
            {
                return Some(self.auto_array_type);
            }
        }
        if ast::is_parameter_declaration(&nodes[declaration]) {
            if nodes[declaration].symbol().is_none() {
                // parameters of function types defined in JSDoc in TS files
                // don't have symbols
                return None;
            }
            let fn_ = nodes[declaration].parent.unwrap();
            // For a parameter of a set accessor, use the type of the get
            // accessor if one is present
            if ast::is_set_accessor_declaration(&nodes[fn_]) && self.has_bindable_name(fn_) {
                let getter = {
                    let parent_symbol = self.get_symbol_of_declaration(fn_);
                    parent_symbol.and_then(|s| {
                        let arena = self.symbol_arena.borrow();
                        ast::get_declaration_of_kind(
                            &arena[s.index()],
                            ast::Kind::GetAccessor,
                            &nodes,
                        )
                    })
                };
                if let Some(getter) = getter {
                    let getter_signature = self.get_signature_from_declaration(getter);
                    let this_parameter = self.get_accessor_this_parameter(fn_);
                    if let Some(this_parameter) = this_parameter
                        && declaration == this_parameter
                    {
                        // Use the type from the *getter*
                        debug_assert!(nodes[this_parameter].type_().is_none());
                        let this_param = self
                            .signature_arena
                            .get(getter_signature)
                            .this_parameter
                            .expect("thisParameter");
                        return Some(self.get_type_of_symbol(this_param));
                    }
                    return Some(self.get_return_type_of_signature(getter_signature));
                }
            }
            if let Some(t) = self.get_parameter_type_of_full_signature(fn_, declaration) {
                return Some(t);
            }
            // Use contextual parameter type if one is available
            let t = if self.sym(nodes[declaration].symbol().unwrap()).name
                == ast::INTERNAL_SYMBOL_NAME_THIS
            {
                self.get_contextual_this_parameter_type(fn_)
            } else {
                self.get_contextually_typed_parameter_type(declaration)
            };
            if let Some(t) = t {
                return Some(self.add_optionality_ex(t, false /*isProperty*/, is_optional));
            }
        }
        // Use the type of the initializer expression if one is present and
        // the declaration is not a parameter of a contextually typed
        // function
        if nodes[declaration].initializer().is_some() {
            let t = self.widen_type_inferred_from_initializer(
                declaration,
                self.check_declaration_initializer(declaration, check_mode, None),
            );
            return Some(self.add_optionality_ex(t, is_property, is_optional));
        }
        if self.no_implicit_any && ast::is_property_declaration(&nodes[declaration]) {
            // We have a property declaration with no type annotation or
            // initializer, in noImplicitAny mode or a .js file. Use control
            // flow analysis of this.xxx assignments in the constructor or
            // static block to determine the type of the property.
            if !ast::has_static_modifier(&nodes[declaration]) {
                let constructor = ast::find_constructor_declaration(
                    &nodes[nodes[declaration].parent.unwrap()],
                    &nodes,
                );
                let t = match constructor {
                    Some(constructor) => self.get_flow_type_in_constructor(
                        nodes[declaration].symbol().unwrap(),
                        constructor,
                    ),
                    None if nodes[declaration]
                        .modifier_flags()
                        .intersects(ast::ModifierFlags::AMBIENT) =>
                    {
                        self.get_type_of_property_in_base_class(
                            nodes[declaration].symbol().unwrap(),
                        )
                    }
                    _ => None,
                };
                let t = t?;
                return Some(self.add_optionality_ex(t, true /*isProperty*/, is_optional));
            } else {
                let parent = nodes[declaration].parent.unwrap();
                let static_blocks: Vec<NodeId> = nodes[parent]
                    .members()
                    .unwrap_or(&[])
                    .iter()
                    .copied()
                    .filter(|&m| ast::is_class_static_block_declaration(&nodes[m]))
                    .collect();
                let t = if !static_blocks.is_empty() {
                    self.get_flow_type_in_static_blocks(
                        nodes[declaration].symbol().unwrap(),
                        &static_blocks,
                    )
                } else if nodes[declaration]
                    .modifier_flags()
                    .intersects(ast::ModifierFlags::AMBIENT)
                {
                    self.get_type_of_property_in_base_class(
                        nodes[declaration].symbol().unwrap(),
                    )
                } else {
                    None
                };
                let t = t?;
                return Some(self.add_optionality_ex(t, true /*isProperty*/, is_optional));
            }
        }
        if ast::is_jsx_attribute(&nodes[declaration]) {
            // if JSX attribute doesn't have initializer, by default the
            // attribute will have boolean value of true.
            // I.e <Elem attr /> is sugar for <Elem attr={true} />
            return Some(self.true_type);
        }
        // If the declaration specifies a binding pattern and is not a
        // parameter of a contextually typed function, use the type implied by
        // the binding pattern
        if let Some(name) = nodes[declaration].name()
            && ast::is_binding_pattern(&nodes[name])
        {
            return Some(self.get_type_from_binding_pattern(
                name,
                false, /*includePatternInType*/
                true,  /*reportErrors*/
            ));
        }
        // No type specified and nothing can be inferred
        None
    }

    /// `(c *Checker) checkDeclarationInitializer` (checker.go).
    pub(crate) fn check_declaration_initializer(
        &mut self,
        declaration: NodeId,
        check_mode: CheckMode,
        contextual_type: Option<TypeId>,
    ) -> TypeId {
        let nodes = self.program_nodes(declaration);
        let initializer = nodes[declaration].initializer().expect("initializer");
        let t = match self.get_quick_type_of_expression(initializer) {
            Some(t) => t,
            None => {
                if let Some(contextual_type) = contextual_type {
                    self.check_expression_with_contextual_type(
                        initializer,
                        contextual_type,
                        None, /*inferenceContext*/
                        check_mode,
                    )
                } else {
                    self.check_expression_cached_ex(initializer, check_mode)
                }
            }
        };
        let root = ast::get_root_declaration(declaration, &nodes);
        if ast::is_parameter_declaration(&nodes[root]) {
            let name = nodes[declaration].name().expect("decl name");
            match nodes[name].kind {
                ast::Kind::ObjectBindingPattern => {
                    if crate::utilities::is_object_literal_type(&self.types, t) {
                        return self.pad_object_literal_type(t, name);
                    }
                }
                ast::Kind::ArrayBindingPattern => {
                    if is_tuple_type(self, t) {
                        return self.pad_tuple_type(t, name);
                    }
                }
                _ => {}
            }
        }
        t
    }

    /// `(c *Checker) padObjectLiteralType` (checker.go).
    pub(crate) fn pad_object_literal_type(&mut self, t: TypeId, pattern: NodeId) -> TypeId {
        let nodes = self.program_nodes(pattern);
        let mut missing_elements: Vec<NodeId> = Vec::new();
        for &e in nodes[pattern].elements().unwrap_or(&[]) {
            if crate::utilities::has_dot_dot_dot_token(&nodes[e]) {
                continue;
            }
            let name = self.get_property_name_from_binding_element(e);
            if name != ast::INTERNAL_SYMBOL_NAME_MISSING
                && self.get_property_of_type(t, &name).is_none()
            {
                missing_elements.push(e);
            }
        }
        if missing_elements.is_empty() {
            return t;
        }
        let mut members = SymbolTable::new();
        for prop in self.get_properties_of_object_type(t) {
            let name = self.sym(prop).name.clone();
            members.set(name, prop);
        }
        for e in missing_elements {
            let name = self.get_property_name_from_binding_element(e);
            let symbol = self.new_symbol(
                ast::SymbolFlags::PROPERTY | ast::SymbolFlags::OPTIONAL,
                &name,
            );
            let resolved = self.get_type_from_binding_element(
                e,
                false, /*includePatternInType*/
                true,  /*reportErrors*/
            );
            self.value_symbol_links.get(symbol).resolved_type = Some(resolved);
            members.set(name, symbol);
        }
        let index_infos = self.get_index_infos_of_type(t);
        let index_infos: Vec<IndexInfoId> = index_infos
            .iter()
            .map(|info| self.index_info_arena.alloc(info.clone()))
            .collect();
        let symbol = self.types.get(t).symbol;
        let object_flags = self.types.get(t).object_flags;
        let result = self.new_anonymous_type(symbol, members, &[], &[], &index_infos);
        self.types.get_mut(result).object_flags = object_flags;
        result
    }

    /// `(c *Checker) getPropertyNameFromBindingElement` (checker.go).
    pub(crate) fn get_property_name_from_binding_element(&mut self, e: NodeId) -> String {
        let nodes = self.program_nodes(e);
        let expr_type = self.get_literal_type_from_property_name(
            nodes[e].property_name_or_name().expect("propertyNameOrName"),
        );
        if crate::utilities::is_type_usable_as_property_name(&self.types, expr_type) {
            return crate::utilities::get_property_name_from_type(&self.types, expr_type);
        }
        ast::INTERNAL_SYMBOL_NAME_MISSING.to_string()
    }

    /// `(c *Checker) padTupleType` (checker.go).
    pub(crate) fn pad_tuple_type(&mut self, t: TypeId, pattern: NodeId) -> TypeId {
        let nodes = self.program_nodes(pattern);
        let pattern_elements = nodes[pattern].elements().unwrap_or(&[]).to_vec();
        let target = self
            .types
            .target_tuple_type(t)
            .expect("TargetTupleType");
        let target_combined_flags = self.types.get(target).as_tuple_type().combined_flags;
        if target_combined_flags.intersects(ElementFlags::VARIABLE)
            || self.get_type_reference_arity(t) >= pattern_elements.len()
        {
            return t;
        }
        let mut element_types = self.get_element_types(t);
        let mut element_infos = self
            .types
            .get(target)
            .as_tuple_type()
            .element_infos
            .clone();
        for i in self.get_type_reference_arity(t)..pattern_elements.len() {
            let e = pattern_elements[i];
            if i < pattern_elements.len() - 1
                || !(ast::is_binding_element(&nodes[e])
                    && crate::utilities::has_dot_dot_dot_token(&nodes[e]))
            {
                let mut element_type = self.any_type;
                if !ast::is_omitted_expression(&nodes[e]) && self.has_default_value(e) {
                    element_type = self.get_type_from_binding_element(
                        e,
                        false, /*includePatternInType*/
                        false, /*reportErrors*/
                    );
                }
                element_types.push(element_type);
                element_infos.push(TupleElementInfo {
                    flags: ElementFlags::OPTIONAL,
                    labeled_declaration: None,
                });
                if !ast::is_omitted_expression(&nodes[e]) && !self.has_default_value(e) {
                    self.report_implicit_any(e, self.any_type, WideningKind::Normal);
                }
            }
        }
        let readonly = self.types.get(target).as_tuple_type().readonly;
        self.create_tuple_type_ex(&element_types, &element_infos, readonly)
    }

    /// `(c *Checker) widenTypeInferredFromInitializer` (checker.go).
    pub(crate) fn widen_type_inferred_from_initializer(
        &mut self,
        declaration: NodeId,
        t: TypeId,
    ) -> TypeId {
        let widened = self.get_widened_literal_type_for_initializer(declaration, t);
        let nodes = self.program_nodes(declaration);
        if ast::is_in_js_file(Some(declaration), &nodes) {
            if self.is_empty_literal_type(widened) {
                self.report_implicit_any(declaration, self.any_type, WideningKind::Normal);
                return self.any_type;
            }
            if self.is_empty_array_literal_type(widened) {
                self.report_implicit_any(declaration, self.any_array_type, WideningKind::Normal);
                return self.any_array_type;
            }
        }
        widened
    }

    /// `(c *Checker) getWidenedLiteralTypeForInitializer` (checker.go).
    pub(crate) fn get_widened_literal_type_for_initializer(
        &mut self,
        declaration: NodeId,
        t: TypeId,
    ) -> TypeId {
        let nodes = self.program_nodes(declaration);
        if self
            .get_combined_node_flags_cached(declaration)
            .intersects(ast::NodeFlags::CONSTANT)
            || crate::utilities::is_declaration_readonly(&nodes[declaration])
        {
            return t;
        }
        self.get_widened_literal_type(t)
    }

    /// `(c *Checker) getTypeOfFuncClassEnumModule` (checker.go:17291).
    pub(crate) fn get_type_of_func_class_enum_module(&mut self, symbol: SymbolId) -> TypeId {
        if self.value_symbol_links.get(symbol).resolved_type.is_none() {
            let t = self.get_type_of_func_class_enum_module_worker(symbol);
            self.value_symbol_links.get(symbol).resolved_type = Some(t);
        }
        self.value_symbol_links.get(symbol).resolved_type.unwrap()
    }

    /// `(c *Checker) getTypeOfFuncClassEnumModuleWorker` (checker.go:17299).
    pub(crate) fn get_type_of_func_class_enum_module_worker(
        &mut self,
        symbol: SymbolId,
    ) -> TypeId {
        let flags = self.sym(symbol).flags;
        if flags.intersects(ast::SymbolFlags::MODULE)
            && crate::utilities::is_shorthand_ambient_module_symbol(&self.sym(symbol))
        {
            return self.any_type;
        } else if flags.intersects(ast::SymbolFlags::VALUE_MODULE)
            && self.sym(symbol).value_declaration.is_some_and(|vd| {
                let nodes = self.program_nodes(vd);
                ast::is_source_file(&nodes[vd])
                    && nodes[vd]
                        .as_source_file()
                        .common_js_module_indicator
                        .is_some()
            })
        {
            if let Some(resolved_module) =
                self.resolve_external_module_symbol(symbol, false /*dontResolveAlias*/)
            {
                if resolved_module != symbol {
                    return self.get_type_of_symbol(resolved_module);
                }
            }
        }
        let t = self.new_object_type(ObjectFlags::ANONYMOUS, Some(symbol));
        if flags.intersects(ast::SymbolFlags::CLASS) {
            if let Some(base_type_variable) = self.get_base_type_variable_of_class(symbol) {
                return self.get_intersection_type(&[t, base_type_variable]);
            }
            return t;
        }
        if self.strict_null_checks && flags.intersects(ast::SymbolFlags::OPTIONAL) {
            return self.get_optional_type(t, true /*isProperty*/);
        }
        t
    }

    /// `(c *Checker) getBaseTypeVariableOfClass` (checker.go:17323).
    pub(crate) fn get_base_type_variable_of_class(&mut self, symbol: SymbolId) -> Option<TypeId> {
        let declared = self.get_declared_type_of_class_or_interface(symbol);
        let base_constructor_type = self.get_base_constructor_type_of_class(declared);
        let flags = self.types.get(base_constructor_type).flags;
        if flags.intersects(TypeFlags::TYPE_VARIABLE) {
            return Some(base_constructor_type);
        }
        if flags.intersects(TypeFlags::INTERSECTION) {
            let types = self.types.get(base_constructor_type).types().to_vec();
            return core::find(&types, |&t| {
                self.types.get(t).flags.intersects(TypeFlags::TYPE_VARIABLE)
            });
        }
        None
    }

    /// `(c *Checker) getBaseConstructorTypeOfClass` (checker.go:17344).
    ///
    /// The base constructor of a class can resolve to
    /// * undefinedType if the class has no extends clause,
    /// * errorType if an error occurred during resolution of the extends expression,
    /// * nullType if the extends expression is the null value,
    /// * anyType if the extends expression has type any, or
    /// * an object type with at least one construct signature.
    pub(crate) fn get_base_constructor_type_of_class(&mut self, t: TypeId) -> TypeId {
        if let Some(resolved) = self
            .types
            .get(t)
            .as_interface_type()
            .and_then(|d| d.resolved_base_constructor_type)
        {
            return resolved;
        }
        let Some(base_type_node) = get_base_type_node_of_class(&self.types, t) else {
            self.types
                .get_mut(t)
                .data
                .as_interface_type_mut()
                .unwrap()
                .resolved_base_constructor_type = Some(self.undefined_type);
            return self.undefined_type;
        };
        if !self.push_type_resolution(
            TypeSystemEntity::Type(t),
            TypeSystemPropertyName::ResolvedBaseConstructorType,
        ) {
            return self.error_type;
        }
        let base_constructor_type = {
            let nodes = self.program_nodes(base_type_node);
            let expression = nodes[base_type_node].expression().unwrap();
            self.check_expression(expression)
        };
        if self
            .types
            .get(base_constructor_type)
            .flags
            .intersects(TypeFlags::OBJECT | TypeFlags::INTERSECTION)
        {
            // Resolving the members of a class requires us to resolve the base class of that class.
            // We force resolution here such that we catch circularities now.
            self.resolve_structured_type_members(base_constructor_type);
        }
        if !self.pop_type_resolution() {
            let t_symbol = self.types.get(t).symbol.unwrap();
            let (value_declaration, arg) = {
                let s = self.sym(t_symbol);
                (s.value_declaration, self.symbol_to_string(t_symbol))
            };
            self.error(
                value_declaration,
                &tsc_diagnostics::X_0_is_referenced_directly_or_indirectly_in_its_own_base_expression,
                &[arg],
            );
            let mut g = self.types.get_mut(t);
            let d = g.data.as_interface_type_mut().unwrap();
            if d.resolved_base_constructor_type.is_none() {
                d.resolved_base_constructor_type = Some(self.error_type);
            }
            return d.resolved_base_constructor_type.unwrap();
        }
        let bct_flags = self.types.get(base_constructor_type).flags;
        if !bct_flags.intersects(TypeFlags::ANY)
            && base_constructor_type != self.null_widening_type
            && !self.is_constructor_type(base_constructor_type)
        {
            let nodes = self.program_nodes(base_type_node);
            let expression = nodes[base_type_node].expression();
            let arg = self.type_to_string(base_constructor_type);
            let err = self.error(
                expression,
                &tsc_diagnostics::Type_0_is_not_a_constructor_function_type,
                &[arg],
            );
            if bct_flags.intersects(TypeFlags::TYPE_PARAMETER) {
                let constraint = self.get_constraint_from_type_parameter(base_constructor_type);
                let mut ctor_return = self.unknown_type;
                if let Some(constraint) = constraint {
                    let ctor_sigs = self.get_signatures_of_type(constraint, SignatureKind::Construct);
                    if !ctor_sigs.is_empty() {
                        ctor_return = self.get_return_type_of_signature(ctor_sigs[0]);
                    }
                }
                if let Some(symbol) = self.types.get(base_constructor_type).symbol {
                    let declarations = self.sym(symbol).declarations.clone();
                    if !declarations.is_empty() {
                        let arg0 = self.symbol_to_string(symbol);
                        let arg1 = self.type_to_string(ctor_return);
                        let related = crate::checker_b::create_diagnostic_for_node(
                            Some(declarations[0]),
                            &self.program_nodes(declarations[0]),
                            &tsc_diagnostics::Did_you_mean_for_0_to_be_constrained_to_type_new_args_Colon_any_1,
                            &[arg0, arg1],
                        );
                        if let Some(err) = err {
                            ast::diagnostic::lock_diagnostic(&err)
                                .add_related_info(Some(related));
                        }
                    }
                }
            }
            let mut g = self.types.get_mut(t);
            let d = g.data.as_interface_type_mut().unwrap();
            if d.resolved_base_constructor_type.is_none() {
                d.resolved_base_constructor_type = Some(self.error_type);
            }
            return d.resolved_base_constructor_type.unwrap();
        }
        let mut g = self.types.get_mut(t);
        let d = g.data.as_interface_type_mut().unwrap();
        if d.resolved_base_constructor_type.is_none() {
            d.resolved_base_constructor_type = Some(base_constructor_type);
        }
        d.resolved_base_constructor_type.unwrap()
    }

    /// `(c *Checker) isFunctionType` (checker.go:17396).
    pub(crate) fn is_function_type(&mut self, t: TypeId) -> bool {
        self.types.get(t).flags.intersects(TypeFlags::OBJECT)
            && !self.get_signatures_of_type(t, SignatureKind::Call).is_empty()
    }

    /// `(c *Checker) isConstructorType` (checker.go:17400).
    pub(crate) fn is_constructor_type(&mut self, t: TypeId) -> bool {
        if !self.get_signatures_of_type(t, SignatureKind::Construct).is_empty() {
            return true;
        }
        if self.types.get(t).flags.intersects(TypeFlags::TYPE_VARIABLE) {
            if let Some(constraint) = self.get_base_constraint_of_type(t) {
                return self.is_mixin_constructor_type(constraint);
            }
        }
        false
    }

    /// `(c *Checker) isMixinConstructorType` (checker.go:17413) — a type is a
    /// mixin constructor if it has a single construct signature taking no
    /// type parameters and a single rest parameter of type `any[]`.
    pub(crate) fn is_mixin_constructor_type(&mut self, t: TypeId) -> bool {
        let signatures = self.get_signatures_of_type(t, SignatureKind::Construct);
        if signatures.len() == 1 {
            let s = signatures[0];
            let (type_parameters_empty, parameters) = {
                let sig = self.signature_arena.get(s);
                (sig.type_parameters.is_empty(), sig.parameters.clone())
            };
            if type_parameters_empty
                && parameters.len() == 1
                && signature_has_rest_parameter(self.signature_arena.get(s))
            {
                let param_type = self.get_type_of_parameter(parameters[0]);
                return crate::utilities::is_type_any(&self.types, param_type)
                    || self
                        .get_element_type_of_array_type(param_type)
                        .is_some_and(|e| e == self.any_type);
            }
        }
        false
    }

    /// `(c *Checker) getTypeOfParameter` (checker.go:17429).
    pub(crate) fn get_type_of_parameter(&mut self, symbol: SymbolId) -> TypeId {
        let declaration = self.sym(symbol).value_declaration;
        let t = self.get_type_of_symbol(symbol);
        let add_optionality = declaration.is_some_and(|d| {
            let nodes = self.program_nodes(d);
            nodes[d].initializer().is_some()
                || crate::utilities::is_optional_declaration(&nodes[d])
        });
        self.add_optionality_ex(t, false, add_optionality)
    }

    /// `(c *Checker) getConstraintOfType` (checker.go:17434).
    pub(crate) fn get_constraint_of_type(&mut self, t: TypeId) -> Option<TypeId> {
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::TYPE_PARAMETER) {
            return self.get_constraint_of_type_parameter(t);
        }
        if flags.intersects(TypeFlags::INDEXED_ACCESS) {
            return self.get_constraint_of_indexed_access(t);
        }
        if flags.intersects(TypeFlags::CONDITIONAL) {
            return self.get_constraint_of_conditional_type(t);
        }
        self.get_base_constraint_of_type(t)
    }

    /// `(c *Checker) getConstraintOfTypeParameter` (checker.go:17446).
    pub(crate) fn get_constraint_of_type_parameter(
        &mut self,
        type_parameter: TypeId,
    ) -> Option<TypeId> {
        if self.has_non_circular_base_constraint(type_parameter) {
            return self.get_constraint_from_type_parameter(type_parameter);
        }
        None
    }

    /// `(c *Checker) hasNonCircularBaseConstraint` (checker.go:17453).
    pub(crate) fn has_non_circular_base_constraint(&mut self, t: TypeId) -> bool {
        self.get_resolved_base_constraint(t, None) != Some(self.circular_constraint_type)
    }

    /// `(c *Checker) getConstraintFromTypeParameter` (checker.go:17458) —
    /// worker; use `get_constraint_of_type_parameter` which guards against
    /// circular constraints.
    pub(crate) fn get_constraint_from_type_parameter(&mut self, t: TypeId) -> Option<TypeId> {
        if !self.types.get(t).flags.intersects(TypeFlags::TYPE_PARAMETER) {
            return None;
        }
        if self
            .types
            .get(t)
            .as_type_parameter()
            .constraint
            .is_none()
        {
            let (target, mapper) = {
                let tp = self.types.get(t).as_type_parameter();
                (tp.target, tp.mapper)
            };
            let constraint = if let Some(target) = target {
                self.instantiate_type(
                    self.get_constraint_of_type_parameter(target)
                        .unwrap_or(self.no_constraint_type),
                    mapper,
                )
            } else if let Some(constraint_declaration) = self.get_constraint_declaration(t) {
                let mut constraint = self.get_type_from_type_node(constraint_declaration);
                if self
                    .types
                    .get(constraint)
                    .flags
                    .intersects(TypeFlags::ANY)
                    && !self.is_error_type(constraint)
                {
                    // use stringNumberSymbolType as the base constraint for mapped
                    // type key constraints (unknown isn't assignable to that, but
                    // `any` was), use unknown otherwise
                    let nodes = self.program_nodes(constraint_declaration);
                    let grandparent = nodes[constraint_declaration]
                        .parent
                        .and_then(|p| nodes[p].parent);
                    if grandparent.is_some_and(|gp| ast::is_mapped_type_node(&nodes[gp])) {
                        constraint = self.string_number_symbol_type;
                    } else {
                        constraint = self.unknown_type;
                    }
                }
                Some(constraint)
            } else {
                self.get_inferred_type_parameter_constraint(t, false)
            };
            let constraint = constraint.unwrap_or(self.no_constraint_type);
            self.types
                .get_mut(t)
                .as_type_parameter_mut()
                .constraint = Some(constraint);
        }
        let constraint = self.types.get(t).as_type_parameter().constraint.unwrap();
        if constraint != self.no_constraint_type {
            return Some(constraint);
        }
        None
    }

    /// `(c *Checker) getConstraintOrUnknownFromTypeParameter` (checker.go:17496).
    pub(crate) fn get_constraint_or_unknown_from_type_parameter(&mut self, t: TypeId) -> TypeId {
        self.get_constraint_from_type_parameter(t)
            .unwrap_or(self.unknown_type)
    }

    /// `(c *Checker) getInferredTypeParameterConstraint` (checker.go:17501).
    pub(crate) fn get_inferred_type_parameter_constraint(
        &mut self,
        t: TypeId,
        omit_type_references: bool,
    ) -> Option<TypeId> {
        let mut inferences: Vec<TypeId> = Vec::new();
        let declarations = self
            .types
            .get(t)
            .symbol
            .map(|s| self.sym(s).declarations.clone())
            .unwrap_or_default();
        for declaration in declarations {
            let nodes = self.program_nodes(declaration);
            let Some(decl_parent) = nodes[declaration].parent else {
                continue;
            };
            if !ast::is_infer_type_node(&nodes[decl_parent]) {
                continue;
            }
            // When an 'infer T' declaration is immediately contained in a type
            // reference node (such as 'Foo<infer T>'), T's constraint is inferred
            // from the constraint of the corresponding type parameter in 'Foo'.
            // When multiple 'infer T' declarations are present, we form an
            // intersection of the inferred constraint types.
            let mut child = decl_parent;
            let mut parent = nodes[child].parent;
            while let Some(p) = parent {
                if !ast::is_parenthesized_type_node(&nodes[p]) {
                    break;
                }
                child = p;
                parent = nodes[p].parent;
            }
            let Some(parent) = parent else {
                continue;
            };
            if ast::is_type_reference_node(&nodes[parent]) && !omit_type_references {
                if let Some(type_parameters) =
                    self.get_type_parameters_for_type_reference_or_import(parent)
                {
                    let index = nodes[parent]
                        .type_arguments()
                        .unwrap_or(&[])
                        .iter()
                        .position(|&a| a == child);
                    if let Some(index) = index
                        && index < type_parameters.len()
                    {
                        if let Some(declared_constraint) =
                            self.get_constraint_of_type_parameter(type_parameters[index])
                        {
                            // Type parameter constraints can reference other type
                            // parameters so constraints need to be instantiated. If
                            // instantiation produces the type parameter itself, we
                            // discard that inference. For example, in
                            //   type Foo<T extends string, U extends T> = [T, U];
                            //   type Bar<T> = T extends Foo<infer X, infer X> ? Foo<X, X> : T;
                            // the instantiated constraint for U is X, so we discard
                            // that inference.
                            let sources = type_parameters.clone();
                            let targets: Vec<Box<dyn Fn(&mut Checker) -> TypeId>> =
                                type_parameters
                                    .iter()
                                    .enumerate()
                                    .map(|(index, _)| {
                                        let sources = sources.clone();
                                        Box::new(move |c: &mut Checker| {
                                            c.get_effective_type_argument_at_index(
                                                parent, &sources, index,
                                            )
                                        })
                                            as Box<dyn Fn(&mut Checker) -> TypeId>
                                    })
                                    .collect();
                            let mapper = new_deferred_type_mapper(self, type_parameters, targets);
                            let constraint =
                                self.instantiate_type(declared_constraint, Some(mapper));
                            if constraint != t {
                                inferences.push(constraint);
                            }
                        }
                    }
                }
            } else if ast::is_parameter_declaration(&nodes[parent])
                && nodes[parent]
                    .as_parameter_declaration()
                    .dot_dot_dot_token
                    .is_some()
                || ast::is_rest_type_node(&nodes[parent])
                || ast::is_named_tuple_member(&nodes[parent])
                    && nodes[parent]
                        .as_named_tuple_member()
                        .dot_dot_dot_token
                        .is_some()
            {
                inferences.push(self.create_array_type(self.unknown_type));
            } else if ast::is_template_literal_type_span(&nodes[parent]) {
                inferences.push(self.string_type);
            } else if ast::is_type_parameter_declaration(&nodes[parent])
                && nodes[parent]
                    .parent
                    .is_some_and(|p| ast::is_mapped_type_node(&nodes[p]))
            {
                inferences.push(self.string_number_symbol_type);
            } else if ast::is_mapped_type_node(&nodes[parent])
                && nodes[parent].type_().is_some()
                && ast::skip_parentheses(nodes[parent].type_().unwrap(), &nodes)
                    == nodes[declaration].parent.unwrap()
                && nodes[parent]
                    .parent
                    .is_some_and(|p| ast::is_conditional_type_node(&nodes[p]))
                && {
                    let parent_parent = nodes[parent].parent.unwrap();
                    nodes[parent_parent]
                        .as_conditional_type_node()
                        .extends_type
                        == Some(parent)
                }
                && {
                    let parent_parent = nodes[parent].parent.unwrap();
                    let check_type =
                        nodes[parent_parent].as_conditional_type_node().check_type;
                    check_type.is_some_and(|ct| ast::is_mapped_type_node(&nodes[ct]))
                        && check_type.is_some_and(|ct| nodes[ct].type_().is_some())
                }
            {
                let parent_parent = nodes[parent].parent.unwrap();
                let check_mapped_type =
                    nodes[parent_parent].as_conditional_type_node().check_type.unwrap();
                let node_type =
                    self.get_type_from_type_node(nodes[check_mapped_type].type_().unwrap());
                let check_mapped_type_parameter =
                    nodes[check_mapped_type].as_mapped_type_node().type_parameter;
                let declared = self.get_declared_type_of_type_parameter(
                    self.get_symbol_of_declaration(check_mapped_type_parameter)
                        .expect("type parameter symbol"),
                );
                let constraint_node = nodes[check_mapped_type_parameter]
                    .as_type_parameter_declaration()
                    .constraint;
                let target = if let Some(constraint_node) = constraint_node {
                    self.get_type_from_type_node(constraint_node)
                } else {
                    self.string_number_symbol_type
                };
                let mapper = new_simple_type_mapper(self, declared, target);
                inferences.push(self.instantiate_type(node_type, Some(mapper)));
            }
        }
        if !inferences.is_empty() {
            return Some(self.get_intersection_type(&inferences));
        }
        None
    }

    /// `(c *Checker) getTypeParametersForTypeReferenceOrImport` (checker.go:17574).
    pub(crate) fn get_type_parameters_for_type_reference_or_import(
        &mut self,
        node: NodeId,
    ) -> Option<Vec<TypeId>> {
        let t = self.get_type_from_type_node(node);
        if !self.is_error_type(t) {
            if let Some(symbol) = self.get_resolved_symbol_or_nil(node) {
                return self.get_type_parameters_for_type_and_symbol(t, symbol);
            }
        }
        None
    }

    /// `(c *Checker) getTypeParametersForTypeAndSymbol` (checker.go:17585).
    pub(crate) fn get_type_parameters_for_type_and_symbol(
        &mut self,
        t: TypeId,
        symbol: SymbolId,
    ) -> Option<Vec<TypeId>> {
        if !self.is_error_type(t) {
            if self.sym(symbol).flags.intersects(ast::SymbolFlags::TYPE_ALIAS) {
                let type_parameters = self.type_alias_links.get(symbol).type_parameters.clone();
                if !type_parameters.is_empty() {
                    return Some(type_parameters);
                }
            }
            if self.types.get(t).object_flags.intersects(ObjectFlags::REFERENCE) {
                let target = self.types.get(t).target().unwrap();
                let d = self.types.get(target).as_interface_type();
                return Some(d.local_type_parameters().to_vec());
            }
        }
        None
    }

    /// `(c *Checker) getEffectiveTypeArgumentAtIndex` (checker.go:17599).
    pub(crate) fn get_effective_type_argument_at_index(
        &mut self,
        node: NodeId,
        type_parameters: &[TypeId],
        index: usize,
    ) -> TypeId {
        let nodes = self.program_nodes(node);
        let type_arguments = nodes[node].type_arguments().unwrap_or(&[]).to_vec();
        if index < type_arguments.len() {
            return self.get_type_from_type_node(type_arguments[index]);
        }
        self.get_effective_type_arguments(node, type_parameters)[index]
    }

    /// `(c *Checker) getConstraintOfIndexedAccess` (checker.go:17607).
    pub(crate) fn get_constraint_of_indexed_access(&mut self, t: TypeId) -> Option<TypeId> {
        if self.has_non_circular_base_constraint(t) {
            return self.get_constraint_from_indexed_access(t);
        }
        None
    }

    /// `(c *Checker) getConstraintFromIndexedAccess` (checker.go:17614).
    pub(crate) fn get_constraint_from_indexed_access(&mut self, t: TypeId) -> Option<TypeId> {
        let (object_type, index_type, access_flags) = {
            let d = self.types.get(t).as_indexed_access_type();
            (d.object_type.unwrap(), d.index_type.unwrap(), d.access_flags)
        };
        if self.is_mapped_type_generic_indexed_access(t) {
            // For indexed access types of the form { [P in K]: E }[X], where K is
            // non-generic and X is generic, we substitute an instantiation of E
            // where P is replaced with X.
            return Some(self.substitute_indexed_mapped_type(object_type, index_type));
        }
        if let Some(index_constraint) = self.get_simplified_type_or_constraint(index_type)
            && index_constraint != index_type
        {
            if let Some(indexed_access) = self.get_indexed_access_type_or_undefined(
                object_type,
                index_constraint,
                access_flags,
                None,
                None,
            ) {
                return Some(indexed_access);
            }
        }
        if let Some(object_constraint) = self.get_simplified_type_or_constraint(object_type)
            && object_constraint != object_type
        {
            return self.get_indexed_access_type_or_undefined(
                object_constraint,
                index_type,
                access_flags,
                None,
                None,
            );
        }
        None
    }

    /// `(c *Checker) getConstraintOfConditionalType` (checker.go:17635).
    pub(crate) fn get_constraint_of_conditional_type(&mut self, t: TypeId) -> Option<TypeId> {
        if self.has_non_circular_base_constraint(t) {
            return self.get_constraint_from_conditional_type(t);
        }
        None
    }

    /// `(c *Checker) getConstraintFromConditionalType` (checker.go:17642).
    pub(crate) fn get_constraint_from_conditional_type(&mut self, t: TypeId) -> Option<TypeId> {
        if let Some(constraint) = self.get_constraint_of_distributive_conditional_type(t) {
            return Some(constraint);
        }
        Some(self.get_default_constraint_of_conditional_type(t))
    }

    /// `(c *Checker) getDefaultConstraintOfConditionalType` (checker.go:17650).
    pub(crate) fn get_default_constraint_of_conditional_type(&mut self, t: TypeId) -> TypeId {
        if self
            .types
            .get(t)
            .as_conditional_type()
            .resolved_default_constraint
            .is_none()
        {
            // An `any` branch of a conditional type would normally be viral —
            // specifically, without special handling here, a conditional type
            // with a single branch of type `any` would be assignable to
            // anything, since its constraint would simplify to just `any`. This
            // result is _usually_ unwanted — so instead here we elide an `any`
            // branch from the constraint type, in effect treating `any` like
            // `never` rather than `unknown` in this location.
            let true_constraint = self.get_inferred_true_type_from_conditional_type(t);
            let false_constraint = self.get_false_type_from_conditional_type(t);
            let resolved = if crate::utilities::is_type_any(&self.types, true_constraint) {
                false_constraint
            } else if crate::utilities::is_type_any(&self.types, false_constraint) {
                true_constraint
            } else {
                self.get_union_type(&[true_constraint, false_constraint])
            };
            self.types
                .get_mut(t)
                .data
                .as_conditional_type_mut()
                .unwrap()
                .resolved_default_constraint = Some(resolved);
        }
        self.types
            .get(t)
            .as_conditional_type()
            .resolved_default_constraint
            .unwrap()
    }

    /// `(c *Checker) getConstraintOfDistributiveConditionalType` (checker.go:17671).
    pub(crate) fn get_constraint_of_distributive_conditional_type(
        &mut self,
        t: TypeId,
    ) -> Option<TypeId> {
        if self
            .types
            .get(t)
            .as_conditional_type()
            .resolved_constraint_of_distributive
            .is_none()
        {
            // Check if we have a conditional type of the form 'T extends U ? X : Y',
            // where T is a constrained type parameter. If so, create an
            // instantiation of the conditional type where T is replaced with its
            // constraint. We do this because if the constraint is a union type it
            // will be distributed over the conditional type and possibly reduced.
            // For example, 'T extends undefined ? never : T' removes 'undefined'
            // from T.
            // We skip returning a distributive constraint for a restrictive
            // instantiation of a conditional type as the constraint for all type
            // params (check type included) have been replace with `unknown`, which
            // is going to produce even more false positive/negative results than
            // the distribute constraint already does.
            // Please note: the distributive constraint is a kludge for emulating
            // what a negated type could to do filter a union - once negated types
            // exist and are applied to the conditional false branch, this
            // "constraint" likely doesn't need to exist.
            let (is_distributive, root_check_type, check_type, mapper) = {
                let d = self.types.get(t).as_conditional_type();
                let root = d.root.as_ref().unwrap();
                (
                    root.is_distributive,
                    root.check_type.unwrap(),
                    d.check_type.unwrap(),
                    d.mapper,
                )
            };
            let restrictive_hit = self
                .cached_types
                .get(&crate::checker_types::CachedTypeKey {
                    kind: crate::checker_types::CachedTypeKind::RestrictiveInstantiation,
                    type_id: t,
                })
                .is_some_and(|&cached| cached == t);
            if is_distributive && !restrictive_hit {
                let mut constraint = self.get_simplified_type(check_type, false /*writing*/);
                if constraint == check_type {
                    constraint = self.get_constraint_of_type(constraint);
                }
                if let Some(constraint) = constraint
                    && constraint != check_type
                {
                    let m = prepend_type_mapping(self, root_check_type, constraint, mapper);
                    let instantiated =
                        self.get_conditional_type_instantiation(t, m, true /*forConstraint*/, None);
                    if !self
                        .types
                        .get(instantiated)
                        .flags
                        .intersects(TypeFlags::NEVER)
                    {
                        self.types
                            .get_mut(t)
                            .data
                            .as_conditional_type_mut()
                            .unwrap()
                            .resolved_constraint_of_distributive = Some(instantiated);
                        return Some(instantiated);
                    }
                }
            }
            self.types
                .get_mut(t)
                .data
                .as_conditional_type_mut()
                .unwrap()
                .resolved_constraint_of_distributive = Some(self.no_constraint_type);
        }
        let resolved = self
            .types
            .get(t)
            .as_conditional_type()
            .resolved_constraint_of_distributive
            .unwrap();
        if resolved != self.no_constraint_type {
            return Some(resolved);
        }
        None
    }

    /// `(c *Checker) getDeclaredTypeOfClassOrInterface` (checker.go:17706).
    pub(crate) fn get_declared_type_of_class_or_interface(&mut self, symbol: SymbolId) -> TypeId {
        if self
            .declared_type_links
            .get(symbol)
            .declared_type
            .is_none()
        {
            let kind = if self.sym(symbol).flags.intersects(ast::SymbolFlags::CLASS) {
                ObjectFlags::CLASS
            } else {
                ObjectFlags::INTERFACE
            };
            let t = self.new_object_type(kind, Some(symbol));
            self.declared_type_links.get(symbol).declared_type = Some(t);
            let outer_type_parameters = self
                .get_outer_type_parameters_of_class_or_interface(symbol)
                .unwrap_or_default();
            let type_parameters = self
                .append_local_type_parameters_of_class_or_interface_or_type_alias(
                    outer_type_parameters.clone(),
                    symbol,
                );
            // A class or interface is generic if it has type parameters or a
            // "this" type. We always give classes a "this" type because it is not
            // feasible to analyze all members to determine if the "this" type
            // escapes the class (in particular, property types inferred from
            // initializers and method return types inferred from return
            // statements are very hard to exhaustively analyze). We give
            // interfaces a "this" type if we can't definitely determine that they
            // are free of "this" references.
            let type_parameters = type_parameters.unwrap_or_default();
            if !type_parameters.is_empty()
                || kind == ObjectFlags::CLASS
                || !self.is_thisless_interface(symbol)
            {
                self.types.get_mut(t).object_flags.insert(ObjectFlags::REFERENCE);
                let this_type = self.new_type_parameter(Some(symbol));
                self.types
                    .get_mut(this_type)
                    .as_type_parameter_mut()
                    .is_this_type = true;
                self.types
                    .get_mut(this_type)
                    .as_type_parameter_mut()
                    .constraint = Some(t);
                let mut all = type_parameters.clone();
                all.push(this_type);
                {
                    let mut g = self.types.get_mut(t);
                    let d = g.data.as_interface_type_mut().unwrap();
                    d.this_type = Some(this_type);
                    d.all_type_parameters = all;
                    d.outer_type_parameter_count = outer_type_parameters.len();
                    d.type_reference.resolved_type_arguments =
                        d.type_parameters().to_vec();
                }
                let key = get_type_list_key(
                    &self.types.get(t).as_interface_type().unwrap().type_reference.resolved_type_arguments,
                );
                let mut g = self.types.get_mut(t);
                let d = g.data.as_interface_type_mut().unwrap();
                d.type_reference.object_type.instantiations.insert(key, t);
                d.type_reference.object_type.target = Some(t);
            }
        }
        self.declared_type_links.get(symbol).declared_type.unwrap()
    }

    /// `(c *Checker) isThislessInterface` (checker.go:17743) — returns true if
    /// the interface given by the symbol is free of "this" references.
    ///
    /// Specifically, the result is true if the interface itself contains no
    /// references to "this" in its body, if all base types are interfaces,
    /// and if none of the base interfaces have a "this" type.
    pub(crate) fn is_thisless_interface(&mut self, symbol: SymbolId) -> bool {
        let declarations = self.sym(symbol).declarations.clone();
        for declaration in declarations {
            let nodes = self.program_nodes(declaration);
            if ast::is_interface_declaration(&nodes[declaration]) {
                if nodes[declaration].flags.intersects(ast::NodeFlags::CONTAINS_THIS) {
                    return false;
                }
                let base_type_nodes: Vec<NodeId> =
                    ast::get_extends_heritage_clause_elements(&nodes[declaration], &nodes)
                        .map(|s| s.to_vec())
                        .unwrap_or_default();
                for node in base_type_nodes {
                    let name = ast::get_heritage_clause_element_name(&nodes[node], &nodes);
                    if let Some(name) = name
                        && (ast::is_entity_name(&nodes[name])
                            || ast::is_entity_name_expression(&nodes[name], &nodes))
                    {
                        let base_symbol = self.resolve_entity_name(
                            name,
                            ast::SymbolFlags::TYPE,
                            true,  /*ignoreErrors*/
                            false,
                            None,
                        );
                        let ok = base_symbol.is_some_and(|base_symbol| {
                            self.sym(base_symbol)
                                .flags
                                .intersects(ast::SymbolFlags::INTERFACE)
                                && {
                                    let declared = self
                                        .get_declared_type_of_class_or_interface(base_symbol);
                                    self.types
                                        .get(declared)
                                        .as_interface_type()
                                        .is_some_and(|d| d.this_type.is_none())
                                }
                        });
                        if !ok {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }

    /// `(c *Checker) isNullOrUndefined` (checker.go:18070).
    pub(crate) fn is_null_or_undefined(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let expr = ast::skip_parentheses(node, &nodes);
        match nodes[expr].kind {
            ast::Kind::NullKeyword => true,
            ast::Kind::Identifier => self.get_resolved_symbol_or_nil(expr) == Some(self.undefined_symbol),
            _ => false,
        }
    }

    /// `(c *Checker) checkRightHandSideOfForOf` (checker.go:18081).
    pub(crate) fn check_right_hand_side_of_for_of(&mut self, statement: NodeId) -> TypeId {
        let nodes = self.program_nodes(statement);
        let r#use = if nodes[statement]
            .as_for_in_or_of_statement()
            .await_modifier
            .is_some()
        {
            crate::checker_types::IterationUse::FOR_AWAIT_OF
        } else {
            crate::checker_types::IterationUse::FOR_OF
        };
        let expression = nodes[statement].expression().unwrap();
        let input_type = self.check_non_null_expression(expression);
        self.check_iterated_type_or_element_type(r#use, input_type, self.undefined_type, Some(expression))
    }

    /// `(c *Checker) getTypeForBindingElement` (checker.go:18087) — return the
    /// inferred type for a binding element.
    pub(crate) fn get_type_for_binding_element(&mut self, declaration: NodeId) -> Option<TypeId> {
        let nodes = self.program_nodes(declaration);
        let check_mode = if crate::utilities::has_dot_dot_dot_token(&nodes[declaration]) {
            CheckMode::REST_BINDING_ELEMENT
        } else {
            CheckMode::NORMAL
        };
        let parent_parent = nodes[declaration].parent.and_then(|p| nodes[p].parent);
        let parent_type = parent_parent
            .and_then(|pp| self.get_type_for_binding_element_parent(pp, check_mode));
        if let Some(parent_type) = parent_type {
            return Some(self.get_binding_element_type_from_parent_type(
                declaration,
                parent_type,
                false, /*noTupleBoundsCheck*/
            ));
        }
        None
    }

    /// `(c *Checker) getTypeForBindingElementParent` (checker.go:18098) —
    /// return the type of a binding element parent. We check SymbolLinks
    /// first to see if a type has been assigned by contextual typing.
    pub(crate) fn get_type_for_binding_element_parent(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> Option<TypeId> {
        if check_mode == CheckMode::NORMAL {
            // We can use a cached resolved type if no optionality was included in that type.
            if let Some(symbol) = self.get_symbol_of_declaration(node) {
                let resolved_type = self.value_symbol_links.get(symbol).resolved_type;
                if let Some(resolved_type) = resolved_type {
                    let nodes = self.program_nodes(node);
                    if !(self.strict_null_checks
                        && crate::utilities::is_optional_declaration(&nodes[node]))
                    {
                        return Some(resolved_type);
                    }
                }
            }
        }
        Some(self.get_type_for_variable_like_declaration(
            node,
            false, /*includeOptionality*/
            check_mode,
        ))
    }

    /// `(c *Checker) getBindingElementTypeFromParentType` (checker.go:18110).
    pub(crate) fn get_binding_element_type_from_parent_type(
        &mut self,
        declaration: NodeId,
        parent_type: TypeId,
        no_tuple_bounds_check: bool,
    ) -> TypeId {
        // If an any type was inferred for parent, infer that for the binding element
        if crate::utilities::is_type_any(&self.types, parent_type) {
            return parent_type;
        }
        let nodes = self.program_nodes(declaration);
        let pattern = nodes[declaration].parent.unwrap();
        let mut parent_type = parent_type;
        // Relax null check on ambient destructuring parameters, since the
        // parameters have no implementation and are just documentation
        if self.strict_null_checks
            && nodes[declaration].flags.intersects(ast::NodeFlags::AMBIENT)
            && ast::is_part_of_parameter_declaration(declaration, &nodes)
        {
            parent_type = self.get_non_nullable_type(parent_type);
        } else {
            let pattern_parent = nodes[pattern].parent.unwrap();
            if let Some(initializer) = nodes[pattern_parent].initializer() {
                let init_type = self.get_type_of_initializer(initializer);
                if self.strict_null_checks
                    && !self.has_type_facts(init_type, TypeFacts::EQ_UNDEFINED)
                {
                    parent_type =
                        self.get_type_with_facts(parent_type, TypeFacts::NE_UNDEFINED);
                }
            }
        }
        let access_flags = AccessFlags::EXPRESSION_POSITION
            | if no_tuple_bounds_check || self.has_default_value(declaration) {
                AccessFlags::ALLOW_MISSING
            } else {
                AccessFlags::NONE
            };
        let t: TypeId;
        match nodes[pattern].kind {
            ast::Kind::ObjectBindingPattern => {
                if crate::utilities::has_dot_dot_dot_token(&nodes[declaration]) {
                    parent_type = self.get_reduced_type(parent_type);
                    if self
                        .types
                        .get(parent_type)
                        .flags
                        .intersects(TypeFlags::UNKNOWN)
                        || !self.is_valid_spread_type(parent_type)
                    {
                        self.error(
                            Some(declaration),
                            &tsc_diagnostics::Rest_types_may_only_be_created_from_object_types,
                            &[],
                        );
                        return self.error_type;
                    }
                    let elements = nodes[pattern].elements().unwrap_or(&[]).to_vec();
                    let mut literal_members: Vec<NodeId> = Vec::with_capacity(elements.len());
                    for element in elements {
                        if !crate::utilities::has_dot_dot_dot_token(&nodes[element]) {
                            if let Some(name) = nodes[element].property_name_or_name() {
                                literal_members.push(name);
                            }
                        }
                    }
                    t = self.get_rest_type(
                        parent_type,
                        &literal_members,
                        nodes[declaration].symbol(),
                    );
                } else {
                    // Use explicitly specified property name ({ p: xxx } form), or
                    // otherwise the implied name ({ p } form)
                    let name = nodes[declaration].property_name_or_name().unwrap();
                    let index_type = self.get_literal_type_from_property_name(name);
                    let declared_type = self.get_indexed_access_type_ex(
                        parent_type,
                        index_type,
                        access_flags,
                        Some(name),
                        None,
                    );
                    t = self.get_flow_type_of_destructuring(declaration, declared_type);
                }
            }
            ast::Kind::ArrayBindingPattern => {
                // This elementType will be used if the specific property
                // corresponding to this index is not present (aka the tuple
                // element property). This call also checks that the parentType is
                // in fact an iterable or array (depending on target language).
                let element_type = self.check_iterated_type_or_element_type(
                    crate::checker_types::IterationUse::DESTRUCTURING
                        | if crate::utilities::has_dot_dot_dot_token(&nodes[declaration]) {
                            crate::checker_types::IterationUse::NONE
                        } else {
                            crate::checker_types::IterationUse::POSSIBLY_OUT_OF_BOUNDS
                        },
                    parent_type,
                    self.undefined_type,
                    Some(pattern),
                );
                let index = nodes[pattern]
                    .elements()
                    .unwrap_or(&[])
                    .iter()
                    .position(|&e| e == declaration)
                    .unwrap();
                if crate::utilities::has_dot_dot_dot_token(&nodes[declaration]) {
                    // If the parent is a tuple type, the rest element has a tuple
                    // type of the remaining tuple element types. Otherwise, the
                    // rest element has an array type with same element type as
                    // the parent type.
                    let base_constraint = self.map_type(
                        parent_type,
                        Rc::new(|c: &mut Checker, t: TypeId| {
                            if c.types
                                .get(t)
                                .flags
                                .intersects(TypeFlags::INSTANTIABLE_NON_PRIMITIVE)
                            {
                                return c.get_base_constraint_or_type(t);
                            }
                            t
                        }),
                    );
                    if crate::checker_d::every_type(self, base_constraint, |c: &mut Checker, t| {
                        is_tuple_type(&c.types, t)
                    }) {
                            t = self.map_type(
                            base_constraint,
                            Rc::new(move |c: &mut Checker, t: TypeId| {
                                c.slice_tuple_type(t, index, 0)
                            }),
                        );
                    } else {
                        t = self.create_array_type(element_type);
                    }
                } else if self.is_array_like_type(parent_type) {
                    let index_type = self.get_number_literal_type(tsc_jsnum::Number(index as f64));
                    let declared_type = self
                        .get_indexed_access_type_or_undefined(
                            parent_type,
                            index_type,
                            access_flags,
                            nodes[declaration].name(),
                            None,
                        )
                        .unwrap_or(self.error_type);
                    t = self.get_flow_type_of_destructuring(declaration, declared_type);
                } else {
                    t = element_type;
                }
            }
            _ => panic!("Unhandled case in getBindingElementTypeFromParentType"),
        }
        if nodes[declaration].initializer().is_none() {
            return t;
        }
        if ast::walk_up_binding_elements_and_patterns(declaration, &nodes)
            .is_some_and(|walked| nodes[walked].type_().is_some())
        {
            // In strict null checking mode, if a default value of a non-undefined
            // type is specified, remove undefined from the final type.
            if self.strict_null_checks
                && !self.has_type_facts(
                    self.check_declaration_initializer(declaration, CheckMode::NORMAL, None),
                    TypeFacts::IS_UNDEFINED,
                )
            {
                return self.get_non_undefined_type(t);
            }
            return t;
        }
        self.widen_type_inferred_from_initializer(
            declaration,
            self.get_union_type_ex(
                &[
                    self.get_non_undefined_type(t),
                    self.check_declaration_initializer(declaration, CheckMode::NORMAL, None),
                ],
                crate::checker_types::UnionReduction::Subtype,
                None,
                None,
            ),
        )
    }

    /// `(c *Checker) getRestType` (checker.go:18195).
    pub(crate) fn get_rest_type(
        &mut self,
        source: TypeId,
        properties: &[NodeId],
        symbol: Option<SymbolId>,
    ) -> TypeId {
        let source = self.filter_type(source, &|_c: &mut Checker, t: TypeId| {
            _c.types.get(t).flags.intersects(TypeFlags::NULLABLE) == false
        });
        if self.types.get(source).flags.intersects(TypeFlags::NEVER) {
            return self.empty_object_type;
        }
        if self.types.get(source).flags.intersects(TypeFlags::UNION) {
            let properties = properties.to_vec();
            return self.map_type(
                source,
                Rc::new(move |c: &mut Checker, t: TypeId| {
                    c.get_rest_type(t, &properties, symbol)
                }),
            );
        }
        let key_types: Vec<TypeId> = properties
            .iter()
            .map(|&p| self.get_literal_type_from_property_name(p))
            .collect();
        let mut omit_key_type = self.get_union_type(&key_types);
        let mut spreadable_properties: Vec<SymbolId> = Vec::new();
        let mut unspreadable_to_rest_keys: Vec<TypeId> = Vec::new();
        for prop in self.get_properties_of_type(source) {
            let literal_type_from_property = self.get_literal_type_from_property(
                prop,
                TypeFlags::STRING_OR_NUMBER_LITERAL_OR_UNIQUE,
                false,
            );
            let modifier_flags = {
                let arena = self.symbol_arena.borrow();
                crate::utilities::get_declaration_modifier_flags_from_symbol(
                    &arena[prop.index()],
                    &self.program_nodes_for_symbol(prop),
                )
            };
            if !self.is_type_assignable_to(literal_type_from_property, omit_key_type)
                && !modifier_flags
                    .intersects(ast::ModifierFlags::PRIVATE | ast::ModifierFlags::PROTECTED)
                && self.is_spreadable_property(prop)
            {
                spreadable_properties.push(prop);
            } else {
                unspreadable_to_rest_keys.push(literal_type_from_property);
            }
        }
        if self.is_generic_object_type(source) || self.is_generic_index_type(omit_key_type) {
            if !unspreadable_to_rest_keys.is_empty() {
                // If the type we're spreading from has properties that cannot
                // be spread into the rest type (e.g. getters, methods), ensure
                // they are explicitly omitted, as they would in the non-generic
                // case.
                let mut keys = vec![omit_key_type];
                keys.extend(unspreadable_to_rest_keys);
                omit_key_type = self.get_union_type(&keys);
            }
            if self
                .types
                .get(omit_key_type)
                .flags
                .intersects(TypeFlags::NEVER)
            {
                return source;
            }
            let Some(omit_type_alias) = self.get_global_omit_symbol() else {
                return self.error_type;
            };
            return self.get_type_alias_instantiation(
                omit_type_alias,
                &[source, omit_key_type],
                None,
            );
        }
        let mut members = SymbolTable::new();
        for prop in spreadable_properties {
            let name = self.sym(prop).name.clone();
            let spread = self.get_spread_symbol(prop, false /*readonly*/);
            members.set(name, spread);
        }
        let index_infos = self.get_index_infos_of_type(source);
        let result = self.new_anonymous_type(
            symbol,
            members,
            &[],
            &[],
            &index_infos,
        );
        self.types
            .get_mut(result)
            .object_flags
            .insert(ObjectFlags::OBJECT_REST_TYPE);
        result
    }

    /// `(c *Checker) getFlowTypeOfDestructuring` (checker.go:18252) — determine
    /// the control flow type associated with a destructuring declaration or
    /// assignment by constructing a synthetic element access expression.
    pub(crate) fn get_flow_type_of_destructuring(
        &mut self,
        node: NodeId,
        declared_type: TypeId,
    ) -> TypeId {
        if let Some(reference) = self.get_synthetic_element_access(node) {
            return self.get_flow_type_of_reference(reference, declared_type);
        }
        declared_type
    }

    /// `(c *Checker) getSyntheticElementAccess` (checker.go:18260).
    pub(crate) fn get_synthetic_element_access(&mut self, node: NodeId) -> Option<NodeId> {
        let parent_access = self.get_parent_element_access(node);
        if let Some(parent_access) = parent_access {
            let nodes = self.program_nodes(node);
            if crate::flow::get_flow_node_of_node(&nodes, parent_access).is_some() {
                let (prop_name, ok) = self.get_destructuring_property_name(&nodes, node);
                if ok {
                    let file_index = node.file_index();
                    let node_loc = nodes[node].loc;
                    drop(nodes);
                    let mut arena = self.program_nodes_mut(file_index);
                    let literal =
                        self.factory.new_string_literal(&mut arena, &prop_name, ast::TokenFlags::NONE);
                    arena[literal].loc = node_loc;
                    let mut lhs_expr = parent_access;
                    if !ast::is_left_hand_side_expression(&arena[parent_access], &arena) {
                        lhs_expr = self
                            .factory
                            .new_parenthesized_expression(&mut arena, Some(parent_access));
                        arena[lhs_expr].loc = node_loc;
                    }
                    let result = self.factory.new_element_access_expression(
                        &mut arena,
                        Some(lhs_expr),
                        None,
                        Some(literal),
                        ast::NodeFlags::NONE,
                    );
                    arena[result].loc = node_loc;
                    arena[literal].parent = Some(result);
                    arena[result].parent = Some(node);
                    if lhs_expr != parent_access {
                        arena[lhs_expr].parent = Some(result);
                    }
                    let flow_node = {
                        let nodes = self.program_nodes(node);
                        crate::flow::get_flow_node_of_node(&nodes, parent_access)
                    };
                    arena[result]
                        .as_element_access_expression_mut()
                        .flow_node_base
                        .flow_node = flow_node;
                    return Some(result);
                }
            }
        }
        None
    }

    /// `(c *Checker) getParentElementAccess` (checker.go:18285).
    pub(crate) fn get_parent_element_access(&mut self, node: NodeId) -> Option<NodeId> {
        let nodes = self.program_nodes(node);
        let ancestor = nodes[node].parent.and_then(|p| nodes[p].parent)?;
        match nodes[ancestor].kind {
            ast::Kind::BindingElement | ast::Kind::PropertyAssignment => {
                self.get_synthetic_element_access(ancestor)
            }
            ast::Kind::ArrayLiteralExpression => {
                self.get_synthetic_element_access(nodes[node].parent.unwrap())
            }
            ast::Kind::VariableDeclaration => nodes[ancestor].initializer(),
            ast::Kind::BinaryExpression => nodes[ancestor].as_binary_expression().right,
            _ => None,
        }
    }

    /// `(c *Checker) getTypeFromBindingPattern` (checker.go:18307) — return the
    /// type implied by a binding pattern.
    pub(crate) fn get_type_from_binding_pattern(
        &mut self,
        pattern: NodeId,
        include_pattern_in_type: bool,
        report_errors: bool,
    ) -> TypeId {
        if include_pattern_in_type {
            self.contextual_binding_patterns.push(pattern);
        }
        let nodes = self.program_nodes(pattern);
        let result = if ast::is_object_binding_pattern(&nodes[pattern]) {
            self.get_type_from_object_binding_pattern(
                pattern,
                include_pattern_in_type,
                report_errors,
            )
        } else {
            self.get_type_from_array_binding_pattern(
                pattern,
                include_pattern_in_type,
                report_errors,
            )
        };
        if include_pattern_in_type {
            self.contextual_binding_patterns.pop();
        }
        result
    }

    /// `(c *Checker) getTypeFromObjectBindingPattern` (checker.go:18324) —
    /// return the type implied by an object binding pattern.
    pub(crate) fn get_type_from_object_binding_pattern(
        &mut self,
        pattern: NodeId,
        include_pattern_in_type: bool,
        report_errors: bool,
    ) -> TypeId {
        let mut members = SymbolTable::new();
        let mut string_index_info: Option<IndexInfoId> = None;
        let mut object_flags =
            ObjectFlags::OBJECT_LITERAL | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL;
        let nodes = self.program_nodes(pattern);
        let elements = nodes[pattern].elements().unwrap_or(&[]).to_vec();
        for e in elements {
            let name = nodes[e].property_name_or_name().unwrap();
            if crate::utilities::has_dot_dot_dot_token(&nodes[e]) {
                string_index_info = Some(self.new_index_info(
                    self.string_type,
                    self.any_type,
                    false, /*isReadonly*/
                    None,
                    vec![],
                ));
                continue;
            }
            let expr_type = self.get_literal_type_from_property_name(name);
            if !crate::utilities::is_type_usable_as_property_name(&self.types, expr_type) {
                // do not include computed properties in the implied type
                object_flags.insert(ObjectFlags::OBJECT_LITERAL_PATTERN_WITH_COMPUTED_PROPERTIES);
                continue;
            }
            let text = crate::utilities::get_property_name_from_type(&self.types, expr_type);
            let mut flags = ast::SymbolFlags::PROPERTY;
            if nodes[e].initializer().is_some() {
                flags |= ast::SymbolFlags::OPTIONAL;
            }
            let symbol = self.new_symbol(flags, &text);
            let t = self.get_type_from_binding_element(e, include_pattern_in_type, report_errors);
            self.value_symbol_links.get(symbol).resolved_type = Some(t);
            members.set(text, symbol);
        }
        let index_infos: Vec<IndexInfoId> = string_index_info
            .map(|id| vec![id])
            .unwrap_or_default();
        let result = self.new_anonymous_type(None, members, &[], &[], &index_infos);
        self.types.get_mut(result).object_flags.insert(object_flags);
        if include_pattern_in_type {
            self.pattern_for_type.write().unwrap().insert(result, pattern);
            self.types
                .get_mut(result)
                .object_flags
                .insert(ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL);
        }
        result
    }

    /// `(c *Checker) getTypeFromArrayBindingPattern` (checker.go:18360) —
    /// return the type implied by an array binding pattern.
    pub(crate) fn get_type_from_array_binding_pattern(
        &mut self,
        pattern: NodeId,
        include_pattern_in_type: bool,
        report_errors: bool,
    ) -> TypeId {
        let nodes = self.program_nodes(pattern);
        let elements = nodes[pattern].elements().unwrap_or(&[]).to_vec();
        let last_element = elements.last().copied();
        let rest_element = last_element.filter(|&e| {
            ast::is_binding_element(&nodes[e])
                && crate::utilities::has_dot_dot_dot_token(&nodes[e])
        });
        if elements.is_empty() || (elements.len() == 1 && rest_element.is_some()) {
            // TODO: remove ScriptTargetES2015
            if self.language_version >= ScriptTarget::ES2015 {
                return self.create_iterable_type(self.any_type);
            }
            return self.any_array_type;
        }
        let min_length = elements
            .iter()
            .rposition(|&e| {
                !(Some(e) == rest_element
                    || nodes[e].name().is_none()
                    || self.has_default_value(e))
            })
            .map(|i| i + 1)
            .unwrap_or(0);
        let mut element_types: Vec<TypeId> = Vec::with_capacity(elements.len());
        let mut element_infos: Vec<TupleElementInfo> = Vec::with_capacity(elements.len());
        for (i, &e) in elements.iter().enumerate() {
            let t = if nodes[e].name().is_none() {
                self.any_type
            } else {
                self.get_type_from_binding_element(e, include_pattern_in_type, report_errors)
            };
            let flags = if Some(e) == rest_element {
                ElementFlags::REST
            } else if i >= min_length {
                ElementFlags::OPTIONAL
            } else {
                ElementFlags::REQUIRED
            };
            element_types.push(t);
            element_infos.push(TupleElementInfo {
                flags,
                ..Default::default()
            });
        }
        let mut result = self.create_tuple_type_ex(&element_types, &element_infos, false);
        if include_pattern_in_type {
            result = self.clone_type_reference(result);
            self.pattern_for_type.write().unwrap().insert(result, pattern);
            self.types
                .get_mut(result)
                .object_flags
                .insert(ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL);
        }
        result
    }

    /// `(c *Checker) getTypeFromBindingElement` (checker.go:18409) — return the
    /// type implied by a binding pattern element.
    pub(crate) fn get_type_from_binding_element(
        &mut self,
        element: NodeId,
        include_pattern_in_type: bool,
        report_errors: bool,
    ) -> TypeId {
        let nodes = self.program_nodes(element);
        if nodes[element].initializer().is_some() {
            // The type implied by a binding pattern is independent of context, so
            // we check the initializer with no contextual type or, if the element
            // itself is a binding pattern, with the type implied by that binding
            // pattern.
            let mut contextual_type = self.unknown_type;
            if nodes[element]
                .name()
                .is_some_and(|n| ast::is_binding_pattern(&nodes[n]))
            {
                contextual_type = self.get_type_from_binding_pattern(
                    nodes[element].name().unwrap(),
                    true,  /*includePatternInType*/
                    false, /*reportErrors*/
                );
            }
            let init_type = self.check_declaration_initializer(
                element,
                CheckMode::NORMAL,
                Some(contextual_type),
            );
            return self.add_optionality(
                self.get_widened_literal_type_for_initializer(element, init_type),
            );
        }
        if nodes[element]
            .name()
            .is_some_and(|n| ast::is_binding_pattern(&nodes[n]))
        {
            return self.get_type_from_binding_pattern(
                nodes[element].name().unwrap(),
                include_pattern_in_type,
                report_errors,
            );
        }
        if report_errors && !self.declaration_belongs_to_private_ambient_member(element) {
            self.report_implicit_any(element, self.any_type, WideningKind::Normal);
        }
        // When we're including the pattern in the type (an indication we're
        // obtaining a contextual type), we use a non-inferrable any type.
        // Inference will never directly infer this type, but it is possible to
        // infer a type that contains it, e.g. for a binding pattern like [foo]
        // or { foo }. In such cases, widening of the binding pattern type
        // substitutes a regular any for the non-inferrable any.
        if include_pattern_in_type {
            return self.non_inferrable_any_type;
        }
        self.any_type
    }

    /// `(c *Checker) declarationBelongsToPrivateAmbientMember` (checker.go:18436).
    pub(crate) fn declaration_belongs_to_private_ambient_member(
        &mut self,
        declaration: NodeId,
    ) -> bool {
        let nodes = self.program_nodes(declaration);
        let mut member_declaration = ast::get_root_declaration(declaration, &nodes);
        if ast::is_parameter_declaration(&nodes[member_declaration]) {
            member_declaration = nodes[member_declaration].parent.unwrap();
        }
        crate::utilities::is_private_within_ambient(&nodes[member_declaration])
    }

    /// `(c *Checker) getTypeOfPrototypeProperty` (checker.go:18444) —
    /// TypeScript 1.0 spec (April 2014): 8.4: every class automatically
    /// contains a static property member named 'prototype', the type of which
    /// is an instantiation of the class type with type Any supplied as a type
    /// argument for each type parameter. It is an error to explicitly declare
    /// a static property member with the name 'prototype'.
    pub(crate) fn get_type_of_prototype_property(&mut self, prototype: SymbolId) -> TypeId {
        let parent = self.get_parent_of_symbol(prototype).unwrap();
        let class_type = self.get_declared_type_of_symbol(parent);
        let type_parameters = self
            .types
            .get(class_type)
            .as_interface_type()
            .map(|d| d.type_parameters().to_vec())
            .unwrap_or_default();
        if !type_parameters.is_empty() {
            let any_type = self.any_type;
            return self.create_type_reference(
                class_type,
                &core::map(&type_parameters, |_| any_type),
            );
        }
        class_type
    }

    /// `(c *Checker) getWidenedTypeForAssignmentDeclaration` (checker.go:18466).
    pub(crate) fn get_widened_type_for_assignment_declaration(
        &mut self,
        symbol: SymbolId,
    ) -> TypeId {
        let mut t: Option<TypeId> = None;
        let (kind, location) = self.is_constructor_declared_this_property(symbol);
        match kind {
            ThisAssignmentDeclarationKind::Typed => {
                let location = location.expect("location should not be nil when this assignment has a type.");
                t = Some(self.get_type_from_type_node(location));
            }
            ThisAssignmentDeclarationKind::Constructor => {
                let location = location.expect(
                    "constructor should not be nil when this assignment is in a constructor.",
                );
                t = self.get_flow_type_in_constructor(symbol, location);
            }
            ThisAssignmentDeclarationKind::Method => {
                t = self.get_type_of_property_in_base_class(symbol);
            }
            ThisAssignmentDeclarationKind::None => {}
        }
        if t.is_none() {
            let mut types: Vec<TypeId> = Vec::new();
            let declarations = self.sym(symbol).declarations.clone();
            let declaration_count = declarations.len();
            for (i, declaration) in declarations.iter().copied().enumerate() {
                let nodes = self.program_nodes(declaration);
                if ast::is_binary_expression(&nodes[declaration])
                    && nodes[declaration].type_().is_some()
                {
                    t = Some(self.get_type_from_type_node(nodes[declaration].type_().unwrap()));
                    break;
                }
                if let Some(assigned_type) =
                    self.get_assignment_declaration_initializer_type(declaration)
                {
                    // We ignore initial assignments of undefined to CommonJS
                    // exports when there are multiple assignment declarations
                    if ast::get_assignment_declaration_kind(declaration, &nodes)
                        != ast::JsDeclarationKind::ExportsProperty
                        || i != 0
                        || declaration_count == 1
                        || !self
                            .types
                            .get(assigned_type)
                            .flags
                            .intersects(TypeFlags::UNDEFINED)
                    {
                        if !types.contains(&assigned_type) {
                            types.push(assigned_type);
                        }
                    }
                }
            }
            if kind == ThisAssignmentDeclarationKind::Method && !types.is_empty() {
                if self.strict_null_checks {
                    if !types.contains(&self.undefined_or_missing_type) {
                        types.push(self.undefined_or_missing_type);
                    }
                }
            }
            if t.is_none() {
                let mut tt = self.any_type;
                if !types.is_empty() {
                    tt = self.get_union_type(&types);
                }
                t = Some(tt);
            }
        }
        let mut t = self.get_widened_type(t.unwrap());
        // report an all-nullable or empty union as an implicit any in JS files
        let value_declaration = self.sym(symbol).value_declaration;
        let filtered = self.filter_type(t, &|c: &mut Checker, u: TypeId| {
            c.types.get(u).flags & !TypeFlags::NULLABLE != TypeFlags::NONE
        });
        if value_declaration.is_some_and(|vd| ast::is_in_js_file(Some(vd), &self.program_nodes(vd)))
            && filtered == self.never_type
        {
            self.report_implicit_any(value_declaration.unwrap(), self.any_type, WideningKind::Normal);
            t = self.any_type;
        }
        t
    }

    /// `(c *Checker) getAssignmentDeclarationInitializerType` (checker.go:18519).
    pub(crate) fn get_assignment_declaration_initializer_type(
        &mut self,
        node: NodeId,
    ) -> Option<TypeId> {
        let nodes = self.program_nodes(node);
        if ast::is_binary_expression(&nodes[node]) {
            let t: TypeId;
            match ast::get_assignment_declaration_kind(node, &nodes) {
                ast::JsDeclarationKind::ModuleExports | ast::JsDeclarationKind::ExportsProperty => {
                    let right_most = ast::get_right_most_assigned_expression(node, &nodes);
                    let checked = self.check_expression_cached(right_most);
                    t = self.get_regular_type_of_literal_type(checked);
                }
                ast::JsDeclarationKind::ThisProperty => {
                    let bin = nodes[node].as_binary_expression();
                    if self.contains_same_named_this_property(
                        bin.left.expect("binary left"),
                        bin.right.expect("binary right"),
                    ) {
                        return None;
                    }
                    t = self.check_expression_for_mutable_location(
                        nodes[node].as_binary_expression().right.expect("binary right"),
                        CheckMode::NORMAL,
                    );
                }
                _ => {
                    t = self.check_expression_for_mutable_location(
                        nodes[node]
                            .as_binary_expression()
                            .right
                            .expect("binary right"),
                        CheckMode::NORMAL,
                    );
                }
            }
            if self.is_empty_array_literal_type(t)
                && !self.has_parent_with_type_annotation(nodes[node].symbol().unwrap())
            {
                self.report_implicit_any(node, self.any_array_type, WideningKind::Normal);
                return Some(self.any_array_type);
            }
            return Some(t);
        }
        if ast::is_call_expression(&nodes[node]) {
            let arg = nodes[node].arguments().unwrap_or(&[])[2];
            return Some(self.get_type_from_property_descriptor(arg));
        }
        None
    }

    /// `(c *Checker) hasParentWithTypeAnnotation` (checker.go:18550) — return
    /// true if the parent symbol of the given assignment declaration symbol
    /// has a declaration with a type annotation.
    pub(crate) fn has_parent_with_type_annotation(&mut self, symbol: SymbolId) -> bool {
        let parent = self.sym(symbol).parent;
        if let Some(parent) = parent {
            let parent_vd = self.sym(parent).value_declaration;
            if let Some(parent_vd) = parent_vd {
                let nodes = self.program_nodes(parent_vd);
                if ast::is_function_expression_or_arrow_function(&nodes[parent_vd]) {
                    let parent_of_vd = nodes[parent_vd].parent;
                    if let Some(possibly_annotated_symbol) =
                        parent_of_vd.and_then(|p| self.get_symbol_of_node(p))
                    {
                        let vd = self.sym(possibly_annotated_symbol).value_declaration;
                        if let Some(vd) = vd {
                            return self.program_nodes(vd)[vd].type_().is_some();
                        }
                    }
                }
            }
        }
        false
    }

    /// `(c *Checker) containsSameNamedThisProperty` (checker.go:18559).
    pub(crate) fn contains_same_named_this_property(
        &mut self,
        this_property: NodeId,
        expression: NodeId,
    ) -> bool {
        fn visit(c: &mut Checker, this_property: NodeId, node: NodeId) -> bool {
            let nodes = c.program_nodes(node);
            if c.is_matching_reference(&nodes, this_property, node) {
                return true;
            }
            if ast::is_function_like(&nodes[node], &nodes) {
                return false;
            }
            let mut found = false;
            nodes[node].for_each_child(&nodes, &mut |child| {
                if visit(c, this_property, child) {
                    found = true;
                    return true;
                }
                false
            });
            found
        }
        visit(self, this_property, expression)
    }

    /// `(c *Checker) getTypeFromPropertyDescriptor` (checker.go:18573).
    pub(crate) fn get_type_from_property_descriptor(&mut self, node: NodeId) -> TypeId {
        let object_literal_type = self.check_expression_cached(node);
        if let Some(value_type) =
            self.get_type_of_property_of_type(object_literal_type, "value")
        {
            return value_type;
        }
        if let Some(get_func) = self.get_type_of_property_of_type(object_literal_type, "get") {
            if let Some(get_sig) = self.get_single_call_signature(get_func) {
                return self.get_return_type_of_signature(get_sig);
            }
        }
        if let Some(set_func) = self.get_type_of_property_of_type(object_literal_type, "set") {
            if let Some(set_sig) = self.get_single_call_signature(set_func) {
                return self.get_type_of_first_parameter_of_signature(set_sig);
            }
        }
        self.any_type
    }

    /// `(c *Checker) isConstructorDeclaredThisProperty` (checker.go:18594) — a
    /// property is considered a constructor declared property when all
    /// declaration sites are this.xxx assignments, when no declaration sites
    /// have JSDoc type annotations, and when at least one declaration site is
    /// in the body of a class constructor.
    pub(crate) fn is_constructor_declared_this_property(
        &mut self,
        symbol: SymbolId,
    ) -> (ThisAssignmentDeclarationKind, Option<NodeId>) {
        let value_declaration = self.sym(symbol).value_declaration;
        if value_declaration.is_none_or(|vd| {
            !ast::is_binary_expression(&self.program_nodes(vd)[vd])
        }) {
            return (ThisAssignmentDeclarationKind::None, None);
        }
        if let Some(&kind) = self.this_expando_kinds.get(&symbol) {
            let location = self.this_expando_locations.get(&symbol).copied().unwrap_or_else(|| {
                panic!("location should be cached whenever this expando symbol is cached")
            });
            return (kind, Some(location));
        }
        let mut all_this = true;
        let mut type_annotation: Option<NodeId> = None;
        let declarations = self.sym(symbol).declarations.clone();
        for declaration in declarations {
            let nodes = self.program_nodes(declaration);
            if !ast::is_binary_expression(&nodes[declaration]) {
                all_this = false;
                break;
            }
            let bin = nodes[declaration].as_binary_expression();
            let is_this_property = ast::get_assignment_declaration_kind(declaration, &nodes)
                == ast::JsDeclarationKind::ThisProperty
                && bin.left.is_some_and(|left| {
                    nodes[left].kind != ast::Kind::ElementAccessExpression
                        || ast::is_string_or_numeric_literal_like(
                            &nodes[nodes[left]
                                .as_element_access_expression()
                                .argument_expression
                                .expect("element access argument")],
                        )
                });
            if is_this_property {
                if bin.type_.is_some() {
                    type_annotation = bin.type_;
                }
            } else {
                all_this = false;
                break;
            }
        }
        let mut location: Option<NodeId> = None;
        let mut kind = ThisAssignmentDeclarationKind::None;
        if all_this {
            if type_annotation.is_some() {
                location = type_annotation;
                kind = ThisAssignmentDeclarationKind::Typed;
            } else {
                location = self.get_declaring_constructor(symbol);
                kind = if location.is_none() {
                    ThisAssignmentDeclarationKind::Method
                } else {
                    ThisAssignmentDeclarationKind::Constructor
                };
            }
        }
        self.this_expando_kinds.insert(symbol, kind);
        if let Some(location) = location {
            self.this_expando_locations.insert(symbol, location);
        }
        (kind, location)
    }

    /// `(c *Checker) isGlobalSymbolConstructor` (checker.go:18639).
    pub(crate) fn is_global_symbol_constructor(&mut self, node: NodeId) -> bool {
        let symbol = self.get_symbol_of_node(node);
        let global_symbol = self.get_global_es_symbol_constructor_type_symbol_or_nil();
        global_symbol.is_some() && symbol == global_symbol
    }

    /// `(c *Checker) widenTypeForVariableLikeDeclaration` (checker.go:18645).
    pub(crate) fn widen_type_for_variable_like_declaration(
        &mut self,
        t: Option<TypeId>,
        declaration: NodeId,
        report_errors: bool,
    ) -> TypeId {
        if let Some(mut t) = t {
            // This special case is required for backwards compatibility with
            // libraries that merge a `symbol` property into `SymbolConstructor`.
            // See https://github.com/microsoft/TypeScript/tsc/issues/1212
            let nodes = self.program_nodes(declaration);
            if self.types.get(t).flags.intersects(TypeFlags::ES_SYMBOL)
                && nodes[declaration]
                    .parent
                    .is_some_and(|p| self.is_global_symbol_constructor(p))
            {
                t = self.get_es_symbol_like_type_for_node(declaration);
            }

            if report_errors {
                self.report_errors_from_widening(declaration, t, WideningKind::Normal);
            }

            // always widen a 'unique symbol' type if the type was created for a
            // different declaration.
            if self
                .types
                .get(t)
                .flags
                .intersects(TypeFlags::UNIQUE_ES_SYMBOL)
                && (ast::is_binding_element(&nodes[declaration])
                    || nodes[declaration].type_().is_none())
                && self.types.get(t).symbol
                    != self.get_symbol_of_declaration(declaration)
            {
                t = self.es_symbol_type;
            }
            return self.get_widened_type(t);
        }
        // Rest parameters default to type any[], other parameters default to
        // type any
        let nodes = self.program_nodes(declaration);
        let t = if ast::is_parameter_declaration(&nodes[declaration])
            && nodes[declaration]
                .as_parameter_declaration()
                .dot_dot_dot_token
                .is_some()
        {
            self.any_array_type
        } else {
            self.any_type
        };
        // Report implicit any errors unless this is a private property within an
        // ambient declaration
        if report_errors {
            if !self.declaration_belongs_to_private_ambient_member(declaration) {
                self.report_implicit_any(declaration, t, WideningKind::Normal);
            }
        }
        t
    }

    /// `(c *Checker) reportImplicitAny` (checker.go:18678).
    pub(crate) fn report_implicit_any(
        &mut self,
        declaration: NodeId,
        t: TypeId,
        widening_kind: WideningKind,
    ) {
        let nodes = self.program_nodes(declaration);
        if ast::is_in_js_file(Some(declaration), &nodes) {
            let source_file = ast::get_source_file_of_node(Some(declaration), &nodes);
            let check_js_enabled = source_file.is_some_and(|sf| {
                ast::is_check_js_enabled_for_file(
                    nodes[sf].as_source_file(),
                    &self.compiler_options,
                )
            });
            if !check_js_enabled {
                // Only report implicit any errors/suggestions in TS and
                // ts-check JS files
                return;
            }
        }
        let type_as_string = self.type_to_string(self.get_widened_type(t));
        let diagnostic: &'static tsc_diagnostics::Message;
        match nodes[declaration].kind {
            ast::Kind::BinaryExpression
            | ast::Kind::PropertyDeclaration
            | ast::Kind::PropertySignature => {
                diagnostic = if self.no_implicit_any {
                    &tsc_diagnostics::Member_0_implicitly_has_an_1_type
                } else {
                    &tsc_diagnostics::Member_0_implicitly_has_an_1_type_but_a_better_type_may_be_inferred_from_usage
                };
            }
            ast::Kind::Parameter => {
                let param = nodes[declaration].as_parameter_declaration();
                let param_name = param.name;
                if let Some(param_name) = param_name
                    && ast::is_identifier(&nodes[param_name])
                {
                    let name = nodes[param_name].as_identifier();
                    let original_keyword_kind = tsc_scanner::utilities::identifier_to_keyword_kind(name);
                    let param_parent = nodes[declaration].parent.unwrap();
                    let parent_parameters =
                        nodes[param_parent].parameters().unwrap_or(&[]).to_vec();
                    if (ast::is_call_signature_declaration(&nodes[param_parent])
                        || ast::is_method_signature_declaration(&nodes[param_parent])
                        || ast::is_function_type_node(&nodes[param_parent]))
                        && parent_parameters.contains(&declaration)
                        && (ast::is_type_node_kind(original_keyword_kind)
                            || {
                                let name_text = nodes[param_name].text(&nodes);
                                let f =
                                    self.resolve_name.clone().expect("Checker::resolve_name");
                                f(
                                    self,
                                    Some(declaration),
                                    &name_text,
                                    ast::SymbolFlags::TYPE,
                                    None,  /*nameNotFoundMessage*/
                                    true,  /*isUse*/
                                    false, /*excludeGlobals*/
                                )
                                .is_some()
                            })
                    {
                        let index = parent_parameters
                            .iter()
                            .position(|&p| p == declaration)
                            .unwrap();
                        let new_name = format!("arg{}", index);
                        let type_name = format!(
                            "{}{}",
                            tsc_scanner::utilities::declaration_name_to_string(
                                Some(param_name),
                                &nodes
                            ),
                            if param.dot_dot_dot_token.is_some() { "[]" } else { "" }
                        );
                        self.error_or_suggestion(
                            self.no_implicit_any,
                            Some(declaration),
                            &tsc_diagnostics::Parameter_has_a_name_but_no_type_Did_you_mean_0_Colon_1,
                            &[new_name, type_name],
                        );
                        return;
                    }
                }
                if param.dot_dot_dot_token.is_some() {
                    diagnostic = if self.no_implicit_any {
                        &tsc_diagnostics::Rest_parameter_0_implicitly_has_an_any_type
                    } else {
                        &tsc_diagnostics::Rest_parameter_0_implicitly_has_an_any_type_but_a_better_type_may_be_inferred_from_usage
                    };
                } else if self.no_implicit_any {
                    diagnostic = &tsc_diagnostics::Parameter_0_implicitly_has_an_1_type;
                } else {
                    diagnostic = &tsc_diagnostics::Parameter_0_implicitly_has_an_1_type_but_a_better_type_may_be_inferred_from_usage;
                }
            }
            ast::Kind::BindingElement => {
                diagnostic = &tsc_diagnostics::Binding_element_0_implicitly_has_an_1_type;
                if !self.no_implicit_any {
                    // Don't issue a suggestion for binding elements since the
                    // codefix doesn't yet support them.
                    return;
                }
            }
            ast::Kind::FunctionDeclaration
            | ast::Kind::MethodDeclaration
            | ast::Kind::MethodSignature
            | ast::Kind::GetAccessor
            | ast::Kind::SetAccessor
            | ast::Kind::FunctionExpression
            | ast::Kind::ArrowFunction => {
                if self.no_implicit_any && nodes[declaration].name().is_none() {
                    if widening_kind == WideningKind::GeneratorYield {
                        self.error(
                            Some(declaration),
                            &tsc_diagnostics::Generator_implicitly_has_yield_type_0_Consider_supplying_a_return_type_annotation,
                            &[type_as_string],
                        );
                    } else {
                        self.error(
                            Some(declaration),
                            &tsc_diagnostics::Function_expression_which_lacks_return_type_annotation_implicitly_has_an_0_return_type,
                            &[type_as_string],
                        );
                    }
                    return;
                }
                if !self.no_implicit_any {
                    diagnostic = &tsc_diagnostics::X_0_implicitly_has_an_1_return_type_but_a_better_type_may_be_inferred_from_usage;
                } else if nodes[declaration].flags.intersects(ast::NodeFlags::REPARSED) {
                    let name = tsc_scanner::utilities::declaration_name_to_string(
                        ast::get_name_of_declaration(Some(declaration), &nodes),
                        &nodes,
                    );
                    if !name.is_empty() {
                        self.error(
                            Some(declaration),
                            &tsc_diagnostics::X_0_which_lacks_return_type_annotation_implicitly_has_an_1_return_type,
                            &[name, type_as_string],
                        );
                    } else {
                        self.error(
                            Some(declaration),
                            &tsc_diagnostics::This_overload_implicitly_returns_the_type_0_because_it_lacks_a_return_type_annotation,
                            &[type_as_string],
                        );
                    }
                    return;
                } else if widening_kind == WideningKind::GeneratorYield {
                    diagnostic = &tsc_diagnostics::X_0_which_lacks_return_type_annotation_implicitly_has_an_1_yield_type;
                } else {
                    diagnostic = &tsc_diagnostics::X_0_which_lacks_return_type_annotation_implicitly_has_an_1_return_type;
                }
            }
            ast::Kind::MappedType => {
                if self.no_implicit_any {
                    self.error(
                        Some(declaration),
                        &tsc_diagnostics::Mapped_object_type_implicitly_has_an_any_template_type,
                        &[],
                    );
                }
                return;
            }
            _ => {
                diagnostic = if self.no_implicit_any {
                    &tsc_diagnostics::Variable_0_implicitly_has_an_1_type
                } else {
                    &tsc_diagnostics::Variable_0_implicitly_has_an_1_type_but_a_better_type_may_be_inferred_from_usage
                };
            }
        }
        let name = tsc_scanner::utilities::declaration_name_to_string(
            ast::get_name_of_declaration(Some(declaration), &nodes),
            &nodes,
        );
        self.error_or_suggestion(
            self.no_implicit_any,
            Some(declaration),
            diagnostic,
            &[name, type_as_string],
        );
    }

    /// `(c *Checker) getWidenedType` (checker.go:18762).
    pub(crate) fn get_widened_type(&mut self, t: TypeId) -> TypeId {
        self.get_widened_type_with_context(t, None /*context*/)
    }

    /// `(c *Checker) getWidenedTypeWithContext` (checker.go:18766).
    pub(crate) fn get_widened_type_with_context(
        &mut self,
        t: TypeId,
        context: Option<Rc<RefCell<WideningContext>>>,
    ) -> TypeId {
        if self
            .types
            .get(t)
            .object_flags
            .intersects(ObjectFlags::REQUIRES_WIDENING)
        {
            if context.is_none() {
                if let Some(&cached) = self.cached_types.get(&CachedTypeKey {
                    kind: CachedTypeKind::Widened,
                    type_id: t,
                }) {
                    return cached;
                }
            }
            let mut result: Option<TypeId> = None;
            let flags = self.types.get(t).flags;
            if flags.intersects(TypeFlags::ANY | TypeFlags::NULLABLE) {
                result = Some(self.any_type);
            } else if is_object_literal_type(&self.types, t) {
                result = Some(self.get_widened_type_of_object_literal(t, context.clone()));
            } else if flags.intersects(TypeFlags::UNION) {
                let union_context = context.unwrap_or_else(|| {
                    Rc::new(RefCell::new(WideningContext {
                        parent: None,
                        property_name: String::new(),
                        siblings: self.types.get(t).types().to_vec(),
                        resolved_properties: Vec::new(),
                        child_contexts: FxHashMap::default(),
                        widened_types: FxHashMap::default(),
                    }))
                });
                let types = self.types.get(t).types().to_vec();
                let widened_types = core::same_map(&types, |t| {
                    if self.types.get(*t).flags.intersects(TypeFlags::NULLABLE) {
                        return *t;
                    }
                    self.get_widened_type_with_context(*t, Some(union_context.clone()))
                });
                // Widening an empty object literal transitions from a highly
                // restrictive type to a highly inclusive one. For that reason we
                // perform subtype reduction here if the union includes empty
                // object types (e.g. reducing {} | string to just {}).
                let union_reduction = if widened_types
                    .iter()
                    .any(|&t| self.is_empty_object_type(t))
                {
                    crate::checker_types::UnionReduction::Subtype
                } else {
                    crate::checker_types::UnionReduction::Literal
                };
                result = Some(self.get_union_type_ex(&widened_types, union_reduction, None, None));
            } else if flags.intersects(TypeFlags::INTERSECTION) {
                let types = self.types.get(t).types().to_vec();
                let widened_types =
                    core::same_map(&types, |t| self.get_widened_type(*t));
                result = Some(self.get_intersection_type(&widened_types));
            } else if self.is_array_or_tuple_type(t) {
                let target = self.types.get(t).target().unwrap_or(t);
                let type_arguments = self.get_type_arguments(t);
                let widened_types =
                    core::same_map(&type_arguments, |t| self.get_widened_type(*t));
                result = Some(self.create_type_reference(target, &widened_types));
            }
            if let Some(result) = result
                && context.is_none()
            {
                self.cached_types.insert(
                    CachedTypeKey {
                        kind: CachedTypeKind::Widened,
                        type_id: t,
                    },
                    result,
                );
            }
            return result.unwrap_or(t);
        }
        t
    }

    /// `(c *Checker) getWidenedTypeOfObjectLiteral` (checker.go:18807).
    pub(crate) fn get_widened_type_of_object_literal(
        &mut self,
        t: TypeId,
        context: Option<Rc<RefCell<WideningContext>>>,
    ) -> TypeId {
        if let Some(context) = &context {
            if let Some(&cached) = context.borrow().widened_types.get(&t) {
                return cached;
            }
        }
        let mut members = SymbolTable::new();
        for prop in self.get_properties_of_object_type(t) {
            let name = self.sym(prop).name.clone();
            let widened = self.get_widened_property(prop, context.clone());
            members.set(name, widened);
        }
        if let Some(context) = &context {
            for prop in self.get_properties_of_context(context) {
                let name = self.sym(prop).name.clone();
                if members.get(&name).is_none() {
                    let undefined_prop = self.get_undefined_property(prop);
                    members.set(name, undefined_prop);
                }
            }
        }
        let index_infos = self.get_index_infos_of_type(t);
        let widened_infos: Vec<IndexInfoId> = index_infos
            .iter()
            .map(|&info_id| {
                let info = self.index_info_arena.get(info_id).clone();
                let widened = self.get_widened_type(info.value_type.expect("index info value type"));
                self.new_index_info(
                    info.key_type.expect("index info key type"),
                    widened,
                    info.is_readonly,
                    info.declaration,
                    info.components.clone(),
                )
            })
            .collect();
        let symbol = self.types.get(t).symbol;
        let result = self.new_anonymous_type(symbol, members, &[], &[], &widened_infos);
        // Retain js literal flag through widening
        let retain =
            self.types.get(t).object_flags & (ObjectFlags::JS_LITERAL | ObjectFlags::NON_INFERRABLE_TYPE);
        self.types.get_mut(result).object_flags.insert(retain);
        // Only cache in child contexts since the root context never widens a
        // particular object literal type more than once
        if let Some(context) = &context
            && context.borrow().parent.is_some()
        {
            context.borrow_mut().widened_types.insert(t, result);
        }
        result
    }

    /// `(c *Checker) getWidenedProperty` (checker.go:18839).
    pub(crate) fn get_widened_property(
        &mut self,
        prop: SymbolId,
        context: Option<Rc<RefCell<WideningContext>>>,
    ) -> SymbolId {
        if !self.sym(prop).flags.intersects(ast::SymbolFlags::PROPERTY) {
            // Since get accessors already widen their return value there is no
            // need to widen accessor based properties here.
            return prop;
        }
        let original = self.get_type_of_symbol(prop);
        let prop_context = context.map(|c| {
            let name = self.sym(prop).name.clone();
            widening_context_get_child_context(&c, &name)
        });
        let widened = self.get_widened_type_with_context(original, prop_context);
        if widened == original {
            return prop;
        }
        self.create_symbol_with_type(prop, widened)
    }

    /// `(c *Checker) getPropertiesOfContext` (checker.go:18868).
    pub(crate) fn get_properties_of_context(
        &mut self,
        context: &Rc<RefCell<WideningContext>>,
    ) -> Vec<SymbolId> {
        {
            let ctx = context.borrow();
            // PORT: `resolvedProperties`/`siblings` are nil-vs-empty in Go;
            // here we treat an empty vec as unresolved (the fields have no
            // `Option` in `WideningContext`). Empty results are recomputed,
            // which is behaviourally equivalent.
            if !ctx.resolved_properties.is_empty() {
                return ctx.resolved_properties.clone();
            }
        }
        let mut names: Vec<(String, SymbolId)> = Vec::new();
        let mut seen: FxHashSet<String> = FxHashSet::default();
        let siblings = self.get_siblings_of_context(context);
        for t in siblings {
            if is_object_literal_type(&self.types, t)
                && !self
                    .types
                    .get(t)
                    .object_flags
                    .intersects(ObjectFlags::CONTAINS_SPREAD)
            {
                for prop in self.get_properties_of_type(t) {
                    let name = self.sym(prop).name.clone();
                    if seen.insert(name.clone()) {
                        names.push((name, prop));
                    }
                }
            }
        }
        let resolved: Vec<SymbolId> = names.into_iter().map(|(_, s)| s).collect();
        context.borrow_mut().resolved_properties = resolved.clone();
        resolved
    }

    /// `(c *Checker) getSiblingsOfContext` (checker.go:18881).
    pub(crate) fn get_siblings_of_context(
        &mut self,
        context: &Rc<RefCell<WideningContext>>,
    ) -> Vec<TypeId> {
        {
            let ctx = context.borrow();
            if !ctx.siblings.is_empty() {
                return ctx.siblings.clone();
            }
        }
        let mut siblings: Vec<TypeId> = Vec::new();
        let (parent, property_name) = {
            let ctx = context.borrow();
            (ctx.parent.clone(), ctx.property_name.clone())
        };
        if let Some(parent) = parent {
            for t in self.get_siblings_of_context(&parent) {
                if is_object_literal_type(&self.types, t) {
                    if let Some(prop) = self.get_property_of_object_type(t, &property_name) {
                        let prop_type = self.get_type_of_symbol(prop);
                        siblings.extend(self.types.get(prop_type).distributed(prop_type));
                    }
                }
            }
        }
        context.borrow_mut().siblings = siblings.clone();
        siblings
    }

    /// `(c *Checker) getUndefinedProperty` (checker.go:18895).
    pub(crate) fn get_undefined_property(&mut self, prop: SymbolId) -> SymbolId {
        let name = self.sym(prop).name.clone();
        if let Some(&cached) = self.undefined_properties.get(&name) {
            return cached;
        }
        let undefined_or_missing_type = self.undefined_or_missing_type;
        let result = self.create_symbol_with_type(prop, undefined_or_missing_type);
        self.symbol_arena.borrow_mut()[result.index()]
            .flags
            .insert(ast::SymbolFlags::OPTIONAL);
        self.undefined_properties.insert(name, result);
        result
    }

    /// `(c *Checker) getTypeOfEnumMember` (checker.go:18903).
    pub(crate) fn get_type_of_enum_member(&mut self, symbol: SymbolId) -> TypeId {
        if self.value_symbol_links.get(symbol).resolved_type.is_none() {
            let resolved = self.get_declared_type_of_enum_member(symbol);
            self.value_symbol_links.get(symbol).resolved_type = Some(resolved);
        }
        self.value_symbol_links.get(symbol).resolved_type.unwrap()
    }

    /// `(c *Checker) getTypeOfAccessors` (checker.go:18911).
    pub(crate) fn get_type_of_accessors(&mut self, symbol: SymbolId) -> TypeId {
        if self.value_symbol_links.get(symbol).resolved_type.is_none() {
            if !self.push_type_resolution(TypeSystemEntity::Symbol(symbol), TypeSystemPropertyName::Type) {
                return self.error_type;
            }
            let declarations = self.sym(symbol).declarations.clone();
            let getter = declarations.iter().copied().find(|&d| {
                self.program_nodes(d)[d].kind == ast::Kind::GetAccessor
            });
            let setter = declarations.iter().copied().find(|&d| {
                self.program_nodes(d)[d].kind == ast::Kind::SetAccessor
            });
            let accessor = declarations.iter().copied().find(|&d| {
                ast::is_auto_accessor_property_declaration(&self.program_nodes(d)[d])
            });
            // We try to resolve a getter type annotation, a setter type
            // annotation, or a getter function body return type inference, in
            // that order.
            let mut t = self.get_annotated_accessor_type(getter);
            if t.is_none() {
                t = self.get_annotated_accessor_type(setter);
            }
            if t.is_none() {
                t = self.get_annotated_accessor_type(accessor);
            }
            if t.is_none()
                && let Some(getter) = getter
                && self.program_nodes(getter)[getter].body().is_some()
            {
                t = Some(self.get_return_type_from_body(getter, CheckMode::NORMAL));
            }
            if t.is_none() && accessor.is_some() {
                t = Some(self.get_widened_type_for_variable_like_declaration(
                    accessor.unwrap(),
                    true, /*reportErrors*/
                ));
            }
            let mut t = t;
            if t.is_none() {
                if let Some(setter) = setter {
                    let nodes = self.program_nodes(setter);
                    if !crate::utilities::is_private_within_ambient(&nodes[setter], &nodes) {
                        let name = self.symbol_to_string(symbol);
                        self.error_or_suggestion(
                            self.no_implicit_any,
                            Some(setter),
                            &tsc_diagnostics::Property_0_implicitly_has_type_any_because_its_set_accessor_lacks_a_parameter_type_annotation,
                            &[name],
                        );
                    }
                } else if let Some(getter) = getter {
                    let nodes = self.program_nodes(getter);
                    if !crate::utilities::is_private_within_ambient(&nodes[getter], &nodes) {
                        let name = self.symbol_to_string(symbol);
                        self.error_or_suggestion(
                            self.no_implicit_any,
                            Some(getter),
                            &tsc_diagnostics::Property_0_implicitly_has_type_any_because_its_get_accessor_lacks_a_return_type_annotation,
                            &[name],
                        );
                    }
                } else if let Some(accessor) = accessor {
                    let nodes = self.program_nodes(accessor);
                    if !crate::utilities::is_private_within_ambient(&nodes[accessor], &nodes) {
                        let name = self.symbol_to_string(symbol);
                        self.error_or_suggestion(
                            self.no_implicit_any,
                            Some(accessor),
                            &tsc_diagnostics::Member_0_implicitly_has_an_1_type,
                            &[name, "any".to_string()],
                        );
                    }
                }
                t = Some(self.any_type);
            }
            if !self.pop_type_resolution() {
                if self.get_annotated_accessor_type_node(getter).is_some() {
                    let name = self.symbol_to_string(symbol);
                    self.error(
                        getter,
                        &tsc_diagnostics::X_0_is_referenced_directly_or_indirectly_in_its_own_type_annotation,
                        &[name],
                    );
                } else if self.get_annotated_accessor_type_node(setter).is_some() {
                    let name = self.symbol_to_string(symbol);
                    self.error(
                        setter,
                        &tsc_diagnostics::X_0_is_referenced_directly_or_indirectly_in_its_own_type_annotation,
                        &[name],
                    );
                } else if self.get_annotated_accessor_type_node(accessor).is_some() {
                    let name = self.symbol_to_string(symbol);
                    self.error(
                        setter,
                        &tsc_diagnostics::X_0_is_referenced_directly_or_indirectly_in_its_own_type_annotation,
                        &[name],
                    );
                } else if getter.is_some() && self.no_implicit_any {
                    let name = self.symbol_to_string(symbol);
                    self.error(
                        getter,
                        &tsc_diagnostics::X_0_implicitly_has_return_type_any_because_it_does_not_have_a_return_type_annotation_and_is_referenced_directly_or_indirectly_in_one_of_its_return_expressions,
                        &[name],
                    );
                }
                t = Some(self.any_type);
            }
            if self.value_symbol_links.get(symbol).resolved_type.is_none() {
                self.value_symbol_links.get(symbol).resolved_type = t;
            }
        }
        self.value_symbol_links.get(symbol).resolved_type.unwrap()
    }

    /// `(c *Checker) getWriteTypeOfAccessors` (checker.go:18962).
    pub(crate) fn get_write_type_of_accessors(&mut self, symbol: SymbolId) -> TypeId {
        if self.value_symbol_links.get(symbol).write_type.is_none() {
            if !self.push_type_resolution(TypeSystemEntity::Symbol(symbol), TypeSystemPropertyName::WriteType) {
                return self.error_type;
            }
            let declarations = self.sym(symbol).declarations.clone();
            let mut setter = declarations.iter().copied().find(|&d| {
                self.program_nodes(d)[d].kind == ast::Kind::SetAccessor
            });
            if setter.is_none() {
                let prop_declaration = declarations.iter().copied().find(|&d| {
                    self.program_nodes(d)[d].kind == ast::Kind::PropertyDeclaration
                });
                if let Some(prop_declaration) = prop_declaration
                    && ast::is_auto_accessor_property_declaration(
                        &self.program_nodes(prop_declaration)[prop_declaration],
                    )
                {
                    setter = Some(prop_declaration);
                }
            }
            let mut write_type = self.get_annotated_accessor_type(setter);
            if !self.pop_type_resolution() {
                if self.get_annotated_accessor_type_node(setter).is_some() {
                    let name = self.symbol_to_string(symbol);
                    self.error(
                        setter,
                        &tsc_diagnostics::X_0_is_referenced_directly_or_indirectly_in_its_own_type_annotation,
                        &[name],
                    );
                }
                write_type = Some(self.any_type);
            }
            // Absent an explicit setter type annotation we use the read type of
            // the accessor.
            if self.value_symbol_links.get(symbol).write_type.is_none() {
                if let Some(write_type) = write_type {
                    self.value_symbol_links.get(symbol).write_type = Some(write_type);
                } else {
                    let read = self.get_type_of_accessors(symbol);
                    self.value_symbol_links.get(symbol).write_type = Some(read);
                }
            }
        }
        self.value_symbol_links.get(symbol).write_type.unwrap()
    }

    /// `(c *Checker) getTypeOfAlias` (checker.go:18990).
    pub(crate) fn get_type_of_alias(&mut self, symbol: SymbolId) -> TypeId {
        if self.value_symbol_links.get(symbol).resolved_type.is_none() {
            if !self.push_type_resolution(TypeSystemEntity::Symbol(symbol), TypeSystemPropertyName::Type) {
                return self.error_type;
            }
            let target_symbol = self.resolve_alias(symbol);
            let export_symbol = self
                .get_declaration_of_alias_symbol(symbol)
                .and_then(|decl| self.get_target_of_alias_declaration(decl));
            // It only makes sense to get the type of a value symbol. If the
            // result of resolving the alias is not a value, then it has no
            // type. To get the type associated with a type symbol, call
            // getDeclaredTypeOfSymbol.
            // This check is important because without it, a call to
            // getTypeOfSymbol could end up recursively calling getTypeOfAlias,
            // causing a stack overflow.
            if self.value_symbol_links.get(symbol).resolved_type.is_none() {
                if self.get_symbol_flags(target_symbol).intersects(ast::SymbolFlags::VALUE) {
                    let t = self.get_type_of_symbol(target_symbol);
                    self.value_symbol_links.get(symbol).resolved_type = Some(t);
                } else {
                    self.value_symbol_links.get(symbol).resolved_type = Some(self.error_type);
                }
            }
            if !self.pop_type_resolution() {
                let to_report = export_symbol.unwrap_or(target_symbol);
                self.report_circularity_error(to_report);
                if self.value_symbol_links.get(symbol).resolved_type.is_none() {
                    self.value_symbol_links.get(symbol).resolved_type = Some(self.error_type);
                }
                return self.value_symbol_links.get(symbol).resolved_type.unwrap();
            }
        }
        self.value_symbol_links.get(symbol).resolved_type.unwrap()
    }

    /// `(c *Checker) addOptionality` (checker.go:19019).
    pub(crate) fn add_optionality(&mut self, t: TypeId) -> TypeId {
        self.add_optionality_ex(t, false /*isProperty*/, true /*isOptional*/)
    }

    /// `(c *Checker) addOptionalityEx` (checker.go:19023).
    pub(crate) fn add_optionality_ex(&mut self, t: TypeId, is_property: bool, is_optional: bool) -> TypeId {
        if self.strict_null_checks && is_optional {
            return self.get_optional_type(t, is_property);
        }
        t
    }

    /// `(c *Checker) getOptionalType` (checker.go:19030).
    pub(crate) fn get_optional_type(&mut self, t: TypeId, is_property: bool) -> TypeId {
        debug_assert!(self.strict_null_checks);
        let missing_or_undefined = if is_property {
            self.undefined_or_missing_type
        } else {
            self.undefined_type
        };
        if t == missing_or_undefined
            || self.types.get(t).flags.intersects(TypeFlags::UNION)
                && self.types.get(t).types().first() == Some(&missing_or_undefined)
        {
            return t;
        }
        self.get_union_type(&[t, missing_or_undefined])
    }

    /// `(c *Checker) getNullableType` (checker.go:19039) — add undefined or
    /// null or both to a type if they are missing.
    pub(crate) fn get_nullable_type(&mut self, t: TypeId, flags: TypeFlags) -> TypeId {
        let missing = (flags & !self.types.get(t).flags) & (TypeFlags::UNDEFINED | TypeFlags::NULL);
        if missing.is_empty() {
            return t;
        }
        if missing == TypeFlags::UNDEFINED {
            return self.get_union_type(&[t, self.undefined_type]);
        }
        if missing == TypeFlags::NULL {
            return self.get_union_type(&[t, self.null_type]);
        }
        self.get_union_type(&[t, self.undefined_type, self.null_type])
    }

    /// `(c *Checker) GetNonNullableType` (checker.go:19053).
    pub fn get_non_nullable_type(&mut self, t: TypeId) -> TypeId {
        if self.strict_null_checks {
            return self.get_adjusted_type_with_facts(t, TypeFacts::NE_UNDEFINED_OR_NULL);
        }
        t
    }

    /// `(c *Checker) IsNullableType` (checker.go:19060).
    pub fn is_nullable_type(&mut self, t: TypeId) -> bool {
        self.has_type_facts(t, TypeFacts::IS_UNDEFINED_OR_NULL)
    }

    /// `(c *Checker) getNonNullableTypeIfNeeded` (checker.go:19064).
    pub(crate) fn get_non_nullable_type_if_needed(&mut self, t: TypeId) -> TypeId {
        if self.is_nullable_type(t) {
            return self.get_non_nullable_type(t);
        }
        t
    }

    /// `(c *Checker) getDeclarationNodeFlagsFromSymbol` (checker.go:19071).
    pub(crate) fn get_declaration_node_flags_from_symbol(&mut self, s: SymbolId) -> ast::NodeFlags {
        if let Some(value_declaration) = self.sym(s).value_declaration {
            return self.get_combined_node_flags_cached(value_declaration);
        }
        ast::NodeFlags::NONE
    }

    /// `(c *Checker) getCombinedNodeFlagsCached` (checker.go:19078) — we hold
    /// onto the last node and result to speed up repeated lookups against the
    /// same node.
    pub(crate) fn get_combined_node_flags_cached(&mut self, node: NodeId) -> ast::NodeFlags {
        if self.last_get_combined_node_flags_node == Some(node) {
            return self.last_get_combined_node_flags_result;
        }
        self.last_get_combined_node_flags_node = Some(node);
        self.last_get_combined_node_flags_result =
            ast::get_combined_node_flags(node, &self.program_nodes(node));
        self.last_get_combined_node_flags_result
    }

    /// `(c *Checker) isVarConstLike` (checker.go:19089).
    pub(crate) fn is_var_const_like(&mut self, node: NodeId) -> bool {
        let block_scope_kind = self.get_combined_node_flags_cached(node) & ast::NodeFlags::BLOCK_SCOPED;
        block_scope_kind == ast::NodeFlags::CONST
            || block_scope_kind == ast::NodeFlags::USING
            || block_scope_kind == ast::NodeFlags::AWAIT_USING
    }

    /// `(c *Checker) getEffectivePropertyNameForPropertyNameNode`
    /// (checker.go:19094).
    pub(crate) fn get_effective_property_name_for_property_name_node(
        &mut self,
        node: NodeId,
    ) -> (String, bool) {
        let nodes = self.program_nodes(node);
        let name = ast::get_property_name_for_property_name_node(node, &nodes);
        if name != ast::symbol::INTERNAL_SYMBOL_NAME_MISSING {
            return (name, true);
        }
        if ast::is_computed_property_name(&nodes[node]) {
            // This is cached so `getTypeOfExpression` isn't constantly
            // reinvoked for every property name lookup
            if let Some(has_name) = self.computed_name_links.get(node).has_name {
                return (self.computed_name_links.get(node).name.clone(), has_name);
            }
            let expression = nodes[node].expression().expect("computed property name expression");
            let expr_type = self.get_type_of_expression(expression);
            let (name, exists) = self.try_get_name_from_type(expr_type);
            let mut links = self.computed_name_links.get(node);
            links.name = name.clone();
            links.has_name = Some(exists);
            return (name, exists);
        }
        (String::new(), false)
    }

    /// `(c *Checker) tryGetNameFromType` (checker.go:19110).
    pub(crate) fn try_get_name_from_type(&mut self, t: TypeId) -> (String, bool) {
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL) {
            let name = self
                .types
                .get(t)
                .as_unique_es_symbol_type()
                .name
                .clone()
                .unwrap_or_default();
            return (name, true);
        }
        if flags.intersects(TypeFlags::STRING_LITERAL) {
            return (crate::checker_d::get_string_literal_value(&self.types, t), true);
        }
        if flags.intersects(TypeFlags::NUMBER_LITERAL) {
            return (
                crate::checker_d::get_number_literal_value(&self.types, t).to_string(),
                true,
            );
        }
        (String::new(), false)
    }

    /// `(c *Checker) getCombinedModifierFlagsCached` (checker.go:19124) — we
    /// hold onto the last node and result to speed up repeated lookups against
    /// the same node.
    pub(crate) fn get_combined_modifier_flags_cached(
        &mut self,
        node: NodeId,
    ) -> ast::ModifierFlags {
        if self.last_get_combined_modifier_flags_node == Some(node) {
            return self.last_get_combined_modifier_flags_result;
        }
        self.last_get_combined_modifier_flags_node = Some(node);
        self.last_get_combined_modifier_flags_result =
            ast::get_combined_modifier_flags(node, &self.program_nodes(node));
        self.last_get_combined_modifier_flags_result
    }

    /// `(c *Checker) pushTypeResolution` (checker.go:19165) — push an entry on
    /// the type resolution stack. If an entry with the given target and the
    /// given property name is already on the stack, and no entries in between
    /// already have a type, then a circularity has occurred.
    pub(crate) fn push_type_resolution(
        &mut self,
        target: TypeSystemEntity,
        property_name: TypeSystemPropertyName,
    ) -> bool {
        let resolution_cycle_start_index =
            self.find_resolution_cycle_start_index(target, property_name);
        if resolution_cycle_start_index >= 0 {
            // A cycle was found
            for i in resolution_cycle_start_index as usize..self.type_resolutions.len() {
                self.type_resolutions[i].result = false;
            }
            return false;
        }
        self.type_resolutions.push(TypeResolution {
            target,
            property_name,
            result: true,
        });
        true
    }

    /// `(c *Checker) popTypeResolution` (checker.go:19181) — pop an entry from
    /// the type resolution stack and return its associated result value. The
    /// result value will be true if no circularities were detected, or false
    /// if a circularity was found.
    pub(crate) fn pop_type_resolution(&mut self) -> bool {
        let last_index = self.type_resolutions.len() - 1;
        let result = self.type_resolutions[last_index].result;
        // Clear the last entry to avoid memory leaks
        self.type_resolutions[last_index] = TypeResolution::default();
        self.type_resolutions.truncate(last_index);
        result
    }

    /// `(c *Checker) findResolutionCycleStartIndex` (checker.go:19192).
    pub(crate) fn find_resolution_cycle_start_index(
        &mut self,
        target: TypeSystemEntity,
        property_name: TypeSystemPropertyName,
    ) -> isize {
        let mut i = self.type_resolutions.len();
        while i > self.resolution_start.max(0) as usize {
            i -= 1;
            let resolution = self.type_resolutions[i];
            if self.type_resolution_has_property(&resolution) {
                return -1;
            }
            if resolution.target == target && resolution.property_name == property_name {
                return i as isize;
            }
        }
        -1
    }

    /// `(c *Checker) typeResolutionHasProperty` (checker.go:19206).
    pub(crate) fn type_resolution_has_property(&mut self, r: &TypeResolution) -> bool {
        match r.property_name {
            TypeSystemPropertyName::Type => {
                let TypeSystemEntity::Symbol(target) = r.target else {
                    panic!("Unhandled case in typeResolutionHasProperty")
                };
                self.value_symbol_links.get(target).resolved_type.is_some()
            }
            TypeSystemPropertyName::DeclaredType => {
                let TypeSystemEntity::Symbol(target) = r.target else {
                    panic!("Unhandled case in typeResolutionHasProperty")
                };
                self.type_alias_links.get(target).declared_type.is_some()
            }
            TypeSystemPropertyName::ResolvedTypeArguments => {
                let TypeSystemEntity::Type(target) = r.target else {
                    panic!("Unhandled case in typeResolutionHasProperty")
                };
                self.types
                    .get(target)
                    .as_type_reference()
                    .resolved_type_arguments
                    .is_some()
            }
            TypeSystemPropertyName::ResolvedBaseTypes => {
                let TypeSystemEntity::Type(target) = r.target else {
                    panic!("Unhandled case in typeResolutionHasProperty")
                };
                self.types.get(target).as_interface_type().base_types_resolved
            }
            TypeSystemPropertyName::ResolvedBaseConstructorType => {
                let TypeSystemEntity::Type(target) = r.target else {
                    panic!("Unhandled case in typeResolutionHasProperty")
                };
                self.types
                    .get(target)
                    .as_interface_type()
                    .resolved_base_constructor_type
                    .is_some()
            }
            TypeSystemPropertyName::ResolvedReturnType => {
                let TypeSystemEntity::Signature(target) = r.target else {
                    panic!("Unhandled case in typeResolutionHasProperty")
                };
                self.signature_arena.get(target).resolved_return_type.is_some()
            }
            TypeSystemPropertyName::ResolvedBaseConstraint => {
                let TypeSystemEntity::Type(target) = r.target else {
                    panic!("Unhandled case in typeResolutionHasProperty")
                };
                self.types
                    .get(target)
                    .as_constrained_type()
                    .resolved_base_constraint
                    .is_some()
            }
            TypeSystemPropertyName::InitializerIsUndefined => {
                let TypeSystemEntity::Node(target) = r.target else {
                    panic!("Unhandled case in typeResolutionHasProperty")
                };
                self.node_links
                    .get(target)
                    .flags
                    .intersects(NodeCheckFlags::INITIALIZER_IS_UNDEFINED_COMPUTED)
            }
            TypeSystemPropertyName::WriteType => {
                let TypeSystemEntity::Symbol(target) = r.target else {
                    panic!("Unhandled case in typeResolutionHasProperty")
                };
                self.value_symbol_links.get(target).write_type.is_some()
            }
            TypeSystemPropertyName::AliasTarget => {
                let TypeSystemEntity::Symbol(target) = r.target else {
                    panic!("Unhandled case in typeResolutionHasProperty")
                };
                self.alias_symbol_links.get(target).alias_target.is_some()
            }
        }
    }

    /// `(c *Checker) reportCircularityError` (checker.go:19230).
    pub(crate) fn report_circularity_error(&mut self, symbol: SymbolId) -> TypeId {
        let declaration = self.sym(symbol).value_declaration;
        // Check if variable has type annotation that circularly references the
        // variable itself
        if let Some(declaration) = declaration {
            let nodes = self.program_nodes(declaration);
            if nodes[declaration].type_().is_some() {
                let name = self.symbol_to_string(symbol);
                self.error(
                    Some(declaration),
                    &tsc_diagnostics::X_0_is_referenced_directly_or_indirectly_in_its_own_type_annotation,
                    &[name],
                );
                return self.error_type;
            }
            // Check if variable has initializer that circularly references the
            // variable itself
            if self.no_implicit_any
                && (!ast::is_parameter_declaration(&nodes[declaration])
                    || nodes[declaration].initializer().is_some())
            {
                let name = self.symbol_to_string(symbol);
                self.error(
                    Some(declaration),
                    &tsc_diagnostics::X_0_implicitly_has_type_any_because_it_does_not_have_a_type_annotation_and_is_referenced_directly_or_indirectly_in_its_own_initializer,
                    &[name],
                );
            }
        } else if self.sym(symbol).flags.intersects(ast::SymbolFlags::ALIAS) {
            if let Some(node) = self.get_declaration_of_alias_symbol(symbol) {
                let name = self.symbol_to_string(symbol);
                self.error(
                    Some(node),
                    &tsc_diagnostics::Circular_definition_of_import_alias_0,
                    &[name],
                );
            }
        }
        // Circularities could also result from parameters in function
        // expressions that end up having themselves as contextual types
        // following type argument inference. In those cases we have already
        // reported an implicit any error so we don't report anything here.
        self.any_type
    }

    /// `(c *Checker) getPropertiesOfType` (checker.go:19253).
    pub(crate) fn get_properties_of_type(&mut self, t: TypeId) -> Vec<SymbolId> {
        let t = self.get_reduced_apparent_type(t);
        if self
            .types
            .get(t)
            .flags
            .intersects(TypeFlags::UNION_OR_INTERSECTION)
        {
            return self.get_properties_of_union_or_intersection_type(t);
        }
        self.get_properties_of_object_type(t)
    }

    /// `(c *Checker) getPropertiesOfObjectType` (checker.go:19261).
    pub(crate) fn get_properties_of_object_type(&mut self, t: TypeId) -> Vec<SymbolId> {
        if self.types.get(t).flags.intersects(TypeFlags::OBJECT) {
            let resolved = self.resolve_structured_type_members(t);
            let properties = self
                .types
                .get(resolved)
                .as_structured_type()
                .map(|st| st.properties.clone());
            return properties.unwrap_or_default();
        }
        Vec::new()
    }

    /// `(c *Checker) getPropertiesOfUnionOrIntersectionType`
    /// (checker.go:19268).
    pub(crate) fn get_properties_of_union_or_intersection_type(
        &mut self,
        t: TypeId,
    ) -> Vec<SymbolId> {
        {
            let resolved_properties = self
                .types
                .get(t)
                .as_union_or_intersection_type()
                .resolved_properties
                .clone();
            // PORT: Go nil-checks `resolvedProperties`; an empty vec stands in
            // for nil (union/intersection types always have >=1 property once
            // resolved in practice, and recomputing an empty result is
            // equivalent).
            if !resolved_properties.is_empty() {
                return resolved_properties;
            }
        }
        let mut checked: FxHashSet<String> = FxHashSet::default();
        let mut props: Vec<SymbolId> = Vec::new();
        let is_intersection = self.types.get(t).flags.intersects(TypeFlags::INTERSECTION);
        let is_union = self.types.get(t).flags.intersects(TypeFlags::UNION);
        let constituents = self.types.get(t).types().to_vec();
        for current in constituents {
            for prop in self.get_properties_of_type(current) {
                let name = self.sym(prop).name.clone();
                if !checked.contains(&name) {
                    checked.insert(name.clone());
                    if let Some(combined_prop) = self.get_property_of_union_or_intersection_type(
                        t,
                        &name,
                        is_intersection, /*skipObjectFunctionPropertyAugment*/
                    ) {
                        props.push(combined_prop);
                    }
                }
            }
            // The properties of a union type are those that are present in all
            // constituent types, so we only need to check the properties of
            // the first type without index signature
            if is_union && self.get_index_infos_of_type(current).is_empty() {
                break;
            }
        }
        self.types
            .get_mut(t)
            .as_union_or_intersection_type_mut()
            .resolved_properties = props.clone();
        props
    }

    /// `(c *Checker) getPropertyOfType` (checker.go:19292).
    pub(crate) fn get_property_of_type(&mut self, t: TypeId, name: &str) -> Option<SymbolId> {
        self.get_property_of_type_ex(
            t,
            name,
            false, /*skipObjectFunctionPropertyAugment*/
            false, /*includeTypeOnlyMembers*/
        )
    }

    /// `(c *Checker) getPropertyOfTypeEx` (checker.go:19296) — return the
    /// symbol for the property with the given name in the given type. Creates
    /// synthetic union properties when necessary, maps primitive types and
    /// type parameters are to their apparent types, and augments with
    /// properties from Object and Function as appropriate.
    pub(crate) fn get_property_of_type_ex(
        &mut self,
        t: TypeId,
        name: &str,
        skip_object_function_property_augment: bool,
        include_type_only_members: bool,
    ) -> Option<SymbolId> {
        let t = self.get_reduced_apparent_type(t);
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::OBJECT) {
            let resolved = self.resolve_structured_type_members(t);
            let (members, call_signature_count, construct_signature_count) = {
                let g = self.types.get(resolved);
                let st = g.as_structured_type().expect("structured type");
                (
                    st.members.clone(),
                    st.call_signature_count,
                    st.signatures.len() - st.call_signature_count,
                )
            };
            let symbol = members.get(name);
            if let Some(symbol_id) = symbol {
                if !include_type_only_members
                    && let Some(t_symbol) = self.types.get(t).symbol
                    && self
                        .sym(t_symbol)
                        .flags
                        .intersects(ast::SymbolFlags::VALUE_MODULE)
                    && self
                        .module_symbol_links
                        .get(t_symbol)
                        .type_only_export_star_map
                        .get(name)
                        .is_some()
                {
                    // If this is the type of a module, `resolved.members.get(name)`
                    // might have effectively skipped over an `export type * from
                    // './foo'`, leaving `symbolIsValue` unable to see that the
                    // symbol is being viewed through a type-only export.
                    return None;
                }
                if self.symbol_is_value_ex(symbol_id, include_type_only_members) {
                    return symbol;
                }
            }
            if skip_object_function_property_augment {
                return None;
            }
            let function_type = if t == self.any_function_type {
                Some(self.global_function_type)
            } else if call_signature_count != 0 {
                Some(self.global_callable_function_type)
            } else if construct_signature_count != 0 {
                Some(self.global_newable_function_type)
            } else {
                None
            };
            if let Some(function_type) = function_type {
                let symbol = self.get_property_of_object_type(function_type, name);
                if symbol.is_some() {
                    return symbol;
                }
            }
            let global_object_type = self.global_object_type;
            return self.get_property_of_object_type(global_object_type, name);
        }
        if flags.intersects(TypeFlags::INTERSECTION) {
            let prop = self.get_property_of_union_or_intersection_type(
                t,
                name,
                true, /*skipObjectFunctionPropertyAugment*/
            );
            if prop.is_some() {
                return prop;
            }
            if !skip_object_function_property_augment {
                return self.get_property_of_union_or_intersection_type(
                    t,
                    name,
                    skip_object_function_property_augment,
                );
            }
            return None;
        }
        if flags.intersects(TypeFlags::UNION) {
            return self.get_property_of_union_or_intersection_type(
                t,
                name,
                skip_object_function_property_augment,
            );
        }
        None
    }

    /// `(c *Checker) getTypeOfPropertyOfType` (checker.go:19358) — return the
    /// type of the given property in the given type, or nil if no such
    /// property exists.
    pub(crate) fn get_type_of_property_of_type(
        &mut self,
        t: TypeId,
        name: &str,
    ) -> Option<TypeId> {
        let prop = self.get_property_of_type(t, name);
        prop.map(|prop| self.get_type_of_symbol(prop))
    }

    /// `(c *Checker) getSignaturesOfType` (checker.go:19366).
    pub(crate) fn get_signatures_of_type(
        &mut self,
        t: TypeId,
        kind: SignatureKind,
    ) -> Vec<SignatureId> {
        let t = self.get_reduced_apparent_type(t);
        self.get_signatures_of_structured_type(t, kind)
    }

    /// `(c *Checker) getSignaturesOfStructuredType` (checker.go:19370).
    pub(crate) fn get_signatures_of_structured_type(
        &mut self,
        t: TypeId,
        kind: SignatureKind,
    ) -> Vec<SignatureId> {
        if !self
            .types
            .get(t)
            .flags
            .intersects(TypeFlags::STRUCTURED_TYPE)
        {
            return Vec::new();
        }
        let resolved = self.resolve_structured_type_members(t);
        let (call_signature_count, signatures) = {
            let g = self.types.get(resolved);
            let st = g.as_structured_type().expect("structured type");
            (st.call_signature_count, st.signatures.clone())
        };
        if kind == SignatureKind::CALL {
            signatures[..call_signature_count].to_vec()
        } else {
            signatures[call_signature_count..].to_vec()
        }
    }

    /// `(c *Checker) getIndexInfosOfType` (checker.go:19381).
    ///
    /// PORT: Go `[]*IndexInfo` → `Vec<IndexInfoId>`. `StructuredType` stores
    /// inline `Vec<IndexInfo>` copies (see `set_structured_type_members`), so
    /// the copies are re-interned into `index_info_arena` — the two sentinel
    /// infos (`enum_number_index_info`, `any_base_type_index_info`) keep their
    /// identity via value equality.
    pub(crate) fn get_index_infos_of_type(&mut self, t: TypeId) -> Vec<IndexInfoId> {
        let t = self.get_reduced_apparent_type(t);
        self.get_index_infos_of_structured_type(t)
    }

    /// `(c *Checker) getIndexInfosOfStructuredType` (checker.go:19385).
    pub(crate) fn get_index_infos_of_structured_type(
        &mut self,
        t: TypeId,
    ) -> Vec<IndexInfoId> {
        if self
            .types
            .get(t)
            .flags
            .intersects(TypeFlags::STRUCTURED_TYPE)
        {
            let resolved = self.resolve_structured_type_members(t);
            let index_infos = {
                let g = self.types.get(resolved);
                let st = g.as_structured_type().expect("structured type");
                st.index_infos.clone()
            };
            return index_infos
                .iter()
                .map(|info| self.intern_index_info(info))
                .collect();
        }
        Vec::new()
    }

    /// PORT helper — re-intern a stored `IndexInfo` copy into
    /// `index_info_arena`, preserving `enum_number_index_info` and
    /// `any_base_type_index_info` identity (Go relies on `*IndexInfo` pointer
    /// equality for these sentinels).
    fn intern_index_info(&mut self, info: &IndexInfo) -> IndexInfoId {
        for sentinel in [self.enum_number_index_info, self.any_base_type_index_info] {
            if !sentinel.is_none() {
                let stored = self.index_info_arena.get(sentinel);
                if stored.key_type == info.key_type
                    && stored.value_type == info.value_type
                    && stored.is_readonly == info.is_readonly
                    && stored.declaration == info.declaration
                    && stored.index_symbol == info.index_symbol
                {
                    return sentinel;
                }
            }
        }
        self.index_info_arena.alloc(info.clone())
    }

    /// `(c *Checker) getIndexInfoOfType` (checker.go:19392) — return the
    /// indexing info of the given kind in the given type. Creates synthetic
    /// union index types when necessary and maps primitive types and type
    /// parameters are to their apparent types.
    pub(crate) fn get_index_info_of_type(
        &mut self,
        t: TypeId,
        key_type: TypeId,
    ) -> Option<IndexInfoId> {
        let index_infos = self.get_index_infos_of_type(t);
        find_index_info(&index_infos, key_type, &self.index_info_arena)
    }

    /// `(c *Checker) getIndexTypeOfType` (checker.go:19397) — return the index
    /// type of the given kind in the given type. Creates synthetic union index
    /// types when necessary and maps primitive types and type parameters are
    /// to their apparent types.
    pub(crate) fn get_index_type_of_type(
        &mut self,
        t: TypeId,
        key_type: TypeId,
    ) -> Option<TypeId> {
        let info = self.get_index_info_of_type(t, key_type);
        info.map(|info| self.index_info_arena.get(info).value_type.unwrap_or(self.any_type))
    }

    /// `(c *Checker) getIndexTypeOfTypeEx` (checker.go:19405).
    pub(crate) fn get_index_type_of_type_ex(
        &mut self,
        t: TypeId,
        key_type: TypeId,
        default_type: TypeId,
    ) -> TypeId {
        if let Some(result) = self.get_index_type_of_type(t, key_type) {
            return result;
        }
        default_type
    }

    /// `(c *Checker) getApplicableIndexInfo` (checker.go:19412).
    pub(crate) fn get_applicable_index_info(
        &mut self,
        t: TypeId,
        key_type: TypeId,
    ) -> Option<IndexInfoId> {
        let index_infos = self.get_index_infos_of_type(t);
        self.find_applicable_index_info(&index_infos, key_type)
    }

    /// `(c *Checker) getApplicableIndexInfoForName` (checker.go:19416).
    pub(crate) fn get_applicable_index_info_for_name(
        &mut self,
        t: TypeId,
        name: &str,
    ) -> Option<IndexInfoId> {
        if crate::checker_d::is_late_bound_name(name) {
            let es_symbol_type = self.es_symbol_type;
            return self.get_applicable_index_info(t, es_symbol_type);
        }
        let key_type = self.get_string_literal_type(name);
        self.get_applicable_index_info(t, key_type)
    }

    /// `(c *Checker) findApplicableIndexInfo` (checker.go:19423).
    pub(crate) fn find_applicable_index_info(
        &mut self,
        index_infos: &[IndexInfoId],
        key_type: TypeId,
    ) -> Option<IndexInfoId> {
        // Index signatures for type 'string' are considered only when no other
        // index signatures apply.
        let mut string_index_info: Option<IndexInfoId> = None;
        let mut applicable_infos: Vec<IndexInfoId> = Vec::with_capacity(8);
        for &info in index_infos {
            let info_key_type = self
                .index_info_arena
                .get(info)
                .key_type
                .expect("index info key type");
            if info_key_type == self.string_type {
                string_index_info = Some(info);
            } else if self.is_applicable_index_type(key_type, info_key_type) {
                applicable_infos.push(info);
            }
        }
        // When more than one index signature is applicable we create a
        // synthetic IndexInfo. Instead of computing the intersected key type,
        // we just use unknownType for the key type as nothing actually depends
        // on the keyType property of the returned IndexInfo.
        match applicable_infos.len() {
            0 => {
                if let Some(string_index_info) = string_index_info {
                    let string_type = self.string_type;
                    if self.is_applicable_index_type(key_type, string_type) {
                        return Some(string_index_info);
                    }
                }
                None
            }
            1 => Some(applicable_infos[0]),
            _ => {
                let mut is_readonly = true;
                let mut types: Vec<TypeId> = Vec::with_capacity(applicable_infos.len());
                for &info in &applicable_infos {
                    let data = self.index_info_arena.get(info).clone();
                    types.push(data.value_type.expect("index info value type"));
                    if !data.is_readonly {
                        is_readonly = false;
                    }
                }
                let intersection = self.get_intersection_type(&types);
                let unknown_type = self.unknown_type;
                Some(self.new_index_info(unknown_type, intersection, is_readonly, None, vec![]))
            }
        }
    }

    /// `(c *Checker) isApplicableIndexType` (checker.go:19452) — a 'string'
    /// index signature applies to types assignable to 'string' or 'number',
    /// and a 'number' index signature applies to types assignable to 'number',
    /// `${number}` and numeric string literal types.
    pub(crate) fn is_applicable_index_type(&mut self, source: TypeId, target: TypeId) -> bool {
        self.is_type_assignable_to(source, target)
            || target == self.string_type && self.is_type_assignable_to(source, self.number_type)
            || target == self.number_type
                && (source == self.numeric_string_type
                    || self
                        .types
                        .get(source)
                        .flags
                        .intersects(TypeFlags::STRING_LITERAL)
                        && crate::scanner_utilities::is_numeric_literal_name(
                            &crate::checker_d::get_string_literal_value(&self.types, source),
                        ))
    }

    /// `(c *Checker) resolveStructuredTypeMembers` (checker.go:19459).
    ///
    /// PORT: Go returns `*StructuredType` (a view into `t`); the port's type
    /// arena is a `RwLock<Vec<Type>>`, so this returns `t` itself — callers
    /// re-read `self.types.get(t).as_structured_type()`.
    pub(crate) fn resolve_structured_type_members(&mut self, t: TypeId) -> TypeId {
        if !self
            .types
            .get(t)
            .object_flags
            .intersects(ObjectFlags::MEMBERS_RESOLVED)
        {
            let flags = self.types.get(t).flags;
            let object_flags = self.types.get(t).object_flags;
            if flags.intersects(TypeFlags::OBJECT) {
                if object_flags.intersects(ObjectFlags::REFERENCE) {
                    self.resolve_type_reference_members(t);
                } else if object_flags.intersects(ObjectFlags::CLASS_OR_INTERFACE) {
                    self.resolve_class_or_interface_members(t);
                } else if object_flags.intersects(ObjectFlags::REVERSE_MAPPED) {
                    self.resolve_reverse_mapped_type_members(t);
                } else if object_flags.intersects(ObjectFlags::ANONYMOUS) {
                    self.resolve_anonymous_type_members(t);
                } else if object_flags.intersects(ObjectFlags::MAPPED) {
                    self.resolve_mapped_type_members(t);
                } else {
                    panic!("Unhandled case in resolveStructuredTypeMembers")
                }
            } else if flags.intersects(TypeFlags::UNION) {
                self.resolve_union_type_members(t);
            } else if flags.intersects(TypeFlags::INTERSECTION) {
                self.resolve_intersection_type_members(t);
            } else {
                panic!("Unhandled case in resolveStructuredTypeMembers")
            }
        }
        t
    }

    /// `(c *Checker) resolveClassOrInterfaceMembers` (checker.go:19484).
    pub(crate) fn resolve_class_or_interface_members(&mut self, t: TypeId) {
        self.resolve_object_type_members(t, t, &[], &[]);
    }

    /// `(c *Checker) resolveTypeReferenceMembers` (checker.go:19488).
    pub(crate) fn resolve_type_reference_members(&mut self, t: TypeId) {
        let source = self.types.get(t).target().expect("type reference target");
        let type_parameters = self
            .types
            .get(source)
            .as_interface_type()
            .expect("interface type")
            .all_type_parameters
            .clone();
        let type_arguments = self.get_type_arguments(t);
        let mut padded_type_arguments = type_arguments;
        if padded_type_arguments.len() + 1 == type_parameters.len() {
            padded_type_arguments.push(t);
        }
        self.resolve_object_type_members(
            t,
            source,
            &type_parameters,
            &padded_type_arguments,
        );
    }

    /// `(c *Checker) resolveObjectTypeMembers` (checker.go:19496).
    pub(crate) fn resolve_object_type_members(
        &mut self,
        t: TypeId,
        source: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
    ) {
        let mut mapper: Option<TypeMapperId> = None;
        let mut members: SymbolTable;
        let mut call_signatures: Vec<SignatureId>;
        let mut construct_signatures: Vec<SignatureId>;
        let mut index_infos: Vec<IndexInfoId>;
        let mut instantiated = false;
        let resolved = self.resolve_declared_members(source);
        let (
            declared_members,
            declared_call_signatures,
            declared_construct_signatures,
            declared_index_infos,
        ) = {
            let g = self.types.get(resolved);
            let data = g.as_interface_type().expect("interface type");
            (
                data.declared_members.clone(),
                data.declared_call_signatures.clone(),
                data.declared_construct_signatures.clone(),
                data.declared_index_infos.clone(),
            )
        };
        if type_parameters == type_arguments {
            members = declared_members;
            call_signatures = declared_call_signatures;
            construct_signatures = declared_construct_signatures;
            index_infos = declared_index_infos
                .iter()
                .map(|info| self.intern_index_info(info))
                .collect();
        } else {
            instantiated = true;
            mapper = Some(new_type_mapper(
                self,
                type_parameters.to_vec(),
                type_arguments.to_vec(),
            ));
            members =
                self.instantiate_symbol_table(&declared_members, mapper.unwrap());
            call_signatures =
                self.instantiate_signatures(&declared_call_signatures, mapper.unwrap());
            construct_signatures = self
                .instantiate_signatures(&declared_construct_signatures, mapper.unwrap());
            index_infos =
                self.instantiate_index_infos(&declared_index_infos, mapper.unwrap());
        }
        let base_types = self.get_base_types(source);
        if !base_types.is_empty() {
            if !instantiated {
                members = members.clone();
            }
            let this_argument = type_arguments.last().copied();
            for base_type in base_types {
                let mut instantiated_base_type = base_type;
                if let Some(this_argument) = this_argument {
                    instantiated_base_type = self.get_type_with_this_argument(
                        self.instantiate_type_ex(base_type, mapper, None),
                        this_argument,
                        false, /*needsApparentType*/
                    );
                }
                members = self.add_inherited_members(
                    members,
                    &self.get_properties_of_type(instantiated_base_type),
                );
                call_signatures.extend(
                    self.get_signatures_of_type(instantiated_base_type, SignatureKind::CALL),
                );
                construct_signatures.extend(
                    self.get_signatures_of_type(instantiated_base_type, SignatureKind::CONSTRUCT),
                );
                let inherited_index_infos: Vec<IndexInfoId> =
                    if instantiated_base_type != self.any_type {
                        self.get_index_infos_of_type(instantiated_base_type)
                    } else {
                        vec![self.any_base_type_index_info]
                    };
                index_infos.extend(inherited_index_infos.iter().copied().filter(|&info| {
                    let key_type = self.index_info_arena.get(info).key_type;
                    find_index_info(&index_infos, key_type.expect("index info key type"), &self.index_info_arena)
                        .is_none()
                }));
            }
        }
        self.set_structured_type_members(
            t,
            members,
            &call_signatures,
            &construct_signatures,
            &index_infos,
        );
    }

    /// `(c *Checker) getBaseTypes` (checker.go:19571).
    pub(crate) fn get_base_types(&mut self, t: TypeId) -> Vec<TypeId> {
        if !self
            .types
            .get(t)
            .object_flags
            .intersects(ObjectFlags::CLASS_OR_INTERFACE | ObjectFlags::TUPLE)
        {
            return Vec::new();
        }
        if !self
            .types
            .get(t)
            .as_interface_type()
            .expect("interface type")
            .base_types_resolved
        {
            if !self.push_type_resolution(
                TypeSystemEntity::Type(t),
                TypeSystemPropertyName::ResolvedBaseTypes,
            ) {
                return self
                    .types
                    .get(t)
                    .as_interface_type()
                    .expect("interface type")
                    .resolved_base_types
                    .clone();
            }
            let object_flags = self.types.get(t).object_flags;
            let symbol = self.types.get(t).symbol;
            if object_flags.intersects(ObjectFlags::TUPLE) {
                let tuple_base = self.get_tuple_base_type(t);
                self.types
                    .get_mut(t)
                    .as_interface_type_mut()
                    .expect("interface type")
                    .resolved_base_types = vec![tuple_base];
            } else if let Some(symbol) = symbol
                && self
                    .sym(symbol)
                    .flags
                    .intersects(ast::SymbolFlags::CLASS | ast::SymbolFlags::INTERFACE)
            {
                if self.sym(symbol).flags.intersects(ast::SymbolFlags::CLASS) {
                    self.resolve_base_types_of_class(t);
                }
                if self
                    .sym(symbol)
                    .flags
                    .intersects(ast::SymbolFlags::INTERFACE)
                {
                    self.resolve_base_types_of_interface(t);
                }
            } else {
                panic!("Unhandled case in getBaseTypes")
            }
            if !self.pop_type_resolution()
                && let Some(symbol) = self.types.get(t).symbol
            {
                let declarations = self.sym(symbol).declarations.clone();
                for declaration in declarations {
                    let nodes = self.program_nodes(declaration);
                    if ast::is_class_declaration(&nodes[declaration])
                        || ast::is_interface_declaration(&nodes[declaration])
                    {
                        self.report_circular_base_type(declaration, t);
                    }
                }
            }
            // In general, base type resolution always precedes member
            // resolution. However, it is possible for resolution of type
            // parameter defaults to cause circularity errors, possibly leaving
            // members partially resolved. Here we ensure any such partial
            // resolution is reset.
            // See https://github.com/microsoft/TypeScript/issues/16861 for an
            // example.
            self.types
                .get_mut(t)
                .object_flags
                .remove(ObjectFlags::MEMBERS_RESOLVED);
            self.types
                .get_mut(t)
                .as_interface_type_mut()
                .expect("interface type")
                .base_types_resolved = true;
        }
        self.types
            .get(t)
            .as_interface_type()
            .expect("interface type")
            .resolved_base_types
            .clone()
    }

    /// `(c *Checker) getTupleBaseType` (checker.go:19602).
    pub(crate) fn get_tuple_base_type(&mut self, t: TypeId) -> TypeId {
        let (type_parameters, element_infos, readonly) = {
            let g = self.types.get(t);
            let data = g.as_tuple_type().expect("tuple type");
            (
                data.interface_type.type_parameters().to_vec(),
                data.element_infos.clone(),
                data.readonly,
            )
        };
        let mut element_types: Vec<TypeId> = Vec::with_capacity(type_parameters.len());
        for (i, tp) in type_parameters.iter().copied().enumerate() {
            if element_infos[i].flags.intersects(ElementFlags::VARIADIC) {
                let number_type = self.number_type;
                element_types.push(self.get_indexed_access_type(tp, number_type));
            } else {
                element_types.push(tp);
            }
        }
        let union = self.get_union_type(&element_types);
        self.create_array_type_ex(union, readonly)
    }

    /// `(c *Checker) resolveBaseTypesOfClass` (checker.go:19616).
    pub(crate) fn resolve_base_types_of_class(&mut self, t: TypeId) {
        let base_constructor_type = {
            let base = self.get_base_constructor_type_of_class(t);
            self.get_apparent_type(base)
        };
        if !self.types.get(base_constructor_type).flags.intersects(
            TypeFlags::OBJECT | TypeFlags::INTERSECTION | TypeFlags::ANY,
        ) {
            return;
        }
        // PORT: Go dereferences `baseTypeNode` without a nil check — an
        // `expect` mirrors the panic.
        let base_type_node =
            get_base_type_node_of_class(self, t).expect("base type node");
        let base_constructor_symbol = self.types.get(base_constructor_type).symbol;
        let mut original_base_type: Option<TypeId> = None;
        if let Some(symbol) = base_constructor_symbol {
            original_base_type = Some(self.get_declared_type_of_symbol(symbol));
        }
        let base_type: TypeId;
        if let Some(symbol) = base_constructor_symbol
            && self.sym(symbol).flags.intersects(ast::SymbolFlags::CLASS)
            && self.are_all_outer_type_parameters_applied(original_base_type.unwrap())
        {
            // When base constructor type is a class with no captured type
            // arguments we know that the constructors all have the same type
            // parameters as the class and all return the instance type of the
            // class. There is no need for further checks and we can apply the
            // type arguments in the same manner as a type reference to get
            // the same error reporting experience.
            base_type = self.get_type_from_class_or_interface_reference(base_type_node, symbol);
        } else if self
            .types
            .get(base_constructor_type)
            .flags
            .intersects(TypeFlags::ANY)
        {
            base_type = base_constructor_type;
        } else {
            // The class derives from a "class-like" constructor function,
            // check that we have at least one construct signature with a
            // matching number of type parameters and use the return type of
            // the first instantiated signature. Elsewhere we check that all
            // instantiated signatures return the same type.
            let type_argument_nodes = {
                let nodes = self.program_nodes(base_type_node);
                nodes[base_type_node]
                    .type_arguments()
                    .unwrap_or(&[])
                    .to_vec()
            };
            let constructors = self.get_instantiated_constructors_for_type_arguments(
                base_constructor_type,
                &type_argument_nodes,
                base_type_node,
            );
            if constructors.is_empty() {
                let nodes = self.program_nodes(base_type_node);
                let expression = nodes[base_type_node].expression();
                self.error(
                    expression,
                    &tsc_diagnostics::No_base_constructor_has_the_specified_number_of_type_arguments,
                    &[] as &[String],
                );
                return;
            }
            base_type = self.get_return_type_of_signature(constructors[0]);
        }
        if self.is_error_type(base_type) {
            return;
        }
        let reduced_base_type = self.get_reduced_type(base_type);
        if !self.is_valid_base_type(reduced_base_type) {
            let nodes = self.program_nodes(base_type_node);
            let error_node = nodes[base_type_node].expression();
            let diagnostic = self.elaborate_never_intersection(None, error_node, base_type);
            let type_str = self.type_to_string(reduced_base_type);
            let diagnostic = crate::utilities::new_diagnostic_chain_for_node(
                self,
                diagnostic,
                error_node,
                &tsc_diagnostics::Base_constructor_return_type_0_is_not_an_object_type_or_intersection_of_object_types_with_statically_known_members,
                &[type_str],
            );
            self.add_diagnostic(diagnostic);
            return;
        }
        if t == reduced_base_type || self.has_base_type(reduced_base_type, t) {
            let symbol = self.types.get(t).symbol;
            let value_declaration = symbol.and_then(|s| self.sym(s).value_declaration);
            let type_str = self.type_to_string(t);
            self.error(
                value_declaration,
                &tsc_diagnostics::Type_0_recursively_references_itself_as_a_base_type,
                &[type_str],
            );
            return;
        }
        self.types
            .get_mut(t)
            .as_interface_type_mut()
            .expect("interface type")
            .resolved_base_types = vec![reduced_base_type];
    }

    /// `(c *Checker) getInstantiatedConstructorsForTypeArguments`
    /// (checker.go:19679).
    pub(crate) fn get_instantiated_constructors_for_type_arguments(
        &mut self,
        t: TypeId,
        type_argument_nodes: &[NodeId],
        location: NodeId,
    ) -> Vec<SignatureId> {
        let signatures =
            self.get_constructors_for_type_arguments(t, type_argument_nodes, location);
        let type_arguments: Vec<TypeId> = type_argument_nodes
            .iter()
            .copied()
            .map(|n| self.get_type_from_type_node(n))
            .collect();
        let is_javascript =
            ast::is_in_js_file(Some(location), &self.program_nodes(location));
        signatures
            .iter()
            .copied()
            .map(|sig| {
                if !self.signature_arena.get(sig).type_parameters.is_empty() {
                    self.get_signature_instantiation(sig, &type_arguments, is_javascript, None)
                } else {
                    sig
                }
            })
            .collect()
    }

    /// `(c *Checker) getConstructorsForTypeArguments` (checker.go:19693).
    pub(crate) fn get_constructors_for_type_arguments(
        &mut self,
        t: TypeId,
        type_argument_nodes: &[NodeId],
        _location: NodeId,
    ) -> Vec<SignatureId> {
        let type_arg_count = type_argument_nodes.len();
        let signatures = self.get_signatures_of_type(t, SignatureKind::CONSTRUCT);
        signatures
            .iter()
            .copied()
            .filter(|&sig| {
                let type_parameters =
                    self.signature_arena.get(sig).type_parameters.clone();
                type_arg_count >= self.get_min_type_argument_count(&type_parameters)
                    && type_arg_count <= type_parameters.len()
            })
            .collect()
    }

    /// `(c *Checker) getSignatureInstantiation` (checker.go:19697).
    pub(crate) fn get_signature_instantiation(
        &mut self,
        sig: SignatureId,
        type_arguments: &[TypeId],
        is_javascript: bool,
        inferred_type_parameters: Option<&[TypeId]>,
    ) -> SignatureId {
        let sig_type_parameters = self.signature_arena.get(sig).type_parameters.clone();
        let min_count = self.get_min_type_argument_count(&sig_type_parameters);
        let filled = self.fill_missing_type_arguments(
            type_arguments,
            &sig_type_parameters,
            min_count,
            is_javascript,
        );
        let instantiated_signature = self
            .get_signature_instantiation_without_filling_in_type_arguments(sig, &filled);
        if let Some(inferred_type_parameters) = inferred_type_parameters
            && !inferred_type_parameters.is_empty()
        {
            let return_type = self.get_return_type_of_signature(instantiated_signature);
            if let Some(return_signature) =
                self.get_single_call_or_construct_signature(return_type)
            {
                let new_return_signature = self.clone_signature(return_signature);
                self.signature_arena.get_mut(new_return_signature).type_parameters =
                    inferred_type_parameters.to_vec();
                let new_return_type = self.get_or_create_type_from_signature(new_return_signature);
                self.types
                    .get_mut(new_return_type)
                    .as_object_type_mut()
                    .expect("object type")
                    .mapper = self.signature_arena.get(instantiated_signature).mapper;
                let new_instantiated_signature =
                    self.clone_signature(instantiated_signature);
                self.signature_arena
                    .get_mut(new_instantiated_signature)
                    .resolved_return_type = Some(new_return_type);
                return new_instantiated_signature;
            }
        }
        instantiated_signature
    }

    /// `(c *Checker) cloneSignature` (checker.go:19716).
    pub(crate) fn clone_signature(&mut self, sig: SignatureId) -> SignatureId {
        let (flags, declaration, type_parameters, this_parameter, parameters, min_argument_count, target, mapper, composite) = {
            let s = self.signature_arena.get(sig);
            (
                s.flags & SignatureFlags::PROPAGATING_FLAGS,
                s.declaration,
                s.type_parameters.clone(),
                s.this_parameter,
                s.parameters.clone(),
                s.min_argument_count,
                s.target,
                s.mapper,
                s.composite,
            )
        };
        let result = self.new_signature(
            flags,
            declaration,
            type_parameters,
            this_parameter,
            parameters,
            None,
            None,
            min_argument_count as i32,
        );
        let mut g = self.signature_arena.get_mut(result);
        g.target = target;
        g.mapper = mapper;
        g.composite = composite;
        result
    }

    /// `(c *Checker) getSignatureInstantiationWithoutFillingInTypeArguments`
    /// (checker.go:19722).
    pub(crate) fn get_signature_instantiation_without_filling_in_type_arguments(
        &mut self,
        sig: SignatureId,
        type_arguments: &[TypeId],
    ) -> SignatureId {
        let key = CachedSignatureKey {
            sig: Some(sig),
            key: get_type_list_key(type_arguments),
        };
        if let Some(&instantiation) = self.cached_signatures.get(&key) {
            return instantiation;
        }
        let instantiation = self.create_signature_instantiation(sig, type_arguments);
        self.cached_signatures.insert(key, instantiation);
        instantiation
    }

    /// `(c *Checker) createSignatureInstantiation` (checker.go:19731).
    pub(crate) fn create_signature_instantiation(
        &mut self,
        sig: SignatureId,
        type_arguments: &[TypeId],
    ) -> SignatureId {
        let mapper = self.create_signature_type_mapper(sig, type_arguments);
        self.instantiate_signature_ex(sig, mapper, true /*eraseTypeParameters*/)
    }

    /// `(c *Checker) createSignatureTypeMapper` (checker.go:19735).
    pub(crate) fn create_signature_type_mapper(
        &mut self,
        sig: SignatureId,
        type_arguments: &[TypeId],
    ) -> TypeMapperId {
        let sources = self.get_type_parameters_for_mapper(sig);
        new_type_mapper(self, sources, type_arguments.to_vec())
    }

    /// `(c *Checker) getTypeParametersForMapper` (checker.go:19739).
    pub(crate) fn get_type_parameters_for_mapper(&mut self, sig: SignatureId) -> Vec<TypeId> {
        let type_parameters = self.signature_arena.get(sig).type_parameters.clone();
        core::same_map(&type_parameters, |tp| {
            let mapper = self.types.get(*tp).mapper();
            self.instantiate_type(*tp, mapper)
        })
        .into_owned()
    }

    /// `(c *Checker) getSingleCallSignature` (checker.go:19743) — if type has
    /// a single call signature and no other members, return that signature.
    /// Otherwise, return None.
    pub(crate) fn get_single_call_signature(&mut self, t: TypeId) -> Option<SignatureId> {
        self.get_single_signature(t, SignatureKind::CALL, false /*allowMembers*/)
    }

    /// `(c *Checker) getSingleCallOrConstructSignature` (checker.go:19748).
    pub(crate) fn get_single_call_or_construct_signature(
        &mut self,
        t: TypeId,
    ) -> Option<SignatureId> {
        let call_sig =
            self.get_single_signature(t, SignatureKind::CALL, false /*allowMembers*/);
        if call_sig.is_some() {
            return call_sig;
        }
        self.get_single_signature(t, SignatureKind::CONSTRUCT, false /*allowMembers*/)
    }

    /// `(c *Checker) getSingleSignature` (checker.go:19756).
    pub(crate) fn get_single_signature(
        &mut self,
        t: TypeId,
        kind: SignatureKind,
        allow_members: bool,
    ) -> Option<SignatureId> {
        if self.types.get(t).flags.intersects(TypeFlags::OBJECT) {
            let resolved = self.resolve_structured_type_members(t);
            let (properties_len, index_infos_len, call_sigs, construct_sigs) = {
                let g = self.types.get(resolved);
                let st = g.as_structured_type().expect("structured type");
                (
                    st.properties.len(),
                    st.index_infos.len(),
                    st.call_signatures().to_vec(),
                    st.construct_signatures().to_vec(),
                )
            };
            if allow_members || (properties_len == 0 && index_infos_len == 0) {
                if kind == SignatureKind::CALL
                    && call_sigs.len() == 1
                    && construct_sigs.is_empty()
                {
                    return Some(call_sigs[0]);
                }
                if kind == SignatureKind::CONSTRUCT
                    && construct_sigs.len() == 1
                    && call_sigs.is_empty()
                {
                    return Some(construct_sigs[0]);
                }
            }
        }
        None
    }

    /// `(c *Checker) getOrCreateTypeFromSignature` (checker.go:19770) — there
    /// are two ways to declare a construct signature, one is by declaring a
    /// class constructor using the constructor keyword, and the other is
    /// declaring a bare construct signature in an object type literal or
    /// interface (using the new keyword). Each way of declaring a constructor
    /// will result in a different declaration kind.
    pub(crate) fn get_or_create_type_from_signature(
        &mut self,
        sig: SignatureId,
    ) -> TypeId {
        if self
            .signature_arena
            .get(sig)
            .isolated_signature_type
            .is_none()
        {
            let (declaration_kind, symbol) = {
                let s = self.signature_arena.get(sig);
                let declaration = s.declaration;
                let kind = declaration.map(|d| self.program_nodes(d)[d].kind);
                let symbol = declaration.and_then(|d| self.program_nodes(d)[d].symbol());
                (kind, symbol)
            };
            // If declaration is undefined, it is likely to be the signature of
            // the default constructor.
            let is_constructor = matches!(
                declaration_kind,
                None | Some(
                    ast::Kind::Unknown
                        | ast::Kind::Constructor
                        | ast::Kind::ConstructSignature
                        | ast::Kind::ConstructorType
                )
            );
            let t = self.new_object_type(
                ObjectFlags::ANONYMOUS | ObjectFlags::SINGLE_SIGNATURE_TYPE,
                symbol,
            );
            if is_constructor {
                self.set_structured_type_members(t, SymbolTable::new(), &[], &[sig], &[]);
            } else {
                self.set_structured_type_members(t, SymbolTable::new(), &[sig], &[], &[]);
            }
            self.signature_arena.get_mut(sig).isolated_signature_type = Some(t);
        }
        self.signature_arena
            .get(sig)
            .isolated_signature_type
            .unwrap()
    }

    /// `(c *Checker) getErasedSignature` (checker.go:19797).
    pub(crate) fn get_erased_signature(&mut self, signature: SignatureId) -> SignatureId {
        let type_parameters = self.signature_arena.get(signature).type_parameters.clone();
        if type_parameters.is_empty() {
            return signature;
        }
        let key = CachedSignatureKey {
            sig: Some(signature),
            key: crate::checker_types::SIGNATURE_KEY_ERASED,
        };
        if let Some(&erased) = self.cached_signatures.get(&key) {
            return erased;
        }
        let any_type = self.any_type;
        let mapper = new_array_to_single_type_mapper(self, type_parameters, any_type);
        let erased = self.instantiate_signature_ex(signature, mapper, true /*eraseTypeParameters*/);
        self.cached_signatures.insert(key, erased);
        erased
    }

    /// `(c *Checker) getCanonicalSignature` (checker.go:19810).
    pub(crate) fn get_canonical_signature(&mut self, signature: SignatureId) -> SignatureId {
        let type_parameters = self.signature_arena.get(signature).type_parameters.clone();
        if type_parameters.is_empty() {
            return signature;
        }
        let key = CachedSignatureKey {
            sig: Some(signature),
            key: crate::checker_types::SIGNATURE_KEY_CANONICAL,
        };
        if let Some(&canonical) = self.cached_signatures.get(&key) {
            return canonical;
        }
        let canonical = self.create_canonical_signature(signature);
        self.cached_signatures.insert(key, canonical);
        canonical
    }

    /// `(c *Checker) createCanonicalSignature` (checker.go:19823) — create an
    /// instantiation of the signature where each unconstrained type parameter
    /// is replaced with its original. When a generic class or interface is
    /// instantiated, each generic method in the class or interface is
    /// instantiated with a fresh set of cloned type parameters (which we need
    /// to handle scenarios where different generations of the same type
    /// parameter are in scope). This leads to a lot of new type identities,
    /// and potentially a lot of work comparing those identities, so here we
    /// create an instantiation that uses the original type identities for
    /// all unconstrained type parameters.
    pub(crate) fn create_canonical_signature(&mut self, signature: SignatureId) -> SignatureId {
        let type_parameters = self.signature_arena.get(signature).type_parameters.clone();
        let type_arguments: Vec<TypeId> = type_parameters
            .iter()
            .copied()
            .map(|tp| {
                let target = self.types.get(tp).target();
                if let Some(target) = target
                    && self.get_constraint_of_type_parameter(target).is_none()
                {
                    return target;
                }
                tp
            })
            .collect();
        let is_javascript = {
            let declaration = self.signature_arena.get(signature).declaration;
            declaration.is_some_and(|d| ast::is_in_js_file(Some(d), &self.program_nodes(d)))
        };
        self.get_signature_instantiation(
            signature,
            &type_arguments,
            is_javascript,
            None, /*inferredTypeParameters*/
        )
    }

    /// `(c *Checker) getBaseSignature` (checker.go:19839).
    pub(crate) fn get_base_signature(&mut self, signature: SignatureId) -> SignatureId {
        let type_parameters = self.signature_arena.get(signature).type_parameters.clone();
        if type_parameters.is_empty() {
            return signature;
        }
        let key = CachedSignatureKey {
            sig: Some(signature),
            key: crate::checker_types::SIGNATURE_KEY_BASE,
        };
        if let Some(&cached) = self.cached_signatures.get(&key) {
            return cached;
        }
        let unknown_type = self.unknown_type;
        let base_constraint_mapper = new_type_mapper(
            self,
            type_parameters.clone(),
            type_parameters
                .iter()
                .copied()
                .map(|tp| self.get_constraint_of_type_parameter(tp).unwrap_or(unknown_type))
                .collect(),
        );
        let mut base_constraints: Vec<TypeId> = type_parameters
            .iter()
            .copied()
            .map(|tp| self.instantiate_type(tp, Some(base_constraint_mapper)))
            .collect();
        // Run the immediate constraint mapper N-1 times so non-circular
        // interdependent type parameters resolve to their external
        // dependencies without adding an extra expansion step for
        // self-recursive constraints.
        for _ in 0..type_parameters.len().saturating_sub(1) {
            base_constraints = self.instantiate_types(&base_constraints, Some(base_constraint_mapper));
        }
        // and then apply a type eraser to remove any remaining circularly
        // dependent type parameters
        let any_type = self.any_type;
        let eraser =
            new_array_to_single_type_mapper(self, type_parameters.clone(), any_type);
        base_constraints = self.instantiate_types(&base_constraints, Some(eraser));
        let result_mapper = new_type_mapper(self, type_parameters, base_constraints);
        let result =
            self.instantiate_signature_ex(signature, result_mapper, true /*eraseTypeParameters*/);
        self.cached_signatures.insert(key, result);
        result
    }

    /// `(c *Checker) instantiateSignatureInContextOf` (checker.go:19865) —
    /// instantiate a generic signature in the context of a non-generic
    /// signature (section 3.8.5 in TypeScript spec).
    pub(crate) fn instantiate_signature_in_context_of(
        &mut self,
        signature: SignatureId,
        contextual_signature: SignatureId,
        inference_context: Option<InferenceContextId>,
        compare_types: Rc<dyn Fn(&mut Checker, TypeId, TypeId) -> Ternary>,
    ) -> SignatureId {
        let type_params = self.get_type_parameters_for_mapper(signature);
        let context = self.new_inference_context(
            type_params,
            signature,
            InferenceFlags::NONE,
            compare_types,
        );
        // We clone the inferenceContext to avoid fixing. For example, when the
        // source signature is <T>(x: T) => T[] and the contextual signature is
        // (...args: A) => B, we want to infer the element type of A's
        // constraint (say 'any') for T but leave it possible to later infer
        // '[any]' back to A.
        let rest_type = self.get_effective_rest_type(contextual_signature);
        let mapper = inference_context.map(|ic| {
            if rest_type.is_some_and(|rt| {
                self.types.get(rt).flags.intersects(TypeFlags::TYPE_PARAMETER)
            }) {
                self.inference_contexts.get(ic).non_fixing_mapper()
            } else {
                self.inference_contexts.get(ic).mapper()
            }
        });
        let source_signature = if let Some(mapper) = mapper {
            self.instantiate_signature(contextual_signature, Some(mapper))
        } else {
            contextual_signature
        };
        let inferences = self.inference_contexts.get(context).inferences.clone();
        self.apply_to_parameter_types(
            source_signature,
            signature,
            Rc::new(move |c: &mut Checker, source: TypeId, target: TypeId| {
                // Type parameters from outer context referenced by source type
                // are fixed by instantiation of the source type
                c.infer_types(
                    inferences.clone(),
                    source,
                    target,
                    InferencePriority::NONE,
                    false,
                );
            }),
        );
        if inference_context.is_none() {
            let inferences = self.inference_contexts.get(context).inferences.clone();
            self.apply_to_return_types(
                contextual_signature,
                signature,
                Rc::new(move |c: &mut Checker, source: TypeId, target: TypeId| {
                    c.infer_types(
                        inferences.clone(),
                        source,
                        target,
                        InferencePriority::RETURN_TYPE,
                        false,
                    );
                }),
            );
        }
        let inferred = self.get_inferred_types(context);
        let is_javascript = {
            let declaration = self.signature_arena.get(contextual_signature).declaration;
            declaration.is_some_and(|d| ast::is_in_js_file(Some(d), &self.program_nodes(d)))
        };
        self.get_signature_instantiation(signature, &inferred, is_javascript, None)
    }

    // __NEXT_METHODS__
}

// ======== Free functions (Go `func` without a `*Checker` receiver) ========

/// `isObjectLiteralType` (checker.go) — package-level helper.
pub(crate) fn is_object_literal_type(types: &crate::types::TypeArena, t: TypeId) -> bool {
    types.get(t).object_flags.intersects(ObjectFlags::OBJECT_LITERAL)
}

/// `(w *WideningContext) getChildContext` (checker.go:18854).
pub(crate) fn widening_context_get_child_context(
    w: &Rc<RefCell<WideningContext>>,
    property_name: &str,
) -> Rc<RefCell<WideningContext>> {
    if let Some(cached) = w.borrow().child_contexts.get(property_name) {
        return cached.clone();
    }
    let result = Rc::new(RefCell::new(WideningContext {
        parent: Some(w.clone()),
        property_name: property_name.to_string(),
        siblings: Vec::new(),
        resolved_properties: Vec::new(),
        child_contexts: FxHashMap::default(),
        widened_types: FxHashMap::default(),
    }));
    w.borrow_mut()
        .child_contexts
        .insert(property_name.to_string(), result.clone());
    result
}

// __NEXT_FNS__
