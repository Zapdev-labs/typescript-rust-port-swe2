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
                TypeSystemPropertyName::ALIAS_TARGET,
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
                TypeSystemPropertyName::ALIAS_TARGET,
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
            TypeSystemPropertyName::TYPE,
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

    // __NEXT_METHODS__
}

// ======== Free functions (Go `func` without a `*Checker` receiver) ========

// __NEXT_FNS__
