// Ported from tsc/internal/checker/symbolaccessibility.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — the symbol-accessibility index
// state referenced by `Checker::external_module_containers` plus the
// `symbolTableID` machinery and `accessibleSymbolChainContext`. Query
// methods stay `PORT(deferred)` with the rest of symbolaccessibility.go.

use rustc_hash::{FxHashMap, FxHashSet};
use tsc_ast::{NodeId, SymbolFlags, SymbolId};

// externalModuleContainerIndex

/// `type externalModuleContainerIndex struct` (symbolaccessibility.go).
#[derive(Default)]
pub struct ExternalModuleContainerIndex {
    /// `complete`.
    pub complete: bool,
    /// `containersByTarget` — `map[*ast.Symbol][]*ast.Symbol`.
    pub containers_by_target: FxHashMap<SymbolId, Vec<SymbolId>>,
    /// `moduleOrder` — `map[*ast.Symbol]int`.
    pub module_order: FxHashMap<SymbolId, i32>,
}

impl ExternalModuleContainerIndex {
    /// `(index *externalModuleContainerIndex) add` — modules are indexed
    /// one at a time, so a repeat of this container is always the last
    /// entry.
    pub fn add(&mut self, target: SymbolId, container: SymbolId) {
        let existing = self.containers_by_target.entry(target).or_default();
        if existing.last() != Some(&container) {
            existing.push(container);
        }
    }
}

// accessibleSymbolChainContext

/// `type accessibleSymbolChainContext struct` (symbolaccessibility.go).
#[derive(Default)]
pub struct AccessibleSymbolChainContext {
    /// `symbol`.
    pub symbol: Option<SymbolId>,
    /// `enclosingDeclaration`.
    pub enclosing_declaration: Option<NodeId>,
    /// `meaning`.
    pub meaning: SymbolFlags,
    /// `useOnlyExternalAliasing`.
    pub use_only_external_aliasing: bool,
    /// `visitedSymbolTablesMap` — `map[ast.SymbolId]map[symbolTableID]struct{}`.
    /// PORT: keyed by the owning `SymbolId`; `Option<SymbolId>` callers use
    /// `SymbolId::NONE` like Go's nil-symbol key (never populated in
    /// practice — Go only inserts under non-nil symbols).
    pub visited_symbol_tables_map: FxHashMap<SymbolId, FxHashSet<SymbolTableId>>,
}

// symbolTableID

/// `type symbolTableID uint64` (symbolaccessibility.go) — uniquely
/// identifies a symbol table by encoding its source. The high 3 bits
/// encode the kind, and the remaining bits encode the `NodeId` or
/// `SymbolId` of the source.
///
/// PORT: widened to `u128` — Go's `ast.NodeId` is a sequential `uint32`,
/// but this port's `NodeId` packs `file:20|local:44` and uses all 64 bits,
/// so kind bits at 61–63 would collide with the file index.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[repr(transparent)]
pub struct SymbolTableId(pub u128);

/// `const stKindShift = 61` — in this port, above the 64-bit `NodeId`
/// payload (see the `u128` note above).
pub const ST_KIND_SHIFT: u32 = 64;

/// `stKindLocals`.
pub const ST_KIND_LOCALS: SymbolTableId = SymbolTableId(0 << ST_KIND_SHIFT);
/// `stKindExports`.
pub const ST_KIND_EXPORTS: SymbolTableId = SymbolTableId(1 << ST_KIND_SHIFT);
/// `stKindMembers`.
pub const ST_KIND_MEMBERS: SymbolTableId = SymbolTableId(2 << ST_KIND_SHIFT);
/// `stKindGlobals`.
pub const ST_KIND_GLOBALS: SymbolTableId = SymbolTableId(3 << ST_KIND_SHIFT);
/// `stKindResolvedExports` — resolved/derived exports from
/// `getExportsOfSymbol`, distinct from raw `sym.Exports`.
pub const ST_KIND_RESOLVED_EXPORTS: SymbolTableId = SymbolTableId(4 << ST_KIND_SHIFT);
/// `stKindMask` — extracts the kind bits from a `SymbolTableId`.
pub const ST_KIND_MASK: SymbolTableId = SymbolTableId(7 << ST_KIND_SHIFT);

/// `symbolTableIDFromLocals`.
pub fn symbol_table_id_from_locals(node: NodeId) -> SymbolTableId {
    SymbolTableId(ST_KIND_LOCALS.0 | node.0 as u128)
}

/// `symbolTableIDFromExports`.
pub fn symbol_table_id_from_exports(sym: SymbolId) -> SymbolTableId {
    SymbolTableId(ST_KIND_EXPORTS.0 | sym.0 as u128)
}

/// `symbolTableIDFromResolvedExports` — an ID for resolved/derived export
/// tables (e.g. from `getExportsOfSymbol`/`getExportsOfModule`, which may
/// include `export *` resolution and late-bound members). Distinct from
/// `symbol_table_id_from_exports` to prevent cache collisions with raw
/// `sym.exports` tables passed by `someSymbolTableInScope`.
pub fn symbol_table_id_from_resolved_exports(sym: SymbolId) -> SymbolTableId {
    SymbolTableId(ST_KIND_RESOLVED_EXPORTS.0 | sym.0 as u128)
}

/// `symbolTableIDFromMembers`.
pub fn symbol_table_id_from_members(sym: SymbolId) -> SymbolTableId {
    SymbolTableId(ST_KIND_MEMBERS.0 | sym.0 as u128)
}

/// `symbolTableIDFromGlobals`.
pub fn symbol_table_id_from_globals() -> SymbolTableId {
    ST_KIND_GLOBALS
}

/// `hasNonGlobalAugmentationExternalModuleSymbol` (symbolaccessibility.go:106).
/// The declaration may live in another file's arena — read it through
/// `Checker::program_nodes`.
pub(crate) fn has_non_global_augmentation_external_module_symbol(
    declaration: NodeId,
    c: &crate::checker_core::Checker,
) -> bool {
    let nodes = c.program_nodes(declaration);
    let d = &nodes[declaration];
    tsc_ast::is_module_with_string_literal_name(d, &nodes)
        || (d.kind == tsc_ast::Kind::SourceFile
            && tsc_ast::is_external_or_commonjs_module(d.as_source_file()))
}

/// `getQualifiedLeftMeaning` (symbolaccessibility.go:110) — if we are
/// looking in value space, the parent meaning is value, otherwise it is
/// namespace.
pub(crate) fn get_qualified_left_meaning(right_meaning: SymbolFlags) -> SymbolFlags {
    if right_meaning == SymbolFlags::VALUE {
        SymbolFlags::VALUE
    } else {
        SymbolFlags::NAMESPACE
    }
}

// ----------------------------------------------------------------------------
// `*Checker` accessibility queries (symbolaccessibility.go).
// ----------------------------------------------------------------------------

use tsc_ast::{self as ast, Node};
use tsc_ast::{Kind, SymbolTable};
use tsc_printer::{SymbolAccessibility, SymbolAccessibilityResult};

use crate::checker_core::Checker;
use crate::types::TypeFlags;

/// `symbol.name` / `symbol.flags` etc. bundle — `*ast.Symbol` reads that
/// would otherwise pin the `symbol_arena` `RefCell` across `&mut` calls.
fn sym_fields(
    c: &Checker,
    s: SymbolId,
) -> (SymbolFlags, Vec<NodeId>, Option<SymbolId>, String, Option<SymbolId>, SymbolTable, SymbolTable) {
    let sym = c.sym(s);
    (
        sym.flags,
        sym.declarations.clone(),
        sym.parent,
        sym.name.clone(),
        sym.export_symbol,
        sym.exports.clone(),
        sym.members.clone(),
    )
}

/// `symbol != nil` — `SymbolId::NONE` is the nil sentinel.
fn is_some_sym(s: SymbolId) -> bool {
    s != SymbolId::NONE
}

/// `c.getMergedSymbol` on an optional symbol (Go accepts nil).
fn merged(c: &mut Checker, s: Option<SymbolId>) -> Option<SymbolId> {
    s.map(|s| c.get_merged_symbol(s))
}

impl Checker {
    /// `(c *Checker) IsTypeSymbolAccessible` (symbolaccessibility.go).
    pub(crate) fn is_type_symbol_accessible(
        &mut self,
        type_symbol: Option<SymbolId>,
        enclosing_declaration: Option<NodeId>,
    ) -> bool {
        let access = self.is_symbol_accessible_worker(
            type_symbol,
            enclosing_declaration,
            ast::SymbolFlags::TYPE, // shouldComputeAliasesToMakeVisible
            false,
            true,
        );
        access.accessibility == SymbolAccessibility::Accessible
    }

    /// `(c *Checker) IsValueSymbolAccessible` (symbolaccessibility.go).
    pub(crate) fn is_value_symbol_accessible(
        &mut self,
        symbol: Option<SymbolId>,
        enclosing_declaration: Option<NodeId>,
    ) -> bool {
        let access = self.is_symbol_accessible_worker(
            symbol,
            enclosing_declaration,
            ast::SymbolFlags::VALUE, // shouldComputeAliasesToMakeVisible
            false,
            true,
        );
        access.accessibility == SymbolAccessibility::Accessible
    }

    /// `(c *Checker) IsSymbolAccessibleByFlags` (symbolaccessibility.go).
    pub(crate) fn is_symbol_accessible_by_flags(
        &mut self,
        symbol: Option<SymbolId>,
        enclosing_declaration: Option<NodeId>,
        flags: SymbolFlags,
    ) -> bool {
        let access = self.is_symbol_accessible_worker(
            symbol,
            enclosing_declaration,
            flags, // shouldComputeAliasesToMakeVisible
            false,
            false, // TODO: Strada bug? Why is this allowModules: false?
        );
        access.accessibility == SymbolAccessibility::Accessible
    }

    /// `(c *Checker) IsAnySymbolAccessible` (symbolaccessibility.go).
    pub(crate) fn is_any_symbol_accessible(
        &mut self,
        symbols: &[SymbolId],
        enclosing_declaration: Option<NodeId>,
        initial_symbol: Option<SymbolId>,
        meaning: SymbolFlags,
        should_compute_aliases_to_make_visible: bool,
        allow_modules: bool,
    ) -> Option<SymbolAccessibilityResult> {
        if symbols.is_empty() {
            return None;
        }

        let mut had_accessible_chain: Option<SymbolId> = None;
        let mut early_module_bail = false;
        for &symbol in symbols {
            // Symbol is accessible if it by itself is accessible
            let accessible_symbol_chain = self.get_accessible_symbol_chain(
                symbol,
                enclosing_declaration,
                meaning, /*useOnlyExternalAliasing*/
                false,
            );
            if !accessible_symbol_chain.is_empty() {
                had_accessible_chain = Some(symbol);
                let has_accessible_declarations = self.has_visible_declarations(
                    accessible_symbol_chain[0],
                    should_compute_aliases_to_make_visible,
                );
                if has_accessible_declarations.is_some() {
                    return has_accessible_declarations;
                }
            }
            if allow_modules {
                let (flags, decls, ..) = sym_fields(self, symbol);
                let _ = flags;
                if decls
                    .iter()
                    .any(|&d| has_non_global_augmentation_external_module_symbol(d, self))
                {
                    if should_compute_aliases_to_make_visible {
                        early_module_bail = true;
                        // Generally speaking, we want to use the aliases that already exist to refer to a module, if present
                        // In order to do so, we need to find those aliases in order to retain them in declaration emit; so
                        // if we are in declaration emit, we cannot use the fast path for module visibility until we've exhausted
                        // all other visibility options (in order to capture the possible aliases used to reference the module)
                        continue;
                    }
                    // Any meaning of a module symbol is always accessible via an `import` type
                    return Some(SymbolAccessibilityResult {
                        accessibility: SymbolAccessibility::Accessible,
                        ..Default::default()
                    });
                }
            }

            // If we haven't got the accessible symbol, it doesn't mean the symbol is actually inaccessible.
            // It could be a qualified symbol and hence verify the path
            // e.g.:
            // module m {
            //     export class c {
            //     }
            // }
            // const x: typeof m.c
            // In the above example when we start with checking if typeof m.c symbol is accessible,
            // we are going to see if c can be accessed in scope directly.
            // But it can't, hence the accessible is going to be undefined, but that doesn't mean m.c is inaccessible
            // It is accessible if the parent m is accessible because then m.c can be accessed through qualification

            let containers = self.get_containers_of_symbol(symbol, enclosing_declaration, meaning);
            let mut next_meaning = meaning;
            if initial_symbol == Some(symbol) {
                next_meaning = get_qualified_left_meaning(meaning);
            }
            if let Some(parent_result) = self.is_any_symbol_accessible(
                &containers,
                enclosing_declaration,
                initial_symbol,
                next_meaning,
                should_compute_aliases_to_make_visible,
                allow_modules,
            ) {
                return Some(parent_result);
            }
        }

        if early_module_bail {
            return Some(SymbolAccessibilityResult {
                accessibility: SymbolAccessibility::Accessible,
                ..Default::default()
            });
        }

        if let Some(had_accessible_chain) = had_accessible_chain {
            let mut module_name = String::new();
            if Some(had_accessible_chain) != initial_symbol {
                module_name = self.symbol_to_string_ex(
                    had_accessible_chain,
                    enclosing_declaration,
                    ast::SymbolFlags::NAMESPACE,
                    crate::types::SymbolFormatFlags::ALLOW_ANY_NODE_KIND,
                );
            }
            return Some(SymbolAccessibilityResult {
                accessibility: SymbolAccessibility::NotAccessible,
                error_symbol_name: self.symbol_to_string_ex(
                    initial_symbol.unwrap_or(SymbolId::NONE),
                    enclosing_declaration,
                    meaning,
                    crate::types::SymbolFormatFlags::ALLOW_ANY_NODE_KIND,
                ),
                error_module_name: module_name,
                ..Default::default()
            });
        }
        None
    }

    /// `(c *Checker) getWithAlternativeContainers` (symbolaccessibility.go).
    fn get_with_alternative_containers(
        &mut self,
        container: SymbolId,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        meaning: SymbolFlags,
    ) -> Vec<SymbolId> {
        let (_, container_decls, ..) = sym_fields(self, container);
        let additional_containers: Vec<SymbolId> = container_decls
            .iter()
            .filter_map(|&d| self.get_file_symbol_if_file_symbol_export_equals_container(d, container))
            .collect();
        let mut reexport_containers: Vec<SymbolId> = Vec::new();
        if enclosing_declaration.is_some() {
            reexport_containers =
                self.get_alternative_containing_modules(symbol, enclosing_declaration.unwrap());
        }
        let object_literal_container = self.get_variable_declaration_of_object_literal(container, meaning);
        let left_meaning = get_qualified_left_meaning(meaning);
        let container_flags = sym_fields(self, container).0;
        if enclosing_declaration.is_some()
            && container_flags.intersects(left_meaning)
            && !self
                .get_accessible_symbol_chain(
                    container,
                    enclosing_declaration,
                    ast::SymbolFlags::NAMESPACE, /*useOnlyExternalAliasing*/
                    false,
                )
                .is_empty()
        {
            // This order expresses a preference for the real container if it is in scope
            let mut res = vec![container];
            res.extend(additional_containers);
            res.extend(reexport_containers);
            if let Some(object_literal_container) = object_literal_container {
                res.push(object_literal_container);
            }
            return res;
        }
        // we potentially have a symbol which is a member of the instance side of something - look for a variable in scope with the container's type
        // which may be acting like a namespace (eg, `Symbol` acts like a namespace when looking up `Symbol.toStringTag`)
        let mut variable_matches: Vec<SymbolId> = Vec::new();
        if meaning == ast::SymbolFlags::VALUE
            && !container_flags.intersects(left_meaning)
            && container_flags.intersects(ast::SymbolFlags::TYPE)
            && {
                let declared = self.get_declared_type_of_symbol(container);
                self.types_handle().get(declared).flags.intersects(TypeFlags::OBJECT)
            }
        {
            let container_type = self.get_declared_type_of_symbol(container);
            self.some_symbol_table_in_scope(
                enclosing_declaration,
                |c2, t, _id, _ignore, _local, _scope| {
                    let mut found = false;
                    for (_, &s) in t {
                        if sym_fields(c2, s).0.intersects(left_meaning)
                            && c2.get_type_of_symbol(s) == container_type
                        {
                            variable_matches.push(s);
                            found = true;
                        }
                    }
                    found
                },
            );
            self.sort_symbols(&mut variable_matches);
        }

        let mut res: Vec<SymbolId> = Vec::new();
        res.extend(variable_matches);
        res.extend(additional_containers);
        res.push(container);
        if let Some(object_literal_container) = object_literal_container {
            res.push(object_literal_container);
        }
        res.extend(reexport_containers);
        res
    }

    /// `(c *Checker) getAlternativeContainingModules` (symbolaccessibility.go).
    fn get_alternative_containing_modules(
        &mut self,
        symbol: SymbolId,
        enclosing_declaration: NodeId,
    ) -> Vec<SymbolId> {
        let containing_file = {
            let nn = self.program_nodes(enclosing_declaration);
            ast::get_source_file_of_node(Some(enclosing_declaration), &nn)
        };
        let Some(containing_file) = containing_file else {
            return Vec::new();
        };
        let id = containing_file;
        {
            let links = self.symbol_container_links.try_get(&symbol);
            if let Some(existing) =
                links.and_then(|l| l.extended_containers_by_file.get(&id))
            {
                return existing.clone();
            }
        }
        let mut results: Vec<SymbolId> = Vec::new();
        let imports: Vec<NodeId> = {
            let nn = self.program_nodes(containing_file);
            nn[containing_file].as_source_file().imports.to_vec()
        };
        if !imports.is_empty() {
            // Try to make an import using an import already in the enclosing file, if possible
            for import_ref in imports {
                if {
                    let nn = self.program_nodes(import_ref);
                    ast::node_is_synthesized(&nn[import_ref])
                } {
                    // Synthetic names can't be resolved by `resolveExternalModuleName` - they'll cause a debug assert if they error
                    continue;
                }
                let attrs = self.get_import_attributes_type_for_module_specifier(import_ref);
                let Some(resolved_module) = self.resolve_external_module_name(
                    enclosing_declaration,
                    Some(import_ref), /*ignoreErrors*/
                    true,
                    attrs,
                ) else {
                    continue;
                };
                let Some(_ref) = self.get_alias_for_symbol_in_container(resolved_module, symbol)
                else {
                    continue;
                };
                results.push(resolved_module);
            }
            if !results.is_empty() {
                self.symbol_container_links
                    .get(symbol)
                    .extended_containers_by_file
                    .insert(id, results.clone());
                return results;
            }
        }

        if let Some(extended) = &self.symbol_container_links.get(symbol).extended_containers {
            return extended.clone();
        }
        // No results from files already being imported by this file - expand search (not location-specific, so cached)
        let results = self.get_external_module_containers(symbol);
        self.symbol_container_links
            .get(symbol)
            .extended_containers = Some(results.clone());
        results
    }

    /// `(c *Checker) getExternalModuleContainers` (symbolaccessibility.go).
    fn get_external_module_containers(&mut self, symbol: SymbolId) -> Vec<SymbolId> {
        if self.external_module_containers.is_none() {
            self.build_external_module_container_index();
        }
        if !self.external_module_containers.as_ref().unwrap().complete {
            // Re-entered from an alias resolved while building the index; answer this query without it.
            return self.scan_external_module_containers(symbol);
        }
        let target = self.get_resolved_target(symbol);
        let parent = self.get_parent_of_symbol(symbol);
        let (containers, parent_order, parent_is_module) = {
            let index = self.external_module_containers.as_ref().unwrap();
            (
                index.containers_by_target.get(&target).cloned().unwrap_or_default(),
                parent.and_then(|p| index.module_order.get(&p).copied()),
                parent.is_some_and(|p| index.module_order.contains_key(&p)),
            )
        };
        let Some(parent_order) = parent_order else {
            return containers;
        };
        let _ = parent_is_module;
        // The parent module contains the symbol even when the symbol is absent from its exports.
        let order_of = |c: SymbolId| -> i32 {
            self.external_module_containers
                .as_ref()
                .unwrap()
                .module_order
                .get(&c)
                .copied()
                .unwrap_or(i32::MAX)
        };
        match containers.binary_search_by_key(&parent_order, |&c| order_of(c)) {
            Err(at) => {
                let mut containers = containers;
                containers.insert(at, parent.unwrap());
                containers
            }
            Ok(_) => containers,
        }
    }

    /// `(c *Checker) buildExternalModuleContainerIndex` (symbolaccessibility.go).
    fn build_external_module_container_index(&mut self) {
        self.external_module_containers = Some(ExternalModuleContainerIndex::default());
        let files = self.files.clone();
        for file in files {
            let is_external = {
                let nn = self.program_nodes(file);
                ast::is_external_module(nn[file].as_source_file())
            };
            if !is_external {
                continue;
            }
            let Some(container) = self.get_symbol_of_declaration(file) else {
                continue;
            };
            {
                let order = self
                    .external_module_containers
                    .as_ref()
                    .unwrap()
                    .module_order
                    .len() as i32;
                self.external_module_containers
                    .as_mut()
                    .unwrap()
                    .module_order
                    .insert(container, order);
            }
            let exports = self.get_exports_of_symbol(container);
            let mut pairs: Vec<(SymbolId, SymbolId)> = Vec::new();
            for (_, &exported) in &exports {
                pairs.push((self.get_resolved_target(exported), container));
            }
            let export_equals = self
                .sym(container)
                .exports
                .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
                .copied();
            if let Some(export_equals) = export_equals {
                pairs.push((self.get_resolved_target(export_equals), container));
            }
            for (target, container) in pairs {
                self.external_module_containers
                    .as_mut()
                    .unwrap()
                    .add(target, container);
            }
        }
        self.external_module_containers.as_mut().unwrap().complete = true;
    }

    /// `(c *Checker) scanExternalModuleContainers` (symbolaccessibility.go).
    fn scan_external_module_containers(&mut self, symbol: SymbolId) -> Vec<SymbolId> {
        let mut containers = Vec::new();
        let files = self.files.clone();
        for file in files {
            let is_external = {
                let nn = self.program_nodes(file);
                ast::is_external_module(nn[file].as_source_file())
            };
            if !is_external {
                continue;
            }
            if let Some(container) = self.get_symbol_of_declaration(file)
                && self
                    .get_alias_for_symbol_in_container(container, symbol)
                    .is_some()
            {
                containers.push(container);
            }
        }
        containers
    }

    /// `(c *Checker) getVariableDeclarationOfObjectLiteral` (symbolaccessibility.go).
    fn get_variable_declaration_of_object_literal(
        &mut self,
        symbol: SymbolId,
        meaning: SymbolFlags,
    ) -> Option<SymbolId> {
        // If we're trying to reference some object literal in, eg `var a = { x: 1 }`, the symbol for the literal, `__object`, is distinct
        // from the symbol of the declaration it is being assigned to. Since we can use the declaration to refer to the literal, however,
        // we'd like to make that connection here - potentially causing us to paint the declaration's visibility, and therefore the literal.
        if !meaning.intersects(ast::SymbolFlags::VALUE) {
            return None;
        }
        let (_, decls, ..) = sym_fields(self, symbol);
        let &first_decl = decls.first()?;
        let dn = self.program_nodes(first_decl);
        let parent = dn[first_decl].parent?;
        if !ast::is_variable_declaration(&dn[parent]) {
            return None;
        }
        let is_lit_child = {
            (ast::is_object_literal_expression(&dn[first_decl])
                && dn[parent].initializer() == Some(first_decl))
                || (ast::is_type_literal_node(&dn[first_decl])
                    && dn[parent].as_variable_declaration().type_ == Some(first_decl))
        };
        drop(dn);
        if is_lit_child {
            return self.get_symbol_of_declaration(parent);
        }
        None
    }

    /// `(c *Checker) getExternalModuleContainer` (symbolaccessibility.go).
    pub(crate) fn get_external_module_container(
        &mut self,
        declaration: NodeId,
    ) -> Option<SymbolId> {
        let node = {
            let nn = self.program_nodes(declaration);
            ast::find_ancestor(
                Some(declaration),
                &nn,
                &mut |n, nodes| has_external_module_symbol(n, nodes),
            )
        };
        let node = node?;
        self.get_symbol_of_declaration(node)
    }

    /// `(c *Checker) getFileSymbolIfFileSymbolExportEqualsContainer` (symbolaccessibility.go).
    pub(crate) fn get_file_symbol_if_file_symbol_export_equals_container(
        &mut self,
        d: NodeId,
        container: SymbolId,
    ) -> Option<SymbolId> {
        let file_symbol = self.get_external_module_container(d)?;
        let exported = self
            .sym(file_symbol)
            .exports
            .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
            .copied()?;
        if self.get_symbol_if_same_reference(exported, container).is_some() {
            return Some(file_symbol);
        }
        None
    }

    /// `(c *Checker) getContainersOfSymbol` (symbolaccessibility.go).
    ///
    /// Attempts to find the symbol corresponding to the container a symbol is in - usually this
    /// is just its' `.parent`, but for locals, this value is `None`.
    pub(crate) fn get_containers_of_symbol(
        &mut self,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        meaning: SymbolFlags,
    ) -> Vec<SymbolId> {
        let container = self.get_parent_of_symbol(symbol);
        let symbol_flags_ = sym_fields(self, symbol).0;
        // Type parameters end up in the `members` lists but are not externally visible
        if let Some(container) = container
            && !symbol_flags_.intersects(ast::SymbolFlags::TYPE_PARAMETER)
        {
            return self.get_with_alternative_containers(
                container,
                symbol,
                enclosing_declaration,
                meaning,
            );
        }
        let mut candidates: Vec<SymbolId> = Vec::new();
        for d in sym_fields(self, symbol).1 {
            let dn = self.program_nodes(d);
            let d_parent = dn[d].parent;
            if !ast::is_ambient_module(&dn[d], &dn) && d_parent.is_some() {
                let d_parent = d_parent.unwrap();
                // direct children of a module
                if has_non_global_augmentation_external_module_symbol(d_parent, self) {
                    let sym = self.get_symbol_of_declaration(d_parent);
                    if let Some(sym) = sym
                        && !candidates.contains(&sym)
                    {
                        candidates.push(sym);
                    }
                    drop(dn);
                    continue;
                }
                // export ='d member of an ambient module
                if ast::is_module_block(&dn[d_parent])
                    && dn[d_parent].parent.is_some()
                    && {
                        let ambient_parent = dn[d_parent].parent.unwrap();
                        let ambient_sym = self.get_symbol_of_declaration(ambient_parent);
                        self.resolve_external_module_symbol(ambient_sym, false) == Some(symbol)
                    }
                {
                    let sym = self.get_symbol_of_declaration(dn[d_parent].parent.unwrap());
                    if let Some(sym) = sym
                        && !candidates.contains(&sym)
                    {
                        candidates.push(sym);
                    }
                    drop(dn);
                    continue;
                }
            }
            // `class B = ...` style: `module.exports.B = class B {}`
            if ast::is_class_expression(&dn[d])
                && d_parent.is_some()
                && ast::is_binary_expression(&dn[d_parent.unwrap()])
            {
                let p = d_parent.unwrap();
                let (op_kind, left) = {
                    let b = dn[p].as_binary_expression();
                    (b.operator_token.map(|t| dn[t].kind), b.left)
                };
                let left_is_access = left.is_some_and(|l| {
                    ast::is_access_expression(&dn[l])
                        && dn[l]
                            .expression()
                            .is_some_and(|e| ast::is_entity_name_expression(&dn[e], &dn))
                });
                if op_kind == Some(Kind::EqualsToken) && left_is_access {
                    let left = left.unwrap();
                    if ast::is_module_exports_access_expression(&dn[left], &dn)
                        || ast::is_exports_identifier(
                            &dn[dn[left].expression().unwrap_or(NodeId::NONE)],
                        )
                    {
                        let source = {
                            ast::get_source_file_of_node(Some(d), &dn)
                        };
                        drop(dn);
                        let sym = source.and_then(|s| self.get_symbol_of_declaration(s));
                        if let Some(sym) = sym
                            && !candidates.contains(&sym)
                        {
                            candidates.push(sym);
                        }
                        continue;
                    }
                    let expr = dn[left].expression().unwrap_or(NodeId::NONE);
                    drop(dn);
                    self.check_expression_cached(expr);
                    let sym = self
                        .symbol_node_links
                        .try_get(expr)
                        .and_then(|l| l.resolved_symbol);
                    if let Some(sym) = sym
                        && !candidates.contains(&sym)
                    {
                        candidates.push(sym);
                    }
                    continue;
                }
            }
        }
        if candidates.is_empty() {
            return Vec::new();
        }

        let mut best_containers: Vec<SymbolId> = Vec::new();
        let mut alternative_containers: Vec<SymbolId> = Vec::new();
        for container in candidates {
            if self
                .get_alias_for_symbol_in_container(container, symbol)
                .is_none()
            {
                continue;
            }
            let all_alts = self.get_with_alternative_containers(
                container,
                symbol,
                enclosing_declaration,
                meaning,
            );
            if all_alts.is_empty() {
                continue;
            }
            best_containers.push(all_alts[0]);
            alternative_containers.extend_from_slice(&all_alts[1..]);
        }
        best_containers.extend(alternative_containers);
        best_containers
    }

    /// `(c *Checker) getAliasForSymbolInContainer` (symbolaccessibility.go).
    pub(crate) fn get_alias_for_symbol_in_container(
        &mut self,
        container: SymbolId,
        symbol: SymbolId,
    ) -> Option<SymbolId> {
        if Some(container) == self.get_parent_of_symbol(symbol) {
            // fast path, `symbol` is either already the alias or isn't aliased
            return Some(symbol);
        }
        // Check if container is a thing with an `export=` which points directly at `symbol`, and if so, return
        // the container itself as the alias for the symbol
        let export_equals = self
            .sym(container)
            .exports
            .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
            .copied();
        if let Some(export_equals) = export_equals
            && self.get_symbol_if_same_reference(export_equals, symbol).is_some()
        {
            return Some(container);
        }
        let exports = self.get_exports_of_symbol(container);
        let (_, _, _, sym_name, ..) = sym_fields(self, symbol);
        if let Some(&quick) = exports.get(&sym_name)
            && self.get_symbol_if_same_reference(quick, symbol).is_some()
        {
            return Some(quick);
        }
        let mut candidates: Vec<SymbolId> = Vec::new();
        for (_, &exported) in &exports {
            if self.get_symbol_if_same_reference(exported, symbol).is_some() {
                candidates.push(exported);
            }
        }
        if !candidates.is_empty() {
            self.sort_symbols(&mut candidates); // _must_ sort exports for stable results - symbol table is randomly iterated
            return Some(candidates[0]);
        }
        None
    }

    /// `(c *Checker) getAccessibleSymbolChain` (symbolaccessibility.go).
    pub(crate) fn get_accessible_symbol_chain(
        &mut self,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        meaning: SymbolFlags,
        use_only_external_aliasing: bool,
    ) -> Vec<SymbolId> {
        let mut ctx = AccessibleSymbolChainContext {
            symbol: Some(symbol),
            enclosing_declaration,
            meaning,
            use_only_external_aliasing,
            visited_symbol_tables_map: FxHashMap::default(),
        };
        self.get_accessible_symbol_chain_ex(&mut ctx)
    }

    /// `(c *Checker) GetAccessibleSymbolChain` (symbolaccessibility.go).
    pub fn get_accessible_symbol_chain_exported(
        &mut self,
        symbol: Option<SymbolId>,
        enclosing_declaration: Option<NodeId>,
        meaning: SymbolFlags,
        use_only_external_aliasing: bool,
    ) -> Vec<SymbolId> {
        match symbol {
            Some(symbol) => self.get_accessible_symbol_chain(
                symbol,
                enclosing_declaration,
                meaning,
                use_only_external_aliasing,
            ),
            None => Vec::new(),
        }
    }

    /// `(c *Checker) getAccessibleSymbolChainEx` (symbolaccessibility.go).
    fn get_accessible_symbol_chain_ex(
        &mut self,
        ctx: &mut AccessibleSymbolChainContext,
    ) -> Vec<SymbolId> {
        let Some(symbol) = ctx.symbol else {
            return Vec::new();
        };
        if is_property_or_method_declaration_symbol(self, symbol) {
            return Vec::new();
        }
        // Go from enclosingDeclaration to the first scope we check, so the cache is keyed off the scope and thus shared more
        let mut first_relevant_location: Option<NodeId> = None;
        self.some_symbol_table_in_scope(
            ctx.enclosing_declaration,
            |_c, _t, _id, _ignore, _local, node| {
                first_relevant_location = node;
                true
            },
        );
        let link_key = crate::types::AccessibleChainCacheKey {
            use_only_external_aliasing: ctx.use_only_external_aliasing,
            location: first_relevant_location.unwrap_or(NodeId::NONE),
            meaning: ctx.meaning,
        };
        if let Some(existing) = self
            .symbol_container_links
            .get(symbol)
            .accessible_chain_cache
            .get(&link_key)
        {
            return existing.clone();
        }

        let mut result: Vec<SymbolId> = Vec::new();
        self.some_symbol_table_in_scope(
            ctx.enclosing_declaration,
            |c2, t, table_id, ignore_qualification, is_local_name_lookup, _node| {
                let res = c2.get_accessible_symbol_chain_from_symbol_table(
                    ctx,
                    t,
                    table_id,
                    ignore_qualification,
                    is_local_name_lookup,
                );
                if !res.is_empty() {
                    result = res;
                    return true;
                }
                false
            },
        );
        self.symbol_container_links
            .get(symbol)
            .accessible_chain_cache
            .insert(link_key, result.clone());
        result
    }

    /// `(c *Checker) getAccessibleSymbolChainFromSymbolTable`
    /// (symbolaccessibility.go).
    ///
    /// `ignoreQualification` is set when a symbol is being looked for through
    /// the exports of another symbol (meaning we have a route to qualify it
    /// already).
    fn get_accessible_symbol_chain_from_symbol_table(
        &mut self,
        ctx: &mut AccessibleSymbolChainContext,
        t: &SymbolTable,
        table_id: SymbolTableId,
        ignore_qualification: bool,
        is_local_name_lookup: bool,
    ) -> Vec<SymbolId> {
        let sym_id = ctx.symbol.unwrap_or(SymbolId::NONE);
        let visited = ctx.visited_symbol_tables_map.entry(sym_id).or_default();
        if visited.contains(&table_id) {
            return Vec::new();
        }
        visited.insert(table_id);

        let res = self.try_symbol_table(ctx, t, table_id, ignore_qualification, is_local_name_lookup);

        ctx.visited_symbol_tables_map
            .entry(sym_id)
            .or_default()
            .remove(&table_id);
        res
    }

    /// `(c *Checker) getSymbolTableAliases` (symbolaccessibility.go) —
    /// returns only the alias symbols from a symbol table, caching the result
    /// by tableId to avoid repeated iteration over large tables.
    /// Members tables are skipped entirely since someSymbolTableInScope filters them
    /// to `SymbolFlags::TYPE & !SymbolFlags::ASSIGNMENT`, which never includes aliases.
    fn get_symbol_table_aliases(
        &mut self,
        symbols: &SymbolTable,
        table_id: SymbolTableId,
    ) -> Vec<SymbolId> {
        let kind = SymbolTableId(table_id.0 & ST_KIND_MASK.0);
        // Members tables never contain alias symbols; skip entirely.
        if kind == ST_KIND_MEMBERS {
            return Vec::new();
        }
        // Cache globals and exports tables (which are large and revisited often).
        // Locals tables are small and per-scope, so they are filtered but not cached.
        let cacheable =
            kind == ST_KIND_GLOBALS || kind == ST_KIND_EXPORTS || kind == ST_KIND_RESOLVED_EXPORTS;
        if cacheable
            && let Some(aliases) = self.symbol_table_alias_cache.get(&table_id)
        {
            return aliases.clone();
        }
        let aliases: Vec<SymbolId> = symbols
            .values()
            .copied()
            .filter(|&s| sym_fields(self, s).0.intersects(ast::SymbolFlags::ALIAS))
            .collect();
        if cacheable {
            self.symbol_table_alias_cache
                .insert(table_id, aliases.clone());
        }
        aliases
    }

    /// `(c *Checker) trySymbolTable` (symbolaccessibility.go).
    fn try_symbol_table(
        &mut self,
        ctx: &mut AccessibleSymbolChainContext,
        symbols: &SymbolTable,
        table_id: SymbolTableId,
        ignore_qualification: bool,
        is_local_name_lookup: bool,
    ) -> Vec<SymbolId> {
        let is_globals = table_id == ST_KIND_GLOBALS;
        let ctx_symbol = ctx.symbol.unwrap_or(SymbolId::NONE);
        let ctx_name = sym_fields(self, ctx_symbol).3;
        // If symbol is directly available by its name in the symbol table
        let res = symbols.get(&ctx_name).copied();
        if let Some(res) = res
            && self.is_accessible(ctx, res /*resolvedAliasSymbol*/, None, ignore_qualification)
        {
            return vec![ctx_symbol];
        }

        let mut candidate_chains: Vec<Vec<SymbolId>> = Vec::new();

        // Check for ExportSymbol by direct name lookup rather than discovering it during
        // the alias iteration below (where it would never match, since only alias-flagged
        // symbols are iterated).
        if let Some(res) = res
            && let Some(export_symbol) = sym_fields(self, res).4
            && {
                let merged_export = self.get_merged_symbol(export_symbol);
                self.is_accessible(
                    ctx,
                    merged_export, /*resolvedAliasSymbol*/
                    None,
                    ignore_qualification,
                )
            }
        {
            candidate_chains.push(vec![ctx_symbol]);
        }

        // Iterate only alias symbols from the table (cached per tableId).
        // This avoids iterating thousands of non-alias symbols in large tables like globals.
        for symbol_from_symbol_table in self.get_symbol_table_aliases(symbols, table_id) {
            // for every non-default, non-export= alias symbol in scope, check if it refers to or can chain to the target symbol
            let (st_flags, st_decls, _, st_name, ..) = sym_fields(self, symbol_from_symbol_table);
            let _ = st_flags;
            if st_name != ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
                && st_name != ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT
                && !(is_umd_export_symbol(self, symbol_from_symbol_table)
                    && ctx.enclosing_declaration.is_some_and(|ed| {
                        let nn = self.program_nodes(ed);
                        ast::get_source_file_of_node(Some(ed), &nn)
                            .is_some_and(|sf| ast::is_external_module(nn[sf].as_source_file()))
                    }))
                // If `!useOnlyExternalAliasing`, we can use any type of alias to get the name
                && (!ctx.use_only_external_aliasing
                    || st_decls.iter().any(|&d| {
                        let nn = self.program_nodes(d);
                        ast::is_external_module_import_equals_declaration(&nn[d], &nn)
                    }))
                // If we're looking up a local name to reference directly, omit namespace reexports, otherwise when we're trawling through an export list to make a dotted name, we can keep it
                && (is_local_name_lookup
                    && !st_decls.iter().any(|&d| {
                        is_namespace_reexport_declaration(self, d)
                    })
                    || !is_local_name_lookup)
                // While exports are generally considered to be in scope, export-specifier declared symbols are _not_
                // See similar comment in `resolveName` for details
                && (ignore_qualification
                    || get_declarations_of_kind(self, symbol_from_symbol_table, Kind::ExportSpecifier)
                        .is_empty())
            {
                let resolved_imported_symbol = self.resolve_alias(symbol_from_symbol_table);
                let candidate = self.get_candidate_list_for_symbol(
                    ctx,
                    symbol_from_symbol_table,
                    resolved_imported_symbol,
                    ignore_qualification,
                );
                if !candidate.is_empty() {
                    candidate_chains.push(candidate);
                }
            }
        }

        if !candidate_chains.is_empty() {
            // pick first, shortest
            candidate_chains.sort_by(|a, b| self.compare_symbol_chains(a, b));
            return candidate_chains[0].clone();
        }

        // If there's no result and we're looking at the global symbol table, treat `globalThis` like an alias and try to lookup thru that
        if is_globals {
            return self.get_candidate_list_for_symbol(
                ctx,
                self.global_this_symbol,
                self.global_this_symbol,
                ignore_qualification,
            );
        }
        Vec::new()
    }

    /// `(c *Checker) compareSymbolChainsWorker` — `c.compareSymbolChains`
    /// (symbolaccessibility.go).
    fn compare_symbol_chains(&mut self, a: &[SymbolId], b: &[SymbolId]) -> std::cmp::Ordering {
        let chain_len = a.len().cmp(&b.len());
        if chain_len != std::cmp::Ordering::Equal {
            return chain_len;
        }
        for idx in 0..a.len() {
            let comparison = self.compare_symbols(a[idx], b[idx]);
            if comparison != 0 {
                return comparison.cmp(&0);
            }
        }
        std::cmp::Ordering::Equal
    }

    /// `(c *Checker) getCandidateListForSymbol` (symbolaccessibility.go).
    fn get_candidate_list_for_symbol(
        &mut self,
        ctx: &mut AccessibleSymbolChainContext,
        symbol_from_symbol_table: SymbolId,
        resolved_imported_symbol: SymbolId,
        ignore_qualification: bool,
    ) -> Vec<SymbolId> {
        if self.is_accessible(
            ctx,
            symbol_from_symbol_table,
            Some(resolved_imported_symbol),
            ignore_qualification,
        ) {
            return vec![symbol_from_symbol_table];
        }

        // Look in the exported members, if we can find accessibleSymbolChain, symbol is accessible using this chain
        // but only if the symbolFromSymbolTable can be qualified
        let candidate_table = self.get_exports_of_symbol(resolved_imported_symbol);
        let candidate_table_id = symbol_table_id_from_resolved_exports(resolved_imported_symbol);
        let accessible_symbols_from_exports = self.get_accessible_symbol_chain_from_symbol_table(
            ctx,
            &candidate_table,
            candidate_table_id, /*ignoreQualification*/
            true,
            false,
        );
        if accessible_symbols_from_exports.is_empty() {
            return Vec::new();
        }
        if !self.can_qualify_symbol(
            ctx,
            symbol_from_symbol_table,
            get_qualified_left_meaning(ctx.meaning),
        ) {
            return Vec::new();
        }
        let mut res = vec![symbol_from_symbol_table];
        res.extend(accessible_symbols_from_exports);
        res
    }

    /// `(c *Checker) isAccessible` (symbolaccessibility.go).
    fn is_accessible(
        &mut self,
        ctx: &AccessibleSymbolChainContext,
        symbol_from_symbol_table: SymbolId,
        resolved_alias_symbol: Option<SymbolId>,
        ignore_qualification: bool,
    ) -> bool {
        let mut like_symbols = false;
        if ctx.symbol == resolved_alias_symbol {
            like_symbols = true;
        }
        if ctx.symbol == Some(symbol_from_symbol_table) {
            like_symbols = true;
        }
        let symbol = merged(self, ctx.symbol);
        if symbol == merged(self, resolved_alias_symbol) {
            like_symbols = true;
        }
        if symbol == merged(self, Some(symbol_from_symbol_table)) {
            like_symbols = true;
        }
        if !like_symbols
            && resolved_alias_symbol.is_some()
            && sym_fields(self, resolved_alias_symbol.unwrap())
                .0
                .intersects(ast::SymbolFlags::ALIAS)
        {
            let mut seen_aliases: FxHashSet<SymbolId> = FxHashSet::default();
            let mut resolved = resolved_alias_symbol;
            while let Some(r) = resolved {
                if !sym_fields(self, r).0.intersects(ast::SymbolFlags::ALIAS)
                    || seen_aliases.contains(&r)
                {
                    break;
                }
                seen_aliases.insert(r);
                let r = self.resolve_alias(r);
                resolved = Some(self.get_merged_symbol(r));
                if symbol == resolved {
                    like_symbols = true;
                    break;
                }
            }
        }
        if !like_symbols {
            return false;
        }
        // if the symbolFromSymbolTable is not external module (it could be if it was determined as ambient external module and would be in globals table)
        // and if symbolFromSymbolTable or alias resolution matches the symbol,
        // check the symbol can be qualified, it is only then this symbol is accessible
        let (_, decls, ..) = sym_fields(self, symbol_from_symbol_table);
        !decls
            .iter()
            .any(|&d| has_non_global_augmentation_external_module_symbol(d, self))
            && (ignore_qualification || {
                let merged_from_table = self.get_merged_symbol(symbol_from_symbol_table);
                self.can_qualify_symbol(ctx, merged_from_table, ctx.meaning)
            })
    }

    /// `(c *Checker) canQualifySymbol` (symbolaccessibility.go).
    fn can_qualify_symbol(
        &mut self,
        ctx: &AccessibleSymbolChainContext,
        symbol_from_symbol_table: SymbolId,
        meaning: SymbolFlags,
    ) -> bool {
        // If the symbol is equivalent and doesn't need further qualification, this symbol is accessible
        if !self.needs_qualification(symbol_from_symbol_table, ctx.enclosing_declaration, meaning) {
            return true;
        }
        // If symbol needs qualification, make sure that parent is accessible, if it is then this symbol is accessible too
        let parent = sym_fields(self, symbol_from_symbol_table).2;
        let mut sub_ctx = AccessibleSymbolChainContext {
            symbol: parent,
            enclosing_declaration: ctx.enclosing_declaration,
            meaning: get_qualified_left_meaning(meaning),
            use_only_external_aliasing: ctx.use_only_external_aliasing,
            visited_symbol_tables_map: ctx.visited_symbol_tables_map.clone(),
        };
        !self.get_accessible_symbol_chain_ex(&mut sub_ctx).is_empty()
    }

    /// `(c *Checker) needsQualification` (symbolaccessibility.go).
    pub(crate) fn needs_qualification(
        &mut self,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        meaning: SymbolFlags,
    ) -> bool {
        let mut qualify = false;
        let name = sym_fields(self, symbol).3;
        self.some_symbol_table_in_scope(
            enclosing_declaration,
            |c2, symbol_table, _id, _ignore, _local, _scope| {
                // If symbol of this name is not available in the symbol table we are ok
                let Some(res) = symbol_table.get(&name).copied() else {
                    return false;
                };
                let mut symbol_from_symbol_table = c2.get_merged_symbol(res);
                // If the symbol with this name is present it should refer to the symbol
                if symbol_from_symbol_table == symbol {
                    // No need to qualify
                    return true;
                }

                // Qualify if the symbol from symbol table has same meaning as expected
                let (sf_flags, ..) = sym_fields(c2, symbol_from_symbol_table);
                let should_resolve_alias = sf_flags.intersects(ast::SymbolFlags::ALIAS)
                    && {
                        let decls = sym_fields(c2, symbol_from_symbol_table).1;
                        !decls.iter().any(|&d| {
                            let nn = c2.program_nodes(d);
                            nn[d].kind == Kind::ExportSpecifier
                        })
                    };
                if should_resolve_alias {
                    symbol_from_symbol_table = c2.resolve_alias(symbol_from_symbol_table);
                }
                let mut flags = sym_fields(c2, symbol_from_symbol_table).0;
                if should_resolve_alias {
                    flags = c2.get_symbol_flags(symbol_from_symbol_table);
                }
                if flags.intersects(meaning) {
                    qualify = true;
                    return true;
                }

                // Continue to the next symbol table
                false
            },
        );

        qualify
    }

    /// `(c *Checker) someSymbolTableInScope` (symbolaccessibility.go).
    /// The callback returns `true` to stop iterating (like Go's `bool` result).
    fn some_symbol_table_in_scope(
        &mut self,
        enclosing_declaration: Option<NodeId>,
        mut callback: impl FnMut(
            &mut Checker,
            &SymbolTable,
            SymbolTableId,
            bool, // ignoreQualification
            bool, // isLocalNameLookup
            Option<NodeId>, // scopeNode
        ) -> bool,
    ) -> bool {
        let mut location = enclosing_declaration;
        while let Some(loc) = location {
            // Locals of a source file are not in scope (because they get merged into the global symbol table)
            let locals = {
                let nn = self.program_nodes(loc);
                if !ast::is_global_source_file(&nn[loc], &nn) {
                    nn[loc].locals().cloned()
                } else {
                    None
                }
            };
            if let Some(locals) = locals {
                if callback(
                    self,
                    &locals,
                    symbol_table_id_from_locals(loc),
                    false,
                    true,
                    Some(loc),
                ) {
                    return true;
                }
            }
            let kind = {
                let nn = self.program_nodes(loc);
                nn[loc].kind
            };
            match kind {
                Kind::SourceFile | Kind::ModuleDeclaration => {
                    {
                        let nn = self.program_nodes(loc);
                        if kind == Kind::SourceFile
                            && !ast::is_external_or_commonjs_module(nn[loc].as_source_file())
                        {
                            // `break` in the Go switch — fall through to the next iteration.
                        } else {
                            drop(nn);
                            let reparsed = {
                                let nn = self.program_nodes(loc);
                                ast::get_reparsed_node_for_node(loc, &nn)
                            };
                            if let Some(sym) = self.get_symbol_of_declaration(reparsed) {
                                let exports = self.sym(sym).exports.clone();
                                if callback(
                                    self,
                                    &exports,
                                    symbol_table_id_from_exports(sym),
                                    false,
                                    true,
                                    Some(loc),
                                ) {
                                    return true;
                                }
                            }
                        }
                    }
                }
                Kind::ClassDeclaration | Kind::ClassExpression | Kind::InterfaceDeclaration => {
                    // Type parameters are bound into `members` lists so they can merge across declarations
                    // This is troublesome, since in all other respects, they behave like locals :cries:
                    // These can never be latebound, so the symbol's raw members are sufficient.
                    if let Some(sym) = self.get_symbol_of_declaration(loc) {
                        let members = self.sym(sym).members.clone();
                        let mut table: Option<SymbolTable> = None;
                        for (key, &member_symbol) in &members {
                            if sym_fields(self, member_symbol)
                                .0
                                .intersects(ast::SymbolFlags::TYPE & !ast::SymbolFlags::ASSIGNMENT) {
                                table.get_or_insert_with(SymbolTable::default).set(
                                    key.clone(),
                                    member_symbol,
                                );
                            }
                        }
                        if let Some(table) = table
                            && callback(
                                self,
                                &table,
                                symbol_table_id_from_members(sym),
                                false,
                                false,
                                Some(loc),
                            )
                        {
                            return true;
                        }
                    }
                    // Class expression names (e.g., `B` in `class B {}`) are not stored in any
                    // scope table — the binder uses bindAnonymousDeclaration. Expose the name
                    // binding here so getAccessibleSymbolChain can resolve self-references.
                    let is_class_expr_with_name = {
                        let nn = self.program_nodes(loc);
                        ast::is_class_expression(&nn[loc])
                            && nn[loc].name().is_some()
                    };
                    if is_class_expr_with_name
                        && let Some(name_table) = self.get_class_expression_name_table(loc)
                        && callback(
                            self,
                            &name_table,
                            symbol_table_id_from_locals(loc),
                            false,
                            true,
                            Some(loc),
                        )
                    {
                        return true;
                    }
                }
                _ => {}
            }
            location = self.program_nodes(loc)[loc].parent;
        }

        callback(
            self,
            &self.globals.clone(),
            symbol_table_id_from_globals(),
            false,
            true,
            None,
        )
    }

    /// `(c *Checker) getClassExpressionNameTable` (symbolaccessibility.go) —
    /// returns a cached symbol table containing the class expression's name
    /// binding. Class expression names are bound via `bindAnonymousDeclaration`
    /// and aren't stored in any container's locals, so this synthesized table
    /// lets `someSymbolTableInScope` expose them during accessibility checks.
    fn get_class_expression_name_table(&mut self, location: NodeId) -> Option<SymbolTable> {
        if let Some(table) = self.class_expression_name_tables.get(&location) {
            return Some(table.clone());
        }
        let class_symbol = self.get_symbol_of_declaration(location)?;
        let name_text = {
            let nn = self.program_nodes(location);
            let name = nn[location].name()?;
            nn[name].as_identifier().text.clone()
        };
        if name_text.is_empty() {
            return None;
        }
        let mut table = SymbolTable::default();
        table.set(name_text, class_symbol);
        self.class_expression_name_tables
            .insert(location, table.clone());
        Some(table)
    }

    /// `(c *Checker) IsSymbolAccessible` (symbolaccessibility.go).
    pub fn is_symbol_accessible(
        &mut self,
        symbol: Option<SymbolId>,
        enclosing_declaration: Option<NodeId>,
        meaning: SymbolFlags,
        should_compute_aliases_to_make_visible: bool,
    ) -> SymbolAccessibilityResult {
        self.is_symbol_accessible_worker(
            symbol,
            enclosing_declaration,
            meaning,
            should_compute_aliases_to_make_visible,
            true, /*allowModules*/
        )
    }

    /// `(c *Checker) isSymbolAccessibleWorker` (symbolaccessibility.go).
    fn is_symbol_accessible_worker(
        &mut self,
        symbol: Option<SymbolId>,
        enclosing_declaration: Option<NodeId>,
        meaning: SymbolFlags,
        should_compute_aliases_to_make_visible: bool,
        allow_modules: bool,
    ) -> SymbolAccessibilityResult {
        if let Some(symbol) = symbol
            && let Some(enclosing_declaration) = enclosing_declaration
        {
            if let Some(result) = self.is_any_symbol_accessible(
                &[symbol],
                Some(enclosing_declaration),
                Some(symbol),
                meaning,
                should_compute_aliases_to_make_visible,
                allow_modules,
            ) {
                return result;
            }

            // This could be a symbol that is not exported in the external module
            // or it could be a symbol from different external module that is not aliased and hence cannot be named
            let decls = sym_fields(self, symbol).1;
            let symbol_external_module = decls
                .iter()
                .find_map(|&d| self.get_external_module_container(d));
            if let Some(symbol_external_module) = symbol_external_module {
                let enclosing_external_module =
                    self.get_external_module_container(enclosing_declaration);
                if Some(symbol_external_module) != enclosing_external_module {
                    // name from different external module that is not visible
                    let in_js = {
                        let nn = self.program_nodes(enclosing_declaration);
                        ast::is_in_js_file(Some(enclosing_declaration), &nn)
                    };
                    return SymbolAccessibilityResult {
                        accessibility: SymbolAccessibility::CannotBeNamed,
                        error_symbol_name: self.symbol_to_string_ex(
                            symbol,
                            Some(enclosing_declaration),
                            meaning,
                            crate::types::SymbolFormatFlags::ALLOW_ANY_NODE_KIND,
                        ),
                        error_module_name: self.symbol_to_string(symbol_external_module),
                        error_node: if in_js { Some(enclosing_declaration) } else { None },
                        ..Default::default()
                    };
                }
            }

            // Just a local name that is not accessible
            return SymbolAccessibilityResult {
                accessibility: SymbolAccessibility::NotAccessible,
                error_symbol_name: self.symbol_to_string_ex(
                    symbol,
                    Some(enclosing_declaration),
                    meaning,
                    crate::types::SymbolFormatFlags::ALLOW_ANY_NODE_KIND,
                ),
                ..Default::default()
            };
        }

        SymbolAccessibilityResult {
            accessibility: SymbolAccessibility::Accessible,
            ..Default::default()
        }
    }
}

/// `isUMDExportSymbol` (symbolaccessibility.go).
fn is_umd_export_symbol(c: &Checker, symbol: SymbolId) -> bool {
    let decls = sym_fields(c, symbol).1;
    decls.first().is_some_and(|&d| {
        let nn = c.program_nodes(d);
        ast::is_namespace_export_declaration(&nn[d])
    })
}

/// `isNamespaceReexportDeclaration` (symbolaccessibility.go).
fn is_namespace_reexport_declaration(c: &Checker, node: NodeId) -> bool {
    let nn = c.program_nodes(node);
    ast::is_namespace_export(&nn[node])
        && nn[node]
            .parent
            .is_some_and(|p| nn[p].module_specifier().is_some())
}

/// `isPropertyOrMethodDeclarationSymbol` (symbolaccessibility.go).
fn is_property_or_method_declaration_symbol(c: &Checker, symbol: SymbolId) -> bool {
    let decls = sym_fields(c, symbol).1;
    if decls.is_empty() {
        return false;
    }
    decls.iter().all(|&d| {
        let nn = c.program_nodes(d);
        matches!(
            nn[d].kind,
            Kind::PropertyDeclaration | Kind::MethodDeclaration | Kind::GetAccessor | Kind::SetAccessor
        )
    })
}

/// `hasExternalModuleSymbol` (symbolaccessibility.go).
fn has_external_module_symbol(declaration: &Node, nodes: &[Node]) -> bool {
    ast::is_ambient_module(declaration, nodes)
        || (declaration.kind == Kind::SourceFile
            && ast::is_external_or_commonjs_module(declaration.as_source_file()))
}

/// `getDeclarationsOfKind` — all declarations of `symbol` matching `kind`.
fn get_declarations_of_kind(c: &Checker, symbol: SymbolId, kind: Kind) -> Vec<NodeId> {
    sym_fields(c, symbol)
        .1
        .into_iter()
        .filter(|&d| {
            let nn = c.program_nodes(d);
            nn[d].kind == kind
        })
        .collect()
}
