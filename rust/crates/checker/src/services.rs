// Ported from tsc/internal/checker/services.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// — free (non-method) functions and data only.
//
// PORT: all `(c *Checker)` methods in services.go are deferred to checker.rs
// (they depend on the full checker: `getSymbolsInScope`, `getPropertyOfType`,
// program state, etc.). This file ports the package-level items:
//
// - `GetResolvedSignatureForSignatureHelp` — routes through the ported
//   `Checker::run_without_resolved_signature_caching` and the
//   `PORT(deferred)` `get_resolved_signature_worker` stub.
// - `isExportSpecifierAlias`.
// - `getPossibleSymbolReferenceNodes` / `getPossibleSymbolReferencePositions`.
// - `knownGenericTypeNames` / `isKnownGenericTypeName`.
//
// `*ast.Node`/`*ast.SourceFile` → `NodeId` + the `nodes` arena parameter;
// `*ast.Identifier`/`*ast.ExportSpecifier` similarly become `NodeId`s.

use tsc_ast::{self as ast, NodeId, SymbolId};
use tsc_core::text::TextPos;
use tsc_debug as debug;

use crate::checker_core::{CheckMode, Checker};
use crate::types::SignatureId;

/// `GetResolvedSignatureForSignatureHelp(node, argumentCount, c)`.
/// `argument_count` is Go's `int` — `-1` is a valid input (unknown arity).
pub fn get_resolved_signature_for_signature_help(
    c: &mut Checker,
    nodes: &[ast::Node],
    node: NodeId,
    argument_count: i32,
) -> (Option<SignatureId>, Vec<SignatureId>) {
    c.run_without_resolved_signature_caching(nodes, node, |c| {
        c.get_resolved_signature_worker(node, CheckMode::IS_FOR_SIGNATURE_HELP, argument_count)
    })
}

/// `isExportSpecifierAlias` — `referenceLocation`/`exportSpecifier` are the
/// nodes Go passes as `*ast.Identifier`/`*ast.ExportSpecifier`.
pub fn is_export_specifier_alias(
    nodes: &[ast::Node],
    reference_location: NodeId,
    export_specifier: NodeId,
) -> bool {
    let export_specifier_data = nodes[export_specifier].as_export_specifier();
    debug::assert_!(
        export_specifier_data.property_name == Some(reference_location)
            || nodes[export_specifier].name() == Some(reference_location),
        "referenceLocation is not export specifier name or property name"
    );
    if let Some(property_name) = export_specifier_data.property_name {
        // Given `export { foo as bar } [from "someModule"]`: It's an alias at
        // `foo`, but at `bar` it's a new symbol.
        property_name == reference_location
    } else {
        // `export { foo } from "foo"` is a re-export.
        // `export { foo };` is not a re-export, it creates an alias for the
        // local variable `foo`.
        // `exportSpecifier.Parent.Parent.ModuleSpecifier() == nil`
        let export_declaration = nodes[export_specifier].parent.and_then(|p| nodes[p].parent);
        export_declaration.is_none_or(|d| nodes[d].module_specifier().is_none())
    }
}

/// `getPossibleSymbolReferenceNodes` — `MapNonNil` over
/// `GetTouchingPropertyName` results, dropping the source file node.
pub fn get_possible_symbol_reference_nodes(
    nodes: &mut Vec<ast::Node>,
    source_file: NodeId,
    symbol_name: &str,
    container: Option<NodeId>,
) -> Vec<NodeId> {
    get_possible_symbol_reference_positions(nodes, source_file, symbol_name, container)
        .into_iter()
        .filter_map(|pos| {
            let reference_location =
                tsc_astnav::tokens::get_touching_property_name(nodes, source_file, pos)?;
            if reference_location != source_file {
                Some(reference_location)
            } else {
                None
            }
        })
        .collect()
}

/// `getPossibleSymbolReferencePositions` — text-scan candidate positions.
///
/// PORT: `container.Pos()` slicing is verbatim — Go's
/// `strings.Index(text[container.Pos():], symbolName)` yields a
/// container-relative index for the *first* match while every later position
/// is absolute (the re-search slices `text[startIndex:]`). That asymmetry is
/// preserved rather than "fixed" (call sites always pass the whole source
/// file as `container`, where `Pos() == 0`).
pub fn get_possible_symbol_reference_positions(
    nodes: &[ast::Node],
    source_file: NodeId,
    symbol_name: &str,
    container: Option<NodeId>,
) -> Vec<TextPos> {
    let mut positions: Vec<TextPos> = Vec::new();

    // TODO: Cache symbol existence for files to save text search
    // Also, need to make this work for unicode escapes.

    // Be resilient in the face of a symbol with no name or zero length name.
    if symbol_name.is_empty() {
        return positions;
    }

    let text = &nodes[source_file].as_source_file().text;
    let bytes = text.as_bytes();
    let source_length = bytes.len();
    let symbol_name_length = symbol_name.len();

    let container = container.unwrap_or(source_file);
    let (container_pos, container_end) = {
        let c = &nodes[container];
        (c.pos(), c.end())
    };

    // See the PORT note above: the first index is relative to
    // `container.pos()`; all later positions are absolute, as in Go.
    let mut position: i64 = text[container_pos as usize..]
        .find(symbol_name)
        .map(|i| i as i64)
        .unwrap_or(-1);
    let end_pos = container_end as i64;
    while position >= 0 && position < end_pos {
        // We found a match. Make sure it's not part of a larger word (i.e. the
        // char before and after it have to be a non-identifier char).
        let end_position = position + symbol_name_length as i64;

        // `rune(text[i])` — Go zero-extends the *byte* (not a decoded rune).
        let before_ok = position == 0
            || !tsc_scanner::scanner::is_identifier_part(bytes[position as usize - 1] as i32);
        let after_ok = end_position as usize == source_length
            || !tsc_scanner::scanner::is_identifier_part(bytes[end_position as usize] as i32);
        if before_ok && after_ok {
            // Found a real match. Keep searching.
            positions.push(position as TextPos);
        }
        let start_index = position + symbol_name_length as i64 + 1;
        if start_index as usize > bytes.len() {
            break;
        }
        match text[start_index as usize..].find(symbol_name) {
            Some(found_index) => position = start_index + found_index as i64,
            None => break,
        }
    }

    positions
}

/// `knownGenericTypeNames` (services.go package var).
pub const KNOWN_GENERIC_TYPE_NAMES: &[&str] = &[
    "Array",
    "ArrayLike",
    "ReadonlyArray",
    "Promise",
    "PromiseLike",
    "Iterable",
    "IterableIterator",
    "AsyncIterable",
    "Set",
    "WeakSet",
    "ReadonlySet",
    "Map",
    "WeakMap",
    "ReadonlyMap",
    "Partial",
    "Required",
    "Readonly",
    "Pick",
    "Omit",
    "NonNullable",
];

/// `isKnownGenericTypeName`.
pub fn is_known_generic_type_name(name: &str) -> bool {
    KNOWN_GENERIC_TYPE_NAMES.contains(&name)
}

// ===========================================================================
// `(c *Checker)` methods (services.go).
//
// PORT conventions (same as the rest of the crate):
// - `*ast.Symbol` → `SymbolId`, `*Type` → `TypeId`, `*ast.Node` → `NodeId`,
//   `*Signature` → `SignatureId`; nil-able Go values → `Option<_>`.
// - Go public/internals pairs whose names differ only by case collapse into
//   one Rust method: the `pub` (public-API) name wins when the signatures are
//   identical (`GetSymbolsInScope`/`getSymbolsInScope`,
//   `IsValidPropertyAccess`/`isValidPropertyAccess`,
//   `GetExportsOfModule`/`getExportsOfModuleAsArray`,
//   `GetElementTypeOfArrayType`/`getElementTypeOfArrayType`, …).
//   When a public wrapper needs a *different* signature than the committed
//   internal, it gets an `_api` suffix (`GetContextualType` →
//   `get_contextual_type_api`, `GetTypeArgumentConstraint` →
//   `get_type_argument_constraint_api`), matching the existing
//   `checker_d::get_symbol_at_location_api` precedent.
// - `IsValidPropertyAccessForCompletions` already lives in `checker_b.rs`
//   (committed); it is not re-ported here.
// - Callees from deferred waves (`get_jsx_type`, `get_jsx_namespace`,
//   `get_effective_type_arguments`, `create_union_or_intersection_property`,
//   `get_reduced_apparent_type`, `get_contextual_type_for_jsx_attribute`,
//   `get_enum_member_value`, `get_jsx_fragment_factory_entity`) are called
//   under their canonical snake_case names and stay `E0599` until those
//   waves land.

use tsc_ast::SymbolFlags;
use tsc_ast::SymbolTable;
use tsc_collections::OrderedMap;
use tsc_evaluator as evaluator;

use crate::checker_types::IterationUse;
use crate::types::{SignatureKind, TypeFlags, TypeId};

/// `symbol.CombinedLocalAndExportSymbolFlags()` — needs the arena because
/// `export_symbol` is a `SymbolId`, not a pointer.
fn combined_local_and_export_symbol_flags(c: &Checker, s: SymbolId) -> SymbolFlags {
    let sym = c.sym(s);
    let mut flags = sym.flags;
    if let Some(export_symbol) = sym.export_symbol {
        flags |= c.sym(export_symbol).flags;
    }
    flags
}

/// `copySymbol` closure of `getSymbolsInScope` (services.go:31).
fn copy_symbol_to_table(
    c: &Checker,
    symbols: &mut SymbolTable,
    symbol: SymbolId,
    meaning: SymbolFlags,
) {
    if combined_local_and_export_symbol_flags(c, symbol).intersects(meaning) {
        let id = c.sym(symbol).name.clone();
        // We will copy all symbols regardless of reserved names because
        // symbolsToArray will check whether the key is a reserved name and
        // it will not copy symbols with reserved names to the array.
        if !symbols.has(id.as_str()) {
            symbols.set(id.into(), symbol);
        }
    }
}

/// `copySymbols` closure of `getSymbolsInScope` (services.go:43).
fn copy_symbols_to_table(
    c: &Checker,
    symbols: &mut SymbolTable,
    source: &SymbolTable,
    meaning: SymbolFlags,
) {
    if meaning != SymbolFlags::NONE {
        for (_, &symbol) in source.entries() {
            copy_symbol_to_table(c, symbols, symbol, meaning);
        }
    }
}

/// `copyLocallyVisibleExportSymbols` closure of `getSymbolsInScope`
/// (services.go:51).
fn copy_locally_visible_export_symbols(
    c: &Checker,
    symbols: &mut SymbolTable,
    source: &SymbolTable,
    meaning: SymbolFlags,
    nodes: &[ast::Node],
) {
    if meaning == SymbolFlags::NONE {
        return;
    }
    for (_, &symbol) in source.entries() {
        // Similar condition as in `resolveNameHelper`
        let has_export_decl = {
            let sym = c.sym(symbol);
            ast::get_declaration_of_kind(&sym, ast::Kind::ExportSpecifier, nodes).is_some()
                || ast::get_declaration_of_kind(&sym, ast::Kind::NamespaceExport, nodes).is_some()
        };
        if !has_export_decl && c.sym(symbol).name != ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT {
            copy_symbol_to_table(c, symbols, symbol, meaning);
        }
    }
}

impl Checker {
    /// `(c *Checker) GetSymbolsInScope` / `getSymbolsInScope` (services.go:16) —
    /// collapsed into one `pub fn` (identical signatures in Go).
    pub fn get_symbols_in_scope(
        &mut self,
        location: NodeId,
        meaning: SymbolFlags,
    ) -> Vec<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((location).file_index());
        if nodes[location]
            .flags
            .intersects(ast::NodeFlags::IN_WITH_STATEMENT)
        {
            // We cannot answer semantic questions within a with block, do not
            // proceed any further
            return Vec::new();
        }

        let mut symbols: SymbolTable = OrderedMap::new();
        let mut is_static_symbol = false;

        let mut location_opt = Some(location);
        let mut last_location: Option<NodeId> = None;
        while let Some(location) = location_opt {
            let loc = &nodes[location];
            if ast::is_module_declaration(loc)
                && loc.as_module_declaration().attributes.is_some()
                && last_location == loc.as_module_declaration().attributes
            {
                // Module declaration is not in scope inside its attributes.
                last_location = Some(location);
                location_opt = loc.parent;
                continue;
            }

            if crate::utilities::can_have_locals(loc)
                && loc.locals().is_some()
                && !ast::is_global_source_file(loc, &nodes)
            {
                let locals = loc.locals().expect("locals checked").clone();
                copy_symbols_to_table(self, &mut symbols, &locals, meaning);
            }

            match loc.kind {
                ast::Kind::SourceFile => {
                    if ast::is_external_module(loc.as_source_file()) {
                        // fallthrough to ModuleDeclaration
                        self.copy_module_scope_exports(&mut symbols, location, meaning, &nodes);
                    }
                }
                ast::Kind::ModuleDeclaration => {
                    self.copy_module_scope_exports(&mut symbols, location, meaning, &nodes);
                }
                ast::Kind::EnumDeclaration => {
                    if let Some(symbol) = self.get_symbol_of_declaration(location) {
                        let exports = self.sym(symbol).exports.clone();
                        copy_symbols_to_table(
                            self,
                            &mut symbols,
                            &exports,
                            meaning & SymbolFlags::ENUM_MEMBER,
                        );
                    }
                }
                ast::Kind::ClassExpression => {
                    let class_name = loc.name();
                    if class_name.is_some() {
                        if let Some(symbol) = loc.symbol() {
                            copy_symbol_to_table(self, &mut symbols, symbol, meaning);
                        }
                    }
                    // fall-through is necessary because we would like to
                    // handle type parameters inside class expressions the
                    // same as class/interface declarations.
                    self.copy_type_parameters_into_scope(
                        &mut symbols,
                        location,
                        meaning,
                        is_static_symbol,
                    );
                }
                ast::Kind::ClassDeclaration | ast::Kind::InterfaceDeclaration => {
                    // If we didn't come from a static member of a class or
                    // interface, add the type parameters into the symbol
                    // table (type parameters of classDeclaration/
                    // classExpression and interface are in the member
                    // property of the symbol. Note: the memberFlags come from
                    // the previous iteration).
                    self.copy_type_parameters_into_scope(
                        &mut symbols,
                        location,
                        meaning,
                        is_static_symbol,
                    );
                }
                ast::Kind::FunctionExpression => {
                    let func_name = loc.name();
                    if func_name.is_some() {
                        if let Some(symbol) = loc.symbol() {
                            copy_symbol_to_table(self, &mut symbols, symbol, meaning);
                        }
                    }
                }
                _ => {}
            }

            if crate::utilities::introduces_arguments_exotic_object(&nodes[location]) {
                copy_symbol_to_table(self, &mut symbols, self.arguments_symbol, meaning);
            }

            is_static_symbol = ast::is_static(&nodes[location]);
            last_location = Some(location);
            location_opt = nodes[location].parent;
        }

        let globals = self.globals.borrow().clone();
        copy_symbols_to_table(self, &mut symbols, &globals, meaning);

        // Not a symbol, a keyword
        symbols.delete(ast::symbol::INTERNAL_SYMBOL_NAME_THIS);
        crate::utilities::symbols_to_array(&symbols)
    }

    /// The SourceFile-fallthrough/ModuleDeclaration arm of
    /// `getSymbolsInScope`'s switch (services.go:81-87).
    fn copy_module_scope_exports(
        &mut self,
        symbols: &mut SymbolTable,
        location: NodeId,
        meaning: SymbolFlags,
        nodes: &[ast::Node],
    ) {
        if let Some(symbol) = self.get_symbol_of_declaration(location) {
            let exports = self.sym(symbol).exports.clone();
            copy_locally_visible_export_symbols(
                self,
                symbols,
                &exports,
                meaning & SymbolFlags::MODULE_MEMBER,
                nodes,
            );
        }
    }

    /// The ClassDeclaration/InterfaceDeclaration (and ClassExpression
    /// fallthrough) arm of `getSymbolsInScope` (services.go:97-105).
    fn copy_type_parameters_into_scope(
        &mut self,
        symbols: &mut SymbolTable,
        location: NodeId,
        meaning: SymbolFlags,
        is_static_symbol: bool,
    ) {
        if !is_static_symbol {
            if let Some(symbol) = self.get_symbol_of_declaration(location) {
                let members = self.get_members_of_symbol(symbol);
                copy_symbols_to_table(self, symbols, &members, meaning & SymbolFlags::TYPE);
            }
        }
    }

    /// `(c *Checker) GetExportsOfModule` (services.go:131) and
    /// `getExportsOfModuleAsArray` (services.go:852) — identical bodies in
    /// Go, collapsed into this one `pub fn`.
    pub fn get_exports_of_module_as_array(&mut self, module_symbol: SymbolId) -> Vec<SymbolId> {
        let exports = self.get_exports_of_module(module_symbol);
        crate::utilities::symbols_to_array(&exports)
    }

    /// `(c *Checker) ForEachExportAndPropertyOfModule` (services.go:135).
    pub fn for_each_export_and_property_of_module(
        &mut self,
        module_symbol: SymbolId,
        cb: &mut dyn FnMut(SymbolId, &str),
    ) {
        let exports = self.get_exports_of_module(module_symbol);
        for (key, &exported_symbol) in exports.entries() {
            if !crate::checker_c::is_reserved_member_name(key) {
                cb(exported_symbol, key);
            }
        }

        let export_equals = self.resolve_external_module_symbol(Some(module_symbol), false);
        if export_equals == Some(module_symbol) {
            return;
        }

        let type_of_symbol = self.get_type_of_symbol(export_equals.unwrap_or(module_symbol));
        if !self.should_treat_properties_of_external_module_as_exports(type_of_symbol) {
            return;
        }

        // forEachPropertyOfType
        let reduced_type = self.get_reduced_apparent_type(type_of_symbol);
        if !self
            .types_handle()
            .get(reduced_type)
            .flags
            .intersects(TypeFlags::STRUCTURED_TYPE)
        {
            return;
        }
        let members = {
            let t = self.resolve_structured_type_members(reduced_type);
            let __arena_guard = self.types.clone();
            let guard = __arena_guard.get(t);
            guard
                .data
                .as_structured_type()
                .map(|s| s.members.clone())
                .unwrap_or_default()
        };
        for (name, &symbol) in members.entries() {
            if self.is_named_member(symbol, name) {
                cb(symbol, name);
            }
        }
    }

    /// `(c *Checker) IsValidPropertyAccess` / `isValidPropertyAccess`
    /// (services.go:164/168) — collapsed.
    pub fn is_valid_property_access(&mut self, node: NodeId, property_name: &str) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::PropertyAccessExpression => {
                let expr = nodes[node]
                    .expression()
                    .expect("property access expression");
                let is_super = nodes[expr].kind == ast::Kind::SuperKeyword;
                let checked = self.check_expression(expr);
                let t = self.get_widened_type(checked);
                self.is_valid_property_access_with_type(node, is_super, property_name, t)
            }
            ast::Kind::QualifiedName => {
                let left = nodes[node]
                    .as_qualified_name()
                    .left
                    .expect("qualified name left");
                let checked = self.check_expression(left);
                let t = self.get_widened_type(checked);
                self.is_valid_property_access_with_type(node, false, property_name, t)
            }
            ast::Kind::ImportType => {
                let t = self.get_type_from_type_node(node);
                self.is_valid_property_access_with_type(node, false, property_name, t)
            }
            _ => panic!(
                "Unexpected node kind in isValidPropertyAccess: {:?}",
                nodes[node].kind
            ),
        }
    }

    /// `(c *Checker) isValidPropertyAccessWithType` (services.go:180).
    pub(crate) fn is_valid_property_access_with_type(
        &mut self,
        node: NodeId,
        is_super: bool,
        property_name: &str,
        t: TypeId,
    ) -> bool {
        // Short-circuiting for improved performance.
        if crate::utilities::is_type_any(&self.types, t) {
            return true;
        }
        let prop = self.get_property_of_type(t, property_name);
        prop.is_some_and(|prop| self.is_property_accessible(node, is_super, false, t, prop))
    }

    // `IsValidPropertyAccessForCompletions` (services.go:198) is already
    // ported in checker_b.rs (`is_valid_property_access_for_completions`).

    /// `(c *Checker) GetAllPossiblePropertiesOfTypes` (services.go:209).
    pub fn get_all_possible_properties_of_types(&mut self, types: &[TypeId]) -> Vec<SymbolId> {
        let union_type = self.get_union_type(types);
        if !self
            .types_handle()
            .get(union_type)
            .flags
            .intersects(TypeFlags::UNION)
        {
            return self.get_augmented_properties_of_type(union_type);
        }

        let mut props: SymbolTable = OrderedMap::new();
        for &member_type in types {
            let augmented_props = self.get_augmented_properties_of_type(member_type);
            for p in augmented_props {
                let name = self.sym(p).name.clone();
                if !props.has(name.as_str()) {
                    let prop = self.create_union_or_intersection_property(union_type, &name, false);
                    // May be undefined if the property is private
                    if let Some(prop) = prop {
                        props.set(name.into(), prop);
                    }
                }
            }
        }
        props.values().copied().collect()
    }

    /// `(c *Checker) IsUnknownSymbol` (services.go:231).
    pub fn is_unknown_symbol(&self, symbol: Option<SymbolId>) -> bool {
        symbol == Some(self.unknown_symbol)
    }

    /// `(c *Checker) IsUndefinedSymbol` (services.go:235).
    pub fn is_undefined_symbol(&self, symbol: Option<SymbolId>) -> bool {
        symbol == Some(self.undefined_symbol)
    }

    /// `(c *Checker) IsArgumentsSymbol` (services.go:239).
    pub fn is_arguments_symbol(&self, symbol: Option<SymbolId>) -> bool {
        symbol == Some(self.arguments_symbol)
    }

    /// `(c *Checker) GetNonOptionalType` (services.go:244).
    pub fn get_non_optional_type(&mut self, t: TypeId) -> TypeId {
        self.remove_optional_type_marker(t)
    }

    /// `(c *Checker) GetStringIndexType` (services.go:248).
    pub fn get_string_index_type(&mut self, t: TypeId) -> Option<TypeId> {
        self.get_index_type_of_type(t, self.string_type)
    }

    /// `(c *Checker) GetNumberIndexType` (services.go:252).
    pub fn get_number_index_type(&mut self, t: TypeId) -> Option<TypeId> {
        self.get_index_type_of_type(t, self.number_type)
    }

    /// `(c *Checker) GetElementTypeOfArrayType` / `getElementTypeOfArrayType`
    /// (services.go:256, checker.go:24037) — identical bodies in Go,
    /// collapsed.
    pub fn get_element_type_of_array_type(&mut self, t: TypeId) -> Option<TypeId> {
        if self.is_array_type(t) {
            return self.get_type_arguments(t).first().copied();
        }
        None
    }

    /// `(c *Checker) GetCallSignatures` (services.go:260).
    pub fn get_call_signatures(&mut self, t: TypeId) -> Vec<SignatureId> {
        self.get_signatures_of_type(t, SignatureKind::Call)
    }

    /// `(c *Checker) GetConstructSignatures` (services.go:264).
    pub fn get_construct_signatures(&mut self, t: TypeId) -> Vec<SignatureId> {
        self.get_signatures_of_type(t, SignatureKind::Construct)
    }

    /// `(c *Checker) GetApparentProperties` (services.go:268).
    pub fn get_apparent_properties(&mut self, t: TypeId) -> Vec<SymbolId> {
        self.get_augmented_properties_of_type(t)
    }

    /// `(c *Checker) getAugmentedPropertiesOfType` (services.go:272).
    pub(crate) fn get_augmented_properties_of_type(&mut self, t: TypeId) -> Vec<SymbolId> {
        let t = self.get_apparent_type(t);
        let props = self.get_properties_of_type(t);
        let mut props_by_name = crate::utilities::create_symbol_table(&props, &self.symbol_arena);
        let mut function_type: Option<TypeId> = None;
        if !self
            .get_signatures_of_type(t, SignatureKind::Call)
            .is_empty()
        {
            function_type = Some(self.global_callable_function_type);
        } else if !self
            .get_signatures_of_type(t, SignatureKind::Construct)
            .is_empty()
        {
            function_type = Some(self.global_newable_function_type);
        }

        if let Some(function_type) = function_type {
            for p in self.get_properties_of_type(function_type) {
                let name = self.sym(p).name.clone();
                if !props_by_name.has(name.as_str()) {
                    props_by_name.set(name.into(), p);
                }
            }
        }
        self.get_named_members(&props_by_name, None)
    }

    /// `(c *Checker) TryGetMemberInModuleExportsAndProperties` (services.go:295).
    pub fn try_get_member_in_module_exports_and_properties(
        &mut self,
        member_name: &str,
        module_symbol: SymbolId,
    ) -> Option<SymbolId> {
        if let Some(symbol) = self.try_get_member_in_module_exports(member_name, module_symbol) {
            return Some(symbol);
        }

        let export_equals = self.resolve_external_module_symbol(Some(module_symbol), false);
        if export_equals == Some(module_symbol) {
            return None;
        }

        let t = self.get_type_of_symbol(export_equals.unwrap_or(module_symbol));
        if self.should_treat_properties_of_external_module_as_exports(t) {
            return self.get_property_of_type(t, member_name);
        }
        None
    }

    /// `(c *Checker) TryGetMemberInModuleExports` (services.go:313).
    pub fn try_get_member_in_module_exports(
        &mut self,
        member_name: &str,
        module_symbol: SymbolId,
    ) -> Option<SymbolId> {
        let symbol_table = self.get_exports_of_module(module_symbol);
        symbol_table.get(member_name).copied()
    }

    /// `(c *Checker) shouldTreatPropertiesOfExternalModuleAsExports`
    /// (services.go:318).
    pub(crate) fn should_treat_properties_of_external_module_as_exports(
        &mut self,
        resolved_external_module_type: TypeId,
    ) -> bool {
        !self.types_handle().get(resolved_external_module_type)
            .flags
            .intersects(TypeFlags::PRIMITIVE)
            || self.types_handle().get(resolved_external_module_type)
                .object_flags
                .intersects(crate::types::ObjectFlags::CLASS)
            // `isArrayOrTupleLikeType` is too expensive to use in this
            // auto-imports hot path.
            || self.is_array_type(resolved_external_module_type)
            || crate::checker_core::is_tuple_type(&self.types, resolved_external_module_type)
    }

    /// `(c *Checker) GetContextualType` (services.go:326) — `_api` suffix
    /// because the internal `get_contextual_type` (checker_d.rs) has the
    /// same signature.
    pub fn get_contextual_type_api(
        &mut self,
        node: NodeId,
        context_flags: crate::types::ContextFlags,
    ) -> Option<TypeId> {
        if context_flags.intersects(crate::types::ContextFlags::IGNORE_NODE_INFERENCES) {
            return self.run_with_inference_blocked_from_source_node(node, |c| {
                c.get_contextual_type(node, context_flags)
            });
        }
        self.get_contextual_type(node, context_flags)
    }

    /// `(c *Checker) runWithInferenceBlockedFromSourceNode` (services.go:333).
    pub(crate) fn run_with_inference_blocked_from_source_node<T>(
        &mut self,
        node: NodeId,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let containing_call = ast::find_ancestor(Some(node), &nodes, &mut |n, ns| {
            ast::is_call_like_expression(n, ns)
        });
        if let Some(containing_call) = containing_call {
            let mut to_mark_skip = Some(node);
            loop {
                if let Some(mark) = to_mark_skip {
                    self.skip_direct_inference_nodes.add(mark);
                    to_mark_skip = nodes[mark].parent;
                }
                if to_mark_skip.is_none() || to_mark_skip == Some(containing_call) {
                    break;
                }
            }
        }

        self.is_inference_partially_blocked = true;
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let result = self.run_without_resolved_signature_caching(&nodes, node, f);
        self.is_inference_partially_blocked = false;

        self.skip_direct_inference_nodes.clear();
        result
    }

    /// `(c *Checker) SkipAlias` (services.go:395).
    pub fn skip_alias(&mut self, symbol: SymbolId) -> Option<SymbolId> {
        if self.sym(symbol).flags.intersects(SymbolFlags::ALIAS) {
            return self.get_aliased_symbol(symbol);
        }
        Some(symbol)
    }

    /// `(c *Checker) GetRootSymbols` (services.go:402).
    pub fn get_root_symbols(&mut self, symbol: SymbolId) -> Vec<SymbolId> {
        let roots = self.get_immediate_root_symbols(symbol);
        if roots.is_empty() {
            return vec![symbol];
        }
        let mut result = Vec::new();
        for root in roots {
            result.extend(self.get_root_symbols(root));
        }
        result
    }

    /// `(c *Checker) GetMappedTypeSymbolOfProperty` (services.go:414).
    pub fn get_mapped_type_symbol_of_property(&mut self, symbol: SymbolId) -> Option<SymbolId> {
        if let Some(value_links) = self.value_symbol_links.try_get(symbol) {
            let containing_type = value_links.containing_type?;
            return self.types_handle().get(containing_type).symbol;
        }
        None
    }

    /// `(c *Checker) getImmediateRootSymbols` (services.go:421).
    pub(crate) fn get_immediate_root_symbols(&mut self, symbol: SymbolId) -> Vec<SymbolId> {
        if self
            .sym(symbol)
            .check_flags
            .intersects(ast::checkflags::CheckFlags::SYNTHETIC)
        {
            let name = self.sym(symbol).name.clone();
            let containing_type = self.value_symbol_links.get(symbol).containing_type;
            let types = containing_type
                .map(|t| self.types_handle().get(t).types().to_vec())
                .unwrap_or_default();
            return types
                .iter()
                .filter_map(|&t| self.get_property_of_type(t, &name))
                .collect();
        }
        if self.sym(symbol).flags.intersects(SymbolFlags::TRANSIENT) {
            if self.spread_links.has(&symbol) {
                let left_spread = self.spread_links.get(symbol).left_spread;
                let right_spread = self.spread_links.get(symbol).right_spread;
                if let Some(left_spread) = left_spread {
                    // PORT: Go returns `{leftSpread, rightSpread}` even when
                    // `rightSpread` is nil (a nil element that panics
                    // downstream); only `Some` values are emitted here.
                    let mut result = vec![left_spread];
                    if let Some(right_spread) = right_spread {
                        result.push(right_spread);
                    }
                    return result;
                }
            }
            if self.mapped_symbol_links.has(&symbol) {
                let synthetic_origin = self.mapped_symbol_links.get(symbol).synthetic_origin;
                if let Some(synthetic_origin) = synthetic_origin {
                    return vec![synthetic_origin];
                }
            }
            if let Some(target) = self.try_get_target(symbol) {
                return vec![target];
            }
        }
        Vec::new()
    }

    /// `(c *Checker) tryGetTarget` (services.go:452).
    pub(crate) fn try_get_target(&mut self, symbol: SymbolId) -> Option<SymbolId> {
        let mut target: Option<SymbolId> = None;
        let mut next = Some(symbol);
        loop {
            next = match next {
                Some(n) if self.value_symbol_links.has(n) => self.value_symbol_links.get(n).target,
                Some(n) if self.export_type_links.has(&n) => self.export_type_links.get(n).target,
                _ => None,
            };
            if next.is_none() {
                break;
            }
            target = next;
        }
        target
    }

    /// `(c *Checker) GetExportSymbolOfSymbol` (services.go:471).
    pub fn get_export_symbol_of_symbol(&mut self, symbol: SymbolId) -> SymbolId {
        let export_symbol = self.sym(symbol).export_symbol.unwrap_or(symbol);
        self.get_merged_symbol(export_symbol)
    }

    /// `(c *Checker) GetExportSpecifierLocalTargetSymbol` (services.go:475).
    /// `node` should be an ExportSpecifier or Identifier.
    pub fn get_export_specifier_local_target_symbol(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::ExportSpecifier => {
                let grandparent = nodes[node].parent.and_then(|p| nodes[p].parent);
                if grandparent.is_some_and(|gp| nodes[gp].module_specifier().is_some()) {
                    return self.get_external_module_member(
                        grandparent.expect("grandparent"),
                        node,
                        false,
                    );
                }
                let name = nodes[node].property_name_or_name()?;
                if nodes[name].kind == ast::Kind::StringLiteral {
                    // Skip for invalid syntax like this: export { "x" }
                    return None;
                }
                self.resolve_entity_name(
                    Some(name),
                    SymbolFlags::VALUE
                        | SymbolFlags::TYPE
                        | SymbolFlags::NAMESPACE
                        | SymbolFlags::ALIAS,
                    true,  /*ignoreErrors*/
                    false, /*dontResolveAlias*/
                    None,
                )
            }
            ast::Kind::Identifier => self.resolve_entity_name(
                Some(node),
                SymbolFlags::VALUE
                    | SymbolFlags::TYPE
                    | SymbolFlags::NAMESPACE
                    | SymbolFlags::ALIAS,
                true,  /*ignoreErrors*/
                false, /*dontResolveAlias*/
                None,
            ),
            _ => panic!(
                "Unhandled case in getExportSpecifierLocalTargetSymbol, node should be ExportSpecifier | Identifier"
            ),
        }
    }

    /// `(c *Checker) GetShorthandAssignmentValueSymbol` (services.go:494).
    pub fn get_shorthand_assignment_value_symbol(
        &mut self,
        location: Option<NodeId>,
    ) -> Option<SymbolId> {
        if let Some(location) = location {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((location).file_index());
            if nodes[location].kind == ast::Kind::ShorthandPropertyAssignment {
                let name = nodes[location].name()?;
                return self.resolve_entity_name(
                    Some(name),
                    SymbolFlags::VALUE | SymbolFlags::ALIAS,
                    true,  /*ignoreErrors*/
                    false, /*dontResolveAlias*/
                    None,
                );
            }
        }
        None
    }

    /// `(c *Checker) GetSymbolsOfParameterPropertyDeclaration`
    /// (services.go:507) — `(parameterSymbol, propertySymbol)`.
    pub fn get_symbols_of_parameter_property_declaration(
        &mut self,
        parameter: NodeId,
        parameter_name: &str,
    ) -> (SymbolId, SymbolId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((parameter).file_index());
        let constructor_declaration = nodes[parameter].parent.expect("parameter parent");
        let class_declaration = nodes[constructor_declaration]
            .parent
            .expect("constructor parent");

        let parameter_symbol = nodes[constructor_declaration]
            .locals()
            .and_then(|locals| self.get_symbol(locals, parameter_name, SymbolFlags::VALUE));
        // `get_members_of_symbol`/`get_symbol` take `&mut self`, so the
        // `nodes` arena borrow ends above (it's an `Rc`).
        let class_symbol = nodes[class_declaration].symbol();
        let property_symbol = class_symbol.and_then(|class_symbol| {
            let members = self.get_members_of_symbol(class_symbol);
            self.get_symbol(&members, parameter_name, SymbolFlags::VALUE)
        });

        if let (Some(parameter_symbol), Some(property_symbol)) = (parameter_symbol, property_symbol)
        {
            return (parameter_symbol, property_symbol);
        }
        panic!(
            "There should exist two symbols, one as property declaration and one as parameter declaration"
        )
    }

    /// `(c *Checker) IsDeclarationUsed` (services.go:523) — checks if an
    /// import declaration identifier is used in the source file.
    pub fn is_declaration_used(
        &mut self,
        source_file: NodeId,
        identifier: NodeId,
        jsx_elements_present: bool,
        jsx_mode_needs_explicit_import: bool,
    ) -> bool {
        if jsx_elements_present && jsx_mode_needs_explicit_import {
            let jsx_namespace = self.get_jsx_namespace(source_file);
            let jsx_fragment_factory = self.get_jsx_fragment_factory(source_file);
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((source_file).file_index());
            let identifier_text = nodes[identifier].text(&nodes).into_owned();
            if identifier_text == jsx_namespace {
                return true;
            }
            if !jsx_fragment_factory.is_empty() && identifier_text == jsx_fragment_factory {
                return true;
            }
        }

        let symbol = self.get_symbol_at_location_api(identifier);
        let Some(symbol) = symbol else {
            return true;
        };

        self.is_symbol_referenced_in_file(source_file, identifier, symbol)
    }

    /// `(c *Checker) IsSymbolReferencedInFile` (services.go:551) — quick
    /// check whether a symbol is used at all in a file.
    pub fn is_symbol_referenced_in_file(
        &mut self,
        source_file: NodeId,
        definition: NodeId,
        symbol: SymbolId,
    ) -> bool {
        let file_index = source_file.file_index();
        let identifier_text = {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((source_file).file_index());
            nodes[definition].text(&nodes).into_owned()
        };
        let tokens = {
            let __program = self.program.clone().expect("program");
            let mut nodes = __program.nodes_mut(file_index);
            get_possible_symbol_reference_nodes(
                &mut nodes,
                source_file,
                &identifier_text,
                Some(source_file),
            )
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((source_file).file_index());
        for token in tokens {
            if !ast::is_identifier(&nodes[token]) {
                continue;
            }
            if token == definition || nodes[token].text(&nodes) != identifier_text {
                continue;
            }
            let ref_symbol = self.get_symbol_at_location_api(token);
            if ref_symbol == Some(symbol) {
                return true;
            }
            if let Some(parent) = nodes[token].parent {
                if nodes[parent].kind == ast::Kind::ShorthandPropertyAssignment {
                    let shorthand_symbol = self.get_shorthand_assignment_value_symbol(Some(parent));
                    if shorthand_symbol == Some(symbol) {
                        return true;
                    }
                }
                if ast::is_export_specifier(&nodes[parent]) {
                    let local_symbol = self
                        .get_local_symbol_for_export_specifier(token, ref_symbol, parent, &nodes);
                    if local_symbol == Some(symbol) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// `(c *Checker) GetReferencesToSymbolInFile` (services.go:586) — all
    /// identifier nodes in the file referencing the given symbol.
    pub fn get_references_to_symbol_in_file(
        &mut self,
        source_file: NodeId,
        symbol: SymbolId,
    ) -> Vec<NodeId> {
        let file_index = source_file.file_index();
        let identifier_text = self.sym(symbol).name.clone();
        let tokens = {
            let __program = self.program.clone().expect("program");
            let mut nodes = __program.nodes_mut(file_index);
            get_possible_symbol_reference_nodes(
                &mut nodes,
                source_file,
                &identifier_text,
                Some(source_file),
            )
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((source_file).file_index());
        let mut result = Vec::new();
        for token in tokens {
            if !ast::is_identifier(&nodes[token]) {
                continue;
            }
            if nodes[token].text(&nodes) != identifier_text {
                continue;
            }
            let ref_symbol = self.get_symbol_at_location_api(token);
            if ref_symbol == Some(symbol) {
                result.push(token);
                continue;
            }
            if let Some(parent) = nodes[token].parent {
                if nodes[parent].kind == ast::Kind::ShorthandPropertyAssignment {
                    let shorthand_symbol = self.get_shorthand_assignment_value_symbol(Some(parent));
                    if shorthand_symbol == Some(symbol) {
                        result.push(token);
                        continue;
                    }
                }
                if ast::is_export_specifier(&nodes[parent]) {
                    let local_symbol = self
                        .get_local_symbol_for_export_specifier(token, ref_symbol, parent, &nodes);
                    if local_symbol == Some(symbol) {
                        result.push(token);
                        continue;
                    }
                }
            }
        }
        result
    }

    /// `(c *Checker) getLocalSymbolForExportSpecifier` (services.go:623).
    pub(crate) fn get_local_symbol_for_export_specifier(
        &mut self,
        reference_location: NodeId,
        reference_symbol: Option<SymbolId>,
        export_specifier: NodeId,
        nodes: &[ast::Node],
    ) -> Option<SymbolId> {
        if is_export_specifier_alias(nodes, reference_location, export_specifier) {
            if let Some(symbol) = self.get_export_specifier_local_target_symbol(export_specifier) {
                return Some(symbol);
            }
        }
        reference_symbol
    }

    /// `(c *Checker) GetTypeArgumentConstraint` (services.go:699) — `_api`
    /// suffix (internal `get_type_argument_constraint` has the same
    /// signature).
    pub fn get_type_argument_constraint_api(&mut self, node: NodeId) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !ast::is_type_node(&nodes[node]) {
            return None;
        }
        self.get_type_argument_constraint(node)
    }

    /// `(c *Checker) getUninstantiatedSignatures` (services.go:707) — gets
    /// generic signatures from the function's/constructor's type.
    pub(crate) fn get_uninstantiated_signatures(&mut self, node: NodeId) -> Vec<SignatureId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::CallExpression | ast::Kind::Decorator => {
                let expr = nodes[node].expression().expect("call expression");
                {
                    let t = self.get_type_of_expression(expr);
                    self.get_signatures_of_type(t, SignatureKind::Call)
                }
            }
            ast::Kind::NewExpression => {
                let expr = nodes[node].expression().expect("new expression");
                {
                    let t = self.get_type_of_expression(expr);
                    self.get_signatures_of_type(t, SignatureKind::Construct)
                }
            }
            ast::Kind::JsxSelfClosingElement | ast::Kind::JsxOpeningElement => {
                let tag_name = nodes[node].tag_name().expect("jsx tag name");
                if crate::utilities::is_jsx_intrinsic_tag_name(tag_name, &nodes) {
                    return Vec::new();
                }
                {
                    let t = self.get_type_of_expression(tag_name);
                    self.get_signatures_of_type(t, SignatureKind::Call)
                }
            }
            ast::Kind::TaggedTemplateExpression => {
                let tag = nodes[node]
                    .as_tagged_template_expression()
                    .tag
                    .expect("tagged template tag");
                {
                    let t = self.get_type_of_expression(tag);
                    self.get_signatures_of_type(t, SignatureKind::Call)
                }
            }
            ast::Kind::BinaryExpression | ast::Kind::JsxOpeningFragment => Vec::new(),
            _ => Vec::new(),
        }
    }

    /// `(c *Checker) getTypeParameterConstraintForPositionAcrossSignatures`
    /// (services.go:726).
    pub(crate) fn get_type_parameter_constraint_for_position_across_signatures(
        &mut self,
        signatures: &[SignatureId],
        position: usize,
    ) -> TypeId {
        let mut relevant_constraints: Vec<TypeId> = Vec::new();
        for &signature in signatures {
            let type_parameters = self.signature_arena.get(signature).type_parameters.clone();
            if position >= type_parameters.len() {
                continue;
            }
            let relevant_type_parameter = type_parameters[position];
            if let Some(relevant_constraint) =
                self.get_constraint_of_type_parameter(relevant_type_parameter)
            {
                relevant_constraints.push(relevant_constraint);
            }
        }
        self.get_union_type(&relevant_constraints)
    }

    /// `(c *Checker) getTypeArgumentConstraint` (services.go:741).
    pub(crate) fn get_type_argument_constraint(&mut self, node: NodeId) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let parent = nodes[node].parent?;
        let mut type_argument_position: i64 = -1;
        if ast::has_type_arguments(&nodes[parent]) {
            if let Some(type_args) = nodes[parent].type_arguments() {
                for (i, &arg) in type_args.iter().enumerate() {
                    if arg == node {
                        type_argument_position = i as i64;
                        break;
                    }
                }
            }
        }

        if type_argument_position >= 0 {
            let position = type_argument_position as usize;
            // The node could be a type argument of a call, a `new` expression,
            // a decorator, an instantiation expression, or a generic type
            // instantiation.
            if ast::is_call_like_expression(&nodes[parent], &nodes) {
                let signatures = self.get_uninstantiated_signatures(parent);
                return Some(
                    self.get_type_parameter_constraint_for_position_across_signatures(
                        &signatures,
                        position,
                    ),
                );
            }

            let grandparent = nodes[parent].parent;
            if grandparent.is_some_and(|gp| ast::is_decorator(&nodes[gp])) {
                let signatures = self.get_uninstantiated_signatures(grandparent.expect("gp"));
                return Some(
                    self.get_type_parameter_constraint_for_position_across_signatures(
                        &signatures,
                        position,
                    ),
                );
            }

            if ast::is_expression_with_type_arguments(&nodes[parent])
                && grandparent.is_some_and(|gp| ast::is_expression_statement(&nodes[gp]))
            {
                let expr = nodes[parent]
                    .expression()
                    .expect("exprWithTypeArgs expression");
                let uninstantiated_type = self.check_expression(expr);

                let call_signatures =
                    self.get_signatures_of_type(uninstantiated_type, SignatureKind::Call);
                let construct_signatures =
                    self.get_signatures_of_type(uninstantiated_type, SignatureKind::Construct);

                let call_constraint = self
                    .get_type_parameter_constraint_for_position_across_signatures(
                        &call_signatures,
                        position,
                    );
                let construct_constraint = self
                    .get_type_parameter_constraint_for_position_across_signatures(
                        &construct_signatures,
                        position,
                    );

                // An instantiation expression instantiates both call and
                // construct signatures, so if both exist type arguments must
                // be assignable to both constraints.
                if self
                    .types_handle()
                    .get(construct_constraint)
                    .flags
                    .intersects(TypeFlags::NEVER)
                {
                    return Some(call_constraint);
                }
                if self
                    .types_handle()
                    .get(call_constraint)
                    .flags
                    .intersects(TypeFlags::NEVER)
                {
                    return Some(construct_constraint);
                }
                return Some(self.get_intersection_type(&[call_constraint, construct_constraint]));
            }

            if ast::is_type_reference_type(&nodes[parent]) {
                let type_parameters = self
                    .get_type_parameters_for_type_reference_or_import(parent)
                    .unwrap_or_default();
                if type_parameters.is_empty() {
                    return None;
                }
                if position >= type_parameters.len() {
                    return None;
                }
                let relevant_type_parameter = type_parameters[position];
                if let Some(constraint) =
                    self.get_constraint_of_type_parameter(relevant_type_parameter)
                {
                    let effective_type_arguments =
                        self.get_effective_type_arguments(parent, &type_parameters);
                    let mapper = crate::mapper::new_type_mapper(
                        self,
                        type_parameters,
                        effective_type_arguments,
                    );
                    return Some(self.instantiate_type(constraint, Some(mapper)));
                }
            }
        }
        None
    }

    /// `(c *Checker) IsTypeInvalidDueToUnionDiscriminant` (services.go:815).
    pub fn is_type_invalid_due_to_union_discriminant(
        &mut self,
        contextual_type: TypeId,
        obj: NodeId,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((obj).file_index());
        let properties: Vec<NodeId> = nodes[obj].properties().unwrap_or(&[]).to_vec();
        properties.iter().any(|&property| {
            let mut name_type: Option<TypeId> = None;
            if let Some(property_name) = nodes[property].name() {
                if ast::is_jsx_namespaced_name(&nodes[property_name]) {
                    let text = nodes[property_name].text(&nodes).into_owned();
                    name_type = Some(self.get_string_literal_type(&text));
                } else {
                    name_type = Some(self.get_literal_type_from_property_name(property_name));
                }
            }
            let mut name = String::new();
            if let Some(name_type) = name_type {
                if crate::utilities::is_type_usable_as_property_name(&self.types, name_type) {
                    name = crate::utilities::get_property_name_from_type(&self.types, name_type);
                }
            }
            let mut expected: Option<TypeId> = None;
            if !name.is_empty() {
                expected = self.get_type_of_property_of_type(contextual_type, &name);
            }
            expected.is_some_and(|expected| {
                crate::checker_d::is_literal_type(&self.types, expected) && {
                    let prop_type = self.get_type_of_node(property);
                    !self.is_type_assignable_to(prop_type, expected)
                }
            })
        })
    }

    /// `(c *Checker) GetExportsAndPropertiesOfModule` (services.go:840) —
    /// unlike `get_exports_of_module`, this includes properties of an
    /// `export =` value.
    pub fn get_exports_and_properties_of_module(
        &mut self,
        module_symbol: SymbolId,
    ) -> Vec<SymbolId> {
        let mut exports = self.get_exports_of_module_as_array(module_symbol);
        let export_equals = self.resolve_external_module_symbol(Some(module_symbol), false);
        if export_equals != Some(module_symbol) {
            let t = self.get_type_of_symbol(export_equals.unwrap_or(module_symbol));
            if self.should_treat_properties_of_external_module_as_exports(t) {
                exports.extend(self.get_properties_of_type(t));
            }
        }
        exports
    }

    /// `(c *Checker) GetJsxIntrinsicTagNamesAt` (services.go:857) — all
    /// properties of the Jsx.IntrinsicElements interface.
    pub fn get_jsx_intrinsic_tag_names_at(&mut self, location: NodeId) -> Vec<SymbolId> {
        let intrinsics = self.get_jsx_type(JSX_NAMES_INTRINSIC_ELEMENTS, location);
        // PORT: Rust's `get_jsx_type` returns `error_type` where Go returns nil.
        if intrinsics == self.error_type {
            return Vec::new();
        }
        self.get_properties_of_type(intrinsics)
    }

    /// `(c *Checker) GetContextualTypeForJsxAttribute` (services.go:865) —
    /// `_api` suffix because the internal `get_contextual_type_for_jsx_attribute`
    /// (jsx.rs) takes an extra `ContextFlags` parameter.
    pub fn get_contextual_type_for_jsx_attribute_api(
        &mut self,
        attribute: NodeId,
    ) -> Option<TypeId> {
        self.get_contextual_type_for_jsx_attribute(attribute, crate::types::ContextFlags::NONE)
    }

    /// `(c *Checker) GetConstantValue` (services.go:869).
    pub fn get_constant_value(&mut self, node: NodeId) -> Option<evaluator::Value> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if nodes[node].kind == ast::Kind::EnumMember {
            return self.get_enum_member_value(node).value;
        }

        if self.symbol_node_links.get(node).resolved_symbol.is_none() {
            self.check_expression_cached(node); // ensure cached resolved symbol is set
        }
        let mut symbol = self.symbol_node_links.get(node).resolved_symbol;
        if symbol.is_none() && ast::is_entity_name_expression(&nodes[node], &nodes) {
            symbol = self.resolve_entity_name(
                Some(node),
                SymbolFlags::VALUE,
                true,  /*ignoreErrors*/
                false, /*dontResolveAlias*/
                None,  /*location*/
            );
        }
        if let Some(symbol) = symbol {
            if self.sym(symbol).flags.intersects(SymbolFlags::ENUM_MEMBER) {
                // inline property/index accesses only for const enums
                let member = self.sym(symbol).value_declaration?;
                let __program = self.program.clone().expect("program");
                let member_nodes = __program.nodes((member).file_index());
                let member_parent = member_nodes[member].parent?;
                if ast::is_enum_const(member_parent, &member_nodes) {
                    return self.get_enum_member_value(member).value;
                }
            }
        }
        None
    }

    /// `(c *Checker) GetCandidateSignaturesForStringLiteralCompletions`
    /// (services.go:909).
    pub fn get_candidate_signatures_for_string_literal_completions(
        &mut self,
        call: NodeId,
        editing_argument: NodeId,
    ) -> Vec<SignatureId> {
        // first, get candidates when inference is blocked from the source node.
        let mut candidates =
            self.run_with_inference_blocked_from_source_node(editing_argument, |c| {
                c.get_resolved_signature_worker(call, CheckMode::NORMAL, 0)
                    .1
            });
        let mut candidates_set: std::collections::HashSet<SignatureId> =
            candidates.iter().copied().collect();

        // next, get candidates where the source node is considered for
        // inference.
        let __program = self.program.clone().expect("program");
        let arg_nodes = __program.nodes((editing_argument).file_index());
        let other_candidates =
            self.run_without_resolved_signature_caching(&arg_nodes, editing_argument, |c| {
                c.get_resolved_signature_worker(call, CheckMode::NORMAL, 0)
                    .1
            });

        for candidate in other_candidates {
            if candidates_set.contains(&candidate) {
                continue;
            }
            candidates.push(candidate);
            candidates_set.insert(candidate);
        }

        candidates
    }

    /// `(c *Checker) GetTypeParameterAtPosition` (services.go:938).
    /// (`GetTypeAtPosition` → `get_type_at_position` in relater.rs.)
    pub fn get_type_parameter_at_position(&mut self, s: SignatureId, pos: usize) -> TypeId {
        let t = self.get_type_at_position(s, pos);
        let target = {
            let __arena_guard = self.types.clone();
            let guard = __arena_guard.get(t);
            if guard.is_index() {
                guard.as_index_type().target
            } else {
                None
            }
        };
        if let Some(target) = target {
            if crate::utilities::is_this_type_parameter(&self.types, target) {
                if let Some(constraint) = self.get_base_constraint_of_type(target) {
                    return self.get_index_type(constraint);
                }
            }
        }
        t
    }

    /// `(c *Checker) GetContextualTypeForArrayLiteralAtPosition`
    /// (services.go:951) — contextual type for an element at the given
    /// position in an array with the given contextual type.
    pub fn get_contextual_type_for_array_literal_at_position(
        &mut self,
        contextual_array_type: Option<TypeId>,
        array_literal: NodeId,
        position: i64,
    ) -> Option<TypeId> {
        contextual_array_type?;
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((array_literal).file_index());
        let mut first_spread_index: i64 = -1;
        let mut last_spread_index: i64 = -1;
        let mut element_index: i64 = 0;
        let elements: Vec<NodeId> = nodes[array_literal].elements().unwrap_or(&[]).to_vec();
        for (i, &elem) in elements.iter().enumerate() {
            if i64::from(nodes[elem].pos()) < position {
                element_index += 1;
            }
            if ast::is_spread_element(&nodes[elem]) {
                if first_spread_index == -1 {
                    first_spread_index = i as i64;
                }
                last_spread_index = i as i64;
            }
        }
        // The array may be incomplete, so we don't know its final length.
        self.get_contextual_type_for_element_expression(
            contextual_array_type,
            element_index as i32,
            -1, /*length*/
            first_spread_index as i32,
            last_spread_index as i32,
        )
    }

    /// `(c *Checker) GetFirstTypeArgumentFromKnownType` (services.go:1007).
    pub fn get_first_type_argument_from_known_type(&mut self, t: TypeId) -> Option<TypeId> {
        let (is_reference, symbol) = {
            let __arena_guard = self.types.clone();
            let guard = __arena_guard.get(t);
            (
                guard
                    .object_flags
                    .intersects(crate::types::ObjectFlags::REFERENCE),
                guard.symbol,
            )
        };
        if is_reference {
            if let Some(symbol) = symbol {
                let name = self.sym(symbol).name.clone();
                if is_known_generic_type_name(&name) {
                    if let Some(global_symbol) =
                        self.get_global_symbol(&name, SymbolFlags::TYPE, None)
                    {
                        let __arena_target_symbol = self.types.clone();
                        let target_symbol = __arena_target_symbol
                            .get(t)
                            .target()
                            .and_then(|tt| self.types_handle().get(tt).symbol);
                        if target_symbol == Some(global_symbol) {
                            return self.get_type_arguments(t).first().copied();
                        }
                    }
                }
            }
        }
        let __arena_alias = self.types.clone();
        let alias = __arena_alias.get(t).alias.clone();
        if let Some(alias) = alias {
            let alias_name = alias
                .symbol
                .map(|s| self.sym(s).name.clone())
                .unwrap_or_default();
            if is_known_generic_type_name(&alias_name) {
                if let Some(global_symbol) =
                    self.get_global_symbol(&alias_name, SymbolFlags::TYPE, None)
                {
                    if alias.symbol == Some(global_symbol) {
                        return alias.type_arguments.first().copied();
                    }
                }
            }
        }
        None
    }

    /// `(c *Checker) GetPropertySymbolsFromContextualType` (services.go:1024)
    /// — all symbols for one property (not every property).
    pub fn get_property_symbols_from_contextual_type(
        &mut self,
        node: NodeId,
        contextual_type: TypeId,
        union_symbol_ok: bool,
    ) -> Vec<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let name_node = nodes[node].name().expect("node name");
        let name = ast::get_text_of_property_name(name_node, &nodes);
        if name.is_empty() {
            return Vec::new();
        }
        if !self
            .types_handle()
            .get(contextual_type)
            .flags
            .intersects(TypeFlags::UNION)
        {
            if let Some(symbol) = self.get_property_of_type(contextual_type, &name) {
                return vec![symbol];
            }
            return Vec::new();
        }
        let all_types: Vec<TypeId> = self.types_handle().get(contextual_type).types().to_vec();
        let parent = nodes[node].parent;
        let mut filtered_types = all_types.clone();
        if parent.is_some_and(|p| {
            ast::is_object_literal_expression(&nodes[p]) || ast::is_jsx_attributes(&nodes[p])
        }) {
            let parent = parent.expect("parent");
            filtered_types.retain(|&t| !self.is_type_invalid_due_to_union_discriminant(t, parent));
        }
        let discriminated_property_symbols: Vec<SymbolId> = filtered_types
            .iter()
            .filter_map(|&t| self.get_property_of_type(t, &name))
            .collect();
        if union_symbol_ok
            && (discriminated_property_symbols.is_empty()
                || discriminated_property_symbols.len() == all_types.len())
        {
            if let Some(symbol) = self.get_property_of_type(contextual_type, &name) {
                return vec![symbol];
            }
        }
        if filtered_types.is_empty() && discriminated_property_symbols.is_empty() {
            // Bad discriminant -- do again without discriminating
            return all_types
                .iter()
                .filter_map(|&t| self.get_property_of_type(t, &name))
                .collect();
        }
        // by eliminating duplicates we might even end up with a single symbol
        // that helps with displaying better quick infos on properties of
        // union types
        let mut seen = std::collections::HashSet::new();
        discriminated_property_symbols
            .into_iter()
            .filter(|s| seen.insert(*s))
            .collect()
    }

    /// `(c *Checker) GetPropertySymbolOfDestructuringAssignment`
    /// (services.go:1069).
    pub fn get_property_symbol_of_destructuring_assignment(
        &mut self,
        location: NodeId,
    ) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((location).file_index());
        let grandparent = nodes[location].parent.and_then(|p| nodes[p].parent)?;
        if is_array_literal_or_object_literal_destructuring_pattern(grandparent, &nodes) {
            // Get the type of the object or array literal and then look for
            // property of given name in the type
            if let Some(type_of_object_literal) = self.get_type_of_assignment_pattern(grandparent) {
                let name = nodes[location].text(&nodes).into_owned();
                return self.get_property_of_type(type_of_object_literal, &name);
            }
        }
        None
    }

    /// `(c *Checker) getTypeOfAssignmentPattern` (services.go:1088) — type
    /// of the object or array literal of a destructuring assignment.
    pub(crate) fn get_type_of_assignment_pattern(&mut self, expr: NodeId) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((expr).file_index());
        let parent = nodes[expr].parent?;
        // If this is from "for of"
        //     for ( { a } of elems) {
        //     }
        if ast::is_for_of_statement(&nodes[parent]) {
            let iterated_type = self.check_right_hand_side_of_for_of(parent);
            return Some(self.check_destructuring_assignment(
                expr,
                iterated_type,
                CheckMode::NORMAL,
                false,
            ));
        }
        // If this is from "for" initializer
        //     for ({a } = elems[0];.....) { }
        if ast::is_binary_expression(&nodes[parent]) {
            let right = nodes[parent]
                .as_binary_expression()
                .right
                .expect("binary right");
            let iterated_type = self.get_type_of_expression(right);
            return Some(self.check_destructuring_assignment(
                expr,
                iterated_type,
                CheckMode::NORMAL,
                false,
            ));
        }
        // If this is from nested object binding pattern
        //     for ({ skills: { primary, secondary } } = multiRobot, i = 0; i < 1; i++) {
        if ast::is_property_assignment(&nodes[parent]) {
            let node = nodes[parent].parent?;
            let type_of_parent_object_literal = self
                .get_type_of_assignment_pattern(node)
                .unwrap_or(self.error_type);
            let properties: Vec<NodeId> = nodes[node].properties().unwrap_or(&[]).to_vec();
            let property_index = properties.iter().position(|&p| p == parent).unwrap_or(0) as usize;
            return self.check_object_literal_destructuring_property_assignment(
                node,
                type_of_parent_object_literal,
                property_index,
                false,
                false,
            );
        }
        // Array literal assignment - array destructuring pattern
        //    [{ property1: p1, property2 }] = elems;
        let type_of_array_literal = self
            .get_type_of_assignment_pattern(parent)
            .unwrap_or(self.error_type);
        let element_type = self.check_iterated_type_or_element_type(
            IterationUse::DESTRUCTURING,
            type_of_array_literal,
            self.undefined_type,
            Some(parent),
        );
        let elements: Vec<NodeId> = nodes[parent].elements().unwrap_or(&[]).to_vec();
        let element_index = elements.iter().position(|&e| e == expr).unwrap_or(0) as usize;
        self.check_array_literal_destructuring_element_assignment(
            parent,
            type_of_array_literal,
            element_index,
            element_type,
            CheckMode::NORMAL,
        )
    }

    /// `(c *Checker) IsLibSymbolForHoverVerbosity` (services.go:1123) — true
    /// if the symbol is declared in a lib file.
    pub fn is_lib_symbol_for_hover_verbosity(&mut self, symbol: Option<SymbolId>) -> bool {
        let Some(symbol) = symbol else { return false };
        let declarations = self.sym(symbol).declarations.clone();
        for decl in declarations {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((decl).file_index());
            let sf = ast::get_source_file_of_node(Some(decl), &nodes);
            if let Some(sf) = sf {
                let path_key = nodes[sf].as_source_file().path_key().clone();
                if self
                    .program
                    .as_ref()
                    .expect("program")
                    .is_source_file_default_library(&path_key)
                {
                    return true;
                }
            }
        }
        false
    }

    /// `(c *Checker) IsLibTypeForHoverVerbosity` (services.go:1138) — true if
    /// the type is declared in a lib file; `Array`/`Promise`-like types are
    /// treated as opaque.
    pub fn is_lib_type_for_hover_verbosity(&mut self, t: TypeId) -> bool {
        let symbol = {
            let __arena_guard = self.types.clone();
            let guard = __arena_guard.get(t);
            if guard
                .object_flags
                .intersects(crate::types::ObjectFlags::REFERENCE)
            {
                guard
                    .target()
                    .and_then(|tt| self.types_handle().get(tt).symbol)
            } else {
                guard.symbol
            }
        };
        if self.is_lib_symbol_for_hover_verbosity(symbol) {
            return true;
        }
        crate::checker_core::is_tuple_type(&self.types, t)
    }
}

/// `JsxNames.IntrinsicElements` (jsx.go:55). The full `JsxNames` table is
/// deferred to the jsx.rs wave; only the constant needed here is defined.
pub const JSX_NAMES_INTRINSIC_ELEMENTS: &str = "IntrinsicElements";

/// `ast.IsArrayLiteralOrObjectLiteralDestructuringPattern` (ast.go:1406).
/// PORT: implemented locally because the ast crate does not export it yet.
fn is_array_literal_or_object_literal_destructuring_pattern(
    node: NodeId,
    nodes: &[ast::Node],
) -> bool {
    if !(ast::is_array_literal_expression(&nodes[node])
        || ast::is_object_literal_expression(&nodes[node]))
    {
        return false;
    }
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    // [a,b,c] from: [a, b, c] = someExpression;
    if ast::is_binary_expression(&nodes[parent]) {
        let bin = nodes[parent].as_binary_expression();
        if bin.left == Some(node)
            && bin
                .operator_token
                .is_some_and(|t| nodes[t].kind == ast::Kind::EqualsToken)
        {
            return true;
        }
    }
    // [a, b, c] from: for([a, b, c] of expression)
    if ast::is_for_of_statement(&nodes[parent]) && nodes[parent].initializer() == Some(node) {
        return true;
    }
    // {x, a: {a, b, c} } = someExpression
    if ast::is_property_assignment(&nodes[parent]) {
        return nodes[parent]
            .parent
            .is_some_and(|gp| is_array_literal_or_object_literal_destructuring_pattern(gp, nodes));
    }
    // [a, b, c] of [x, [a, b, c] ] = someExpression
    is_array_literal_or_object_literal_destructuring_pattern(parent, nodes)
}
