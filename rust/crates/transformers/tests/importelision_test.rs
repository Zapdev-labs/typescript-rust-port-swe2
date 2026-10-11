//! Ported from tsc/internal/transformers/tstransforms/importelision_test.go
//! `TestImportElision` @ ec47d33c23e464a17cdf2475632cba629bee8763.
//!
//! Each case parses `input` (plus a bound `other.ts` module when `other` is
//! non-empty), runs `NewTypeEraserTransformer` then
//! `NewImportElisionTransformer`, and asserts the emitted output.
//!
//! PORT: Go drives the transform with `checker.NewChecker(&fakeProgram)` +
//! `c.NewEmitResolver(emitContext)`. The Rust checker's emit resolver is a
//! `PORT(deferred)` shell (`crates/checker/src/emitresolver.rs`) and
//! `Checker::new_checker` still panics on deferred helper state, so this test
//! supplies `FakeEmitResolver` — a binder-level stand-in implementing the four
//! `EmitResolver` members `ImportElisionTransformer` consults
//! (`mark_linked_references_recursively`, `is_referenced_alias_declaration`,
//! `is_value_alias_declaration`,
//! `is_top_level_value_import_equals_with_entity_name`) with the same
//! mark/resolve semantics as `checker.go`/`emitresolver.go`
//! (`markLinkedReferences`, `markAliasReferenced`, `resolveAlias`,
//! `getSymbolFlagsEx`, `isAliasResolvedToValue`). `fakeProgram`'s
//! `getResolvedModule`/`getSourceFileForResolvedModule` pair collapses into
//! `FakeEmitResolver::modules`, keyed by module-specifier text. Checker-only
//! inputs that never occur in this table (merged/global/lib symbols, JS
//! aliases, `getTypeOnlyAliasDeclaration` links, const-enum inlining knobs)
//! are absent; every other `EmitResolver`/`ReferenceResolver` method is
//! `unimplemented!()` — the transform never calls them.
//!
//! `Symbol` is not `Clone`, so name resolution runs `NameResolver::resolve`
//! against a field-wise scratch copy of the bound symbol arena
//! (`resolve` needs `&mut Vec<Symbol>` only to append transient
//! `arguments`/`require` symbols; `SymbolId`s index identically into the
//! scratch and real arenas).

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::{FxHashMap, FxHashSet};
use tsc_ast::symbol::{INTERNAL_SYMBOL_NAME_DEFAULT, INTERNAL_SYMBOL_NAME_EXPORT_EQUALS};
use tsc_ast::symbolflags::SymbolFlags;
use tsc_ast::{
    self as ast, Kind, ModifierFlags, Node, NodeFlags, NodeId, Symbol, SymbolId, SymbolTable,
};
use tsc_binder::binder::bind_source_file;
use tsc_binder::nameresolver::NameResolver;
use tsc_binder::referenceresolver::ReferenceResolver;
use tsc_core::options_generated::{CompilerOptions, NewLineKind};
use tsc_evaluator::Value;
use tsc_nodebuilder::{Flags, InternalFlags, SymbolTracker};
use tsc_printer::{
    EmitContext, EmitResolver, PrintHandlers, Printer, PrinterOptions, SymbolAccessibilityResult,
    TypeReferenceSerializationKind,
};
use tsc_testutil::parsetestutil;
use tsc_transformers::TransformOptions;
use tsc_transformers::tstransforms::{new_import_elision_transformer, new_type_eraser_transformer};

// ---------------------------------------------------------------------------
// Fake emit resolver (stands in for `checker.NewChecker` + `NewEmitResolver`)
// ---------------------------------------------------------------------------

/// A bound source file in its own arena — the `other.ts` module the Go test
/// wires through `fakeProgram.getSourceFileForResolvedModule`.
struct BoundFile {
    nodes: Vec<Node>,
    file: NodeId,
}

/// `(SymbolId, arena)` result of an alias chain; `None` plays Go's
/// `unknownSymbol` (unresolved module/name — conservatively a value).
type Resolved<'a> = Option<(&'a [Node], &'a [Symbol], SymbolId)>;

struct FakeEmitResolver {
    /// Owned separately from the `EmitContext` handed to the transforms;
    /// `emit_context()` is never invoked by `ImportElisionTransformer`.
    emit_context: Rc<RefCell<EmitContext>>,
    compiler_options: CompilerOptions,
    /// Shared `Symbol` arena for all bound files (SPEC §5.2 — `SymbolId`s
    /// are program-wide; the test binds every file into one `Vec`).
    symbols: Vec<Symbol>,
    /// Module specifier text → bound external module file.
    modules: FxHashMap<String, BoundFile>,
    /// `aliasSymbolLinks.referenced` — main-file `SymbolId`s marked by
    /// `mark_linked_references_recursively`.
    referenced: RefCell<FxHashSet<SymbolId>>,
}

fn clone_symbols(symbols: &[Symbol]) -> Vec<Symbol> {
    symbols
        .iter()
        .map(|s| Symbol {
            flags: s.flags,
            check_flags: s.check_flags,
            name: s.name.clone(),
            declarations: s.declarations.clone(),
            value_declaration: s.value_declaration,
            members: s.members.clone(),
            exports: s.exports.clone(),
            parent: s.parent,
            export_symbol: s.export_symbol,
        })
        .collect()
}

/// `isConstEnumOrConstEnumOnlyModule`.
fn is_const_enum_or_const_enum_only_module(s: &Symbol) -> bool {
    s.flags.intersects(SymbolFlags::CONST_ENUM)
        || s.flags.intersects(SymbolFlags::CONST_ENUM_ONLY_MODULE)
}

/// `getExportSymbolOfValueSymbolIfExported` (no checker merging).
fn export_symbol_of_value_symbol_if_exported(symbols: &[Symbol], symbol: SymbolId) -> SymbolId {
    let s = &symbols[symbol.index()];
    if s.flags.intersects(SymbolFlags::EXPORT_VALUE) && s.export_symbol.is_some() {
        s.export_symbol.unwrap()
    } else {
        symbol
    }
}

/// `getDeclarationOfAliasSymbol` — last `IsAliasSymbolDeclaration`.
fn declaration_of_alias_symbol(
    symbol: SymbolId,
    nodes: &[Node],
    symbols: &[Symbol],
) -> Option<NodeId> {
    symbols[symbol.index()]
        .declarations
        .iter()
        .rev()
        .copied()
        .find(|&d| ast::is_alias_symbol_declaration(d, nodes))
}

/// `IsInTypeQuery` (checker/utilities.go).
fn is_in_type_query(node: NodeId, nodes: &[Node]) -> bool {
    let mut current = nodes[node].parent;
    while let Some(n) = current {
        match nodes[n].kind {
            Kind::TypeQuery => return true,
            Kind::Identifier | Kind::QualifiedName => current = nodes[n].parent,
            _ => return false,
        }
    }
    false
}

/// `isInvalidComputedPropertyName` (checker.go).
fn is_invalid_computed_property_name(node: NodeId, nodes: &[Node]) -> bool {
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    let Some(grandparent) = nodes[parent].parent else {
        return false;
    };
    (ast::is_type_literal_node(&nodes[grandparent])
        || ast::is_class_like(Some(grandparent), nodes)
        || ast::is_interface_declaration(&nodes[grandparent]))
        && nodes[node].expression().is_some_and(|e| {
            nodes[e].kind == Kind::BinaryExpression
                && nodes[nodes[e].as_binary_expression().operator_token.unwrap()].kind
                    == Kind::InKeyword
        })
        && !ast::is_accessor(&nodes[parent])
}

/// `shouldMarkIdentifierAliasReferenced` (checker.go).
fn should_mark_identifier_alias_referenced(node: NodeId, nodes: &[Node]) -> bool {
    if let Some(parent) = nodes[node].parent {
        // A property access expression LHS? checkPropertyAccessExpression will handle that.
        if ast::is_property_access_expression(&nodes[parent])
            && nodes[parent].expression() == Some(node)
        {
            return false;
        }
        // Next two check for an identifier inside a type only export.
        if ast::is_export_specifier(&nodes[parent]) && nodes[parent].is_type_only() {
            return false;
        }
        if let Some(grandparent) = nodes[parent].parent
            && let Some(great_grandparent) = nodes[grandparent].parent
            && nodes[great_grandparent].kind == Kind::ExportDeclaration
            && nodes[great_grandparent].is_type_only()
        {
            return false;
        }
    }
    true
}

/// `isPartOfImportEqualsModuleReference` (checker.go).
fn is_part_of_import_equals_module_reference(node: NodeId, nodes: &[Node]) -> bool {
    let Some(import_equals) =
        ast::find_ancestor_kind(Some(node), Kind::ImportEqualsDeclaration, nodes)
    else {
        return false;
    };
    let module_reference = nodes[import_equals]
        .as_import_equals_declaration()
        .module_reference;
    let mut current = Some(node);
    while let Some(n) = current {
        if n == import_equals {
            break;
        }
        if Some(n) == module_reference {
            return true;
        }
        current = nodes[n].parent;
    }
    false
}

/// The module specifier of the `ImportDeclaration`/`ExportDeclaration`
/// enclosing an alias declaration (`getExternalModuleName` for those kinds).
fn enclosing_module_specifier(nodes: &[Node], decl: NodeId) -> Option<NodeId> {
    let mut current = nodes[decl].parent;
    while let Some(n) = current {
        match nodes[n].kind {
            Kind::ImportDeclaration | Kind::ExportDeclaration => {
                return nodes[n].module_specifier();
            }
            _ => current = nodes[n].parent,
        }
    }
    None
}

impl FakeEmitResolver {
    /// The shared `Symbol` arena (program-wide `SymbolId`s — `nodes`/`file`
    /// are accepted only to keep call sites readable).
    fn symbols_of<'a>(&'a self, _nodes: &'a [Node], _file: NodeId) -> Option<&'a [Symbol]> {
        Some(self.symbols.as_slice())
    }

    /// `resolveName` — runs the binder `NameResolver` over a scratch copy of
    /// the bound arena (see the module header).
    fn resolve_name(
        &self,
        location: Option<NodeId>,
        name: &str,
        meaning: SymbolFlags,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> Option<SymbolId> {
        let scratch = std::cell::RefCell::new(clone_symbols(symbols));
        let mut resolver = NameResolver {
            host: None,
            for_suggestion: false,
            compiler_options: std::rc::Rc::new(self.compiler_options.clone()),
            globals: std::rc::Rc::new(std::cell::RefCell::new(SymbolTable::default())),
            arguments_symbol: None,
            require_symbol: None,
            get_symbol_of_declaration_hook: None,
            error_hook: None,
            lookup_hook: None,
            symbol_referenced: None,
            set_requires_scope_change_cache: None,
            get_requires_scope_change_cache: None,
            on_property_with_invalid_initializer: None,
            on_failed_to_resolve_symbol: None,
            on_successfully_resolved_symbol: None,
        };
        resolver.resolve(
            location, name, meaning, None,  // nameNotFoundMessage
            true,  // isUse
            false, // excludeGlobals
            nodes, &scratch,
        )
    }

    /// `resolveEntityName` — resolves an identifier/qualified
    /// name/property-access entity to a symbol in `nodes`'s arena without
    /// following aliases (`dontResolveAlias`).
    fn resolve_entity_name(
        &self,
        entity: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> Option<SymbolId> {
        match nodes[entity].kind {
            Kind::Identifier => {
                let text = nodes[entity].text(nodes).into_owned();
                self.resolve_name(Some(entity), &text, SymbolFlags::ALL, nodes, symbols)
            }
            Kind::QualifiedName => {
                let q = nodes[entity].as_qualified_name();
                let left = self.resolve_entity_name(q.left?, nodes, symbols)?;
                let text = nodes[q.right?].text(nodes).into_owned();
                symbols[left.index()].members.get(&text).copied()
            }
            Kind::PropertyAccessExpression => {
                let left = nodes[entity].expression()?;
                let left = self.resolve_entity_name(left, nodes, symbols)?;
                let text = nodes[nodes[entity].name()?].text(nodes).into_owned();
                symbols[left.index()].members.get(&text).copied()
            }
            _ => None,
        }
    }

    /// `resolveExternalModuleName` against the fake's module table — returns
    /// the target file's arena pair and its module symbol.
    fn module_symbol<'a>(
        &'a self,
        specifier: Option<NodeId>,
        nodes: &[Node],
    ) -> Option<(&'a [Node], &'a [Symbol], SymbolId)> {
        let text = nodes[specifier?].text(nodes).into_owned();
        let bound = self.modules.get(&text)?;
        let symbols = self.symbols_of(&bound.nodes, bound.file)?;
        let file_symbol = bound.nodes[bound.file].symbol()?;
        Some((bound.nodes.as_slice(), symbols, file_symbol))
    }

    /// `resolveAlias` — follows `getTargetOfAliasDeclaration` hops until a
    /// non-alias symbol or failure (`None` ≡ `unknownSymbol`). Only the
    /// declaration kinds reachable from this test's inputs are handled.
    fn resolve_alias<'a>(
        &'a self,
        mut nodes: &'a [Node],
        mut symbols: &'a [Symbol],
        mut symbol: SymbolId,
    ) -> Resolved<'a> {
        let mut seen: FxHashSet<(usize, SymbolId)> = FxHashSet::default();
        for _ in 0..128 {
            if !symbols[symbol.index()].flags.intersects(SymbolFlags::ALIAS) {
                return Some((nodes, symbols, symbol));
            }
            if !seen.insert((nodes.as_ptr() as usize, symbol)) {
                // Alias cycle — Go's seenSymbols break.
                return Some((nodes, symbols, symbol));
            }
            let decl = declaration_of_alias_symbol(symbol, nodes, symbols)?;
            let (n2, s2, target) = match nodes[decl].kind {
                Kind::ImportClause
                | Kind::NamespaceImport
                | Kind::NamespaceExport
                | Kind::ImportSpecifier => {
                    let spec = enclosing_module_specifier(nodes, decl)?;
                    let (mnodes, msyms, file_sym) = self.module_symbol(Some(spec), nodes)?;
                    let target = match nodes[decl].kind {
                        Kind::NamespaceImport | Kind::NamespaceExport => file_sym,
                        Kind::ImportClause => msyms[file_sym.index()]
                            .exports
                            .get(INTERNAL_SYMBOL_NAME_DEFAULT)
                            .or_else(|| {
                                msyms[file_sym.index()]
                                    .exports
                                    .get(INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
                            })
                            .copied()?,
                        _ => {
                            let name = nodes[decl].property_name_or_name()?;
                            let text = nodes[name].text(nodes).into_owned();
                            msyms[file_sym.index()].exports.get(&text).copied()?
                        }
                    };
                    (mnodes, msyms, target)
                }
                Kind::ExportSpecifier => {
                    let named_exports = nodes[decl].parent?;
                    let export_decl = nodes[named_exports].parent?;
                    let name = nodes[decl].property_name_or_name()?;
                    let text = nodes[name].text(nodes).into_owned();
                    if nodes[export_decl].module_specifier().is_some() {
                        let (mnodes, msyms, file_sym) =
                            self.module_symbol(nodes[export_decl].module_specifier(), nodes)?;
                        (
                            mnodes,
                            msyms,
                            msyms[file_sym.index()].exports.get(&text).copied()?,
                        )
                    } else {
                        let target = self.resolve_entity_name(name, nodes, symbols)?;
                        (nodes, symbols, target)
                    }
                }
                Kind::ExportAssignment => {
                    let expression = nodes[decl].expression()?;
                    let target = self.resolve_entity_name(expression, nodes, symbols)?;
                    (nodes, symbols, target)
                }
                Kind::ImportEqualsDeclaration => {
                    let module_reference = nodes[decl]
                        .as_import_equals_declaration()
                        .module_reference?;
                    if ast::is_external_module_reference(&nodes[module_reference]) {
                        let expression = nodes[module_reference].expression()?;
                        let (mnodes, msyms, file_sym) =
                            self.module_symbol(Some(expression), nodes)?;
                        (mnodes, msyms, file_sym)
                    } else {
                        let target = self.resolve_entity_name(module_reference, nodes, symbols)?;
                        (nodes, symbols, target)
                    }
                }
                _ => return None,
            };
            nodes = n2;
            symbols = s2;
            symbol = target;
        }
        None
    }

    /// `getTypeOnlyAliasDeclaration` default walk (mirrors
    /// `referenceResolver.isTypeOnlyAliasDeclaration`).
    fn is_type_only_alias(&self, symbol: SymbolId, nodes: &[Node], symbols: &[Symbol]) -> bool {
        let mut node = declaration_of_alias_symbol(symbol, nodes, symbols);
        while let Some(n) = node {
            match nodes[n].kind {
                Kind::ImportEqualsDeclaration | Kind::ExportDeclaration => {
                    return nodes[n].is_type_only();
                }
                Kind::ImportClause | Kind::ImportSpecifier | Kind::ExportSpecifier => {
                    if nodes[n].is_type_only() {
                        return true;
                    }
                    node = nodes[n].parent;
                }
                Kind::NamedImports | Kind::NamedExports => {
                    node = nodes[n].parent;
                }
                _ => break,
            }
        }
        false
    }

    /// `getSymbolFlagsEx`.
    fn symbol_flags_ex(
        &self,
        nodes: &[Node],
        symbols: &[Symbol],
        symbol: SymbolId,
        exclude_type_only_meanings: bool,
        exclude_local_meanings: bool,
    ) -> SymbolFlags {
        let mut flags = if exclude_local_meanings {
            SymbolFlags::NONE
        } else {
            symbols[symbol.index()].flags
        };
        let mut seen: FxHashSet<(usize, SymbolId)> = FxHashSet::default();
        let (mut nodes, mut symbols, mut symbol) = (nodes, symbols, symbol);
        while symbols[symbol.index()].flags.intersects(SymbolFlags::ALIAS) {
            if exclude_type_only_meanings && self.is_type_only_alias(symbol, nodes, symbols) {
                break;
            }
            let Some((tn, ts, target)) = self.resolve_alias(nodes, symbols, symbol) else {
                return SymbolFlags::ALL; // unknownSymbol
            };
            let target = export_symbol_of_value_symbol_if_exported(ts, target);
            if ts[target.index()].flags.intersects(SymbolFlags::ALIAS) {
                let symbol_key = (symbols.as_ptr() as usize, symbol);
                let target_key = (ts.as_ptr() as usize, target);
                if target_key == symbol_key || seen.contains(&target_key) {
                    break;
                }
                if seen.is_empty() {
                    seen.insert(symbol_key);
                }
                seen.insert(target_key);
            }
            flags |= ts[target.index()].flags;
            nodes = tn;
            symbols = ts;
            symbol = target;
        }
        flags
    }

    /// `isAliasResolvedToValue`.
    fn is_alias_resolved_to_value(
        &self,
        nodes: &[Node],
        symbols: &[Symbol],
        symbol: Option<SymbolId>,
        exclude_type_only_values: bool,
    ) -> bool {
        let Some(symbol) = symbol else { return false };
        // Go first ensures the container's `export=` symbol merge ran via
        // `resolveExternalModuleSymbol`; with no checker merging there is
        // nothing to merge here.
        match self.resolve_alias(nodes, symbols, symbol) {
            None => !exclude_type_only_values || !self.is_type_only_alias(symbol, nodes, symbols),
            Some((_, ts, target)) => {
                let target = export_symbol_of_value_symbol_if_exported(ts, target);
                self.symbol_flags_ex(nodes, symbols, symbol, exclude_type_only_values, true)
                    .intersects(SymbolFlags::VALUE)
                    // ShouldPreserveConstEnums() is off in this table.
                    && !is_const_enum_or_const_enum_only_module(&ts[target.index()])
            }
        }
    }

    // -- markLinkedReferences -------------------------------------------------

    /// `markIdentifierAliasReferenced`.
    fn mark_identifier_alias_referenced(
        &self,
        location: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) {
        if ast::is_this_in_type_query(location, nodes) {
            return;
        }
        let text = nodes[location].text(nodes).into_owned();
        if let Some(symbol) =
            self.resolve_name(Some(location), &text, SymbolFlags::ALL, nodes, symbols)
        {
            // argumentsSymbol/unknownSymbol cannot come out of this fake's
            // resolver, so a successful result is always markable.
            self.mark_alias_referenced(symbol, location, nodes, symbols);
        }
    }

    /// `markAliasReferenced` (GetIsolatedModules()/ShouldPreserveConstEnums()
    /// are off in this table, so the const-enum exceptions collapse to
    /// "not a const enum target").
    fn mark_alias_referenced(
        &self,
        symbol: SymbolId,
        location: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) {
        if is_in_type_query(location, nodes) {
            return;
        }
        if !ast::is_non_local_alias(Some(&symbols[symbol.index()]), SymbolFlags::VALUE) {
            return;
        }
        if !self
            .symbol_flags_ex(nodes, symbols, symbol, true, false)
            .intersects(SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE)
        {
            return;
        }
        let is_const_enum_target =
            self.resolve_alias(nodes, symbols, symbol)
                .is_some_and(|(_, ts, t)| {
                    is_const_enum_or_const_enum_only_module(
                        &ts[export_symbol_of_value_symbol_if_exported(ts, t).index()],
                    )
                });
        if !is_const_enum_target {
            self.mark_alias_symbol_as_referenced(symbol, nodes, symbols);
        }
    }

    /// `markAliasSymbolAsReferenced`.
    fn mark_alias_symbol_as_referenced(
        &self,
        symbol: SymbolId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) {
        if !self.referenced.borrow_mut().insert(symbol) {
            return;
        }
        // We defer checking of the reference of an `import =` until the
        // import itself is referenced, so that a chain of imports can be
        // elided if ultimately the final input is only used in a type
        // position.
        if let Some(decl) = declaration_of_alias_symbol(symbol, nodes, symbols)
            && nodes[decl].kind == Kind::ImportEqualsDeclaration
        {
            let module_reference = nodes[decl].as_import_equals_declaration().module_reference;
            if let Some(module_reference) = module_reference
                && !ast::is_external_module_reference(&nodes[module_reference])
            {
                let resolves_to_value = self
                    .resolve_alias(nodes, symbols, symbol)
                    .is_some_and(|(_, ts, t)| ts[t.index()].flags.intersects(SymbolFlags::VALUE));
                if resolves_to_value {
                    let left = ast::get_first_identifier(module_reference, nodes);
                    self.mark_identifier_alias_referenced(left, nodes, symbols);
                }
            }
        }
    }

    /// `markExportAsReferenced`.
    fn mark_export_as_referenced(&self, node: NodeId, nodes: &[Node], symbols: &[Symbol]) {
        let Some(symbol) = nodes[node].symbol() else {
            return;
        };
        let mark_alias = match self.resolve_alias(nodes, symbols, symbol) {
            None => true, // unknownSymbol
            Some((_, ts, target)) => {
                self.symbol_flags_ex(nodes, symbols, symbol, true, false)
                    .intersects(SymbolFlags::VALUE)
                    && !is_const_enum_or_const_enum_only_module(&ts[target.index()])
            }
        };
        if mark_alias {
            self.mark_alias_symbol_as_referenced(symbol, nodes, symbols);
        }
    }

    /// `markPropertyAliasReferenced` (the const-enum property lookup arm is
    /// omitted — no const enums appear in this table).
    fn mark_property_alias_referenced(&self, location: NodeId, nodes: &[Node], symbols: &[Symbol]) {
        if is_part_of_import_equals_module_reference(location, nodes) {
            return;
        }
        let left = if ast::is_property_access_expression(&nodes[location]) {
            nodes[location].expression()
        } else {
            nodes[location].as_qualified_name().left
        };
        let Some(left) = left else { return };
        if nodes[left].kind == Kind::ThisKeyword || nodes[left].kind != Kind::Identifier {
            return;
        }
        let text = nodes[left].text(nodes).into_owned();
        if let Some(parent_symbol) =
            self.resolve_name(Some(left), &text, SymbolFlags::ALL, nodes, symbols)
        {
            self.mark_alias_referenced(parent_symbol, location, nodes, symbols);
        }
    }

    /// `markExportAssignmentAliasReferenced`.
    fn mark_export_assignment_alias_referenced(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) {
        let Some(id) = nodes[node].expression() else {
            return;
        };
        if nodes[id].kind == Kind::Identifier
            && let Some(symbol) = self.resolve_entity_name(id, nodes, symbols)
        {
            let symbol = export_symbol_of_value_symbol_if_exported(symbols, symbol);
            self.mark_alias_referenced(symbol, id, nodes, symbols);
        }
    }

    /// `markImportEqualsAliasReferenced` (only exported import-equals
    /// declarations reach this — the file walk skips the rest).
    fn mark_import_equals_alias_referenced(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) {
        if ast::has_syntactic_modifier(&nodes[node], ModifierFlags::EXPORT) {
            self.mark_export_as_referenced(node, nodes, symbols);
        }
    }

    /// `checkExternalImportOrExportDeclaration`, reduced to the parts
    /// reachable here: a string-literal module reference directly under a
    /// `SourceFile`.
    fn check_external_import_or_export(&self, node: NodeId, nodes: &[Node]) -> bool {
        let Some(module_name) = ast::get_external_module_name(&nodes[node], nodes) else {
            return false;
        };
        if nodes[module_name].kind != Kind::StringLiteral {
            return false;
        }
        nodes[node]
            .parent
            .is_some_and(|p| nodes[p].kind == Kind::SourceFile)
    }

    /// `markExportSpecifierAliasReferenced`.
    fn mark_export_specifier_alias_referenced(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) {
        let export_decl = nodes[node].parent.and_then(|p| nodes[p].parent);
        let Some(export_decl) = export_decl else {
            return;
        };
        if nodes[export_decl].module_specifier().is_some()
            || nodes[node].is_type_only()
            || nodes[export_decl].is_type_only()
        {
            return;
        }
        let Some(exported_name) = nodes[node].property_name_or_name() else {
            return;
        };
        if nodes[exported_name].kind == Kind::StringLiteral {
            return; // Skip for invalid syntax like this: export { "x" }
        }
        let text = nodes[exported_name].text(nodes).into_owned();
        let symbol = self.resolve_name(
            Some(exported_name),
            &text,
            SymbolFlags::VALUE | SymbolFlags::TYPE | SymbolFlags::NAMESPACE | SymbolFlags::ALIAS,
            nodes,
            symbols,
        );
        // undefinedSymbol/globalThisSymbol cannot come out of this fake's
        // resolver — only the global-source-file check remains.
        let is_global = symbol.is_some_and(|s| {
            symbols[s.index()]
                .declarations
                .first()
                .and_then(|&d| ast::get_declaration_container(d, nodes))
                .is_some_and(|dc| ast::is_global_source_file(&nodes[dc], nodes))
        });
        if symbol.is_some() && is_global {
            return; // non-local symbol
        }
        let mut target = symbol;
        if let Some(t) = target
            && symbols[t.index()].flags.intersects(SymbolFlags::ALIAS)
        {
            target = self.resolve_alias(nodes, symbols, t).map(|(_, _, t)| t);
        }
        let target_is_value = match target {
            None => true, // unresolved names keep the export
            Some(t) => self
                .symbol_flags_ex(nodes, symbols, t, false, false)
                .intersects(SymbolFlags::VALUE),
        };
        if target_is_value {
            self.mark_export_as_referenced(node, nodes, symbols);
            self.mark_identifier_alias_referenced(exported_name, nodes, symbols);
        }
    }

    /// `markLinkedReferences` with `ReferenceHintUnspecified` (the
    /// `EmitDecoratorMetadata`-gated decorator arm and the JSX arm are
    /// omitted — no case in this table sets them).
    fn mark_linked_references(&self, node: NodeId, nodes: &[Node], symbols: &[Symbol]) {
        if nodes[node].flags.intersects(NodeFlags::AMBIENT)
            && nodes[node].kind != Kind::PropertySignature
            && nodes[node].kind != Kind::PropertyDeclaration
        {
            return;
        }
        match nodes[node].kind {
            Kind::Identifier => {
                // Shorthand-property-with-object-assignment-initializer edge
                // case (`{ s = 5 }` in a non-assignment context).
                if let Some(parent) = nodes[node].parent
                    && ast::is_shorthand_property_assignment(&nodes[parent])
                    && nodes[parent].name() == Some(node)
                    && nodes[parent]
                        .as_shorthand_property_assignment()
                        .object_assignment_initializer
                        .is_some()
                    && !nodes[parent]
                        .parent
                        .is_some_and(|gp| ast::is_assignment_target(gp, nodes))
                {
                    return;
                }
                let res = ast::find_many_ancestors(
                    Some(node),
                    nodes,
                    &mut [
                        &mut |n: &Node| ast::is_meta_property(n),
                        &mut |n: &Node| ast::is_decorator(n),
                        &mut |n: &Node| {
                            matches!(n.kind, Kind::ForInStatement | Kind::ForOfStatement)
                        },
                        &mut |n: &Node| ast::is_computed_property_name(n),
                        &mut |n: &Node| ast::is_heritage_clause(n),
                    ],
                );
                let [
                    meta_property,
                    decorator,
                    for_node,
                    computed_name,
                    heritage_clause,
                ] = <[Option<NodeId>; 5]>::try_from(res).ok().unwrap();
                if meta_property.is_some() {
                    return;
                }
                if let Some(decorator) = decorator {
                    let decorated = nodes[decorator].parent;
                    if let Some(decorated) = decorated
                        && !ast::node_can_be_decorated(
                            false, // legacyDecorators is off in this table
                            decorated,
                            nodes[decorated].parent,
                            nodes[decorated].parent.and_then(|p| nodes[p].parent),
                            nodes,
                        )
                    {
                        return;
                    }
                }
                if let Some(for_node) = for_node {
                    let data = nodes[for_node].as_for_in_or_of_statement();
                    if data.initializer.is_some_and(|i| {
                        ast::is_variable_declaration_list(&nodes[i])
                            && nodes[i]
                                .as_variable_declaration_list()
                                .declarations
                                .as_ref()
                                .is_some_and(|d| d.nodes.is_empty())
                    }) && data.expression.is_some_and(|e| {
                        e == node || ast::is_node_descendant_of(Some(node), Some(e), nodes)
                    }) {
                        return;
                    }
                }
                if let Some(computed_name) = computed_name
                    && is_invalid_computed_property_name(computed_name, nodes)
                {
                    return;
                }
                if let Some(heritage) = heritage_clause {
                    let parent = nodes[heritage].parent;
                    if parent.is_some_and(|p| ast::is_interface_declaration(&nodes[p])) {
                        return;
                    }
                    if ast::is_class_like(parent, nodes)
                        && nodes[heritage].as_heritage_clause().token == Kind::ExtendsKeyword
                        && let Some(first) =
                            ast::get_class_extends_heritage_element(&nodes[parent.unwrap()], nodes)
                        && node != first
                        && !ast::is_node_descendant_of(Some(node), Some(first), nodes)
                    {
                        return;
                    }
                }
                let is_expression = ast::is_expression_node(node, nodes)
                    || nodes[node]
                        .parent
                        .is_some_and(|p| ast::is_shorthand_property_assignment(&nodes[p]));
                if is_expression && should_mark_identifier_alias_referenced(node, nodes) {
                    if let Some(parent) = nodes[node].parent
                        && ast::is_property_access_or_qualified_name(&nodes[parent])
                    {
                        let left = if ast::is_property_access_expression(&nodes[parent]) {
                            nodes[parent].expression()
                        } else {
                            nodes[parent].as_qualified_name().left
                        };
                        if left != Some(node) {
                            return; // Only mark the LHS (the RHS is a property lookup)
                        }
                    }
                    self.mark_identifier_alias_referenced(node, nodes, symbols);
                }
            }
            Kind::PropertyAccessExpression | Kind::QualifiedName => {
                let mut top = node;
                while ast::is_property_access_or_qualified_name(&nodes[top]) {
                    if ast::is_part_of_type_node(top, nodes) {
                        return;
                    }
                    match nodes[top].parent {
                        Some(p) => top = p,
                        None => break,
                    }
                }
                self.mark_property_alias_referenced(node, nodes, symbols);
            }
            Kind::ExportAssignment => {
                self.mark_export_assignment_alias_referenced(node, nodes, symbols);
            }
            Kind::ImportEqualsDeclaration => {
                let internal = nodes[node]
                    .as_import_equals_declaration()
                    .module_reference
                    .is_some_and(|m| !ast::is_external_module_reference(&nodes[m]));
                if internal || self.check_external_import_or_export(node, nodes) {
                    self.mark_import_equals_alias_referenced(node, nodes, symbols);
                }
            }
            Kind::ExportSpecifier => {
                self.mark_export_specifier_alias_referenced(node, nodes, symbols);
            }
            _ => {}
        }
    }

    /// The `MarkLinkedReferencesRecursively` visitor body.
    fn mark_visit(&self, node: NodeId, nodes: &[Node], symbols: &[Symbol]) {
        match nodes[node].kind {
            // These are deferred and marked in a chain when referenced.
            Kind::ImportEqualsDeclaration
                if !ast::has_syntactic_modifier(&nodes[node], ModifierFlags::EXPORT) =>
            {
                return;
            }
            // These are ultimately what get marked by calls on other nodes —
            // skip them.
            Kind::ImportDeclaration => return,
            _ => {}
        }
        self.mark_linked_references(node, nodes, symbols);
        nodes[node].for_each_child(nodes, &mut |child| {
            self.mark_visit(child, nodes, symbols);
            false
        });
    }
}

impl ReferenceResolver for FakeEmitResolver {
    fn get_referenced_export_container(
        &mut self,
        _node: NodeId,
        _prefix_locals: bool,
        _nodes: &[Node],
        _symbols: &std::cell::RefCell<Vec<Symbol>>,
    ) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_referenced_import_declaration(
        &mut self,
        _node: NodeId,
        _nodes: &[Node],
        _symbols: &std::cell::RefCell<Vec<Symbol>>,
    ) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_referenced_value_declaration(
        &mut self,
        _node: NodeId,
        _nodes: &[Node],
        _symbols: &std::cell::RefCell<Vec<Symbol>>,
    ) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_referenced_value_declarations(
        &mut self,
        _node: NodeId,
        _nodes: &[Node],
        _symbols: &std::cell::RefCell<Vec<Symbol>>,
    ) -> Vec<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_element_access_expression_name(&mut self, _expression: Option<NodeId>) -> String {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_referenced_member_value_declaration(
        &mut self,
        _node: NodeId,
        _nodes: &[Node],
        _symbols: &std::cell::RefCell<Vec<Symbol>>,
    ) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }
}

impl EmitResolver for FakeEmitResolver {
    fn emit_context(&self) -> &Rc<RefCell<EmitContext>> {
        &self.emit_context
    }

    /// `IsReferencedAliasDeclaration`.
    fn is_referenced_alias_declaration(&self, node: NodeId, nodes: &[Node]) -> bool {
        // `canCollectSymbolAliasAccessibilityData` is always true here.
        if !ast::is_parse_tree_node(&nodes[node]) {
            return true;
        }
        if !ast::is_alias_symbol_declaration(node, nodes) {
            return false;
        }
        let Some(symbol) = nodes[node].symbol() else {
            return false;
        };
        if self.referenced.borrow().contains(&symbol) {
            return true;
        }
        if nodes[node]
            .modifier_flags()
            .intersects(ModifierFlags::EXPORT)
            && let Some(file) = ast::get_source_file_of_node(Some(node), nodes)
            && let Some(symbols) = self.symbols_of(nodes, file)
            && let Some((_, ts, target)) = self.resolve_alias(nodes, symbols, symbol)
        {
            let target = export_symbol_of_value_symbol_if_exported(ts, target);
            return ts[target.index()].flags.intersects(SymbolFlags::VALUE)
                && !is_const_enum_or_const_enum_only_module(&ts[target.index()]);
        }
        false
    }

    /// `IsValueAliasDeclaration` / `isValueAliasDeclarationWorker`.
    fn is_value_alias_declaration(&self, node: NodeId, nodes: &[Node]) -> bool {
        if !ast::is_parse_tree_node(&nodes[node]) {
            return true;
        }
        let Some(file) = ast::get_source_file_of_node(Some(node), nodes) else {
            return false;
        };
        let Some(symbols) = self.symbols_of(nodes, file) else {
            return false;
        };
        match nodes[node].kind {
            Kind::ImportEqualsDeclaration => {
                self.is_alias_resolved_to_value(nodes, symbols, nodes[node].symbol(), false)
            }
            Kind::ImportClause
            | Kind::NamespaceImport
            | Kind::ImportSpecifier
            | Kind::ExportSpecifier => nodes[node]
                .symbol()
                .is_some_and(|s| self.is_alias_resolved_to_value(nodes, symbols, Some(s), true)),
            Kind::ExportDeclaration => {
                let Some(clause) = nodes[node].as_export_declaration().export_clause else {
                    return false;
                };
                if ast::is_namespace_export(&nodes[clause]) {
                    return true;
                }
                nodes[clause]
                    .as_named_exports()
                    .elements
                    .as_ref()
                    .is_some_and(|e| {
                        e.nodes
                            .iter()
                            .any(|&s| self.is_value_alias_declaration(s, nodes))
                    })
            }
            Kind::ExportAssignment => {
                if let Some(expression) = nodes[node].expression()
                    && nodes[expression].kind == Kind::Identifier
                {
                    return self.is_alias_resolved_to_value(
                        nodes,
                        symbols,
                        nodes[node].symbol(),
                        true,
                    );
                }
                true
            }
            _ => false,
        }
    }

    /// `IsTopLevelValueImportEqualsWithEntityName`.
    fn is_top_level_value_import_equals_with_entity_name(
        &self,
        node: NodeId,
        nodes: &[Node],
    ) -> bool {
        if !ast::is_parse_tree_node(&nodes[node])
            || nodes[node].kind != Kind::ImportEqualsDeclaration
            || nodes[node]
                .parent
                .is_none_or(|p| nodes[p].kind != Kind::SourceFile)
        {
            return false;
        }
        let module_reference = nodes[node].as_import_equals_declaration().module_reference;
        if ast::node_is_missing(module_reference, nodes)
            || module_reference.is_some_and(|m| nodes[m].kind == Kind::ExternalModuleReference)
        {
            return false;
        }
        let Some(file) = ast::get_source_file_of_node(Some(node), nodes) else {
            return false;
        };
        let Some(symbols) = self.symbols_of(nodes, file) else {
            return false;
        };
        self.is_alias_resolved_to_value(nodes, symbols, nodes[node].symbol(), false)
    }

    /// `MarkLinkedReferencesRecursively`.
    fn mark_linked_references_recursively(&mut self, file: NodeId, nodes: &mut Vec<Node>) {
        if !ast::is_parse_tree_node(&nodes[file]) {
            return;
        }
        if let Some(symbols) = self.symbols_of(nodes, file) {
            self.mark_visit(file, nodes, symbols);
        }
    }

    // -- the remaining EmitResolver members are unreachable from this
    //    transform ------------------------------------------------------------

    fn get_external_module_file_from_declaration(
        &self,
        _node: NodeId,
        _nodes: &[Node],
    ) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_effective_declaration_flags(
        &self,
        _node: NodeId,
        _flags: ModifierFlags,
        _nodes: &[Node],
    ) -> ModifierFlags {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_type_reference_serialization_kind(
        &self,
        _name: NodeId,
        _serial_scope: Option<NodeId>,
        _nodes: &[Node],
    ) -> TypeReferenceSerializationKind {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_constant_value(&self, _node: NodeId, _nodes: &[Node]) -> Option<Value> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_jsx_factory_entity(&self, _location: NodeId, _nodes: &[Node]) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_jsx_fragment_factory_entity(
        &self,
        _location: NodeId,
        _nodes: &[Node],
    ) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn entity_name_texts(&self, _e: NodeId, _nodes: &[Node]) -> Vec<String> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn set_referenced_import_declaration(
        &mut self,
        _node: NodeId,
        _ref_: Option<NodeId>,
        _nodes: &[Node],
    ) {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn precalculate_declaration_emit_visibility(&mut self, _file: NodeId, _nodes: &[Node]) {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_symbol_accessible(
        &self,
        _symbol: SymbolId,
        _enclosing_declaration: Option<NodeId>,
        _meaning: SymbolFlags,
        _should_compute_alias_to_mark_visible: bool,
        _nodes: &[Node],
        _symbols: &[Symbol],
    ) -> SymbolAccessibilityResult {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_entity_name_visible(
        &self,
        _entity_name: NodeId,
        _enclosing_declaration: Option<NodeId>,
        _nodes: &[Node],
    ) -> SymbolAccessibilityResult {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_expando_function_declaration(&self, _node: NodeId, _nodes: &[Node]) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_expando_function_declaration_unsafe(&self, _node: NodeId, _nodes: &[Node]) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_literal_const_declaration(&self, _node: NodeId, _nodes: &[Node]) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn requires_adding_implicit_undefined(
        &self,
        _node: NodeId,
        _symbol: Option<SymbolId>,
        _enclosing_declaration: Option<NodeId>,
        _nodes: &[Node],
        _symbols: &[Symbol],
    ) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_declaration_visible(&self, _node: NodeId, _nodes: &[Node]) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_name_resolvable(&self, _location: Option<NodeId>, _name: &str, _nodes: &[Node]) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_import_required_by_augmentation(&self, _decl: NodeId, _nodes: &[Node]) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_definitely_reference_to_global_symbol_object(
        &self,
        _node: NodeId,
        _nodes: &[Node],
    ) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_implementation_of_overload(&self, _node: NodeId, _nodes: &[Node]) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_enum_member_value(&self, _node: NodeId, _nodes: &[Node]) -> tsc_evaluator::Result {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_late_bound(&self, _node: NodeId, _nodes: &[Node]) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_optional_parameter(&self, _node: NodeId, _nodes: &[Node]) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn is_this_property_assignment_declaration_redundant(
        &self,
        _node: NodeId,
        _nodes: &[Node],
    ) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_properties_of_container_function(
        &self,
        _node: NodeId,
        _nodes: &[Node],
        _symbols: &[Symbol],
    ) -> Vec<SymbolId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn requires_adding_implicit_undefined_unsafe(
        &self,
        _node: NodeId,
        _symbol: Option<SymbolId>,
        _enclosing_declaration: Option<NodeId>,
        _nodes: &[Node],
        _symbols: &[Symbol],
    ) -> bool {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn get_referenced_value_declaration_unsafe(
        &self,
        _node: NodeId,
        _nodes: &[Node],
    ) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn create_type_of_declaration(
        &self,
        _declaration: NodeId,
        _enclosing_declaration: Option<NodeId>,
        _flags: Flags,
        _internal_flags: InternalFlags,
        _tracker: &mut dyn SymbolTracker,
        _nodes: &mut Vec<Node>,
    ) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn create_return_type_of_signature_declaration(
        &self,
        _signature_declaration: NodeId,
        _enclosing_declaration: Option<NodeId>,
        _flags: Flags,
        _internal_flags: InternalFlags,
        _tracker: &mut dyn SymbolTracker,
        _nodes: &mut Vec<Node>,
    ) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn create_type_parameters_of_signature_declaration(
        &self,
        _signature_declaration: NodeId,
        _enclosing_declaration: Option<NodeId>,
        _flags: Flags,
        _internal_flags: InternalFlags,
        _tracker: &mut dyn SymbolTracker,
        _nodes: &mut Vec<Node>,
    ) -> Vec<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn create_literal_const_value(
        &self,
        _node: NodeId,
        _tracker: &mut dyn SymbolTracker,
        _nodes: &mut Vec<Node>,
    ) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn create_type_of_expression(
        &self,
        _expression: NodeId,
        _enclosing_declaration: Option<NodeId>,
        _flags: Flags,
        _internal_flags: InternalFlags,
        _tracker: &mut dyn SymbolTracker,
        _nodes: &mut Vec<Node>,
    ) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn create_late_bound_index_signatures(
        &self,
        _container: NodeId,
        _enclosing_declaration: Option<NodeId>,
        _flags: Flags,
        _internal_flags: InternalFlags,
        _tracker: &mut dyn SymbolTracker,
        _nodes: &mut Vec<Node>,
    ) -> Vec<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }

    fn try_js_type_node_to_type_node(
        &self,
        _type_node: NodeId,
        _enclosing_declaration: Option<NodeId>,
        _flags: Flags,
        _internal_flags: InternalFlags,
        _tracker: &mut dyn SymbolTracker,
        _nodes: &mut Vec<Node>,
    ) -> Option<NodeId> {
        unimplemented!("unused by ImportElisionTransformer")
    }
}

// ---------------------------------------------------------------------------
// Test driver
// ---------------------------------------------------------------------------

fn check_emit(
    title: &str,
    input: &str,
    expected: &str,
    other: &str,
    jsx: bool,
) -> Result<(), String> {
    let (file, mut nodes) = parsetestutil::parse_typescript(input, jsx);
    parsetestutil::check_diagnostics(&nodes, file).map_err(|e| format!("{title}: {e}"))?;
    let mut symbols = Vec::new();
    bind_source_file(&mut nodes, file, &mut symbols);

    let mut modules = FxHashMap::default();
    if !other.is_empty() {
        let (other_file, mut other_nodes) = parsetestutil::parse_typescript(other, jsx);
        parsetestutil::check_diagnostics(&other_nodes, other_file)
            .map_err(|e| format!("{title} (other): {e}"))?;
        bind_source_file(&mut other_nodes, other_file, &mut symbols);
        modules.insert(
            "other".to_string(),
            BoundFile {
                nodes: other_nodes,
                file: other_file,
            },
        );
    }

    let compiler_options = CompilerOptions::default();
    let emit_context = Rc::new(RefCell::new(EmitContext::new()));
    let resolver: Rc<RefCell<FakeEmitResolver>> = Rc::new(RefCell::new(FakeEmitResolver {
        emit_context: Rc::new(RefCell::new(EmitContext::new())),
        compiler_options: CompilerOptions::default(),
        symbols,
        modules,
        referenced: RefCell::new(FxHashSet::default()),
    }));
    let opts = TransformOptions {
        compiler_options: Some(&compiler_options),
        context: Some(emit_context.clone()),
        resolver: Some(resolver.clone()),
        emit_resolver: Some(resolver),
        ..Default::default()
    };

    let file = new_type_eraser_transformer(&opts)
        .expect("NewTypeEraserTransformer returned nil")
        .transform_source_file(&mut nodes, file)
        .expect("transformed SourceFile");
    let file = new_import_elision_transformer(&opts)
        .expect("NewImportElisionTransformer returned nil")
        .transform_source_file(&mut nodes, file)
        .expect("transformed SourceFile");

    let mut emit_context = emit_context.borrow_mut();
    let mut printer = Printer::new(
        PrinterOptions {
            new_line: NewLineKind::LF,
            ..Default::default()
        },
        PrintHandlers::default(),
        &mut emit_context,
        &mut nodes,
        &[],
    );
    let text = printer.emit_source_file(file);
    let actual = text.strip_suffix('\n').unwrap_or(&text);
    if actual != expected {
        return Err(format!(
            "{title}: input {input:?}\n  expected: {expected:?}\n  actual:   {actual:?}"
        ));
    }
    Ok(())
}

static DATA: &[(&str, &str, &str, &str, bool)] = &[
    (
        "ImportEquals#1",
        "import x = require(\"other\"); x;",
        "import x = require(\"other\");\nx;",
        "",
        false,
    ),
    (
        "ImportEquals#2",
        "import x = require(\"other\");",
        "",
        "",
        false,
    ),
    (
        "ImportDeclaration#1",
        "import \"m\";",
        "import \"m\";",
        "",
        false,
    ),
    (
        "ImportDeclaration#2",
        "import * as x from \"other\"; x;",
        "import * as x from \"other\";\nx;",
        "",
        false,
    ),
    (
        "ImportDeclaration#3",
        "import x from \"other\"; x;",
        "import x from \"other\";\nx;",
        "",
        false,
    ),
    (
        "ImportDeclaration#4",
        "import { x } from \"other\"; x;",
        "import { x } from \"other\";\nx;",
        "",
        false,
    ),
    (
        "ImportDeclaration#5",
        "import * as x from \"other\";",
        "",
        "",
        false,
    ),
    (
        "ImportDeclaration#6",
        "import x from \"other\";",
        "",
        "",
        false,
    ),
    (
        "ImportDeclaration#7",
        "import { x } from \"other\";",
        "",
        "",
        false,
    ),
    (
        "ExportDeclaration#1",
        "export * from \"other\";",
        "export * from \"other\";",
        "export let x;",
        false,
    ),
    (
        "ExportDeclaration#2",
        "export * as x from \"other\";",
        "export * as x from \"other\";",
        "export let x;",
        false,
    ),
    (
        "ExportDeclaration#3",
        "export * from \"other\";",
        "export * from \"other\";",
        "export let x;",
        false,
    ),
    (
        "ExportDeclaration#4",
        "export * as x from \"other\";",
        "export * as x from \"other\";",
        "export let x;",
        false,
    ),
    (
        "ExportDeclaration#5",
        "export { x } from \"other\";",
        "export { x } from \"other\";",
        "export let x;",
        false,
    ),
    (
        "ExportDeclaration#6",
        "export { x } from \"other\";",
        "",
        "export type x = any;",
        false,
    ),
    (
        "ExportDeclaration#7",
        "export { x }; let x;",
        "export { x };\nlet x;",
        "",
        false,
    ),
    (
        "ExportDeclaration#8",
        "export { x }; type x = any;",
        "",
        "",
        false,
    ),
    (
        "ExportDeclaration#9",
        "import { x } from \"other\"; export { x };",
        "",
        "export type x = any;",
        false,
    ),
    (
        "ExportAssignment#1",
        "let x; export default x;",
        "let x;\nexport default x;",
        "",
        false,
    ),
    (
        "ExportAssignment#2",
        "type x = any; export default x;",
        "",
        "",
        false,
    ),
];

#[test]
fn tstransforms_import_elision() {
    let mut failures = Vec::new();
    for (title, input, expected, other, jsx) in DATA {
        if let Err(e) = check_emit(title, input, expected, other, *jsx) {
            failures.push(e);
        }
    }
    if !failures.is_empty() {
        panic!("{} emit failures:\n{}", failures.len(), failures.join("\n"));
    }
}
