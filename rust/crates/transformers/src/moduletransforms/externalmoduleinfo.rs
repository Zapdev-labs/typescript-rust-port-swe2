// Ported from tsc/internal/transformers/moduletransforms/externalmoduleinfo.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `collectExternalModuleInfo` — a single pass over a source file's top-level
// statements that gathers the imports, exports, and helper needs the
// CommonJS transform consumes, plus the `tslib` helpers-import synthesis
// shared by the CJS and ESM transforms.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use tsc_ast::{self as ast, Node, NodeId, Symbol};
use tsc_binder::referenceresolver::ReferenceResolver;
use tsc_collections::{MultiMap, OrderedSet, Set};
use tsc_core::options_generated::{CompilerOptions, ModuleKind};
use tsc_printer::{EmitContext, EmitFlags, EmitHelper};

/// `type externalModuleInfo struct`
#[derive(Default)]
pub struct ExternalModuleInfo {
    /// imports and reexports of other external modules
    pub external_imports: Vec<NodeId>, /* ImportDeclaration | ImportEqualsDeclaration | ExportDeclaration */
    /// Maps local names to their associated export specifiers (excludes reexports)
    pub export_specifiers: MultiMap<String, NodeId>,
    /// Maps local declarations to their associated export aliases
    pub exported_bindings: MultiMap<NodeId, NodeId>,
    /// all exported names in the module, both local and re-exported,
    /// excluding the names of locally exported function declarations
    pub exported_names: Vec<NodeId>,
    /// all of the top-level exported function declarations
    pub exported_functions: OrderedSet<NodeId>,
    /// an `export=`/`module.exports=` declaration if one was present
    pub export_equals: Option<NodeId>,
    /// whether this module contains `export *`
    pub has_export_stars_to_export_values: bool,
}

/// `type externalModuleInfoCollector struct`
///
/// PORT: `resolver` and `symbols` are `Option`s mirroring `TransformOptions`;
/// Go dereferences the nil `ReferenceResolver` interface when the collector
/// actually consults it, so the `expect`s below fire at the same points a Go
/// nil-pointer panic would.
struct ExternalModuleInfoCollector<'a, 'b> {
    source_file: NodeId,
    compiler_options: &'a CompilerOptions,
    emit_context: &'b Rc<RefCell<EmitContext>>,
    resolver: Option<&'b Rc<RefCell<dyn ReferenceResolver + 'a>>>,
    symbols: Option<&'b RefCell<Vec<Symbol>>>,
    unique_exports: Set<String>,
    has_export_default: bool,
    output: ExternalModuleInfo,
}

/// `collectExternalModuleInfo(sourceFile, compilerOptions, emitContext, resolver)`
///
/// PORT: `symbols` is the binder-owned symbol arena the `ReferenceResolver`
/// methods index into — the Rust trait surfaces `&mut Vec<Symbol>` where Go
/// reads through `*ast.Symbol` pointers.
pub fn collect_external_module_info<'a>(
    source_file: NodeId,
    compiler_options: &'a CompilerOptions,
    emit_context: &Rc<RefCell<EmitContext>>,
    resolver: Option<&Rc<RefCell<dyn ReferenceResolver + 'a>>>,
    symbols: Option<&RefCell<Vec<Symbol>>>,
    nodes: &mut Vec<Node>,
) -> ExternalModuleInfo {
    let mut c = ExternalModuleInfoCollector {
        source_file,
        compiler_options,
        emit_context,
        resolver,
        symbols,
        unique_exports: Set::default(),
        has_export_default: false,
        output: ExternalModuleInfo::default(),
    };
    c.collect(nodes);
    c.output
}

impl<'a, 'b> ExternalModuleInfoCollector<'a, 'b> {
    fn resolver(&self) -> std::cell::RefMut<'_, dyn ReferenceResolver + 'a> {
        self.resolver
            .expect("opts.Resolver is required to collect external module info")
            .borrow_mut()
    }

    fn symbols(&self) -> std::cell::RefMut<'_, Vec<Symbol>> {
        self.symbols
            .expect("opts.symbols (the binder symbol arena) is required alongside opts.Resolver")
            .borrow_mut()
    }

    fn with_symbols<R>(
        &self,
        f: impl FnOnce(&std::cell::RefCell<Vec<Symbol>>) -> R,
    ) -> R {
        f(self.symbols
            .expect("opts.symbols (the binder symbol arena) is required alongside opts.Resolver"))
    }

    fn most_original(&self, node: NodeId) -> NodeId {
        self.emit_context
            .borrow()
            .most_original(Some(node))
            .expect("MostOriginal returned nil for a non-nil node")
    }

    /// `(c *externalModuleInfoCollector) collect`
    fn collect(&mut self, nodes: &mut Vec<Node>) {
        let mut has_import_star = false;
        let mut has_import_default = false;
        let statements: Vec<NodeId> = nodes[self.source_file]
            .as_source_file()
            .statements
            .as_ref()
            .map(|l| l.nodes.iter().copied().collect())
            .unwrap_or_default();
        for node in statements {
            // Look through NotEmittedStatement to find elided export= declarations
            // (e.g., `declare export = x` is elided by the type eraser but must still be collected)
            if ast::is_not_emitted_statement(&nodes[node]) {
                if let Some(original) = self.emit_context.borrow().most_original(Some(node))
                    && ast::is_export_assignment(&nodes[original])
                {
                    let n = nodes[original].as_export_assignment();
                    if n.is_export_equals && self.output.export_equals.is_none() {
                        self.output.export_equals = Some(original);
                    }
                }
                continue;
            }
            match nodes[node].kind {
                ast::Kind::ImportDeclaration => {
                    // import "mod"
                    // import x from "mod"
                    // import * as x from "mod"
                    // import { x, y } from "mod"
                    self.add_external_import(node);
                    if !has_import_star && get_import_needs_import_star_helper(nodes, node) {
                        has_import_star = true;
                    }
                    if !has_import_default && get_import_needs_import_default_helper(nodes, node) {
                        has_import_default = true;
                    }
                }
                ast::Kind::ImportEqualsDeclaration => {
                    let n = nodes[node].as_import_equals_declaration();
                    if n.module_reference
                        .is_some_and(|m| ast::is_external_module_reference(&nodes[m]))
                    {
                        // import x = require("mod")
                        self.add_external_import(node);
                    }
                }
                ast::Kind::ExportDeclaration => {
                    let n = nodes[node].as_export_declaration();
                    let (module_specifier, export_clause) = (n.module_specifier, n.export_clause);
                    if module_specifier.is_some() {
                        // export * from "mod"
                        // export * as ns from "mod"
                        // export { x, y } from "mod"
                        self.add_external_import(node);
                        if export_clause.is_none() {
                            // export * from "mod"
                            self.output.has_export_stars_to_export_values = true;
                        } else if ast::is_named_exports(&nodes[export_clause.unwrap()]) {
                            // export { x, y } from "mod"
                            self.add_exported_names_for_export_declaration(nodes, node);
                            if !has_import_default {
                                has_import_default =
                                    contains_default_reference(nodes, export_clause);
                            }
                        } else {
                            // export * as ns from "mod"
                            let name = nodes[export_clause.unwrap()].name().unwrap();
                            let name_text = nodes[name].text(nodes).into_owned();
                            if self.add_unique_export(&name_text) {
                                self.add_exported_binding(node, name);
                                self.add_exported_name(name);
                            }
                            // we use the same helpers for `export * as ns` as we do for `import * as ns`
                            has_import_star = true;
                        }
                    } else {
                        // export { x, y }
                        self.add_exported_names_for_export_declaration(nodes, node);
                    }
                }
                ast::Kind::ExportAssignment => {
                    let n = nodes[node].as_export_assignment();
                    if n.is_export_equals && self.output.export_equals.is_none() {
                        // export = x
                        self.output.export_equals = Some(node);
                    }
                }
                ast::Kind::VariableStatement => {
                    if ast::has_syntactic_modifier(&nodes[node], ast::ModifierFlags::EXPORT) {
                        let declarations: Vec<NodeId> = nodes[node]
                            .as_variable_statement()
                            .declaration_list
                            .and_then(|dl| {
                                nodes[dl]
                                    .as_variable_declaration_list()
                                    .declarations
                                    .as_ref()
                                    .map(|d| d.nodes.iter().copied().collect())
                            })
                            .unwrap_or_default();
                        for decl in declarations {
                            self.collect_exported_variable_info(nodes, decl);
                        }
                    }
                }
                ast::Kind::FunctionDeclaration => {
                    if ast::has_syntactic_modifier(&nodes[node], ast::ModifierFlags::EXPORT) {
                        let is_default =
                            ast::has_syntactic_modifier(&nodes[node], ast::ModifierFlags::DEFAULT);
                        self.add_exported_function_declaration(nodes, node, None, is_default);
                    }
                }
                ast::Kind::ClassDeclaration => {
                    if ast::has_syntactic_modifier(&nodes[node], ast::ModifierFlags::EXPORT) {
                        if ast::has_syntactic_modifier(&nodes[node], ast::ModifierFlags::DEFAULT) {
                            // export default class { }
                            if !self.has_export_default {
                                let mut name = nodes[node].name();
                                if name.is_none() {
                                    name = Some(
                                        self.emit_context
                                            .borrow_mut()
                                            .factory
                                            .new_generated_name_for_node(nodes, node),
                                    );
                                }
                                self.add_exported_binding(node, name.unwrap());
                                self.has_export_default = true;
                            }
                        } else {
                            // export class x { }
                            if let Some(name) = nodes[node].name() {
                                let name_text = nodes[name].text(nodes).into_owned();
                                if self.add_unique_export(&name_text) {
                                    self.add_exported_binding(node, name);
                                    self.add_exported_name(name);
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// `(c *externalModuleInfoCollector) addUniqueExport`
    fn add_unique_export(&mut self, name: &str) -> bool {
        if !self.unique_exports.has(name) {
            self.unique_exports.add(name.to_string());
            return true;
        }
        false
    }

    /// `(c *externalModuleInfoCollector) addExportedBinding`
    fn add_exported_binding(&mut self, decl: NodeId, name: NodeId) {
        self.output
            .exported_bindings
            .add(self.most_original(decl), name);
    }

    /// `(c *externalModuleInfoCollector) addExternalImport`
    fn add_external_import(
        &mut self,
        node: NodeId, /* ImportDeclaration | ImportEqualsDeclaration | ExportDeclaration */
    ) {
        self.output.external_imports.push(node);
    }

    /// `(c *externalModuleInfoCollector) addExportedName`
    fn add_exported_name(&mut self, name: NodeId) {
        self.output.exported_names.push(name);
    }

    /// `(c *externalModuleInfoCollector) addExportedNamesForExportDeclaration`
    /// — `node` must be an `ExportDeclaration`.
    fn add_exported_names_for_export_declaration(&mut self, nodes: &mut Vec<Node>, node: NodeId) {
        let (export_clause, module_specifier) = {
            let d = nodes[node].as_export_declaration();
            (d.export_clause, d.module_specifier)
        };
        let elements: Vec<NodeId> = export_clause
            .and_then(|c| nodes[c].elements().map(|e| e.to_vec()))
            .unwrap_or_default();
        for specifier in elements {
            let specifier_name = nodes[specifier].name().unwrap();
            let specifier_name_text = nodes[specifier_name].text(nodes).into_owned();
            if !self.add_unique_export(&specifier_name_text) {
                continue;
            }
            let name = nodes[specifier].property_name_or_name().unwrap();
            if nodes[name].kind != ast::Kind::StringLiteral {
                if module_specifier.is_none() {
                    let key = nodes[name].text(nodes).into_owned();
                    self.output.export_specifiers.add(key, specifier);
                }

                let original = self.most_original(name);
                let mut decl = self.with_symbols(|symbols| {
                    self.resolver()
                        .get_referenced_import_declaration(original, nodes, symbols)
                });
                if decl.is_none() {
                    decl = self.with_symbols(|symbols| {
                        self.resolver().get_referenced_value_declaration(
                            original, nodes, symbols,
                        )
                    });
                }
                if let Some(decl) = decl {
                    if nodes[decl].kind == ast::Kind::FunctionDeclaration {
                        self.unique_exports.delete(specifier_name_text.as_str());
                        let is_default =
                            ast::module_export_name_is_default(&nodes[specifier_name], nodes);
                        self.add_exported_function_declaration(
                            nodes,
                            decl,
                            Some(specifier_name),
                            is_default,
                        );
                        continue;
                    }
                    self.add_exported_binding(decl, specifier_name);
                }
            }

            self.add_exported_name(specifier_name);
        }
    }

    /// `(c *externalModuleInfoCollector) addExportedFunctionDeclaration` —
    /// `node` must be a `FunctionDeclaration`.
    fn add_exported_function_declaration(
        &mut self,
        nodes: &mut Vec<Node>,
        node: NodeId,
        name: Option<NodeId>,
        is_default: bool,
    ) {
        self.output.exported_functions.add(self.most_original(node));
        if is_default {
            // export default function() { }
            // function x() { } + export { x as default };
            if !self.has_export_default {
                let name = match name {
                    Some(n) => n,
                    None => self
                        .emit_context
                        .borrow_mut()
                        .factory
                        .new_generated_name_for_node(nodes, node),
                };
                self.add_exported_binding(node, name);
                self.has_export_default = true;
            }
        } else {
            // export function x() { }
            // function x() { } + export { x }
            let name = name.or_else(|| nodes[node].name());
            let name_text = nodes[name.unwrap()].text(nodes).into_owned();
            if self.add_unique_export(&name_text) {
                self.add_exported_binding(node, name.unwrap());
            }
        }
    }

    /// `(c *externalModuleInfoCollector) collectExportedVariableInfo` —
    /// `decl` must be a `VariableDeclaration` or `BindingElement`.
    fn collect_exported_variable_info(&mut self, nodes: &mut Vec<Node>, decl: NodeId) {
        let name = nodes[decl].name();
        if name.is_some_and(|n| ast::is_binding_pattern(&nodes[n])) {
            let elements: Vec<NodeId> = nodes[name.unwrap()]
                .elements()
                .map(|e| e.to_vec())
                .unwrap_or_default();
            for element in elements {
                if nodes[element].as_binding_element().name.is_some() {
                    self.collect_exported_variable_info(nodes, element);
                }
            }
        } else if !self.emit_context.borrow().has_auto_generate_info(name) {
            let text = nodes[name.unwrap()].text(nodes).into_owned();
            if self.add_unique_export(&text) {
                self.add_exported_name(name.unwrap());
                if crate::is_local_name(&self.emit_context.borrow(), name.unwrap()) {
                    self.add_exported_binding(decl, name.unwrap());
                }
            }
        }
    }
}

/// `externalHelpersModuleNameText`
pub(crate) const EXTERNAL_HELPERS_MODULE_NAME_TEXT: &str = "tslib";

/// `createExternalHelpersImportDeclarationIfNeeded(emitContext, sourceFile, compilerOptions, fileModuleKind, hasExportStarsToExportValues, hasImportStar, hasImportDefault)`
///
/// `source_file` is the `SourceFile` node.
#[allow(clippy::too_many_arguments)]
pub fn create_external_helpers_import_declaration_if_needed(
    emit_context: &mut EmitContext,
    nodes: &mut Vec<Node>,
    source_file: NodeId,
    compiler_options: &CompilerOptions,
    file_module_kind: ModuleKind,
    has_export_stars_to_export_values: bool,
    has_import_star: bool,
    has_import_default: bool,
) -> Option<NodeId> {
    if !(compiler_options.import_helpers.is_true()
        && ast::is_effective_external_module(nodes[source_file].as_source_file(), compiler_options))
    {
        return None;
    }
    let module_kind = compiler_options.get_emit_module_kind();
    let helpers = get_imported_helpers(emit_context, source_file);
    if file_module_kind == ModuleKind::CommonJS
        || (file_module_kind == ModuleKind::None && module_kind == ModuleKind::CommonJS)
    {
        // When we emit to a non-ES module, generate a synthetic `import tslib = require("tslib")` to be further transformed.
        let external_helpers_module_name = get_or_create_external_helpers_module_name_if_needed(
            emit_context,
            nodes,
            source_file,
            compiler_options,
            &helpers,
            has_export_stars_to_export_values,
            has_import_star || has_import_default,
            file_module_kind,
        );
        if let Some(external_helpers_module_name) = external_helpers_module_name {
            let external_helpers_import_declaration = {
                let f = &mut emit_context.factory;
                let literal = f.new_string_literal(
                    nodes,
                    EXTERNAL_HELPERS_MODULE_NAME_TEXT,
                    ast::TokenFlags::NONE,
                );
                let module_reference = f.new_external_module_reference(nodes, Some(literal));
                f.new_import_equals_declaration(
                    nodes,
                    None,  /* modifiers */
                    false, /* isTypeOnly */
                    Some(external_helpers_module_name),
                    Some(module_reference),
                )
            };
            emit_context.add_emit_flags(
                external_helpers_import_declaration,
                EmitFlags::CUSTOM_PROLOGUE,
            );
            return Some(external_helpers_import_declaration);
        }
    } else {
        // When we emit as an ES module, generate an `import` declaration that uses named imports for helpers.
        // If we cannot determine the implied module kind under `module: preserve` we assume ESM.
        let mut helper_names: Vec<&'static str> = Vec::new();
        for helper in &helpers {
            let import_name = helper.import_name;
            if !import_name.is_empty() {
                helper_names =
                    tsc_core::core::append_if_unique(&helper_names, import_name).into_owned();
            }
        }
        if !helper_names.is_empty() {
            helper_names.sort_by(|a, b| {
                tsc_stringutil::compare_strings_case_sensitive(a.as_bytes(), b.as_bytes()).cmp(&0)
            });
            // Alias the imports if the names are used somewhere in the file.
            // NOTE: We don't need to care about global import collisions as this is a module.
            let mut import_specifiers: Vec<NodeId> = Vec::new();
            for &name in &helper_names {
                let unique =
                    emit_context
                        .is_file_level_unique_name(nodes, source_file, name, &mut |_| false);
                let specifier = {
                    let f = &mut emit_context.factory;
                    if unique {
                        let ident = f.new_identifier(nodes, name);
                        f.new_import_specifier(
                            nodes,
                            false, /* isTypeOnly */
                            None,  /* propertyName */
                            Some(ident),
                        )
                    } else {
                        let property_name = f.new_identifier(nodes, name);
                        let scoped = f.new_unscoped_helper_name(nodes, name);
                        f.new_import_specifier(
                            nodes,
                            false, /* isTypeOnly */
                            Some(property_name),
                            Some(scoped),
                        )
                    }
                };
                import_specifiers.push(specifier);
            }
            let parse_node = emit_context
                .most_original(Some(source_file))
                .expect("MostOriginal returned nil for a non-nil node");
            emit_context.add_emit_flags(parse_node, EmitFlags::EXTERNAL_HELPERS);
            let external_helpers_import_declaration = {
                let f = &mut emit_context.factory;
                let specifier_list = f.new_node_list(import_specifiers);
                let named_bindings = f.new_named_imports(nodes, Some(specifier_list));
                let literal = f.new_string_literal(
                    nodes,
                    EXTERNAL_HELPERS_MODULE_NAME_TEXT,
                    ast::TokenFlags::NONE,
                );
                let import_clause = f.new_import_clause(
                    nodes,
                    ast::Kind::Unknown, /* phaseModifier */
                    None,               /* name */
                    Some(named_bindings),
                );
                f.new_import_declaration(
                    nodes,
                    None, /* modifiers */
                    Some(import_clause),
                    Some(literal),
                    None, /* attributes */
                )
            };
            emit_context.add_emit_flags(
                external_helpers_import_declaration,
                EmitFlags::CUSTOM_PROLOGUE,
            );
            return Some(external_helpers_import_declaration);
        }
    }
    None
}

/// `getImportedHelpers(emitContext, sourceFile)` — `source_file` is the
/// `SourceFile` node.
fn get_imported_helpers(emit_context: &EmitContext, source_file: NodeId) -> Vec<Arc<EmitHelper>> {
    emit_context
        .get_emit_helpers(source_file)
        .into_iter()
        .filter(|h| !h.scoped)
        .collect()
}

/// `getOrCreateExternalHelpersModuleNameIfNeeded(emitContext, node, compilerOptions, helpers, hasExportStarsToExportValues, hasImportStarOrImportDefault, fileModuleKind)`
#[allow(clippy::too_many_arguments)]
fn get_or_create_external_helpers_module_name_if_needed(
    emit_context: &mut EmitContext,
    nodes: &mut Vec<Node>,
    node: NodeId, /* SourceFile */
    _compiler_options: &CompilerOptions,
    helpers: &[Arc<EmitHelper>],
    has_export_stars_to_export_values: bool,
    has_import_star_or_import_default: bool,
    file_module_kind: ModuleKind,
) -> Option<NodeId> {
    if let Some(name) = emit_context.get_external_helpers_module_name(nodes, node) {
        return Some(name);
    }

    let create = !helpers.is_empty()
        || (has_export_stars_to_export_values || has_import_star_or_import_default)
            && file_module_kind < ModuleKind::System;

    if create {
        let external_helpers_module_name = emit_context
            .factory
            .new_unique_name(nodes, EXTERNAL_HELPERS_MODULE_NAME_TEXT);
        emit_context.set_external_helpers_module_name(nodes, node, external_helpers_module_name);
        return Some(external_helpers_module_name);
    }
    None
}

/// `isNamedDefaultReference(e)` — `e` must be an `ImportSpecifier` or
/// `ExportSpecifier`.
pub fn is_named_default_reference(nodes: &[Node], e: NodeId) -> bool {
    ast::module_export_name_is_default(&nodes[nodes[e].property_name_or_name().unwrap()], nodes)
}

/// `containsDefaultReference(node)` — `node` must be a `NamedImportBindings`
/// or `NamedExportBindings` node (or `None`, mirroring Go nil).
pub fn contains_default_reference(nodes: &[Node], node: Option<NodeId>) -> bool {
    node.is_some_and(|n| {
        (ast::is_named_imports(&nodes[n]) || ast::is_named_exports(&nodes[n]))
            && nodes[n]
                .elements()
                .is_some_and(|e| e.iter().any(|&el| is_named_default_reference(nodes, el)))
    })
}

/// `getExportNeedsImportStarHelper(node)` — `node` must be an
/// `ExportDeclaration`.
pub fn get_export_needs_import_star_helper(nodes: &[Node], node: NodeId) -> bool {
    ast::get_namespace_declaration_node(&nodes[node], nodes).is_some()
}

/// `getImportNeedsImportStarHelper(node)` — `node` must be an
/// `ImportDeclaration`.
pub fn get_import_needs_import_star_helper(nodes: &[Node], node: NodeId) -> bool {
    if ast::get_namespace_declaration_node(&nodes[node], nodes).is_some() {
        return true;
    }
    let Some(import_clause) = nodes[node].as_import_declaration().import_clause else {
        return false;
    };
    let Some(bindings) = nodes[import_clause].as_import_clause().named_bindings else {
        return false;
    };
    if !ast::is_named_imports(&nodes[bindings]) {
        return false;
    }
    let elements = nodes[bindings]
        .as_named_imports()
        .elements
        .as_ref()
        .map(|e| e.nodes.to_vec())
        .unwrap_or_default();
    let mut default_ref_count = 0usize;
    for &binding in elements.iter() {
        if is_named_default_reference(nodes, binding) {
            default_ref_count += 1;
        }
    }
    // Import star is required if there's default named refs mixed with non-default refs, or if theres non-default refs and it has a default import
    (default_ref_count > 0 && default_ref_count != elements.len())
        || ((elements.len() - default_ref_count) != 0
            && ast::is_default_import(&nodes[node], nodes))
}

/// `getImportNeedsImportDefaultHelper(node)` — `node` must be an
/// `ImportDeclaration`.
pub fn get_import_needs_import_default_helper(nodes: &[Node], node: NodeId) -> bool {
    // Import default is needed if there's a default import or a default ref and no other refs (meaning an import star helper wasn't requested)
    !get_import_needs_import_star_helper(nodes, node)
        && (ast::is_default_import(&nodes[node], nodes)
            || (nodes[node].as_import_declaration().import_clause.is_some()
                && contains_default_reference(
                    nodes,
                    nodes[nodes[node].as_import_declaration().import_clause.unwrap()]
                        .as_import_clause()
                        .named_bindings,
                )))
}
