// Ported from tsc/internal/ls/importTracker.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(idents): Go refers to AST nodes and symbols by pointer; the Rust port
// uses `NodeId`/`SymbolId` into per-file arenas (`program.nodes(file_index)`)
// and the shared symbol arena (`program.symbols` == `checker.symbol_arena`).
// `ImportTracker` is a boxed closure (Go func value); it captures
// `Rc<RefCell<Checker>>` and borrows it per call since the language service
// is single-threaded.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use tsc_ast::ast::FileReference;
use tsc_ast::{self as ast, Kind, ModifierFlags, Node, NodeId, SymbolFlags, SymbolId};
use tsc_checker::checker_core::Checker;
use tsc_collections::Set;
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_tspath::RootedFilePath;

/// `type ImpExpKind int32`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ImpExpKind {
    /// `ImpExpKindUnknown`.
    Unknown,
    /// `ImpExpKindImport`.
    Import,
    /// `ImpExpKindExport`.
    Export,
}

/// `type ImportExportSymbol struct`.
pub(crate) struct ImportExportSymbol {
    /// `kind`.
    pub(crate) kind: ImpExpKind,
    /// `symbol`.
    pub(crate) symbol: SymbolId,
    /// `exportInfo` — nil for imports in Go.
    pub(crate) export_info: Option<Rc<ExportInfo>>,
}

/// `type ExportKind int`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ExportKind {
    /// `ExportKindNamed`.
    Named,
    /// `ExportKindDefault`.
    Default,
    /// `ExportKindExportEquals`.
    ExportEquals,
    /// `ExportKindUMD`.
    #[allow(dead_code)]
    Umd,
    /// `ExportKindModule`.
    Module,
}

/// `type ExportInfo struct`.
pub(crate) struct ExportInfo {
    /// `exportingModuleSymbol`.
    pub(crate) exporting_module_symbol: SymbolId,
    /// `exportKind`.
    pub(crate) export_kind: ExportKind,
}

/// `type LocationAndSymbol struct`.
pub(crate) struct LocationAndSymbol {
    /// `importLocation`.
    pub(crate) import_location: NodeId,
    /// `importSymbol` — may be nil in Go when `GetSymbolAtLocation` fails.
    pub(crate) import_symbol: Option<SymbolId>,
}

/// `type ImportsResult struct`.
pub(crate) struct ImportsResult {
    /// `importSearches`.
    pub(crate) import_searches: Vec<LocationAndSymbol>,
    /// `singleReferences`.
    pub(crate) single_references: Vec<NodeId>,
    /// `indirectUsers`.
    pub(crate) indirect_users: Vec<NodeId>,
}

/// `type ImportTracker func(...) *ImportsResult`.
pub(crate) type ImportTracker =
    Box<dyn FnMut(SymbolId, &ExportInfo, bool) -> Rc<ImportsResult>>;

/// `type ModuleReferenceKind int32`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ModuleReferenceKind {
    /// `ModuleReferenceKindImport`.
    Import,
    /// `ModuleReferenceKindReference`.
    Reference,
    /// `ModuleReferenceKindImplicit`.
    Implicit,
}

/// `type ModuleReference struct`.
pub(crate) struct ModuleReference {
    /// `kind`.
    pub(crate) kind: ModuleReferenceKind,
    /// `literal` — for import and implicit kinds (StringLiteralLike).
    pub(crate) literal: Option<NodeId>,
    /// `referencingFile` — nil in Go for `ModuleReferenceKindImport`.
    pub(crate) referencing_file: Option<NodeId>,
    /// `ref` — for reference kind.
    pub(crate) file_ref: Option<FileReference>,
}

/// `createImportTracker`.
/// Creates the imports map and returns an ImportTracker that uses it.
/// Call this lazily to avoid calling `getDirectImportsMap` unnecessarily.
pub(crate) fn create_import_tracker(
    ctx: Context,
    program: Rc<Program>,
    source_files: Vec<NodeId>,
    source_files_set: Set<RootedFilePath>,
    checker: Rc<RefCell<Checker>>,
) -> ImportTracker {
    let all_direct_imports = {
        let mut c = checker.borrow_mut();
        get_direct_imports_map(&ctx, &program, &source_files, &mut c)
    };
    Box::new(move |export_symbol, export_info, is_for_rename| {
        let mut c = checker.borrow_mut();
        let (direct_imports, indirect_users) = get_importers_for_export(
            &program,
            &source_files,
            &source_files_set,
            &all_direct_imports,
            export_info,
            &mut c,
        );
        let (import_searches, single_references) = get_searches_from_direct_imports(
            &program,
            &direct_imports,
            export_symbol,
            export_info.export_kind,
            &mut c,
            is_for_rename,
        );
        Rc::new(ImportsResult {
            import_searches,
            single_references,
            indirect_users,
        })
    })
}

/// `getDirectImportsMap`.
/// Returns a map from a module symbol to all import statements that directly
/// reference the module.
fn get_direct_imports_map(
    ctx: &Context,
    program: &Rc<Program>,
    source_files: &[NodeId],
    checker: &mut Checker,
) -> HashMap<SymbolId, Vec<NodeId>> {
    let mut result: HashMap<SymbolId, Vec<NodeId>> = HashMap::new();
    for &source_file in source_files {
        if ctx.is_cancelled() {
            return result;
        }
        let imports = collect_import_pairs(program, source_file);
        for (import_decl, module_specifier) in imports {
            if let Some(module_symbol) = checker.get_symbol_at_location_api(module_specifier) {
                result
                    .entry(module_symbol)
                    .or_default()
                    .push(import_decl);
            }
        }
    }
    result
}

/// `forEachImport` — collects `(importStatement, imported)` pairs instead of
/// invoking a callback, so callers can borrow the checker freely.
/// Calls `action` for each import, re-export, or require() in a file.
fn collect_import_pairs(program: &Rc<Program>, source_file: NodeId) -> Vec<(NodeId, NodeId)> {
    let mut result: Vec<(NodeId, NodeId)> = Vec::new();
    for_each_import(program, source_file, &mut |import_statement, imported| {
        result.push((import_statement, imported));
    });
    result
}

/// `forEachImport`.
pub(crate) fn for_each_import(
    program: &Rc<Program>,
    source_file: NodeId,
    action: &mut dyn FnMut(NodeId, NodeId),
) {
    let nodes = program.nodes(source_file.file_index());
    let sf = nodes[source_file].as_source_file();
    let mut implicit_imports: Vec<NodeId> = Vec::new();
    let (_, jsx_specifier) = program.get_jsx_runtime_import_specifier(sf.path_key());
    if let Some(jsx_specifier) = jsx_specifier {
        implicit_imports.push(jsx_specifier);
    }
    if let Some(import_helpers_specifier) =
        program.get_import_helpers_import_specifier(sf.path_key())
    {
        implicit_imports.push(import_helpers_specifier);
    }
    if sf.external_module_indicator.is_some()
        || !sf.imports().is_empty()
        || !implicit_imports.is_empty()
    {
        let imports: Vec<NodeId> = sf.imports().to_vec();
        drop(nodes);
        for i in imports {
            let nodes = program.nodes(source_file.file_index());
            let Some(import_decl) = ast::import_from_module_specifier(i, &nodes) else {
                continue;
            };
            action(import_decl, i);
        }
        for i in implicit_imports {
            let nodes = program.nodes(source_file.file_index());
            let Some(import_decl) = ast::import_from_module_specifier(i, &nodes) else {
                continue;
            };
            action(import_decl, i);
        }
    } else {
        for_each_possible_import_or_export_statement(
            program,
            source_file,
            &mut |node| {
                let nodes = program.nodes(node.file_index());
                match nodes[node].kind {
                    Kind::ExportDeclaration
                    | Kind::ImportDeclaration
                    | Kind::JSImportDeclaration => {
                        if let Some(specifier) = nodes[node].module_specifier() {
                            if ast::is_string_literal(&nodes[specifier]) {
                                action(node, specifier);
                            }
                        }
                    }
                    Kind::ImportEqualsDeclaration => {
                        if is_external_module_import_equals(node, &nodes) {
                            if let Some(expression) = nodes[node]
                                .as_import_equals_declaration()
                                .module_reference
                                .and_then(|m| nodes[m].expression())
                            {
                                action(node, expression);
                            }
                        }
                    }
                    _ => {}
                }
                false
            },
        );
    }
}

/// `forEachPossibleImportOrExportStatement`.
fn for_each_possible_import_or_export_statement(
    program: &Rc<Program>,
    source_file_like: NodeId,
    action: &mut dyn FnMut(NodeId) -> bool,
) -> bool {
    let statements = {
        let nodes = program.nodes(source_file_like.file_index());
        get_statements_of_source_file_like(source_file_like, &nodes)
    };
    for statement in statements {
        let is_ambient_module = {
            let nodes = program.nodes(statement.file_index());
            is_ambient_module_declaration(statement, &nodes)
        };
        if action(statement)
            || (is_ambient_module
                && for_each_possible_import_or_export_statement(program, statement, action))
        {
            return true;
        }
    }
    false
}

/// `getSourceFileLikeForImportDeclaration`.
fn get_source_file_like_for_import_declaration(node: NodeId, nodes: &[Node]) -> NodeId {
    if ast::is_call_expression(&nodes[node]) || ast::is_js_doc_import_tag(&nodes[node]) {
        return ast::get_source_file_of_node(Some(node), nodes).expect("source file of node");
    }
    let parent = nodes[node].parent.expect("parent");
    if ast::is_source_file(&nodes[parent]) {
        return parent;
    }
    debug_assert!(
        nodes[parent].kind == Kind::ModuleBlock
            && nodes[parent]
                .parent
                .is_some_and(|gp| is_ambient_module_declaration(gp, nodes)),
        "expected ModuleBlock inside ambient module declaration"
    );
    nodes[parent].parent.expect("ambient module declaration")
}

/// `isAmbientModuleDeclaration`.
fn is_ambient_module_declaration(node: NodeId, nodes: &[Node]) -> bool {
    ast::is_module_declaration(&nodes[node])
        && nodes[node]
            .name()
            .is_some_and(|n| ast::is_string_literal(&nodes[n]))
}

/// `getStatementsOfSourceFileLike`.
fn get_statements_of_source_file_like(node: NodeId, nodes: &[Node]) -> Vec<NodeId> {
    if ast::is_source_file(&nodes[node]) {
        return nodes[node].statements().map(|s| s.to_vec()).unwrap_or_default();
    }
    if let Some(body) = nodes[node].body() {
        return nodes[body].statements().map(|s| s.to_vec()).unwrap_or_default();
    }
    Vec::new()
}

/// `getImportersForExport`.
fn get_importers_for_export(
    program: &Rc<Program>,
    source_files: &[NodeId],
    source_files_set: &Set<RootedFilePath>,
    all_direct_imports: &HashMap<SymbolId, Vec<NodeId>>,
    export_info: &ExportInfo,
    checker: &mut Checker,
) -> (Vec<NodeId>, Vec<NodeId>) {
    let mut direct_imports: Vec<NodeId> = Vec::new();
    let mut indirect_user_declarations: Vec<NodeId> = Vec::new();
    let mut mark_seen_direct_import = crate::utilities::node_seen_tracker();
    let mut mark_seen_indirect_user = crate::utilities::node_seen_tracker();
    let is_available_through_global = {
        let value_declaration = checker.symbol_arena.get_ref(export_info.exporting_module_symbol)
        .value_declaration;
        match value_declaration {
            Some(vd) => {
                let nodes = program.nodes(vd.file_index());
                crate::utilities::is_source_file_with_global_exports(Some(vd), &nodes)
            }
            None => false,
        }
    };

    // Adds a module and all of its transitive dependencies as possible indirect users
    fn add_indirect_user(
        program: &Rc<Program>,
        checker: &mut Checker,
        all_direct_imports: &HashMap<SymbolId, Vec<NodeId>>,
        is_available_through_global: bool,
        indirect_user_declarations: &mut Vec<NodeId>,
        mark_seen_indirect_user: &mut dyn FnMut(NodeId) -> bool,
        source_file_like: NodeId,
        add_transitive_dependencies: bool,
    ) {
        // When isAvailableThroughGlobal, getIndirectUsers already returns all source files,
        // so indirectUserDeclarations is never consulted. Nothing to do here.
        if is_available_through_global {
            return;
        }
        if !mark_seen_indirect_user(source_file_like) {
            return;
        }
        indirect_user_declarations.push(source_file_like);
        if !add_transitive_dependencies {
            return;
        }
        let module_symbol = {
            let nodes = program.nodes(source_file_like.file_index());
            nodes[source_file_like].symbol()
        };
        let Some(module_symbol) = module_symbol else {
            return;
        };
        let module_symbol = checker.get_merged_symbol(module_symbol);
        debug_assert!(
            checker.symbol_arena.get_ref(module_symbol)
                .flags
                .intersects(SymbolFlags::MODULE)
        );
        for direct_import in all_direct_imports
            .get(&module_symbol)
            .cloned()
            .unwrap_or_default()
        {
            let is_import_type = {
                let nodes = program.nodes(direct_import.file_index());
                ast::is_import_type_node(&nodes[direct_import])
            };
            if !is_import_type {
                let source_file_like = {
                    let nodes = program.nodes(direct_import.file_index());
                    get_source_file_like_for_import_declaration(direct_import, &nodes)
                };
                add_indirect_user(
                    program,
                    checker,
                    all_direct_imports,
                    is_available_through_global,
                    indirect_user_declarations,
                    mark_seen_indirect_user,
                    source_file_like,
                    true, /*addTransitiveDependencies*/
                );
            }
        }
    }

    // `isExported`
    fn is_exported(mut node: Option<NodeId>, stop_at_ambient_module: bool, nodes: &[Node]) -> bool {
        while let Some(n) = node {
            if stop_at_ambient_module && is_ambient_module_declaration(n, nodes) {
                break;
            }
            if ast::has_syntactic_modifier(&nodes[n], ModifierFlags::EXPORT) {
                return true;
            }
            node = nodes[n].parent;
        }
        false
    }

    // `handleImportCall`
    fn handle_import_call(
        program: &Rc<Program>,
        checker: &mut Checker,
        all_direct_imports: &HashMap<SymbolId, Vec<NodeId>>,
        is_available_through_global: bool,
        indirect_user_declarations: &mut Vec<NodeId>,
        mark_seen_indirect_user: &mut dyn FnMut(NodeId) -> bool,
        import_call: NodeId,
    ) {
        let (top, exported) = {
            let nodes = program.nodes(import_call.file_index());
            let top = ast::find_ancestor(Some(import_call), &nodes, &mut |n, ns| {
                is_ambient_module_declaration(n.id, ns)
            })
            .or_else(|| ast::get_source_file_of_node(Some(import_call), &nodes))
            .expect("top");
            (
                top,
                is_exported(Some(import_call), true /*stopAtAmbientModule*/, &nodes),
            )
        };
        add_indirect_user(
            program,
            checker,
            all_direct_imports,
            is_available_through_global,
            indirect_user_declarations,
            mark_seen_indirect_user,
            top,
            exported,
        );
    }

    // `handleNamespaceImport`
    #[allow(clippy::too_many_arguments)]
    fn handle_namespace_import(
        program: &Rc<Program>,
        checker: &mut Checker,
        all_direct_imports: &HashMap<SymbolId, Vec<NodeId>>,
        export_info: &ExportInfo,
        is_available_through_global: bool,
        direct_imports: &mut Vec<NodeId>,
        indirect_user_declarations: &mut Vec<NodeId>,
        mark_seen_indirect_user: &mut dyn FnMut(NodeId) -> bool,
        import_declaration: NodeId,
        name: Option<NodeId>,
        is_re_export: bool,
        already_added_direct: bool,
    ) {
        if export_info.export_kind == ExportKind::ExportEquals {
            // This is a direct import, not import-as-namespace.
            if !already_added_direct {
                direct_imports.push(import_declaration);
            }
        } else if !is_available_through_global {
            let source_file_like = {
                let nodes = program.nodes(import_declaration.file_index());
                get_source_file_like_for_import_declaration(import_declaration, &nodes)
            };
            debug_assert!({
                let nodes = program.nodes(source_file_like.file_index());
                ast::is_source_file(&nodes[source_file_like])
                    || ast::is_module_declaration(&nodes[source_file_like])
            });
            let re_exports = is_re_export
                || find_namespace_re_exports(program, source_file_like, name, checker);
            add_indirect_user(
                program,
                checker,
                all_direct_imports,
                is_available_through_global,
                indirect_user_declarations,
                mark_seen_indirect_user,
                source_file_like,
                re_exports,
            );
        }
    }

    // `handleDirectImports` — needs recursion into itself for
    // `export *`, so it is a recursive fn.
    #[allow(clippy::too_many_arguments)]
    fn handle_direct_imports(
        program: &Rc<Program>,
        checker: &mut Checker,
        all_direct_imports: &HashMap<SymbolId, Vec<NodeId>>,
        export_info: &ExportInfo,
        is_available_through_global: bool,
        direct_imports: &mut Vec<NodeId>,
        indirect_user_declarations: &mut Vec<NodeId>,
        mark_seen_direct_import: &mut dyn FnMut(NodeId) -> bool,
        mark_seen_indirect_user: &mut dyn FnMut(NodeId) -> bool,
        exporting_module_symbol: SymbolId,
    ) {
        let these_direct_imports = all_direct_imports
            .get(&exporting_module_symbol)
            .cloned()
            .unwrap_or_default();
        for direct in these_direct_imports {
            if !mark_seen_direct_import(direct) {
                continue;
            }
            // !!! cancellation
            let kind = {
                let nodes = program.nodes(direct.file_index());
                nodes[direct].kind
            };
            match kind {
                Kind::CallExpression => {
                    let is_import_call = {
                        let nodes = program.nodes(direct.file_index());
                        ast::is_import_call(&nodes[direct], &nodes)
                    };
                    if is_import_call {
                        handle_import_call(
                            program,
                            checker,
                            all_direct_imports,
                            is_available_through_global,
                            indirect_user_declarations,
                            mark_seen_indirect_user,
                            direct,
                        );
                    } else if !is_available_through_global {
                        let (parent, is_variable_declaration) = {
                            let nodes = program.nodes(direct.file_index());
                            (
                                nodes[direct].parent,
                                nodes[direct]
                                    .parent
                                    .is_some_and(|p| ast::is_variable_declaration(&nodes[p])),
                            )
                        };
                        if export_info.export_kind == ExportKind::ExportEquals
                            && is_variable_declaration
                        {
                            let name = {
                                let nodes = program.nodes(direct.file_index());
                                parent.and_then(|p| nodes[p].name())
                            };
                            if let Some(name) = name {
                                let nodes = program.nodes(name.file_index());
                                if ast::is_identifier(&nodes[name]) {
                                    direct_imports.push(name);
                                }
                            }
                        }
                    }
                }
                Kind::Identifier => {
                    // Nothing
                }
                Kind::ImportEqualsDeclaration => {
                    let (name, is_re_export) = {
                        let nodes = program.nodes(direct.file_index());
                        (
                            nodes[direct].name(),
                            ast::has_syntactic_modifier(&nodes[direct], ModifierFlags::EXPORT),
                        )
                    };
                    handle_namespace_import(
                        program,
                        checker,
                        all_direct_imports,
                        export_info,
                        is_available_through_global,
                        direct_imports,
                        indirect_user_declarations,
                        mark_seen_indirect_user,
                        direct,
                        name,
                        is_re_export,
                        false, /*alreadyAddedDirect*/
                    );
                }
                Kind::ImportDeclaration | Kind::JSImportDeclaration | Kind::JSDocImportTag => {
                    direct_imports.push(direct);
                    let mut handled_namespace = false;
                    {
                        let nodes = program.nodes(direct.file_index());
                        if let Some(import_clause) = nodes[direct].import_clause() {
                            if let Some(named_bindings) =
                                nodes[import_clause].as_import_clause().named_bindings
                            {
                                if ast::is_namespace_import(&nodes[named_bindings]) {
                                    let name = nodes[named_bindings].name();
                                    handled_namespace = true;
                                    drop(nodes);
                                    handle_namespace_import(
                                        program,
                                        checker,
                                        all_direct_imports,
                                        export_info,
                                        is_available_through_global,
                                        direct_imports,
                                        indirect_user_declarations,
                                        mark_seen_indirect_user,
                                        direct,
                                        name,
                                        false, /*isReExport*/
                                        true,  /*alreadyAddedDirect*/
                                    );
                                }
                            }
                        }
                    }
                    if handled_namespace {
                        continue;
                    }
                    let is_default = {
                        let nodes = program.nodes(direct.file_index());
                        ast::is_default_import(&nodes[direct], &nodes)
                    };
                    if !is_available_through_global && is_default {
                        let source_file_like = {
                            let nodes = program.nodes(direct.file_index());
                            get_source_file_like_for_import_declaration(direct, &nodes)
                        };
                        add_indirect_user(
                            program,
                            checker,
                            all_direct_imports,
                            is_available_through_global,
                            indirect_user_declarations,
                            mark_seen_indirect_user,
                            source_file_like,
                            false,
                        );
                        // Add a check for indirect uses to handle synthetic default imports
                    }
                }
                Kind::ExportDeclaration => {
                    let export_clause = {
                        let nodes = program.nodes(direct.file_index());
                        nodes[direct].as_export_declaration().export_clause
                    };
                    match export_clause {
                        None => {
                            // This is `export * from "foo"`, so imports of this module may import the export too.
                            if let Some(containing) = get_containing_module_symbol(
                                program, direct, checker,
                            ) {
                                handle_direct_imports(
                                    program,
                                    checker,
                                    all_direct_imports,
                                    export_info,
                                    is_available_through_global,
                                    direct_imports,
                                    indirect_user_declarations,
                                    mark_seen_direct_import,
                                    mark_seen_indirect_user,
                                    containing,
                                );
                            }
                        }
                        Some(export_clause) => {
                            let is_namespace_export = {
                                let nodes = program.nodes(export_clause.file_index());
                                ast::is_namespace_export(&nodes[export_clause])
                            };
                            if is_namespace_export {
                                // `export * as foo from "foo"` add to indirect uses
                                let source_file_like = {
                                    let nodes = program.nodes(direct.file_index());
                                    get_source_file_like_for_import_declaration(direct, &nodes)
                                };
                                add_indirect_user(
                                    program,
                                    checker,
                                    all_direct_imports,
                                    is_available_through_global,
                                    indirect_user_declarations,
                                    mark_seen_indirect_user,
                                    source_file_like,
                                    true, /*addTransitiveDependencies*/
                                );
                            } else {
                                // This is `export { foo } from "foo"` and creates an alias symbol, so recursive search will get handle re-exports.
                                direct_imports.push(direct);
                            }
                        }
                    }
                }
                Kind::ImportType => {
                    {
                        let nodes = program.nodes(direct.file_index());
                        let import_type = nodes[direct].as_import_type_node();
                        if !is_available_through_global
                            && import_type.is_type_of
                            && import_type.qualifier.is_none()
                            && is_exported(Some(direct), false, &nodes)
                        {
                            let source_file = ast::get_source_file_of_node(Some(direct), &nodes)
                                .expect("source file of node");
                            drop(nodes);
                            add_indirect_user(
                                program,
                                checker,
                                all_direct_imports,
                                is_available_through_global,
                                indirect_user_declarations,
                                mark_seen_indirect_user,
                                source_file,
                                true, /*addTransitiveDependencies*/
                            );
                        }
                    }
                    direct_imports.push(direct);
                }
                _ => {
                    // `debug.FailBadSyntaxKind` — unexpected import kind.
                    debug_assert!(false, "Unexpected import kind: {:?}", kind);
                }
            }
        }
    }

    handle_direct_imports(
        program,
        checker,
        all_direct_imports,
        export_info,
        is_available_through_global,
        &mut direct_imports,
        &mut indirect_user_declarations,
        &mut mark_seen_direct_import,
        &mut mark_seen_indirect_user,
        export_info.exporting_module_symbol,
    );

    // `getIndirectUsers`
    let indirect_users: Vec<NodeId> = if is_available_through_global {
        // It has `export as namespace`, so anything could potentially use it.
        source_files.to_vec()
    } else {
        // Module augmentations may use this module's exports without importing it.
        let declarations = checker.symbol_arena.get_ref(export_info.exporting_module_symbol)
        .declarations
        .clone();
        for decl in declarations {
            let (is_augmentation, file_name) = {
                let nodes = program.nodes(decl.file_index());
                let sf = ast::get_source_file_of_node(Some(decl), &nodes);
                (
                    ast::is_external_module_augmentation(&nodes[decl], &nodes),
                    sf.map(|sf| nodes[sf].as_source_file().file_name().clone()),
                )
            };
            if is_augmentation && file_name.is_some_and(|f| source_files_set.has(&f)) {
                add_indirect_user(
                    program,
                    checker,
                    all_direct_imports,
                    is_available_through_global,
                    &mut indirect_user_declarations,
                    &mut mark_seen_indirect_user,
                    decl,
                    false,
                );
            }
        }
        // This may return duplicates (if there are multiple module declarations in a single source file, all importing the same thing as a namespace), but `State.markSearchedSymbol` will handle that.
        let mut result = Vec::with_capacity(indirect_user_declarations.len());
        for decl in &indirect_user_declarations {
            let nodes = program.nodes(decl.file_index());
            if let Some(sf) = ast::get_source_file_of_node(Some(*decl), &nodes) {
                result.push(sf);
            }
        }
        result
    };
    (direct_imports, indirect_users)
}

/// `getContainingModuleSymbol`.
fn get_containing_module_symbol(
    program: &Rc<Program>,
    importer: NodeId,
    checker: &mut Checker,
) -> Option<SymbolId> {
    let symbol = {
        let nodes = program.nodes(importer.file_index());
        let source_file_like = get_source_file_like_for_import_declaration(importer, &nodes);
        nodes[source_file_like].symbol()
    };
    symbol.map(|s| checker.get_merged_symbol(s))
}

/// `findNamespaceReExports`.
/// Returns 'true' if the namespace 'name' is re-exported from this module,
/// and 'false' if it is only used locally.
fn find_namespace_re_exports(
    program: &Rc<Program>,
    source_file_like: NodeId,
    name: Option<NodeId>,
    checker: &mut Checker,
) -> bool {
    let Some(name) = name else {
        return false;
    };
    let Some(namespace_import_symbol) = checker.get_symbol_at_location_api(name) else {
        return false;
    };
    for_each_possible_import_or_export_statement(
        program,
        source_file_like,
        &mut |statement| {
            let nodes = program.nodes(statement.file_index());
            if !ast::is_export_declaration(&nodes[statement]) {
                return false;
            }
            let export_clause = nodes[statement].as_export_declaration().export_clause;
            let module_specifier = nodes[statement].module_specifier();
            if module_specifier.is_some() {
                return false;
            }
            let Some(export_clause) = export_clause else {
                return false;
            };
            if !ast::is_named_exports(&nodes[export_clause]) {
                return false;
            }
            let elements = nodes[export_clause].elements().map(|e| e.to_vec());
            let Some(elements) = elements else {
                return false;
            };
            drop(nodes);
            elements.into_iter().any(|element| {
                checker.get_export_specifier_local_target_symbol(element)
                    == Some(namespace_import_symbol)
            })
        },
    )
}

/// `getSearchesFromDirectImports`.
fn get_searches_from_direct_imports(
    program: &Rc<Program>,
    direct_imports: &[NodeId],
    export_symbol: SymbolId,
    export_kind: ExportKind,
    checker: &mut Checker,
    is_for_rename: bool,
) -> (Vec<LocationAndSymbol>, Vec<NodeId>) {
    let mut import_searches: Vec<LocationAndSymbol> = Vec::new();
    let mut single_references: Vec<NodeId> = Vec::new();

    let export_symbol_name = checker.symbol_arena.get_ref(export_symbol)
        .name
        .clone();

    let is_name_match = |name: &str| -> bool {
        // Use name of "default" even in `export =` case because we may have allowSyntheticDefaultImports
        name == export_symbol_name.as_ref()
            || (export_kind != ExportKind::Named
                && name == ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT)
    };

    // `import x = require("./x")` or `import * as x from "./x"`.
    // An `export =` may be imported by this syntax, so it may be a direct import.
    // If it's not a direct import, it will be in `indirectUsers`, so we don't have to do anything here.
    macro_rules! handle_namespace_import_like {
        ($import_name:expr) => {{
            let import_name: NodeId = $import_name;
            // Don't rename an import that already has a different name than the export.
            let text = {
                let nodes = program.nodes(import_name.file_index());
                nodes[import_name].text(&nodes).into_owned()
            };
            if export_kind == ExportKind::ExportEquals
                && (!is_for_rename || is_name_match(&text))
            {
                let symbol = checker.get_symbol_at_location_api(import_name);
                import_searches.push(LocationAndSymbol {
                    import_location: import_name,
                    import_symbol: symbol,
                });
            }
        }};
    }

    // `searchForNamedImport`
    let search_for_named_import = |named_bindings: Option<NodeId>,
                                       import_searches: &mut Vec<LocationAndSymbol>,
                                       single_references: &mut Vec<NodeId>,
                                       checker: &mut Checker| {
        let Some(named_bindings) = named_bindings else {
            return;
        };
        let elements = {
            let nodes = program.nodes(named_bindings.file_index());
            nodes[named_bindings]
                .elements()
                .map(|e| e.to_vec())
                .unwrap_or_default()
        };
        for element in elements {
            let (name, property_name, is_export_specifier) = {
                let nodes = program.nodes(element.file_index());
                (
                    nodes[element].name(),
                    nodes[element].property_name(),
                    ast::is_export_specifier(&nodes[element]),
                )
            };
            let text_node = property_name.or(name);
            let text = {
                let Some(t) = text_node else { continue };
                let nodes = program.nodes(t.file_index());
                nodes[t].text(&nodes).into_owned()
            };
            if !is_name_match(&text) {
                continue;
            }
            if let Some(property_name) = property_name {
                // This is `import { foo as bar } from "./a"` or `export { foo as bar } from "./a"`. `foo` isn't a local in the file, so just add it as a single reference.
                single_references.push(property_name);
                // If renaming `{ foo as bar }`, don't touch `bar`, just `foo`.
                // But do rename `foo` in ` { default as foo }` if that's the original export name.
                let name_text = {
                    let Some(name) = name else { continue };
                    let nodes = program.nodes(name.file_index());
                    nodes[name].text(&nodes).into_owned()
                };
                if !is_for_rename || name_text == export_symbol_name.as_ref() {
                    // Search locally for `bar`.
                    if let Some(name) = name {
                        let symbol = checker.get_symbol_at_location_api(name);
                        import_searches.push(LocationAndSymbol {
                            import_location: name,
                            import_symbol: symbol,
                        });
                    }
                }
            } else {
                // PORT: this else-branch means `propertyName == nil`, so Go's
                // `IsExportSpecifier(element) && element.PropertyName() != nil`
                // check is always false — always `GetSymbolAtLocation(name)`.
                let _ = is_export_specifier;
                let local_symbol =
                    name.and_then(|name| checker.get_symbol_at_location_api(name));
                if let Some(name) = name {
                    import_searches.push(LocationAndSymbol {
                        import_location: name,
                        import_symbol: local_symbol,
                    });
                }
            }
        }
    };

    // `handleImport`
    for &decl in direct_imports {
        let nodes = program.nodes(decl.file_index());
        // `IsImportEqualsDeclaration`
        if ast::is_import_equals_declaration(&nodes[decl]) {
            if is_external_module_import_equals(decl, &nodes) {
                if let Some(name) = nodes[decl].name() {
                    let name = name;
                    drop(nodes);
                    handle_namespace_import_like!(name);
                }
            }
            continue;
        }
        if ast::is_identifier(&nodes[decl]) {
            drop(nodes);
            handle_namespace_import_like!(decl);
            continue;
        }
        if ast::is_import_type_node(&nodes[decl]) {
            let import_type = nodes[decl].as_import_type_node();
            if let Some(qualifier) = import_type.qualifier {
                let first_identifier = ast::get_first_identifier(qualifier, &nodes);
                let text = nodes[first_identifier].text(&nodes).into_owned();
                if text == export_symbol_name.as_ref() {
                    single_references.push(first_identifier);
                }
            } else if export_kind == ExportKind::ExportEquals {
                if let Some(argument) = import_type.argument {
                    if let Some(literal) = nodes[argument].as_literal_type_node().literal {
                        single_references.push(literal);
                    }
                }
            }
            continue;
        }
        // Ignore if there's a grammar error
        let module_specifier = nodes[decl].module_specifier();
        if !module_specifier.is_some_and(|m| ast::is_string_literal(&nodes[m])) {
            continue;
        }
        if ast::is_export_declaration(&nodes[decl]) {
            let export_clause = nodes[decl].as_export_declaration().export_clause;
            if let Some(export_clause) = export_clause {
                if ast::is_named_exports(&nodes[export_clause]) {
                    drop(nodes);
                    search_for_named_import(
                        Some(export_clause),
                        &mut import_searches,
                        &mut single_references,
                        checker,
                    );
                }
            }
            continue;
        }
        if let Some(import_clause) = nodes[decl].import_clause() {
            let named_bindings = nodes[import_clause].as_import_clause().named_bindings;
            if let Some(named_bindings) = named_bindings {
                match nodes[named_bindings].kind {
                    Kind::NamespaceImport => {
                        if let Some(name) = nodes[named_bindings].name() {
                            drop(nodes);
                            handle_namespace_import_like!(name);
                        } else {
                            drop(nodes);
                        }
                    }
                    Kind::NamedImports => {
                        // 'default' might be accessed as a named import `{ default as foo }`.
                        if export_kind == ExportKind::Named
                            || export_kind == ExportKind::Default
                        {
                            drop(nodes);
                            search_for_named_import(
                                Some(named_bindings),
                                &mut import_searches,
                                &mut single_references,
                                checker,
                            );
                        } else {
                            drop(nodes);
                        }
                    }
                    _ => {
                        drop(nodes);
                    }
                }
            }
            // `export =` might be imported by a default import if `--allowSyntheticDefaultImports` is on, so this handles both ExportKind.Default and ExportKind.ExportEquals.
            // If a default import has the same name as the default export, allow to rename it.
            // Given `import f` and `export default function f`, we will rename both, but for `import g` we will rename just that.
            let nodes = program.nodes(decl.file_index());
            if let Some(name) = nodes[import_clause].name() {
                if export_kind == ExportKind::Default
                    || export_kind == ExportKind::ExportEquals
                {
                    let name_text = nodes[name].text(&nodes).into_owned();
                    let no_default = symbol_name_no_default(
                        program,
                        checker,
                        export_symbol,
                    );
                    if !is_for_rename || name_text == no_default {
                        drop(nodes);
                        let default_import_alias =
                            checker.get_symbol_at_location_api(name);
                        import_searches.push(LocationAndSymbol {
                            import_location: name,
                            import_symbol: default_import_alias,
                        });
                    }
                }
            }
        }
    }
    (import_searches, single_references)
}

/// `getImportOrExportSymbol`.
pub(crate) fn get_import_or_export_symbol(
    program: &Rc<Program>,
    node: NodeId,
    symbol: SymbolId,
    checker: &mut Checker,
    coming_from_export: bool,
) -> Option<ImportExportSymbol> {
    let result = get_export(program, node, symbol, checker, coming_from_export);
    if result.is_some() || coming_from_export {
        return result;
    }

    // `getImport`
    let nodes = program.nodes(node.file_index());
    if !is_node_import(node, &nodes) {
        return None;
    }
    let (symbol_flags, symbol_name) = {
        let arena = checker.symbol_arena.clone();
        let sym = &arena[symbol.index()];
        (sym.flags, sym.name.clone())
    };
    // JS destructuring from `require(...)` is import-like for references, but the binding element
    // itself is still a local variable symbol rather than an alias.
    let imported_symbol = if symbol_flags.intersects(SymbolFlags::ALIAS) {
        checker.get_immediate_aliased_symbol(symbol)
    } else {
        crate::utilities::get_property_symbol_of_object_binding_pattern_without_property_name(
            symbol, checker,
        )
    };
    let Some(imported_symbol) = imported_symbol else {
        return None;
    };
    // Search on the local symbol in the exporting module, not the exported symbol.
    let imported_symbol = skip_export_specifier_symbol(program, imported_symbol, checker);
    let Some(imported_symbol) = imported_symbol else {
        return None;
    };
    // Similarly, skip past the symbol for 'export ='
    let imported_symbol = {
        let name = checker.symbol_arena.get_ref(imported_symbol)
            .name
            .clone();
        if name.as_ref() == "export=" {
            get_export_equals_local_symbol(program, imported_symbol, checker)?
        } else {
            imported_symbol
        }
    };
    // If the import has a different name than the export, do not continue searching.
    // If `importedName` is undefined, do continue searching as the export is anonymous.
    // (All imports returned from this function will be ignored anyway if we are in rename and this is a not a named export.)
    let imported_name = symbol_name_no_default(program, checker, imported_symbol);
    if imported_name.is_empty()
        || imported_name == ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT
        || imported_name == symbol_name.as_ref()
    {
        return Some(ImportExportSymbol {
            kind: ImpExpKind::Import,
            symbol: imported_symbol,
            export_info: None,
        });
    }
    None
}

/// `exportInfo` closure inside `getImportOrExportSymbol`.
fn export_info_result(
    symbol: SymbolId,
    kind: ExportKind,
    checker: &mut Checker,
) -> Option<ImportExportSymbol> {
    get_export_info(symbol, kind, checker).map(|export_info| ImportExportSymbol {
        kind: ImpExpKind::Export,
        symbol,
        export_info: Some(Rc::new(export_info)),
    })
}

/// `getExportAssignmentExport` — get the symbol for the `export =` node; its
/// parent is the module it's the export of.
fn get_export_assignment_export(
    nodes: &[Node],
    ex: NodeId,
    symbol: SymbolId,
    checker: &mut Checker,
) -> Option<ImportExportSymbol> {
    let ex_symbol = nodes[ex].symbol()?;
    let exporting_module_symbol =
        checker.symbol_arena.get_ref(ex_symbol).parent?;
    let export_kind = if nodes[ex].as_export_assignment().is_export_equals {
        ExportKind::ExportEquals
    } else {
        ExportKind::Default
    };
    Some(ImportExportSymbol {
        kind: ImpExpKind::Export,
        symbol,
        export_info: Some(Rc::new(ExportInfo {
            exporting_module_symbol,
            export_kind,
        })),
    })
}

/// `getExportKindForDeclaration` — not meant for use with export specifiers
/// or export assignment.
fn get_export_kind_for_declaration(node: NodeId, nodes: &[Node]) -> ExportKind {
    if ast::has_syntactic_modifier(&nodes[node], ModifierFlags::DEFAULT) {
        return ExportKind::Default;
    }
    ExportKind::Named
}

/// `getSpecialPropertyExport`.
fn get_special_property_export(
    node: NodeId,
    use_lhs_symbol: bool,
    symbol: SymbolId,
    nodes: &[Node],
    checker: &mut Checker,
) -> Option<ImportExportSymbol> {
    let kind = match ast::get_assignment_declaration_kind(node, nodes) {
        ast::JsDeclarationKind::ExportsProperty => ExportKind::Named,
        ast::JsDeclarationKind::ModuleExports => ExportKind::ExportEquals,
        _ => return None,
    };
    let sym = if use_lhs_symbol {
        nodes[node].symbol()?
    } else {
        symbol
    };
    export_info_result(sym, kind, checker)
}

/// `getExport` closure inside `getImportOrExportSymbol`.
fn get_export(
    program: &Rc<Program>,
    node: NodeId,
    symbol: SymbolId,
    checker: &mut Checker,
    coming_from_export: bool,
) -> Option<ImportExportSymbol> {
    let nodes = program.nodes(node.file_index());
    let export_symbol = checker.symbol_arena.get_ref(symbol).export_symbol;
    let parent = nodes[node].parent?;
    let grandparent = nodes[parent].parent;
    if let Some(export_symbol) = export_symbol {
        if ast::is_property_access_expression(&nodes[parent]) {
            // When accessing an export of a JS module, there's no alias. The symbol will still be flagged as an export even though we're at the use.
            // So check that we are at the declaration.
            let in_binary_and_declared = grandparent.is_some_and(|gp| {
                ast::is_binary_expression(&nodes[gp])
                    && checker.symbol_arena.get_ref(symbol)
                        .declarations
                        .contains(&parent)
            });
            if in_binary_and_declared {
                return get_special_property_export(
                    grandparent.expect("grandparent"),
                    false, /*useLhsSymbol*/
                    symbol,
                    &nodes,
                    checker,
                );
            }
            return None;
        }
        return export_info_result(
            export_symbol,
            get_export_kind_for_declaration(parent, &nodes),
            checker,
        );
    }
    let export_node = get_export_node(parent, node, &nodes);
    if let Some(export_node) = export_node {
        if ast::has_syntactic_modifier(&nodes[export_node], ModifierFlags::EXPORT)
            || ast::is_implicitly_exported_js_doc_declaration(&nodes[export_node], &nodes)
        {
            if ast::is_import_equals_declaration(&nodes[export_node])
                && nodes[export_node]
                    .as_import_equals_declaration()
                    .module_reference
                    == Some(node)
            {
                // We're at `Y` in `export import X = Y`. This is not the exported symbol, the left-hand-side is. So treat this as an import statement.
                if coming_from_export {
                    return None;
                }
                let name = nodes[export_node].name()?;
                let lhs_symbol = checker.get_symbol_at_location_api(name)?;
                return Some(ImportExportSymbol {
                    kind: ImpExpKind::Import,
                    symbol: lhs_symbol,
                    export_info: None,
                });
            }
            let kind = get_export_kind_for_declaration(export_node, &nodes);
            return export_info_result(symbol, kind, checker);
        }
    }
    if ast::is_namespace_export(&nodes[parent]) {
        return export_info_result(symbol, ExportKind::Named, checker);
    }
    if ast::is_export_assignment(&nodes[parent]) {
        return get_export_assignment_export(&nodes, parent, symbol, checker);
    }
    if let Some(gp) = grandparent {
        if ast::is_export_assignment(&nodes[gp]) {
            return get_export_assignment_export(&nodes, gp, symbol, checker);
        }
    }
    if ast::is_binary_expression(&nodes[parent]) {
        return get_special_property_export(parent, true /*useLhsSymbol*/, symbol, &nodes, checker);
    }
    if let Some(gp) = grandparent {
        if ast::is_binary_expression(&nodes[gp]) {
            return get_special_property_export(
                gp, true, /*useLhsSymbol*/
                symbol, &nodes, checker,
            );
        }
    }
    if ast::is_js_doc_typedef_tag(&nodes[parent])
        || ast::is_js_doc_callback_tag(&nodes[parent])
    {
        return export_info_result(symbol, ExportKind::Named, checker);
    }
    None
}

/// `getExportInfo`.
pub(crate) fn get_export_info(
    export_symbol: SymbolId,
    export_kind: ExportKind,
    c: &mut Checker,
) -> Option<ExportInfo> {
    // Parent can be nil if an `export` is not at the top-level (which is a compile error).
    let parent = c.symbol_arena.get_ref(export_symbol).parent;
    if let Some(parent) = parent {
        let exporting_module_symbol = c.get_merged_symbol(parent);
        // `export` may appear in a namespace. In that case, just rely on global search.
        if tsc_checker::utilities::is_external_module_symbol(exporting_module_symbol, c) {
            return Some(ExportInfo {
                exporting_module_symbol,
                export_kind,
            });
        }
    }
    None
}

/// `getExportNode`.
/// If a reference is a class expression, the exported node would be its parent.
/// If a reference is a variable declaration, the exported node would be the variable statement.
fn get_export_node(parent: NodeId, node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let declaration = if ast::is_variable_declaration(&nodes[parent]) {
        Some(parent)
    } else if ast::is_binding_element(&nodes[parent]) {
        ast::walk_up_binding_elements_and_patterns(parent, nodes)
    } else {
        None
    };
    if let Some(declaration) = declaration {
        let decl_parent = nodes[declaration].parent;
        let grandparent = decl_parent.and_then(|p| nodes[p].parent);
        if nodes[parent].name() == Some(node)
            && !decl_parent.is_some_and(|p| ast::is_catch_clause(&nodes[p]))
            && grandparent.is_some_and(|gp| ast::is_variable_statement(&nodes[gp]))
        {
            return grandparent;
        }
        return None;
    }
    Some(parent)
}

/// `isNodeImport`.
fn is_node_import(node: NodeId, nodes: &[Node]) -> bool {
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    match nodes[parent].kind {
        Kind::ImportEqualsDeclaration => {
            nodes[parent].name() == Some(node)
                && is_external_module_import_equals(parent, nodes)
        }
        Kind::ImportSpecifier => {
            // For a rename import `{ foo as bar }`, don't search for the imported symbol. Just find local uses of `bar`.
            nodes[parent].property_name().is_none()
        }
        Kind::ImportClause | Kind::NamespaceImport => {
            debug_assert!(nodes[parent].name() == Some(node));
            true
        }
        Kind::BindingElement => {
            ast::is_in_js_file(Some(node), nodes)
                && nodes[parent]
                    .parent
                    .and_then(|p| nodes[p].parent)
                    .is_some_and(|gp| {
                        ast::is_variable_declaration_initialized_to_bare_or_accessed_require(
                            gp, nodes,
                        )
                    })
        }
        _ => false,
    }
}

/// `isExternalModuleImportEquals`.
fn is_external_module_import_equals(node: NodeId, nodes: &[Node]) -> bool {
    let module_reference = nodes[node]
        .as_import_equals_declaration()
        .module_reference;
    module_reference.is_some_and(|m| {
        ast::is_external_module_reference(&nodes[m])
            && nodes[m]
                .expression()
                .is_some_and(|e| nodes[e].kind == Kind::StringLiteral)
    })
}

/// `skipExportSpecifierSymbol`.
/// If at an export specifier, go to the symbol it refers to.
fn skip_export_specifier_symbol(
    program: &Rc<Program>,
    symbol: SymbolId,
    checker: &mut Checker,
) -> Option<SymbolId> {
    // For `export { foo } from './bar", there's nothing to skip, because it does not create a new alias. But `export { foo } does.
    let declarations = checker.symbol_arena.get_ref(symbol)
        .declarations
        .clone();
    for declaration in declarations {
        let nodes = program.nodes(declaration.file_index());
        if ast::is_export_specifier(&nodes[declaration])
            && nodes[declaration].property_name().is_none()
            && nodes[declaration]
                .parent
                .and_then(|p| nodes[p].parent)
                .and_then(|gp| nodes[gp].module_specifier())
                .is_none()
        {
            return Some(
                checker
                    .get_export_specifier_local_target_symbol(declaration)
                    .unwrap_or(symbol),
            );
        }
        if ast::is_property_access_expression(&nodes[declaration]) {
            let expr = nodes[declaration].expression();
            let name = nodes[declaration].name();
            if let (Some(expr), Some(name)) = (expr, name) {
                if ast::is_module_exports_access_expression(&nodes[expr], &nodes)
                    && !ast::is_private_identifier(&nodes[name])
                {
                    // Export of form 'module.exports.propName = expr';
                    drop(nodes);
                    return checker.get_symbol_at_location_api(declaration);
                }
            }
        }
        if ast::is_shorthand_property_assignment(&nodes[declaration]) {
            let grandparent = nodes[declaration]
                .parent
                .and_then(|p| nodes[p].parent);
            if let Some(gp) = grandparent {
                if ast::is_binary_expression(&nodes[gp])
                    && ast::get_assignment_declaration_kind(gp, &nodes)
                        == ast::JsDeclarationKind::ModuleExports
                {
                    if let Some(name) = nodes[declaration].name() {
                        drop(nodes);
                        return checker.get_export_specifier_local_target_symbol(name);
                    }
                }
            }
        }
    }
    Some(symbol)
}

/// `getExportEqualsLocalSymbol`.
fn get_export_equals_local_symbol(
    program: &Rc<Program>,
    imported_symbol: SymbolId,
    checker: &mut Checker,
) -> Option<SymbolId> {
    if checker.symbol_arena.get_ref(imported_symbol)
        .flags
        .intersects(SymbolFlags::ALIAS)
    {
        return checker.get_immediate_aliased_symbol(imported_symbol);
    }
    let decl = checker.symbol_arena.get_ref(imported_symbol).value_declaration;
    let decl = decl.expect("value declaration");
    let nodes = program.nodes(decl.file_index());
    if ast::is_export_assignment(&nodes[decl]) {
        return nodes[decl].expression().and_then(|e| nodes[e].symbol());
    }
    if ast::is_binary_expression(&nodes[decl]) {
        return nodes[decl]
            .as_binary_expression()
            .right
            .and_then(|r| nodes[r].symbol());
    }
    if ast::is_source_file(&nodes[decl]) {
        return nodes[decl].symbol();
    }
    None
}

/// `symbolNameNoDefault`.
fn symbol_name_no_default(
    program: &Rc<Program>,
    checker: &mut Checker,
    symbol: SymbolId,
) -> String {
    let (name, declarations) = {
        let arena = checker.symbol_arena.clone();
        let sym = &arena[symbol.index()];
        (sym.name.to_string(), sym.declarations.clone())
    };
    if name != ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT {
        return name;
    }
    for decl in declarations {
        let nodes = program.nodes(decl.file_index());
        if let Some(name) = ast::get_name_of_declaration(Some(decl), &nodes) {
            if ast::is_identifier(&nodes[name]) {
                return nodes[name].text(&nodes).into_owned();
            }
        }
    }
    String::new()
}

/// `findModuleReferences` — finds all references to a module symbol across the
/// given source files. This includes import statements, `<reference>`
/// directives, and implicit references (e.g., JSX runtime imports).
pub(crate) fn find_module_references(
    program: &Rc<Program>,
    source_files: &[NodeId],
    search_module_symbol: SymbolId,
    checker: &mut Checker,
) -> Vec<ModuleReference> {
    let mut refs: Vec<ModuleReference> = Vec::new();
    let search_source_file = checker.symbol_arena.get_ref(search_module_symbol)
        .value_declaration;

    for &referencing_file in source_files {
        if let Some(search_source_file) = search_source_file {
            let is_source_file = {
                let nodes = program.nodes(search_source_file.file_index());
                nodes[search_source_file].kind == Kind::SourceFile
            };
            if is_source_file {
                // Check <reference path> directives
                let (referenced_files, type_reference_directives) = {
                    let nodes = program.nodes(referencing_file.file_index());
                    let sf = nodes[referencing_file].as_source_file();
                    (
                        sf.referenced_files.clone(),
                        sf.type_reference_directives.clone(),
                    )
                };
                for file_ref in &referenced_files {
                    if program.get_source_file_from_reference(referencing_file, file_ref)
                        == Some(search_source_file)
                    {
                        refs.push(ModuleReference {
                            kind: ModuleReferenceKind::Reference,
                            referencing_file: Some(referencing_file),
                            literal: None,
                            file_ref: Some(file_ref.clone()),
                        });
                    }
                }

                // Check <reference types> directives
                let search_file_name = {
                    let nodes = program.nodes(search_source_file.file_index());
                    nodes[search_source_file]
                        .as_source_file()
                        .file_name()
                        .clone()
                };
                for file_ref in &type_reference_directives {
                    if let Some(referenced) = program
                        .get_resolved_type_reference_directive_from_type_reference_directive(
                            file_ref,
                            referencing_file,
                        )
                    {
                        if referenced.resolved_file_name == search_file_name {
                            refs.push(ModuleReference {
                                kind: ModuleReferenceKind::Reference,
                                referencing_file: Some(referencing_file),
                                literal: None,
                                file_ref: Some(file_ref.clone()),
                            });
                        }
                    }
                }
            }
        }

        // Check all imports (including require() calls)
        let pairs = collect_import_pairs(program, referencing_file);
        for (import_decl, module_specifier) in pairs {
            let module_symbol = checker.get_symbol_at_location_api(module_specifier);
            if module_symbol == Some(search_module_symbol) {
                let is_synthesized = {
                    let nodes = program.nodes(import_decl.file_index());
                    ast::node_is_synthesized(&nodes[import_decl])
                };
                if is_synthesized {
                    refs.push(ModuleReference {
                        kind: ModuleReferenceKind::Implicit,
                        literal: Some(module_specifier),
                        referencing_file: Some(referencing_file),
                        file_ref: None,
                    });
                } else {
                    refs.push(ModuleReference {
                        kind: ModuleReferenceKind::Import,
                        literal: Some(module_specifier),
                        referencing_file: None,
                        file_ref: None,
                    });
                }
            }
        }
    }

    refs
}
