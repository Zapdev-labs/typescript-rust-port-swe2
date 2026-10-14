// Ported from tsc/internal/ls/callhierarchy.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `*ast.Node` → `NodeId`; `*ast.Symbol` → `SymbolId`; `*checker.Checker`
//   → `&Rc<RefCell<Checker>>`. `resolveCallHierarchyDeclaration`'s `any`
//   result (`*ast.Node` | `[]*ast.Node`) → `ResolvedCallHierarchyDeclarations`.
// - `getSymbolKindFromNode` is private in `symbols.rs`; a faithful copy lives
//   here.
// - `moveRangePastModifiers` is a local helper (the only other copy lives in
//   the transformers crate).
// - `incomingEntry`/`sync.Once` are unnecessary: Go only needed a lazily
//   computed `HasTextDocumentPosition`; the Rust `handle_cross_project` takes
//   `(uri, position)` directly, so both are computed eagerly up front.
// - `collections.Set[lsproto.Location]`/`map[lsproto.Location]T` dedup uses
//   `Vec::contains`/`Vec::position` — `lsproto::Location` is `PartialEq` but
//   not `Hash` (same adaptation as `combine_location_array`).
// - `handleCrossProject`'s `symbolAndEntriesToIncomingCalls` parameter
//   (`params *incomingEntry`) is unused by the callee in Go, so the closure
//   here does not carry it.
// - All `program.nodes(file_index)` snapshots are `Rc<Vec<Node>>`, so the
//   file-arena of each visited node is fetched locally at every step (nodes
//   from other files — e.g. `symbol.value_declaration` — use their own arena).

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use tsc_ast::{self as ast, JsDeclarationKind, Kind, ModifierFlags, Node, NodeFlags, NodeId, SymbolId};
use tsc_astnav::tokens;
use tsc_checker::checker_core::Checker;
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::text::{TextPos, TextRange};
use tsc_lsconv::converters::{file_name_to_document_uri, source_file_script};
use tsc_lsproto::{self as lsproto, SymbolKind};
use tsc_printer::{
    EmitContext, EmitTextWriter, PrintHandlers, Printer, PrinterOptions,
    get_single_line_string_writer,
};
use tsc_scanner::scanner::{
    SkipTriviaOptions, get_token_pos_of_node, skip_trivia, skip_trivia_ex,
};
use tsc_spanmap::Feature;
use tsc_tspath::RootedFilePath;

use crate::api::Error;
use crate::crossproject::combine_incoming_calls;
use crate::definition::lsp_range_contains;
use crate::findallreferences::{
    CrossProjectOrchestrator, EntryKind, ReferenceEntry, SymbolAndEntriesData,
    SymbolEntryTransformOptions,
};
use crate::languageservice::LanguageService;

/// `type CallHierarchyDeclaration = *ast.Node`.
type CallHierarchyDeclaration = NodeId;

/// `resolveCallHierarchyDeclaration`'s `any` result — `*ast.Node` or
/// `[]*ast.Node`.
enum ResolvedCallHierarchyDeclarations {
    Single(CallHierarchyDeclaration),
    Multiple(Vec<CallHierarchyDeclaration>),
}

/// `type callSite struct`.
struct CallSite {
    /// `declaration`.
    declaration: NodeId,
    /// `textRange`.
    text_range: TextRange,
    /// `sourceFile`.
    source_file: NodeId,
}

/// `isNamedExpression` — indicates whether a node is a named function or
/// class expression.
fn is_named_expression(node: Option<NodeId>, nodes: &[Node]) -> bool {
    let Some(node) = node else { return false };
    if !ast::is_function_expression(&nodes[node]) && !ast::is_class_expression(&nodes[node]) {
        return false;
    }
    nodes[node]
        .name()
        .is_some_and(|name| ast::is_identifier(&nodes[name]))
}

/// `isVariableLike`.
fn is_variable_like(node: Option<NodeId>, nodes: &[Node]) -> bool {
    let Some(node) = node else { return false };
    ast::is_property_declaration(&nodes[node]) || ast::is_variable_declaration(&nodes[node])
}

/// `isAssignedExpression` — indicates whether a node is a function, arrow, or
/// class expression assigned to a constant variable or class property.
fn is_assigned_expression(node: Option<NodeId>, nodes: &[Node]) -> bool {
    let Some(node) = node else { return false };
    if !(ast::is_function_expression(&nodes[node])
        || ast::is_arrow_function(&nodes[node])
        || ast::is_class_expression(&nodes[node]))
    {
        return false;
    }
    if nodes[node].name().is_some() {
        return false;
    }
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    if !is_variable_like(Some(parent), nodes) {
        return false;
    }

    if nodes[parent].initializer() != Some(node) {
        return false;
    }

    let Some(name) = nodes[parent].name() else {
        return false;
    };
    if !ast::is_identifier(&nodes[name]) {
        return false;
    }

    ast::get_combined_node_flags(parent, nodes).intersects(NodeFlags::CONST)
        || ast::is_property_declaration(&nodes[parent])
}

/// `isPossibleCallHierarchyDeclaration` — indicates whether a node could
/// possibly be a call hierarchy declaration.
///
/// See `resolve_call_hierarchy_declaration` for the specific rules.
fn is_possible_call_hierarchy_declaration(node: Option<NodeId>, nodes: &[Node]) -> bool {
    let Some(node) = node else { return false };
    ast::is_source_file(&nodes[node])
        || ast::is_module_declaration(&nodes[node])
        || ast::is_function_declaration(&nodes[node])
        || ast::is_function_expression(&nodes[node])
        || ast::is_class_declaration(&nodes[node])
        || ast::is_class_expression(&nodes[node])
        || ast::is_class_static_block_declaration(&nodes[node])
        || ast::is_method_declaration(&nodes[node])
        || ast::is_method_signature_declaration(&nodes[node])
        || ast::is_get_accessor_declaration(&nodes[node])
        || ast::is_set_accessor_declaration(&nodes[node])
}

/// `isValidCallHierarchyDeclaration` — indicates whether a node is a valid
/// call hierarchy declaration.
///
/// See `resolve_call_hierarchy_declaration` for the specific rules.
fn is_valid_call_hierarchy_declaration(node: Option<NodeId>, nodes: &[Node]) -> bool {
    let Some(node) = node else { return false };

    if ast::is_source_file(&nodes[node]) {
        return true;
    }

    if ast::is_module_declaration(&nodes[node]) {
        return nodes[node]
            .name()
            .is_some_and(|name| ast::is_identifier(&nodes[name]));
    }

    ast::is_function_declaration(&nodes[node])
        || ast::is_class_declaration(&nodes[node])
        || ast::is_class_static_block_declaration(&nodes[node])
        || ast::is_method_declaration(&nodes[node])
        || ast::is_method_signature_declaration(&nodes[node])
        || ast::is_get_accessor_declaration(&nodes[node])
        || ast::is_set_accessor_declaration(&nodes[node])
        || is_named_expression(Some(node), nodes)
        || is_assigned_expression(Some(node), nodes)
}

/// `getCallHierarchyDeclarationReferenceNode` — gets the node that can be
/// used as a reference to a call hierarchy declaration.
fn get_call_hierarchy_declaration_reference_node(
    node: Option<NodeId>,
    nodes: &[Node],
) -> Option<NodeId> {
    let node = node?;

    if ast::is_source_file(&nodes[node]) {
        return Some(node);
    }

    if let Some(name) = nodes[node].name() {
        return Some(name);
    }

    if is_assigned_expression(Some(node), nodes) {
        return nodes[nodes[node].parent?].name();
    }

    if let Some(modifiers) = nodes[node].modifiers() {
        for &mod_ in &modifiers.nodes {
            if nodes[mod_].kind == Kind::DefaultKeyword {
                return Some(mod_);
            }
        }
    }

    None
}

/// `getSymbolOfCallHierarchyDeclaration` — gets the symbol for a call
/// hierarchy declaration.
fn get_symbol_of_call_hierarchy_declaration(
    c: &Rc<RefCell<Checker>>,
    program: &Rc<Program>,
    node: NodeId,
) -> Option<SymbolId> {
    let location = {
        let nodes = program.nodes(node.file_index());
        if ast::is_class_static_block_declaration(&nodes[node]) {
            return None;
        }
        get_call_hierarchy_declaration_reference_node(Some(node), &nodes)?
    };
    c.borrow_mut().get_symbol_at_location_api(location)
}

/// `moveRangePastModifiers`.
fn move_range_past_modifiers(node: NodeId, nodes: &[Node]) -> TextRange {
    if let Some(modifiers) = nodes[node].modifiers() {
        if let Some(&last_mod) = modifiers.nodes.last() {
            return TextRange::new(nodes[last_mod].end(), nodes[node].end());
        }
    }
    TextRange::new(nodes[node].pos(), nodes[node].end())
}

/// `getCallHierarchyItemName` — gets the text and range for the name of a
/// call hierarchy declaration.
fn get_call_hierarchy_item_name(
    program: &Rc<Program>,
    node: NodeId,
) -> (String, TextPos, TextPos) {
    let nodes = program.nodes(node.file_index());

    if ast::is_source_file(&nodes[node]) {
        let file_name = nodes[node].as_source_file().file_name().as_string().to_string();
        return (file_name, 0, 0);
    }

    if (ast::is_function_declaration(&nodes[node]) || ast::is_class_declaration(&nodes[node]))
        && nodes[node].name().is_none()
    {
        if let Some(modifiers) = nodes[node].modifiers() {
            for &mod_ in &modifiers.nodes {
                if nodes[mod_].kind == Kind::DefaultKeyword {
                    let source_file =
                        ast::get_source_file_of_node(Some(node), &nodes).unwrap_or(node);
                    let start = skip_trivia(
                        nodes[source_file].as_source_file().text(),
                        nodes[mod_].pos(),
                    );
                    return ("default".to_string(), start, nodes[mod_].end());
                }
            }
        }
    }

    if ast::is_class_static_block_declaration(&nodes[node]) {
        let source_file = ast::get_source_file_of_node(Some(node), &nodes).unwrap_or(node);
        let pos = skip_trivia(
            nodes[source_file].as_source_file().text(),
            move_range_past_modifiers(node, &nodes).pos(),
        );
        let end = pos + 6; // "static".length
        let (c, done) = program.get_type_checker_for_file(Context::background(), source_file);
        let symbol = nodes[node]
            .parent
            .and_then(|p| c.borrow_mut().get_symbol_at_location_api(p));
        let mut prefix = String::new();
        if let Some(symbol) = symbol {
            prefix = format!("{} ", c.borrow_mut().symbol_to_string(symbol));
        }
        done();
        return (format!("{prefix}static {{}}"), pos, end);
    }

    let decl_name = if is_assigned_expression(Some(node), &nodes) {
        nodes[node].parent.and_then(|p| nodes[p].name())
    } else {
        ast::get_name_of_declaration(Some(node), &nodes)
    };

    if decl_name.is_none() || !ast::node_is_present(decl_name, &nodes) {
        let source_file = ast::get_source_file_of_node(Some(node), &nodes).unwrap_or(node);
        if ast::is_function_declaration(&nodes[node])
            || ast::is_function_expression(&nodes[node])
        {
            let kw_pos = skip_trivia(
                nodes[source_file].as_source_file().text(),
                move_range_past_modifiers(node, &nodes).pos(),
            );
            return ("(anonymous)".to_string(), kw_pos, kw_pos + 8); // "function".length
        }
        if ast::is_class_declaration(&nodes[node]) || ast::is_class_expression(&nodes[node]) {
            let kw_pos = skip_trivia(
                nodes[source_file].as_source_file().text(),
                move_range_past_modifiers(node, &nodes).pos(),
            );
            return ("(anonymous)".to_string(), kw_pos, kw_pos + 5); // "class".length
        }
        debug_assert!(
            decl_name.is_some(),
            "Expected call hierarchy item to have a name"
        );
    }

    let decl_name = decl_name.unwrap();
    let text = get_text_of_call_hierarchy_name(program, node, decl_name, node);

    let source_file = ast::get_source_file_of_node(Some(node), &nodes).unwrap_or(node);
    let name_pos = skip_trivia(
        nodes[source_file].as_source_file().text(),
        nodes[decl_name].pos(),
    );

    (text, name_pos, nodes[decl_name].end())
}

/// `getTextOfCallHierarchyName`.
fn get_text_of_call_hierarchy_name(
    program: &Rc<Program>,
    source_node: NodeId,
    name: NodeId,
    print_node: NodeId,
) -> String {
    {
        let nodes = program.nodes(name.file_index());
        if ast::is_identifier(&nodes[name]) || ast::is_string_or_numeric_literal_like(&nodes[name])
        {
            return nodes[name].text(&nodes).into_owned();
        }
        if ast::is_computed_property_name(&nodes[name]) {
            if let Some(expr) = nodes[name].expression() {
                if ast::is_string_or_numeric_literal_like(&nodes[expr]) {
                    return nodes[expr].text(&nodes).into_owned();
                }
            }
        }
    }

    let source_file = {
        let nodes = program.nodes(source_node.file_index());
        ast::get_source_file_of_node(Some(source_node), &nodes)
    };
    let (c, done) = program.get_type_checker_for_file(
        Context::background(),
        source_file.expect("source file"),
    );
    let symbol = c.borrow_mut().get_symbol_at_location_api(name);
    if let Some(symbol) = symbol {
        let text = c.borrow_mut().symbol_to_string(symbol);
        if !text.is_empty() {
            done();
            return text;
        }
    }
    done();

    // `printer.NewPrinter(PrinterOptions{RemoveComments: true})` + `p.Write`.
    let mut emit_context = EmitContext::new();
    let mut nodes = program.nodes_mut(source_node.file_index());
    let symbols = program.symbols.clone();
    let mut writer = get_single_line_string_writer();
    {
        let mut p = Printer::new(
            PrinterOptions {
                remove_comments: true,
                ..Default::default()
            },
            PrintHandlers::default(),
            &mut emit_context,
            &mut nodes,
            &symbols,
        );
        p.write(Some(print_node), source_file, &mut writer, None);
    }
    writer.get_text()
}

/// `getCallHierarchyItemContainerName`.
fn get_call_hierarchy_item_container_name(program: &Rc<Program>, node: NodeId) -> String {
    let nodes = program.nodes(node.file_index());

    if is_assigned_expression(Some(node), &nodes) {
        let parent = nodes[node].parent.unwrap();
        if ast::is_property_declaration(&nodes[parent])
            && nodes[parent]
                .parent
                .is_some_and(|pp| ast::is_class_like(Some(pp), &nodes))
        {
            let grandparent = nodes[parent].parent.unwrap();
            if ast::is_class_expression(&nodes[grandparent]) {
                if let Some(assigned_name) = ast::get_assigned_name(grandparent, &nodes) {
                    return get_text_of_call_hierarchy_name(
                        program,
                        node,
                        assigned_name,
                        assigned_name,
                    );
                }
            } else if let Some(name) = nodes[grandparent].name() {
                return get_text_of_call_hierarchy_name(program, node, name, name);
            }
        }
        // parent.Parent.Parent.Parent is a ModuleBlock
        if let Some(module_block) = nodes[parent]
            .parent
            .and_then(|pp| nodes[pp].parent)
            .and_then(|ppp| nodes[ppp].parent)
        {
            if ast::is_module_block(&nodes[module_block]) {
                if let Some(mod_parent) = nodes[module_block].parent {
                    if ast::is_module_declaration(&nodes[mod_parent]) {
                        if let Some(name) = nodes[mod_parent].name() {
                            if ast::is_identifier(&nodes[name]) {
                                return nodes[name].text(&nodes).into_owned();
                            }
                        }
                    }
                }
            }
        }
        return String::new();
    }

    match nodes[node].kind {
        Kind::GetAccessor | Kind::SetAccessor | Kind::MethodDeclaration => {
            if let Some(parent) = nodes[node].parent {
                if nodes[parent].kind == Kind::ObjectLiteralExpression {
                    if let Some(assigned_name) = ast::get_assigned_name(parent, &nodes) {
                        return get_text_of_call_hierarchy_name(
                            program,
                            node,
                            assigned_name,
                            assigned_name,
                        );
                    }
                }
                if let Some(name) = ast::get_name_of_declaration(Some(parent), &nodes) {
                    return get_text_of_call_hierarchy_name(program, node, name, name);
                }
            }
        }
        Kind::FunctionDeclaration | Kind::ClassDeclaration | Kind::ModuleDeclaration => {
            if nodes[node]
                .parent
                .is_some_and(|p| ast::is_module_block(&nodes[p]))
            {
                let module_block = nodes[node].parent.unwrap();
                if let Some(mod_decl) = nodes[module_block].parent {
                    if ast::is_module_declaration(&nodes[mod_decl]) {
                        if let Some(name) = nodes[mod_decl].name() {
                            if ast::is_identifier(&nodes[name]) {
                                return nodes[name].text(&nodes).into_owned();
                            }
                        }
                    }
                }
            }
        }
        _ => {}
    }

    String::new()
}

/// `findImplementation` — finds the implementation of a function-like
/// declaration, if one exists.
fn find_implementation(
    c: &Rc<RefCell<Checker>>,
    program: &Rc<Program>,
    node: NodeId,
) -> Option<NodeId> {
    {
        let nodes = program.nodes(node.file_index());
        if !ast::is_function_like_declaration(Some(node), &nodes) {
            return Some(node);
        }

        if nodes[node].body().is_some() {
            return Some(node);
        }

        if ast::is_constructor_declaration(&nodes[node]) {
            let parent = nodes[node].parent?;
            return ast::get_first_constructor_with_body(&nodes[parent], &nodes);
        }
    }

    {
        let nodes = program.nodes(node.file_index());
        if ast::is_function_declaration(&nodes[node]) || ast::is_method_declaration(&nodes[node])
        {
            drop(nodes);
            let symbol = get_symbol_of_call_hierarchy_declaration(c, program, node);
            if let Some(symbol) = symbol {
                let value_declaration = c.borrow().symbol_arena.get_ref(symbol)
                    .value_declaration;
                if let Some(vd) = value_declaration {
                    let vd_nodes = program.nodes(vd.file_index());
                    if ast::is_function_like_declaration(Some(vd), &vd_nodes)
                        && vd_nodes[vd].body().is_some()
                    {
                        return Some(vd);
                    }
                }
            }
            return None;
        }
    }

    Some(node)
}

/// `findAllInitialDeclarations`.
fn find_all_initial_declarations(
    c: &Rc<RefCell<Checker>>,
    program: &Rc<Program>,
    node: NodeId,
) -> Option<Vec<NodeId>> {
    {
        let nodes = program.nodes(node.file_index());
        if ast::is_class_static_block_declaration(&nodes[node]) {
            return None;
        }
    }

    let symbol = get_symbol_of_call_hierarchy_declaration(c, program, node)?;
    let declarations = {
        let arena = c.borrow().symbol_arena.clone();
        let arena = arena.clone();
        let symbol = &arena[symbol.index()];
        if symbol.declarations.is_empty() {
            return None;
        }
        symbol.declarations.clone()
    };

    // `declKey{file, pos}` per declaration, then a stable index sort.
    let mut keys: Vec<(RootedFilePath, TextPos)> = Vec::with_capacity(declarations.len());
    for &decl in &declarations {
        let decl_nodes = program.nodes(decl.file_index());
        let file_name = ast::get_source_file_of_node(Some(decl), &decl_nodes)
            .map(|sf| decl_nodes[sf].as_source_file().file_name().clone())
            .unwrap_or_default();
        keys.push((file_name, decl_nodes[decl].pos()));
    }

    let mut indices: Vec<usize> = (0..declarations.len()).collect();
    indices.sort_by(|&a, &b| {
        keys[a]
            .0
            .compare(&keys[b].0)
            .cmp(&0)
            .then(keys[a].1.cmp(&keys[b].1))
    });

    let mut result: Vec<NodeId> = Vec::new();
    let mut last_decl_parent: Option<Option<NodeId>> = None;
    let mut last_decl_end: TextPos = 0;
    let mut has_last = false;

    for i in indices {
        let decl = declarations[i];
        let (parent, pos, end) = {
            let decl_nodes = program.nodes(decl.file_index());
            (decl_nodes[decl].parent, decl_nodes[decl].pos(), decl_nodes[decl].end())
        };
        let valid = {
            let decl_nodes = program.nodes(decl.file_index());
            is_valid_call_hierarchy_declaration(Some(decl), &decl_nodes)
        };
        if valid {
            if !has_last || last_decl_parent != Some(parent) || last_decl_end != pos {
                result.push(decl);
            }
            last_decl_parent = Some(parent);
            last_decl_end = end;
            has_last = true;
        }
    }

    if result.is_empty() {
        return None;
    }
    Some(result)
}

/// `findImplementationOrAllInitialDeclarations` — find the implementation or
/// the first declaration for a call hierarchy declaration.
fn find_implementation_or_all_initial_declarations(
    c: &Rc<RefCell<Checker>>,
    program: &Rc<Program>,
    node: NodeId,
) -> ResolvedCallHierarchyDeclarations {
    {
        let nodes = program.nodes(node.file_index());
        if ast::is_class_static_block_declaration(&nodes[node]) {
            return ResolvedCallHierarchyDeclarations::Single(node);
        }

        if ast::is_function_like_declaration(Some(node), &nodes) {
            drop(nodes);
            if let Some(impl_) = find_implementation(c, program, node) {
                return ResolvedCallHierarchyDeclarations::Single(impl_);
            }
            if let Some(decls) = find_all_initial_declarations(c, program, node) {
                return ResolvedCallHierarchyDeclarations::Multiple(decls);
            }
            return ResolvedCallHierarchyDeclarations::Single(node);
        }
    }

    if let Some(decls) = find_all_initial_declarations(c, program, node) {
        return ResolvedCallHierarchyDeclarations::Multiple(decls);
    }
    ResolvedCallHierarchyDeclarations::Single(node)
}

/// `resolveCallHierarchyDeclaration` — resolves the call hierarchy
/// declaration for a node.
///
/// A call hierarchy item must refer to either a SourceFile, Module
/// Declaration, Class Static Block, or something intrinsically callable that
/// has a name. If a call is contained in a non-named callable Node (function
/// expression, arrow function, etc.), then its containing `CallHierarchyItem`
/// is a containing function or SourceFile that matches that list.
fn resolve_call_hierarchy_declaration(
    program: &Rc<Program>,
    location: Option<NodeId>,
) -> Option<ResolvedCallHierarchyDeclarations> {
    let (c, done) = program.get_type_checker(Context::background());

    let mut following_symbol = false;
    let mut location = location;
    let mut result = None;

    while let Some(loc) = location {
        let mut early_return: Option<Option<ResolvedCallHierarchyDeclarations>> = None;
        {
            let nodes = program.nodes(loc.file_index());
            if is_valid_call_hierarchy_declaration(Some(loc), &nodes) {
                early_return = Some(Some(find_implementation_or_all_initial_declarations(
                    &c, program, loc,
                )));
            } else if is_possible_call_hierarchy_declaration(Some(loc), &nodes) {
                if let Some(ancestor) = ast::find_ancestor(Some(loc), &nodes, &mut |n, nodes| {
                    is_valid_call_hierarchy_declaration(Some(n.id), nodes)
                }) {
                    early_return = Some(Some(find_implementation_or_all_initial_declarations(
                        &c, program, ancestor,
                    )));
                }
            }

            if early_return.is_none() && ast::is_declaration_name(loc, &nodes) {
                let parent = nodes[loc].parent;
                if is_valid_call_hierarchy_declaration(parent, &nodes) {
                    early_return = Some(Some(find_implementation_or_all_initial_declarations(
                        &c,
                        program,
                        parent.unwrap(),
                    )));
                } else if is_possible_call_hierarchy_declaration(parent, &nodes) {
                    if let Some(ancestor) =
                        ast::find_ancestor(parent, &nodes, &mut |n, nodes| {
                            is_valid_call_hierarchy_declaration(Some(n.id), nodes)
                        })
                    {
                        early_return = Some(Some(find_implementation_or_all_initial_declarations(
                            &c, program, ancestor,
                        )));
                    }
                }
                if early_return.is_none() {
                    if is_variable_like(parent, &nodes) {
                        if let Some(initializer) =
                            parent.and_then(|p| nodes[p].initializer())
                        {
                            if is_assigned_expression(Some(initializer), &nodes) {
                                early_return =
                                    Some(Some(ResolvedCallHierarchyDeclarations::Single(
                                        initializer,
                                    )));
                            }
                        }
                    }
                    if early_return.is_none() {
                        early_return = Some(None);
                    }
                }
            }

            if early_return.is_none() && ast::is_constructor_declaration(&nodes[loc]) {
                let parent = nodes[loc].parent;
                if is_valid_call_hierarchy_declaration(parent, &nodes) {
                    early_return =
                        Some(Some(ResolvedCallHierarchyDeclarations::Single(parent.unwrap())));
                } else {
                    early_return = Some(None);
                }
            }

            if early_return.is_none()
                && nodes[loc].kind == Kind::StaticKeyword
                && nodes[loc]
                    .parent
                    .is_some_and(|p| ast::is_class_static_block_declaration(&nodes[p]))
            {
                location = nodes[loc].parent;
                early_return = Some(None); // continue
            }

            // #39453
            if early_return.is_none() && ast::is_variable_declaration(&nodes[loc]) {
                if let Some(initializer) = nodes[loc].initializer() {
                    if is_assigned_expression(Some(initializer), &nodes) {
                        early_return =
                            Some(Some(ResolvedCallHierarchyDeclarations::Single(initializer)));
                    }
                }
            }
        }

        if let Some(ret) = early_return {
            // `location = location.Parent`-style `continue` for the static
            // keyword case was already applied above; `ret == None` means Go's
            // `return nil` unless we continued.
            if location == Some(loc) {
                result = ret;
                break;
            }
            continue;
        }

        if !following_symbol {
            let symbol = c.borrow_mut().get_symbol_at_location_api(loc);
            if let Some(mut symbol) = symbol {
                if c.borrow().symbol_arena.get_ref(symbol)
                    .flags
                    .intersects(ast::SymbolFlags::ALIAS)
                {
                    if let Some(aliased) = c.borrow_mut().get_aliased_symbol(symbol) {
                        symbol = aliased;
                    }
                }
                let value_declaration = c.borrow().symbol_arena.get_ref(symbol)
                    .value_declaration;
                if let Some(vd) = value_declaration {
                    following_symbol = true;
                    location = Some(vd);
                    continue;
                }
            }
        }

        break;
    }

    done();
    result
}

/// `convertEntryToCallSite`.
fn convert_entry_to_call_site(entry: &ReferenceEntry, program: &Rc<Program>) -> Option<CallSite> {
    if entry.kind != EntryKind::Node {
        return None;
    }

    let node = entry.node?;
    let nodes = program.nodes(node.file_index());
    if !ast::is_call_or_new_expression_target(node, true /*includeElementAccess*/, true /*skipPastOuterExpressions*/, &nodes)
        && !ast::is_tagged_template_tag(node, true, true, &nodes)
        && !ast::is_decorator_target(node, true, true, &nodes)
        && !ast::is_jsx_opening_like_element_tag_name(node, true, true, &nodes)
        && !ast::is_right_side_of_property_access(node, &nodes)
        && !ast::is_argument_expression_of_element_access(node, &nodes)
    {
        return None;
    }

    let source_file = ast::get_source_file_of_node(Some(node), &nodes)?;
    let ancestor = ast::find_ancestor(Some(node), &nodes, &mut |n, nodes| {
        is_valid_call_hierarchy_declaration(Some(n.id), nodes)
    })
    .unwrap_or(source_file);

    let start = skip_trivia(
        nodes[source_file].as_source_file().text(),
        nodes[node].pos(),
    );
    Some(CallSite {
        declaration: ancestor,
        text_range: TextRange::new(start, nodes[node].end()),
        source_file,
    })
}

/// `getCallSiteGroupKey` — `ast.GetNodeId(site.declaration)`; `NodeId`
/// already is the node id.
fn get_call_site_group_key(site: &CallSite) -> NodeId {
    site.declaration
}

/// `callSiteCollector`.
struct CallSiteCollector<'p> {
    /// `program`.
    program: &'p Rc<Program>,
    /// `callSites`.
    call_sites: Vec<CallSite>,
}

impl CallSiteCollector<'_> {
    /// `recordCallSite`.
    fn record_call_site(&mut self, node: NodeId, nodes: &[Node]) {
        let target = if ast::is_tagged_template_expression(&nodes[node]) {
            nodes[node].as_tagged_template_expression().tag
        } else if ast::is_jsx_opening_element(&nodes[node])
            || ast::is_jsx_self_closing_element(&nodes[node])
        {
            nodes[node].tag_name()
        } else if ast::is_property_access_expression(&nodes[node])
            || ast::is_element_access_expression(&nodes[node])
            || ast::is_class_static_block_declaration(&nodes[node])
        {
            Some(node)
        } else if ast::is_call_expression(&nodes[node])
            || ast::is_new_expression(&nodes[node])
            || ast::is_decorator(&nodes[node])
        {
            nodes[node].expression()
        } else {
            None
        };

        let Some(target) = target else { return };

        let Some(declaration) = resolve_call_hierarchy_declaration(self.program, Some(target))
        else {
            return;
        };

        let (source_file, start, end) = {
            let t_nodes = self.program.nodes(target.file_index());
            let source_file = ast::get_source_file_of_node(Some(target), &t_nodes).unwrap_or(target);
            let start = skip_trivia(
                t_nodes[source_file].as_source_file().text(),
                t_nodes[target].pos(),
            );
            (source_file, start, t_nodes[target].end())
        };
        let text_range = TextRange::new(start, end);

        match declaration {
            ResolvedCallHierarchyDeclarations::Single(decl) => {
                self.call_sites.push(CallSite {
                    declaration: decl,
                    text_range,
                    source_file,
                });
            }
            ResolvedCallHierarchyDeclarations::Multiple(decls) => {
                for decl in decls {
                    self.call_sites.push(CallSite {
                        declaration: decl,
                        text_range,
                        source_file,
                    });
                }
            }
        }
    }

    /// `collect`.
    fn collect(&mut self, node: Option<NodeId>, nodes: &[Node]) {
        let Some(node) = node else { return };

        // do not descend into ambient nodes.
        if nodes[node].flags.intersects(NodeFlags::AMBIENT) {
            return;
        }

        // do not descend into other call site declarations, other than class
        // member names
        if is_valid_call_hierarchy_declaration(Some(node), nodes) {
            if ast::is_class_like(Some(node), nodes) {
                if let Some(members) = nodes[node].members() {
                    for &member in members {
                        if let Some(name) = nodes[member].name() {
                            if ast::is_computed_property_name(&nodes[name]) {
                                self.collect(nodes[name].expression(), nodes);
                            }
                        }
                    }
                }
            }
            return;
        }

        match nodes[node].kind {
            Kind::Identifier
            | Kind::ImportEqualsDeclaration
            | Kind::ImportDeclaration
            | Kind::ExportDeclaration
            | Kind::InterfaceDeclaration
            | Kind::TypeAliasDeclaration => {
                // do not descend into nodes that cannot contain callable nodes
                return;
            }
            Kind::ClassStaticBlockDeclaration => {
                self.record_call_site(node, nodes);
                return;
            }
            Kind::TypeAssertionExpression | Kind::AsExpression | Kind::SatisfiesExpression => {
                // do not descend into the type side of an assertion
                self.collect(nodes[node].expression(), nodes);
                return;
            }
            Kind::VariableDeclaration | Kind::Parameter => {
                // do not descend into the type of a variable or parameter
                // declaration
                self.collect(nodes[node].name(), nodes);
                self.collect(nodes[node].initializer(), nodes);
                return;
            }
            Kind::CallExpression | Kind::NewExpression => {
                // do not descend into the type arguments of a call/new
                // expression
                self.record_call_site(node, nodes);
                self.collect(nodes[node].expression(), nodes);
                if let Some(args) = nodes[node].arguments() {
                    for &arg in args {
                        self.collect(Some(arg), nodes);
                    }
                }
                return;
            }
            Kind::TaggedTemplateExpression => {
                // do not descend into the type arguments of a tagged template
                // expression
                self.record_call_site(node, nodes);
                let tagged = nodes[node].as_tagged_template_expression();
                self.collect(tagged.tag, nodes);
                self.collect(tagged.template, nodes);
                return;
            }
            Kind::JsxOpeningElement | Kind::JsxSelfClosingElement => {
                // do not descend into the type arguments of a
                // JsxOpeningLikeElement
                self.record_call_site(node, nodes);
                self.collect(nodes[node].tag_name(), nodes);
                self.collect(nodes[node].attributes(), nodes);
                return;
            }
            Kind::Decorator => {
                self.record_call_site(node, nodes);
                self.collect(nodes[node].expression(), nodes);
                return;
            }
            Kind::PropertyAccessExpression | Kind::ElementAccessExpression => {
                self.record_call_site(node, nodes);
                // Go does `ForEachChild` + `return` here — no
                // `IsPartOfTypeNode` check.
                nodes[node].for_each_child(nodes, &mut |child| {
                    self.collect(Some(child), nodes);
                    false
                });
                return;
            }
            _ => {}
        }

        if ast::is_part_of_type_node(node, nodes) {
            // do not descend into types
            return;
        }

        nodes[node].for_each_child(nodes, &mut |child| {
            self.collect(Some(child), nodes);
            false
        });
    }
}

/// `collectCallSites`.
fn collect_call_sites(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    node: NodeId,
) -> Vec<CallSite> {
    let mut collector = CallSiteCollector {
        program,
        call_sites: Vec::new(),
    };

    let nodes = program.nodes(node.file_index());
    match nodes[node].kind {
        Kind::SourceFile => {
            if let Some(statements) = nodes[node].statements() {
                for &stmt in statements {
                    collector.collect(Some(stmt), &nodes);
                }
            }
        }

        Kind::ModuleDeclaration => {
            let body = nodes[node].body();
            let collect_body = !ast::has_syntactic_modifier(&nodes[node], ModifierFlags::AMBIENT)
                && body.is_some_and(|b| ast::is_module_block(&nodes[b]));
            if collect_body {
                if let Some(statements) = body.and_then(|b| nodes[b].statements()) {
                    for &stmt in statements {
                        collector.collect(Some(stmt), &nodes);
                    }
                }
            }
        }

        Kind::FunctionDeclaration
        | Kind::FunctionExpression
        | Kind::ArrowFunction
        | Kind::MethodDeclaration
        | Kind::GetAccessor
        | Kind::SetAccessor => {
            if let Some(impl_) = find_implementation(c, program, node) {
                let impl_nodes = program.nodes(impl_.file_index());
                if let Some(params) = impl_nodes[impl_].parameters() {
                    for &param in params {
                        collector.collect(Some(param), &impl_nodes);
                    }
                }
                collector.collect(impl_nodes[impl_].body(), &impl_nodes);
            }
        }

        Kind::ClassDeclaration | Kind::ClassExpression => {
            if let Some(modifiers) = nodes[node].modifiers() {
                for &mod_ in &modifiers.nodes {
                    collector.collect(Some(mod_), &nodes);
                }
            }

            if let Some(heritage) = ast::get_class_extends_heritage_element(&nodes[node], &nodes) {
                collector.collect(nodes[heritage].expression(), &nodes);
            }

            if let Some(members) = nodes[node].members() {
                for &member in members {
                    if ast::can_have_modifiers(&nodes[member]) {
                        if let Some(member_modifiers) = nodes[member].modifiers() {
                            for &mod_ in &member_modifiers.nodes {
                                collector.collect(Some(mod_), &nodes);
                            }
                        }
                    }

                    if ast::is_property_declaration(&nodes[member]) {
                        collector.collect(nodes[member].initializer(), &nodes);
                    } else if ast::is_constructor_declaration(&nodes[member]) {
                        if let Some(body) = nodes[member].body() {
                            if let Some(params) = nodes[member].parameters() {
                                for &param in params {
                                    collector.collect(Some(param), &nodes);
                                }
                            }
                            collector.collect(Some(body), &nodes);
                        }
                    } else if ast::is_class_static_block_declaration(&nodes[member]) {
                        collector.collect(Some(member), &nodes);
                    }
                }
            }
        }

        Kind::ClassStaticBlockDeclaration => {
            let body = nodes[node].as_class_static_block_declaration().body;
            collector.collect(body, &nodes);
        }

        _ => {
            // `debug.AssertNever(node)` — Go's debug package panics
            // unconditionally.
            panic!(
                "unexpected call hierarchy declaration kind: {:?}",
                nodes[node].kind
            );
        }
    }

    collector.call_sites
}

impl<'h> LanguageService<'h> {
    /// `createCallHierarchyItem` — creates a `CallHierarchyItem` for a call
    /// hierarchy declaration.
    fn create_call_hierarchy_item(
        &self,
        program: &Rc<Program>,
        node: NodeId,
    ) -> Option<lsproto::CallHierarchyItem> {
        let nodes = program.nodes(node.file_index());
        let source_file = ast::get_source_file_of_node(Some(node), &nodes)?;
        let (name_text, name_pos, name_end) = get_call_hierarchy_item_name(program, node);
        let container_name = get_call_hierarchy_item_container_name(program, node);

        let kind = get_symbol_kind_from_node(&nodes, node);

        let text = nodes[source_file].as_source_file().text();
        let full_start = skip_trivia_ex(
            text,
            nodes[node].pos(),
            Some(&SkipTriviaOptions {
                stop_at_comments: true,
                ..Default::default()
            }),
        );
        let script = source_file_script(source_file, &nodes);
        let (mut span, span_fidelity) = self.converters.to_lsp_range_for_feature(
            &script,
            TextRange::new(full_start, nodes[node].end()),
            Feature::CallHierarchy,
        );
        let (selection_span, selection_fidelity) = self.converters.to_lsp_range_for_feature(
            &script,
            TextRange::new(name_pos, name_end),
            Feature::CallHierarchy,
        );
        if !selection_fidelity.is_single_segment() {
            return None;
        }
        if span_fidelity.is_none()
            || (!nodes[source_file].as_source_file().content_mapper().is_empty()
                && !lsp_range_contains(&span, &selection_span))
        {
            span = selection_span.clone();
        }

        let item = lsproto::CallHierarchyItem {
            name: name_text,
            kind,
            uri: file_name_to_document_uri(
                nodes[source_file].as_source_file().original_file_name(&nodes),
            ),
            range: span,
            selection_range: selection_span,
            detail: if container_name.is_empty() {
                None
            } else {
                Some(container_name)
            },
            ..Default::default()
        };

        Some(item)
    }

    /// `convertCallSiteGroupToIncomingCall`.
    fn convert_call_site_group_to_incoming_call(
        &self,
        program: &Rc<Program>,
        entries: &[CallSite],
    ) -> Option<lsproto::CallHierarchyIncomingCall> {
        let mut from_ranges: Vec<lsproto::Range> = Vec::with_capacity(entries.len());
        for entry in entries {
            let nodes = program.nodes(entry.source_file.file_index());
            let script = source_file_script(entry.source_file, &nodes);
            let (lsp_range, fidelity) = self.converters.to_lsp_range_for_feature(
                &script,
                entry.text_range,
                Feature::CallHierarchy,
            );
            if !fidelity.is_none() {
                from_ranges.push(lsp_range);
            }
        }
        let from = self.create_call_hierarchy_item(program, entries[0].declaration)?;
        if from_ranges.is_empty() {
            return None;
        }

        from_ranges.sort_by(|a, b| lsproto::compare_ranges(a, b).cmp(&0));

        Some(lsproto::CallHierarchyIncomingCall {
            from: Some(from),
            from_ranges: Some(from_ranges),
            ..Default::default()
        })
    }

    /// `convertCallSiteGroupToOutgoingCall`.
    fn convert_call_site_group_to_outgoing_call(
        &self,
        program: &Rc<Program>,
        entries: &[CallSite],
    ) -> Option<lsproto::CallHierarchyOutgoingCall> {
        let mut from_ranges: Vec<lsproto::Range> = Vec::with_capacity(entries.len());
        for entry in entries {
            let nodes = program.nodes(entry.source_file.file_index());
            let script = source_file_script(entry.source_file, &nodes);
            let (lsp_range, fidelity) = self.converters.to_lsp_range_for_feature(
                &script,
                entry.text_range,
                Feature::CallHierarchy,
            );
            if !fidelity.is_none() {
                from_ranges.push(lsp_range);
            }
        }
        let to = self.create_call_hierarchy_item(program, entries[0].declaration)?;
        if from_ranges.is_empty() {
            return None;
        }

        from_ranges.sort_by(|a, b| lsproto::compare_ranges(a, b).cmp(&0));

        Some(lsproto::CallHierarchyOutgoingCall {
            to: Some(to),
            from_ranges: Some(from_ranges),
            ..Default::default()
        })
    }

    /// `symbolAndEntriesToIncomingCalls`.
    fn symbol_and_entries_to_incoming_calls(
        &self,
        _ctx: &Context,
        data: SymbolAndEntriesData,
        _options: SymbolEntryTransformOptions,
    ) -> Result<lsproto::CallHierarchyIncomingCallsResponse, Error> {
        let program = self.get_program();
        let mut ref_entries: Vec<Rc<RefCell<ReferenceEntry>>> = Vec::new();
        for symbol_and_entry in &data.symbols_and_entries {
            ref_entries.extend(symbol_and_entry.borrow().references.iter().cloned());
        }

        let mut call_sites: Vec<CallSite> = Vec::new();
        for entry in &ref_entries {
            if let Some(site) = convert_entry_to_call_site(&entry.borrow(), &program) {
                call_sites.push(site);
            }
        }

        if call_sites.is_empty() {
            return Ok(lsproto::CallHierarchyIncomingCallsOrNull::default());
        }

        let mut grouped: HashMap<NodeId, Vec<CallSite>> = HashMap::new();
        for site in call_sites {
            grouped.entry(get_call_site_group_key(&site)).or_default().push(site);
        }

        let mut result: Vec<lsproto::CallHierarchyIncomingCall> = Vec::new();
        for sites in grouped.values() {
            if let Some(incoming_call) =
                self.convert_call_site_group_to_incoming_call(&program, sites)
            {
                result.push(incoming_call);
            }
        }
        Ok(lsproto::CallHierarchyIncomingCallsOrNull {
            call_hierarchy_incoming_calls: Some(result),
        })
    }

    /// `getIncomingCalls` — gets the call sites that call into the provided
    /// call hierarchy declaration.
    fn get_incoming_calls(
        &self,
        ctx: &Context,
        program: &Rc<Program>,
        declaration: NodeId,
        orchestrator: Option<&dyn CrossProjectOrchestrator<'h>>,
    ) -> Result<lsproto::CallHierarchyIncomingCallsResponse, Error> {
        // Source files and modules have no incoming calls.
        {
            let nodes = program.nodes(declaration.file_index());
            if ast::is_source_file(&nodes[declaration])
                || ast::is_module_declaration(&nodes[declaration])
                || ast::is_class_static_block_declaration(&nodes[declaration])
            {
                return Ok(lsproto::CallHierarchyIncomingCallsOrNull::default());
            }
        }

        let Some(location) = ({
            let nodes = program.nodes(declaration.file_index());
            get_call_hierarchy_declaration_reference_node(Some(declaration), &nodes)
        }) else {
            return Ok(lsproto::CallHierarchyIncomingCallsOrNull::default());
        };
        let (uri, position) = {
            let nodes = program.nodes(location.file_index());
            let location_file =
                ast::get_source_file_of_node(Some(location), &nodes).unwrap_or(location);
            let location_start = get_token_pos_of_node(
                location,
                nodes[location_file].as_source_file(),
                false, /*includeJsDoc*/
                &nodes,
            );
            let script = source_file_script(location_file, &nodes);
            let (_, fidelity) = self.converters.to_lsp_position_for_feature(
                &script,
                location_start,
                Feature::CallHierarchy,
            );
            if fidelity.is_none() {
                return Ok(lsproto::CallHierarchyIncomingCallsOrNull::default());
            }
            let uri = file_name_to_document_uri(
                nodes[location_file].as_source_file().original_file_name(&nodes),
            );
            let (position, _) = self.converters.to_lsp_position(&script, location_start);
            (uri, position)
        };

        let mut result = self.handle_cross_project(
            ctx,
            &uri,
            position,
            orchestrator,
            |ls, ctx, data, options| ls.symbol_and_entries_to_incoming_calls(ctx, data, options),
            &combine_incoming_calls,
            false, /*isRename*/
            false, /*implementations*/
            SymbolEntryTransformOptions::default(),
            None, /*defaultProjectData*/
        )?;

        if let Some(calls) = &mut result.call_hierarchy_incoming_calls {
            calls.sort_by(|a, b| {
                let a_uri = a.from.as_ref().map(|f| f.uri.as_str()).unwrap_or("");
                let b_uri = b.from.as_ref().map(|f| f.uri.as_str()).unwrap_or("");
                match a_uri.cmp(b_uri) {
                    std::cmp::Ordering::Equal => {
                        let a_range = a.from_ranges.as_ref().and_then(|r| r.first());
                        let b_range = b.from_ranges.as_ref().and_then(|r| r.first());
                        match (a_range, b_range) {
                            (Some(a_range), Some(b_range)) => {
                                lsproto::compare_ranges(a_range, b_range).cmp(&0)
                            }
                            _ => std::cmp::Ordering::Equal,
                        }
                    }
                    ord => ord,
                }
            });
        }
        Ok(result)
    }

    /// `getOutgoingCalls` — gets the call sites that call out of the provided
    /// call hierarchy declaration.
    fn get_outgoing_calls(
        &self,
        program: &Rc<Program>,
        declaration: NodeId,
    ) -> Vec<lsproto::CallHierarchyOutgoingCall> {
        {
            let nodes = program.nodes(declaration.file_index());
            if nodes[declaration].flags.intersects(NodeFlags::AMBIENT)
                || ast::is_method_signature_declaration(&nodes[declaration])
            {
                return Vec::new();
            }
        }

        let (c, done) = program.get_type_checker(Context::background());
        let call_sites = collect_call_sites(program, &c, declaration);
        done();

        if call_sites.is_empty() {
            return Vec::new();
        }

        let mut grouped: HashMap<NodeId, Vec<CallSite>> = HashMap::new();
        for site in call_sites {
            grouped.entry(get_call_site_group_key(&site)).or_default().push(site);
        }

        let mut result: Vec<lsproto::CallHierarchyOutgoingCall> = Vec::new();
        for sites in grouped.values() {
            if let Some(outgoing_call) =
                self.convert_call_site_group_to_outgoing_call(program, sites)
            {
                result.push(outgoing_call);
            }
        }

        result.sort_by(|a, b| {
            let a_uri = a.to.as_ref().map(|f| f.uri.as_str()).unwrap_or("");
            let b_uri = b.to.as_ref().map(|f| f.uri.as_str()).unwrap_or("");
            match a_uri.cmp(b_uri) {
                std::cmp::Ordering::Equal => {
                    let a_range = a.from_ranges.as_ref().and_then(|r| r.first());
                    let b_range = b.from_ranges.as_ref().and_then(|r| r.first());
                    match (a_range, b_range) {
                        (Some(a_range), Some(b_range)) => {
                            lsproto::compare_ranges(a_range, b_range).cmp(&0)
                        }
                        _ => std::cmp::Ordering::Equal,
                    }
                }
                ord => ord,
            }
        });

        result
    }

    /// `ProvidePrepareCallHierarchy`.
    pub fn provide_prepare_call_hierarchy(
        &self,
        _ctx: &Context,
        document_uri: &lsproto::DocumentUri,
        position: lsproto::Position,
    ) -> Result<lsproto::CallHierarchyPrepareResponse, Error> {
        let (program, file) = self.get_program_and_file(document_uri);
        let declarations = self.call_hierarchy_declarations(file, position, &program, false);
        let mut items: Vec<lsproto::CallHierarchyItem> = Vec::new();
        let mut seen: Vec<lsproto::Location> = Vec::new();
        for declaration in declarations {
            if let Some(item) = self.create_call_hierarchy_item(&program, declaration) {
                let location = lsproto::Location {
                    uri: item.uri.clone(),
                    range: item.selection_range.clone(),
                };
                if !seen.contains(&location) {
                    seen.push(location);
                    items.push(item);
                }
            }
        }

        if items.is_empty() {
            return Ok(lsproto::CallHierarchyItemsOrNull::default());
        }
        Ok(lsproto::CallHierarchyItemsOrNull {
            call_hierarchy_items: Some(items),
        })
    }

    /// `ProvideCallHierarchyIncomingCalls`.
    pub fn provide_call_hierarchy_incoming_calls(
        &self,
        ctx: &Context,
        item: &lsproto::CallHierarchyItem,
        orchestrator: Option<&dyn CrossProjectOrchestrator<'h>>,
    ) -> Result<lsproto::CallHierarchyIncomingCallsResponse, Error> {
        let program = self.get_program();
        let file_name = item.uri.file_name();
        let Some(file) = program.get_source_file(&file_name) else {
            return Ok(lsproto::CallHierarchyIncomingCallsOrNull::default());
        };

        let declarations =
            self.call_hierarchy_declarations(file, item.selection_range.start.clone(), &program, true);
        let mut calls: Vec<lsproto::CallHierarchyIncomingCall> = Vec::new();
        let mut seen: Vec<lsproto::Location> = Vec::new();
        for declaration in declarations {
            let response = self.get_incoming_calls(ctx, &program, declaration, orchestrator)?;
            if let Some(resp_calls) = response.call_hierarchy_incoming_calls {
                for call in resp_calls {
                    let Some(from) = &call.from else {
                        continue;
                    };
                    let location = lsproto::Location {
                        uri: from.uri.clone(),
                        range: from.selection_range.clone(),
                    };
                    if let Some(idx) = seen.iter().position(|l| *l == location) {
                        let existing = &mut calls[idx];
                        if let (Some(existing_ranges), Some(new_ranges)) =
                            (&mut existing.from_ranges, &call.from_ranges)
                        {
                            for from_range in new_ranges {
                                if !existing_ranges.contains(from_range) {
                                    existing_ranges.push(from_range.clone());
                                }
                            }
                        }
                    } else {
                        seen.push(location);
                        calls.push(call);
                    }
                }
            }
        }
        if calls.is_empty() {
            return Ok(lsproto::CallHierarchyIncomingCallsOrNull::default());
        }
        Ok(lsproto::CallHierarchyIncomingCallsOrNull {
            call_hierarchy_incoming_calls: Some(calls),
        })
    }

    /// `ProvideCallHierarchyOutgoingCalls`.
    pub fn provide_call_hierarchy_outgoing_calls(
        &self,
        _ctx: &Context,
        item: &lsproto::CallHierarchyItem,
    ) -> Result<lsproto::CallHierarchyOutgoingCallsResponse, Error> {
        let program = self.get_program();
        let file_name = item.uri.file_name();
        let Some(file) = program.get_source_file(&file_name) else {
            return Ok(lsproto::CallHierarchyOutgoingCallsOrNull::default());
        };

        let declarations =
            self.call_hierarchy_declarations(file, item.selection_range.start.clone(), &program, true);
        let mut calls: Vec<lsproto::CallHierarchyOutgoingCall> = Vec::new();
        let mut seen: Vec<lsproto::Location> = Vec::new();
        for declaration in declarations {
            for call in self.get_outgoing_calls(&program, declaration) {
                let Some(to) = &call.to else {
                    continue;
                };
                let location = lsproto::Location {
                    uri: to.uri.clone(),
                    range: to.selection_range.clone(),
                };
                if let Some(idx) = seen.iter().position(|l| *l == location) {
                    let existing = &mut calls[idx];
                    if let (Some(existing_ranges), Some(new_ranges)) =
                        (&mut existing.from_ranges, &call.from_ranges)
                    {
                        for from_range in new_ranges {
                            if !existing_ranges.contains(from_range) {
                                existing_ranges.push(from_range.clone());
                            }
                        }
                    }
                } else {
                    seen.push(location);
                    calls.push(call);
                }
            }
        }
        if calls.is_empty() {
            return Ok(lsproto::CallHierarchyOutgoingCallsOrNull::default());
        }
        Ok(lsproto::CallHierarchyOutgoingCallsOrNull {
            call_hierarchy_outgoing_calls: Some(calls),
        })
    }

    /// `callHierarchyDeclarations`.
    fn call_hierarchy_declarations(
        &self,
        file: NodeId,
        position: lsproto::Position,
        program: &Rc<Program>,
        allow_source_file: bool,
    ) -> Vec<CallHierarchyDeclaration> {
        // `positions` borrows from `nodes` via `SourceFileScript` — keep the
        // arena snapshot alive for the whole loop.
        let nodes = program.nodes(file.file_index());
        let positions = self.converters.from_lsp_position_for_source_file(
            file,
            &nodes,
            position,
            Feature::CallHierarchy,
        );
        let mut declarations: Vec<CallHierarchyDeclaration> = Vec::new();
        let mut seen: HashSet<NodeId> = HashSet::new();
        for mapped in positions {
            if !mapped.fidelity.is_single_segment() {
                continue;
            }
            let file = mapped.script.file;
            let pos = mapped.position;
            let node = if pos != 0 {
                let mut nodes = program.nodes_mut(file.file_index());
                tokens::get_touching_property_name(&mut nodes, file, pos)
            } else {
                Some(file)
            };
            let Some(node) = node else {
                continue;
            };
            {
                let nodes = program.nodes(file.file_index());
                if !allow_source_file && nodes[node].kind == Kind::SourceFile {
                    continue;
                }
            }
            match resolve_call_hierarchy_declaration(program, Some(node)) {
                Some(ResolvedCallHierarchyDeclarations::Single(declaration)) => {
                    if seen.insert(declaration) {
                        declarations.push(declaration);
                    }
                }
                Some(ResolvedCallHierarchyDeclarations::Multiple(decls)) => {
                    for declaration in decls {
                        if seen.insert(declaration) {
                            declarations.push(declaration);
                        }
                    }
                }
                None => {}
            }
        }
        declarations
    }
}

/// `getSymbolKindFromNode` — local copy (the canonical copy is private in
/// `symbols.rs`). Converts an AST node to an LSP `SymbolKind`; combines
/// `getNodeKind` with VS Code's `fromProtocolScriptElementKind`.
fn get_symbol_kind_from_node(nodes: &[Node], node: NodeId) -> SymbolKind {
    match nodes[node].kind {
        Kind::SourceFile => {
            if ast::is_external_module(nodes[node].as_source_file()) {
                return SymbolKind::Module;
            }
            SymbolKind::File
        }
        Kind::ModuleDeclaration => SymbolKind::Namespace,
        Kind::ClassDeclaration | Kind::ClassExpression => SymbolKind::Class,
        Kind::InterfaceDeclaration => SymbolKind::Interface,
        Kind::TypeAliasDeclaration | Kind::JSDocTypedefTag | Kind::JSDocCallbackTag => {
            SymbolKind::Class
        }
        Kind::EnumDeclaration => SymbolKind::Enum,
        Kind::VariableDeclaration => SymbolKind::Variable,
        Kind::ArrowFunction | Kind::FunctionDeclaration | Kind::FunctionExpression => {
            SymbolKind::Function
        }
        Kind::GetAccessor | Kind::SetAccessor => SymbolKind::Property,
        Kind::MethodDeclaration | Kind::MethodSignature => SymbolKind::Method,
        Kind::PropertyDeclaration
        | Kind::PropertySignature
        | Kind::PropertyAssignment
        | Kind::ShorthandPropertyAssignment
        | Kind::SpreadAssignment
        | Kind::IndexSignature => SymbolKind::Property,
        Kind::CallSignature => SymbolKind::Method,
        Kind::ConstructSignature => SymbolKind::Constructor,
        Kind::Constructor | Kind::ClassStaticBlockDeclaration => SymbolKind::Constructor,
        Kind::TypeParameter => SymbolKind::TypeParameter,
        Kind::EnumMember => SymbolKind::EnumMember,
        Kind::Parameter => {
            if ast::has_syntactic_modifier(
                &nodes[node],
                ModifierFlags::PARAMETER_PROPERTY_MODIFIER,
            ) {
                return SymbolKind::Property;
            }
            SymbolKind::Variable
        }
        Kind::BinaryExpression | Kind::CallExpression => {
            let kind = ast::get_assignment_declaration_kind(node, nodes);
            match kind {
                JsDeclarationKind::ThisProperty
                | JsDeclarationKind::Property
                | JsDeclarationKind::ObjectDefinePropertyValue => return SymbolKind::Property,
                _ => {}
            }
            SymbolKind::Variable
        }
        Kind::StringLiteral | Kind::NoSubstitutionTemplateLiteral | Kind::NumericLiteral => {
            // String literals used as property names (e.g., in
            // Object.defineProperty)
            SymbolKind::Property
        }
        _ => SymbolKind::Variable,
    }
}
