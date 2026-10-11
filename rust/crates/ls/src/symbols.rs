// Ported from tsc/internal/ls/symbols.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use tsc_ast::ast::Node;
use tsc_ast::kind_generated::Kind;
use tsc_ast::{self as ast, JsDeclarationKind, ModifierFlags, NodeFlags, NodeId};
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::text::TextRange;
use tsc_lsconv::converters::{source_file_script, Converters};
use tsc_lsproto::{self as lsproto, SymbolKind};
use tsc_lsutil::userpreferences_generated::UserPreferences;
use tsc_spanmap::Feature;
use tsc_tspath::{PathKey, RootedFilePath};

use crate::api::Error;
use crate::languageservice::LanguageService;
use crate::utilities::get_container_node;

const MAX_LENGTH: usize = 150;

impl<'h> LanguageService<'h> {
    /// `ProvideDocumentSymbols`.
    pub fn provide_document_symbols(
        &self,
        ctx: &Context,
        document_uri: lsproto::DocumentUri,
    ) -> Result<lsproto::DocumentSymbolResponse, Error> {
        let (program, file) = self.get_program_and_file(&document_uri);
        let mut projections: Vec<NodeId> = vec![file];
        {
            let nodes = program.nodes(file.file_index());
            projections.extend_from_slice(
                nodes[file].as_source_file().supplemental_source_files(),
            );
        }
        let mut symbols: Vec<lsproto::DocumentSymbol> = Vec::new();
        let mut seen: HashSet<(String, SymbolKind, (u32, u32), (u32, u32))> = HashSet::new();
        for projection in projections {
            let mut nodes = program.nodes_mut(projection.file_index());
            for symbol in
                self.get_document_symbols_for_children(ctx, &mut nodes, projection, projection)
            {
                let key = (
                    symbol.name.clone(),
                    symbol.kind,
                    (symbol.range.start.line, symbol.range.start.character),
                    (symbol.range.end.line, symbol.range.end.character),
                );
                if seen.insert(key) {
                    symbols.push(symbol);
                }
            }
        }
        if lsproto::get_client_capabilities(ctx)
            .text_document
            .document_symbol
            .hierarchical_document_symbol_support
        {
            return Ok(lsproto::SymbolInformationsOrDocumentSymbolsOrNull {
                document_symbols: Some(symbols),
                symbol_informations: None,
            });
        }
        // Client doesn't support hierarchical document symbols, return flat
        // SymbolInformation array
        let symbol_infos = flatten_document_symbols(&symbols, &document_uri);
        Ok(lsproto::SymbolInformationsOrDocumentSymbolsOrNull {
            symbol_informations: Some(symbol_infos),
            document_symbols: None,
        })
    }

    /// `getDocumentSymbolInformations` converts hierarchical DocumentSymbols
    /// to a flat SymbolInformation array.
    pub(crate) fn get_document_symbol_informations(
        &self,
        ctx: &Context,
        program: &Rc<Program>,
        file: NodeId,
        document_uri: &lsproto::DocumentUri,
    ) -> Vec<lsproto::SymbolInformation> {
        // First get hierarchical symbols
        let mut nodes = program.nodes_mut(file.file_index());
        let doc_symbols =
            self.get_document_symbols_for_children(ctx, &mut nodes, file, file);
        flatten_document_symbols(&doc_symbols, document_uri)
    }

    /// `getDocumentSymbolsForChildren`.
    fn get_document_symbols_for_children(
        &self,
        ctx: &Context,
        nodes: &mut Vec<Node>,
        node: NodeId,
        file: NodeId,
    ) -> Vec<lsproto::DocumentSymbol> {
        let mut st = DocSymbolsState {
            l: self,
            ctx,
            nodes,
            file,
            symbols: Vec::new(),
            expando_targets: HashSet::new(),
        };
        st.for_each_child(node);
        merge_expandos(st.symbols)
    }

    /// `newDocumentSymbol`.
    fn new_document_symbol(
        &self,
        nodes: &mut Vec<Node>,
        node: NodeId,
        name: Option<NodeId>,
        children: Vec<lsproto::DocumentSymbol>,
    ) -> Option<lsproto::DocumentSymbol> {
        let file = ast::get_source_file_of_node(Some(node), nodes)?;
        let source_text = nodes[file].as_source_file().text().to_string();
        let node_start_pos = tsc_scanner::scanner::skip_trivia(&source_text, nodes[node].pos());
        let name = name.or_else(|| ast::get_name_of_declaration(Some(node), nodes));
        let text: String;
        let name_start_pos: i32;
        let name_end_pos: i32;
        if ast::is_module_declaration(&nodes[node]) && !ast::is_ambient_module(&nodes[node], nodes)
        {
            text = get_module_name(nodes, node);
            let name = name?;
            name_start_pos = tsc_scanner::scanner::skip_trivia(&source_text, nodes[name].pos());
            name_end_pos = nodes[get_interior_module(nodes, node)]
                .name()
                .map(|n| nodes[n].end())
                .unwrap_or_else(|| nodes[node].end());
        } else if ast::is_export_assignment(&nodes[node])
            && nodes[node].as_export_assignment().is_export_equals
        {
            text = "export=".to_string();
            if let Some(name) = name.filter(|&n| !ast::node_is_missing(Some(n), nodes)) {
                name_start_pos =
                    tsc_scanner::scanner::skip_trivia(&source_text, nodes[name].pos());
                name_end_pos = nodes[name].end();
            } else {
                name_start_pos = node_start_pos;
                name_end_pos = nodes[node].end();
            }
        } else if let Some(name) = name {
            text = get_text_of_name(nodes, name);
            name_start_pos = tsc_scanner::scanner::skip_trivia(&source_text, nodes[name].pos())
                .max(node_start_pos);
            name_end_pos = nodes[name].end().max(node_start_pos);
        } else {
            text = get_unnamed_node_label(nodes, node);
            name_start_pos = node_start_pos;
            name_end_pos = node_start_pos;
        }
        if text.is_empty() {
            return None;
        }
        let mut text = text;
        let truncated = tsc_stringutil::truncate_by_runes(text.as_bytes(), MAX_LENGTH as i32);
        let truncated_len = truncated.len();
        let truncated = truncated.to_vec();
        if truncated_len < text.len() {
            text = String::from_utf8_lossy(&truncated).into_owned() + "...";
        }

        let kind = get_symbol_kind_from_node(nodes, node);
        let script = source_file_script(file, nodes);
        let (selection_range, selection_fidelity) = self.converters.to_lsp_range_for_feature(
            &script,
            TextRange::new(name_start_pos, name_end_pos),
            Feature::DocumentSymbols,
        );
        if !selection_fidelity.is_single_segment() {
            return None;
        }
        let (mut symbol_range, range_fidelity) = self.converters.to_lsp_range_for_feature(
            &script,
            TextRange::new(node_start_pos, nodes[node].end()),
            Feature::DocumentSymbols,
        );
        if range_fidelity.is_none() {
            symbol_range = selection_range.clone();
        }
        Some(lsproto::DocumentSymbol {
            name: text,
            detail: None,
            kind,
            tags: None,
            deprecated: None,
            range: symbol_range,
            selection_range,
            children: Some(children),
        })
    }
}

/// `flattenDocumentSymbols` — flattens the hierarchy.
fn flatten_document_symbols(
    doc_symbols: &[lsproto::DocumentSymbol],
    document_uri: &lsproto::DocumentUri,
) -> Vec<lsproto::SymbolInformation> {
    let mut result: Vec<lsproto::SymbolInformation> = Vec::new();
    fn flatten(
        symbols: &[lsproto::DocumentSymbol],
        container_name: Option<&String>,
        document_uri: &lsproto::DocumentUri,
        result: &mut Vec<lsproto::SymbolInformation>,
    ) {
        for symbol in symbols {
            result.push(lsproto::SymbolInformation {
                name: symbol.name.clone(),
                kind: symbol.kind,
                tags: symbol.tags.clone(),
                container_name: container_name.cloned(),
                deprecated: symbol.deprecated,
                location: lsproto::Location {
                    uri: document_uri.clone(),
                    range: symbol.range.clone(),
                },
            });

            // Recursively flatten children with this symbol as container
            if let Some(children) = &symbol.children
                && !children.is_empty()
            {
                flatten(children, Some(&symbol.name), document_uri, result);
            }
        }
    }
    flatten(doc_symbols, None, document_uri, &mut result);
    result
}

/// Shared state standing in for Go's `symbols`/`expandoTargets` closures in
/// `getDocumentSymbolsForChildren`.
struct DocSymbolsState<'a, 'b, 'h> {
    l: &'a LanguageService<'h>,
    ctx: &'a Context,
    nodes: &'b mut Vec<Node>,
    file: NodeId,
    symbols: Vec<lsproto::DocumentSymbol>,
    expando_targets: HashSet<String>,
}

impl<'a, 'b, 'h> DocSymbolsState<'a, 'b, 'h> {
    /// `addSymbolForNode`.
    fn add_symbol_for_node(
        &mut self,
        node: NodeId,
        name: Option<NodeId>,
        children: Vec<lsproto::DocumentSymbol>,
    ) {
        if !self.nodes[node].flags.intersects(NodeFlags::REPARSED) {
            let symbol = self.l.new_document_symbol(self.nodes, node, name, children);
            if let Some(symbol) = symbol {
                self.symbols.push(symbol);
            }
        }
    }

    /// `n.ForEachChild(visit)` — children are collected first because
    /// `for_each_child` borrows the arena immutably.
    fn for_each_child(&mut self, node: NodeId) {
        let mut children: Vec<NodeId> = Vec::new();
        self.nodes[node].for_each_child(self.nodes, &mut |child| {
            children.push(child);
            false
        });
        for child in children {
            if self.visit(child) {
                break;
            }
        }
    }

    /// `getSymbolsForChildren`.
    fn get_symbols_for_children(
        &mut self,
        node: Option<NodeId>,
    ) -> Vec<lsproto::DocumentSymbol> {
        let mut result: Vec<lsproto::DocumentSymbol> = Vec::new();
        if let Some(node) = node {
            let save_expando_targets = std::mem::take(&mut self.expando_targets);
            let save_symbols = std::mem::take(&mut self.symbols);
            self.for_each_child(node);
            result = std::mem::take(&mut self.symbols);
            self.symbols = save_symbols;
            self.expando_targets = save_expando_targets;
        }
        result
    }

    /// `getSymbolsForNode`.
    fn get_symbols_for_node(&mut self, node: Option<NodeId>) -> Vec<lsproto::DocumentSymbol> {
        let mut result: Vec<lsproto::DocumentSymbol> = Vec::new();
        if let Some(node) = node {
            let save_symbols = std::mem::take(&mut self.symbols);
            self.visit(node);
            result = std::mem::take(&mut self.symbols);
            self.symbols = save_symbols;
        }
        result
    }

    /// `startNode` inlined at its only call site: save the current
    /// `symbols`/`expandoTargets`, run `body`, then `endNode` (restore +
    /// `addSymbolForNode(node, name, <accumulated>)`).
    fn with_started_node(
        &mut self,
        node: NodeId,
        name: Option<NodeId>,
        body: impl FnOnce(&mut Self),
    ) {
        let save_expando_targets = std::mem::take(&mut self.expando_targets);
        let save_symbols = std::mem::take(&mut self.symbols);
        body(self);
        let result = std::mem::take(&mut self.symbols);
        self.symbols = save_symbols;
        self.expando_targets = save_expando_targets;
        self.add_symbol_for_node(node, name, result);
    }

    /// `visit` — returns `true` to stop `ForEachChild` iteration.
    fn visit(&mut self, node: NodeId) -> bool {
        if self.ctx.is_cancelled() {
            return true;
        }
        if !self.nodes[node].flags.intersects(NodeFlags::REPARSED) {
            let jsdocs = ast::js_doc(self.nodes, node, Some(self.file));
            for jsdoc in jsdocs {
                if let Some(tag_list) = self.nodes[jsdoc].as_js_doc().tags.clone() {
                    for tag in tag_list.nodes {
                        if ast::is_js_doc_typedef_tag(&self.nodes[tag])
                            || ast::is_js_doc_callback_tag(&self.nodes[tag])
                        {
                            self.add_symbol_for_node(tag, None /*name*/, Vec::new());
                        }
                    }
                }
            }
        }
        if self.nodes[node].parent.is_some_and(|p| {
            self.nodes[p].kind == Kind::SourceFile
                && ast::is_import_or_import_equals_declaration(&self.nodes[node])
        }) {
            return false;
        }
        match self.nodes[node].kind {
            Kind::ClassDeclaration
            | Kind::ClassExpression
            | Kind::InterfaceDeclaration
            | Kind::EnumDeclaration => {
                if ast::is_class_like(Some(node), self.nodes) {
                    let decl_name = ast::get_declaration_name(self.nodes, node);
                    if !decl_name.is_empty() {
                        self.expando_targets.insert(decl_name);
                    }
                }
                let children = self.get_symbols_for_children(Some(node));
                self.add_symbol_for_node(node, None /*name*/, children);
            }
            Kind::ModuleDeclaration => {
                let interior = get_interior_module(self.nodes, node);
                let children = self.get_symbols_for_children(Some(interior));
                self.add_symbol_for_node(node, None /*name*/, children);
            }
            Kind::Constructor => {
                let body = self.nodes[node].body();
                let children = self.get_symbols_for_children(body);
                self.add_symbol_for_node(node, None /*name*/, children);
                let parameters = self.nodes[node]
                    .parameters()
                    .map(|p| p.to_vec())
                    .unwrap_or_default();
                for param in parameters {
                    if ast::is_parameter_property_declaration(
                        &self.nodes[param],
                        &self.nodes[node],
                    ) {
                        self.add_symbol_for_node(param, None /*name*/, Vec::new());
                    }
                }
            }
            Kind::FunctionDeclaration
            | Kind::FunctionExpression
            | Kind::ArrowFunction
            | Kind::MethodDeclaration
            | Kind::GetAccessor
            | Kind::SetAccessor => {
                let decl_name = ast::get_declaration_name(self.nodes, node);
                if !decl_name.is_empty() {
                    self.expando_targets.insert(decl_name);
                }
                let body = self.nodes[node].body();
                let children = self.get_symbols_for_children(body);
                self.add_symbol_for_node(node, None /*name*/, children);
            }
            Kind::VariableDeclaration
            | Kind::BindingElement
            | Kind::PropertyAssignment
            | Kind::PropertyDeclaration => {
                if let Some(node_name) = self.nodes[node].name() {
                    if ast::is_binding_pattern(&self.nodes[node_name]) {
                        self.visit(node_name);
                    } else {
                        let initializer = self.nodes[node].initializer();
                        let children = self.get_symbols_for_children(initializer);
                        self.add_symbol_for_node(node, None /*name*/, children);
                    }
                }
            }
            Kind::SpreadAssignment => {
                let expression = self.nodes[node].expression();
                self.add_symbol_for_node(node, expression, Vec::new());
            }
            Kind::MethodSignature
            | Kind::PropertySignature
            | Kind::CallSignature
            | Kind::ConstructSignature
            | Kind::IndexSignature
            | Kind::EnumMember
            | Kind::ShorthandPropertyAssignment
            | Kind::TypeAliasDeclaration
            | Kind::ImportEqualsDeclaration
            | Kind::ExportSpecifier => {
                self.add_symbol_for_node(node, None /*name*/, Vec::new());
            }
            Kind::ImportClause => {
                // Handle default import case e.g.:
                //    import d from "mod";
                if let Some(name) = self.nodes[node].name() {
                    self.add_symbol_for_node(name, Some(name), Vec::new());
                }
                // Handle named bindings in imports e.g.:
                //    import * as NS from "mod";
                //    import {a, b as B} from "mod";
                if let Some(named_bindings) =
                    self.nodes[node].as_import_clause().named_bindings
                {
                    if self.nodes[named_bindings].kind == Kind::NamespaceImport {
                        self.add_symbol_for_node(named_bindings, None /*name*/, Vec::new());
                    } else {
                        let elements = self.nodes[named_bindings]
                            .elements()
                            .map(|e| e.to_vec())
                            .unwrap_or_default();
                        for element in elements {
                            self.add_symbol_for_node(element, None /*name*/, Vec::new());
                        }
                    }
                }
            }
            Kind::BinaryExpression | Kind::CallExpression => {
                let assignment_kind = ast::get_assignment_declaration_kind(node, self.nodes);
                match assignment_kind {
                    // `module.exports = ...` should be reparsed into a
                    // JSExportAssignment, and `exports.a = ...` into a
                    // CommonJSExport.
                    JsDeclarationKind::None
                    | JsDeclarationKind::ThisProperty
                    | JsDeclarationKind::ModuleExports
                    | JsDeclarationKind::ExportsProperty
                    | JsDeclarationKind::ObjectDefinePropertyExports => {
                        self.for_each_child(node);
                    }
                    JsDeclarationKind::Property | JsDeclarationKind::ObjectDefinePropertyValue => {
                        let target: Option<NodeId>;
                        let mut target_function: Option<NodeId>;
                        let definition: Option<NodeId>;
                        let mut property_name: Option<NodeId> = None;
                        // `A.b = ... ` or `A.prototype.b = ...`
                        if ast::is_binary_expression(&self.nodes[node]) {
                            let binary_expr = self.nodes[node].as_binary_expression();
                            target = binary_expr.left;
                            target_function =
                                target.and_then(|t| self.nodes[t].expression());
                            definition = binary_expr.right;
                            if let Some(t) = target {
                                if ast::is_property_access_expression(&self.nodes[t]) {
                                    // `A.b` or `A.prototype.b`
                                    property_name = self.nodes[t]
                                        .as_property_access_expression()
                                        .name;
                                } else {
                                    // `A["b"]` or `A.prototype["b"]`
                                    property_name = self.nodes[t]
                                        .as_element_access_expression()
                                        .argument_expression;
                                }
                            }
                        } else {
                            // `Object.defineProperty(A, "b", {...})`
                            let args = self.nodes[node]
                                .arguments()
                                .map(|a| a.to_vec())
                                .unwrap_or_default();
                            target_function = Some(args[0]);
                            target = Some(args[1]);
                            property_name = target;
                            definition = Some(args[2]);
                        }
                        if let Some(tf) = target_function {
                            if is_prototype_expando(self.nodes, tf) {
                                target_function = self.nodes[tf].expression();
                                // If we see a prototype assignment, start
                                // tracking the target as an expando target.
                                if let Some(tf2) = target_function {
                                    if ast::is_identifier(&self.nodes[tf2]) {
                                        let text =
                                            self.nodes[tf2].text(self.nodes).to_string();
                                        self.expando_targets.insert(text);
                                    }
                                }
                            }
                        }
                        let is_expando_target = target_function.is_some_and(|tf| {
                            ast::is_identifier(&self.nodes[tf])
                                && self
                                    .expando_targets
                                    .contains(self.nodes[tf].text(self.nodes).as_ref())
                        });
                        if is_expando_target {
                            let name = target_function;
                            self.with_started_node(node, name, |st| {
                                let children = st.get_symbols_for_node(definition);
                                if let Some(target) = target {
                                    st.add_symbol_for_node(target, property_name, children);
                                }
                            });
                        } else {
                            self.for_each_child(node);
                        }
                    }
                }
            }
            Kind::ExportAssignment => {
                if self.nodes[node].as_export_assignment().is_export_equals {
                    let expression = self.nodes[node].expression();
                    let children = self.get_symbols_for_node(expression);
                    self.add_symbol_for_node(node, None /*name*/, children);
                } else {
                    self.for_each_child(node);
                }
            }
            _ => {
                self.for_each_child(node);
            }
        }
        false
    }
}

/// `isPrototypeExpando` — target is `f.prototype`.
fn is_prototype_expando(nodes: &[Node], target: NodeId) -> bool {
    if ast::is_access_expression(&nodes[target]) {
        if let Some(access_name) = ast::get_element_or_property_access_name(&nodes[target], nodes)
        {
            return &*nodes[access_name].text(nodes) == "prototype";
        }
    }
    false
}

/// `mergeExpandos` — merges expando symbols into their target symbols, and
/// namespaces of same name.
fn merge_expandos(symbols: Vec<lsproto::DocumentSymbol>) -> Vec<lsproto::DocumentSymbol> {
    // Collect symbols that can be an expando target.
    let mut name_to_expando_target_index: HashMap<String, Vec<usize>> = HashMap::new();
    // Collect namespaces.
    let mut name_to_namespace_index: HashMap<String, usize> = HashMap::new();
    for (i, symbol) in symbols.iter().enumerate() {
        if is_anonymous_name(&symbol.name) {
            continue;
        }
        if symbol.kind == SymbolKind::Class
            || symbol.kind == SymbolKind::Function
            || symbol.kind == SymbolKind::Variable
        {
            name_to_expando_target_index
                .entry(symbol.name.clone())
                .or_default()
                .push(i);
        }
        if symbol.kind == SymbolKind::Namespace {
            name_to_namespace_index
                .entry(symbol.name.clone())
                .or_insert(i);
        }
    }
    let mut slots: Vec<Option<lsproto::DocumentSymbol>> =
        symbols.into_iter().map(Some).collect();
    for i in 0..slots.len() {
        let Some(mut symbol) = slots[i].take() else {
            continue;
        };
        if let Some(children) = symbol.children.take() {
            symbol.children = Some(merge_expandos(children));
        }

        // Anonymous symbols never merge.
        if is_anonymous_name(&symbol.name) {
            slots[i] = Some(symbol);
            continue;
        }

        let mut merged = false;
        // Merge expandos.
        if symbol.kind == SymbolKind::Property {
            if let Some(indices) = name_to_expando_target_index.get(&symbol.name) {
                for &target_index in indices.iter().rev() {
                    if let Some(Some(target_symbol)) = slots.get_mut(target_index) {
                        merge_children(target_symbol, &mut symbol);
                    }
                    // Mark this symbol as merged.
                    merged = true;
                }
            }
        }
        // Merge namespaces.
        if symbol.kind == SymbolKind::Namespace {
            if let Some(&target_index) = name_to_namespace_index.get(&symbol.name)
                && target_index != i
            {
                if let Some(Some(target_symbol)) = slots.get_mut(target_index) {
                    merge_children(target_symbol, &mut symbol);
                }
                // Mark this symbol as merged.
                merged = true;
            }
        }
        if !merged {
            slots[i] = Some(symbol);
        }
    }
    slots.into_iter().flatten().collect()
}

/// `mergeChildren`.
fn merge_children(
    target: &mut lsproto::DocumentSymbol,
    source: &mut lsproto::DocumentSymbol,
) {
    if let Some(source_children) = source.children.take() {
        if target.children.is_none() {
            target.children = Some(source_children);
        } else {
            let mut merged = target.children.take().unwrap_or_default();
            merged.extend(source_children);
            let mut merged = merge_expandos(merged);
            merged.sort_by(|a, b| lsproto::compare_ranges(&a.range, &b.range).cmp(&0));
            target.children = Some(merged);
        }
    }
}

/// `isAnonymousName` — see `getUnnamedNodeLabel`.
fn is_anonymous_name(name: &str) -> bool {
    name == "<function>"
        || name == "<class>"
        || name == "export="
        || name == "default"
        || name == "constructor"
        || name == "()"
        || name == "new()"
        || name == "[]"
        || name.ends_with(") callback")
}

/// `getTextOfName`.
fn get_text_of_name(nodes: &[Node], node: NodeId) -> String {
    match nodes[node].kind {
        Kind::Identifier | Kind::PrivateIdentifier | Kind::NumericLiteral => {
            nodes[node].text(nodes).to_string()
        }
        Kind::StringLiteral => {
            format!(
                "\"{}\"",
                tsc_printer::escape_string(
                    &nodes[node].text(nodes),
                    tsc_printer::QuoteChar::DoubleQuote,
                )
            )
        }
        Kind::NoSubstitutionTemplateLiteral => {
            format!(
                "`{}`",
                tsc_printer::escape_string(
                    &nodes[node].text(nodes),
                    tsc_printer::QuoteChar::Backtick,
                )
            )
        }
        Kind::ComputedPropertyName => {
            if let Some(expression) = nodes[node].expression()
                && ast::is_string_or_numeric_literal_like(&nodes[expression])
            {
                return get_text_of_name(nodes, expression);
            }
            tsc_scanner::utilities::get_text_of_node(node, nodes)
        }
        _ => tsc_scanner::utilities::get_text_of_node(node, nodes),
    }
}

/// `getUnnamedNodeLabel`.
fn get_unnamed_node_label(nodes: &[Node], node: NodeId) -> String {
    if let Some(parent) =
        nodes[node].parent.and_then(|p| ast::walk_up_parenthesized_expressions(p, nodes))
    {
        if ast::is_export_assignment(&nodes[parent]) {
            if nodes[parent].as_export_assignment().is_export_equals {
                return "export=".to_string();
            }
            return "default".to_string();
        }
    }
    match nodes[node].kind {
        Kind::FunctionDeclaration | Kind::FunctionExpression | Kind::ArrowFunction => {
            if nodes[node].modifier_flags().intersects(ModifierFlags::DEFAULT) {
                return "default".to_string();
            }
            if let Some(parent) = nodes[node].parent {
                if ast::is_call_expression(&nodes[parent]) {
                    if let Some(expression) = nodes[parent].expression() {
                        let name = get_call_expression_name(nodes, expression);
                        if !name.is_empty() {
                            let name = clean_callback_text(&name);
                            if name.len() > MAX_LENGTH {
                                return format!("{} callback", name);
                            }
                            let args =
                                clean_callback_text(&get_call_expression_literal_args(nodes, parent));
                            return format!("{}({}) callback", name, args);
                        }
                    }
                }
            }
            "<function>".to_string()
        }
        Kind::ClassDeclaration | Kind::ClassExpression => {
            if nodes[node].modifier_flags().intersects(ModifierFlags::DEFAULT) {
                return "default".to_string();
            }
            "<class>".to_string()
        }
        Kind::Constructor => "constructor".to_string(),
        Kind::CallSignature => "()".to_string(),
        Kind::ConstructSignature => "new()".to_string(),
        Kind::IndexSignature => "[]".to_string(),
        _ => String::new(),
    }
}

/// `getCallExpressionName`.
fn get_call_expression_name(nodes: &[Node], node: NodeId) -> String {
    match nodes[node].kind {
        Kind::Identifier | Kind::PrivateIdentifier => nodes[node].text(nodes).to_string(),
        Kind::PropertyAccessExpression => {
            let left = nodes[node]
                .expression()
                .map(|e| get_call_expression_name(nodes, e))
                .unwrap_or_default();
            let right = nodes[node]
                .name()
                .map(|n| get_call_expression_name(nodes, n))
                .unwrap_or_default();
            if !left.is_empty() {
                return format!("{}.{}", left, right);
            }
            right
        }
        _ => String::new(),
    }
}

/// `getCallExpressionLiteralArgs`.
fn get_call_expression_literal_args(nodes: &[Node], call_expr: NodeId) -> String {
    let mut parts: Vec<String> = Vec::new();
    if let Some(args) = nodes[call_expr].arguments() {
        for &arg in args {
            if ast::is_string_literal_like(&nodes[arg])
                || ast::is_template_expression(&nodes[arg])
            {
                parts.push(tsc_scanner::utilities::get_text_of_node(arg, nodes));
            }
        }
    }
    parts.join(", ")
}

/// `cleanCallbackText`.
fn clean_callback_text(text: &str) -> String {
    let truncated = tsc_stringutil::truncate_by_runes(text.as_bytes(), MAX_LENGTH as i32);
    let truncated_len = truncated.len();
    let mut text = if truncated_len < text.len() {
        String::from_utf8_lossy(truncated).into_owned() + "..."
    } else {
        text.to_string()
    };
    text.retain(|r| !tsc_stringutil::is_line_break(r));
    text
}

/// `getInteriorModule`.
fn get_interior_module(nodes: &[Node], node: NodeId) -> NodeId {
    let mut node = node;
    while let Some(body) = nodes[node].body() {
        if ast::is_module_declaration(&nodes[body]) {
            node = body;
        } else {
            break;
        }
    }
    node
}

/// `getModuleName`.
fn get_module_name(nodes: &[Node], node: NodeId) -> String {
    let mut node = node;
    let mut result = nodes[node]
        .name()
        .map(|n| nodes[n].text(nodes).to_string())
        .unwrap_or_default();
    while let Some(body) = nodes[node].body() {
        if ast::is_module_declaration(&nodes[body]) {
            node = body;
            if let Some(name) = nodes[node].name() {
                result = format!("{}.{}", result, nodes[name].text(nodes));
            }
        } else {
            break;
        }
    }
    result
}

/// `DeclarationInfo`.
struct DeclarationInfo {
    name: String,
    declaration: NodeId,
    match_score: i32,
    /// The program that owns `declaration`'s arena — declarations in the
    /// merged set can come from different programs.
    program: Rc<Program>,
    /// `ast.GetSourceFileOfNode(declaration).PathKey()` precomputed: the Go
    /// comparator reads it through shared pointers; we cannot reach arenas
    /// inside `sort_by`.
    path_key: PathKey,
    /// `declaration.Pos()` — same reason as `path_key`.
    pos: i32,
}

/// `ProvideWorkspaceSymbols`.
pub fn provide_workspace_symbols(
    ctx: &Context,
    programs: &[Rc<Program>],
    converters: &Converters,
    preferences: &UserPreferences,
    query: &str,
) -> Result<lsproto::WorkspaceSymbolResponse, Error> {
    let exclude_library_symbols = preferences.exclude_library_symbols_in_nav_to.is_true();
    // Obtain set of non-declaration source files from all active programs.
    let mut source_files: HashMap<PathKey, (Rc<Program>, NodeId)> = HashMap::new();
    for program in programs {
        for source_file in program.source_files() {
            let nodes = program.nodes(source_file.file_index());
            if (program.has_ts_file() || !nodes[source_file].as_source_file().is_declaration_file)
                && !should_exclude_file(&nodes, source_file, program, exclude_library_symbols)
            {
                let key = nodes[source_file].as_source_file().path_key().clone();
                source_files.insert(key, (program.clone(), source_file));
            }
        }
    }
    // Create DeclarationInfos for all declarations in the source files.
    let mut infos: Vec<DeclarationInfo> = Vec::new();
    for (program, source_file) in source_files.values() {
        if ctx.is_cancelled() {
            return Ok(lsproto::SymbolInformationsOrWorkspaceSymbolsOrNull {
                symbol_informations: None,
                workspace_symbols: None,
            });
        }
        // `get_declaration_map` borrows `nodes`; collect the map entries then
        // drop the arena handle before per-declaration work.
        let declaration_map: Vec<(String, Vec<NodeId>)> = {
            let mut nodes = program.nodes_mut(source_file.file_index());
            ast::get_declaration_map(&mut nodes, *source_file)
                .iter()
                .map(|(name, decls)| (name.clone(), decls.clone()))
                .collect()
        };
        for (name, declarations) in declaration_map {
            let score = get_match_score(&name, query);
            if score >= 0 {
                for declaration in declarations {
                    let (path_key, pos) = {
                        let decl_nodes = program.nodes(declaration.file_index());
                        let sf =
                            ast::get_source_file_of_node(Some(declaration), &decl_nodes);
                        (
                            sf.map(|s| {
                                decl_nodes[s].as_source_file().path_key().clone()
                            })
                            .unwrap_or_default(),
                            decl_nodes[declaration].pos(),
                        )
                    };
                    infos.push(DeclarationInfo {
                        name: name.clone(),
                        declaration,
                        match_score: score,
                        program: program.clone(),
                        path_key,
                        pos,
                    });
                }
            }
        }
    }
    // Sort the DeclarationInfos and return the top 256 matches.
    infos.sort_by(compare_declaration_infos);
    let count = infos.len().min(256);
    let mut symbols: Vec<lsproto::SymbolInformation> = Vec::with_capacity(count);
    for info in &infos[0..count] {
        let node = info.declaration;
        let program = &info.program;
        let (source_file, container_name) = {
            let nodes = program.nodes(node.file_index());
            let source_file = ast::get_source_file_of_node(Some(node), &nodes);
            let container_name = get_container_node(node, &nodes)
                .map(|container| ast::get_declaration_name(&nodes, container));
            (source_file, container_name)
        };
        let Some(source_file) = source_file else {
            continue;
        };
        // Use the name node's span so that VS selects just the symbol name
        // (matching the TS5 navto behaviour). GetNameOfDeclaration is always
        // non-nil here because computeDeclarationMap only adds declarations
        // whose GetDeclarationName (string form) is non-empty, which implies
        // a name node exists.
        let mut nodes = program.nodes_mut(source_file.file_index());
        let Some(name_node) = ast::get_name_of_declaration(Some(node), &nodes) else {
            continue;
        };
        let name_start =
            tsc_astnav::tokens::get_start_of_node(&mut nodes, source_file, name_node, false);
        let name_range = TextRange::new(name_start, nodes[name_node].end());
        let script = source_file_script(source_file, &nodes);
        let (location, fidelity) =
            converters.to_lsp_location_for_feature(&script, name_range, Feature::DocumentSymbols);
        if !fidelity.is_single_segment() {
            // The name has no counterpart in the original text, so there is
            // nothing to navigate to.
            continue;
        }
        symbols.push(lsproto::SymbolInformation {
            name: info.name.clone(),
            kind: {
                let decl_nodes = program.nodes(node.file_index());
                get_symbol_kind_from_node(&decl_nodes, node)
            },
            tags: None,
            container_name,
            deprecated: None,
            location,
        });
    }

    Ok(lsproto::SymbolInformationsOrWorkspaceSymbolsOrNull {
        symbol_informations: Some(symbols),
        workspace_symbols: None,
    })
}

/// `shouldExcludeFile` — `nodes` is `file`'s arena.
fn should_exclude_file(
    nodes: &[Node],
    file: NodeId,
    program: &Rc<Program>,
    exclude_library_symbols: bool,
) -> bool {
    exclude_library_symbols
        && (is_inside_node_modules(nodes[file].as_source_file().file_name())
            || program.is_lib_file(file))
}

/// `isInsideNodeModules`.
fn is_inside_node_modules(file_name: &RootedFilePath) -> bool {
    file_name.contains_lowercase_directory_sequence("/node_modules/")
}

/// `getMatchScore` — return a score for matching `s` against `pattern`.
fn get_match_score(s: &str, pattern: &str) -> i32 {
    let mut score: i32 = 0;
    let mut s = s;
    for p in pattern.chars() {
        let exact = p.is_uppercase();
        loop {
            let Some(c) = s.chars().next() else {
                return -1;
            };
            s = &s[c.len_utf8()..];
            if (exact && c == p)
                || (!exact
                    && c.to_lowercase().collect::<String>()
                        == p.to_lowercase().collect::<String>())
            {
                break;
            }
            score += 1;
        }
    }
    score
}

/// `compareDeclarationInfos` — sort by ascending match score, then ascending
/// case insensitive name, then ascending case sensitive name, and finally by
/// source file name and position.
fn compare_declaration_infos(d1: &DeclarationInfo, d2: &DeclarationInfo) -> std::cmp::Ordering {
    if d1.match_score != d2.match_score {
        return d1.match_score.cmp(&d2.match_score);
    }
    let c = tsc_stringutil::compare_strings_case_insensitive(
        d1.name.as_bytes(),
        d2.name.as_bytes(),
    );
    if c != 0 {
        return c.cmp(&0);
    }
    let c = d1.name.cmp(&d2.name);
    if c != std::cmp::Ordering::Equal {
        return c;
    }
    if d1.path_key != d2.path_key {
        return d1.path_key.cmp(&d2.path_key);
    }
    d1.pos.cmp(&d2.pos)
}

/// `getSymbolKindFromNode` — converts an AST node to an LSP SymbolKind.
/// Combines getNodeKind with VS Code's fromProtocolScriptElementKind.
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
