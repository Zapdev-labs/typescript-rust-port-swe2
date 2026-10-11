// Ported from tsc/internal/ls/definition.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
//
// - `*ast.Symbol`/`*ast.Node`/`*checker.Signature`/`*checker.Type` are
//   `SymbolId`/`NodeId`/`SignatureId`/`TypeId`. Symbol fields are read via
//   `checker.symbol_arena.borrow()`; node fields via `program.nodes(...)`
//   snapshots.
// - `lsproto.Location`/`Range` do not implement `Hash`, so the Go
//   `collections.Set[lsproto.Location]` dedup in `combineDefinitionResponses`
//   is a linear `Vec` scan.
// - `getDeclarationsFromLocation`/`getDeclarationsFromObjectLiteralElement`/
//   `getDeclarationNameForKeyword` are the canonical copies (Go has them in
//   definition.go); `hover.rs` keeps sibling-owned local duplicates.

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::{self as ast, Kind, Node, NodeId, SymbolFlags, SymbolId};
use tsc_checker::checker_core::Checker;
use tsc_checker::types::{ContextFlags, TypeId};
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::text::{TextPos, TextRange};
use tsc_lsproto::{self as lsproto};
use tsc_scanner::scanner;
use tsc_spanmap::Feature;

use crate::api::Error;
use crate::findallreferences::RefInfo;
use crate::languageservice::LanguageService;
use crate::utilities::*;

impl<'h> LanguageService<'h> {
    /// `ProvideDefinition`.
    pub fn provide_definition(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
        position: lsproto::Position,
    ) -> Result<lsproto::DefinitionResponse, Error> {
        if self.user_preferences().prefer_go_to_source_definition {
            return self.provide_source_definition(ctx, document_uri, position);
        }
        self.provide_definition_worker(ctx, document_uri, position)
    }

    /// `provideDefinitionWorker`.
    fn provide_definition_worker(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
        position: lsproto::Position,
    ) -> Result<lsproto::DefinitionResponse, Error> {
        let caps = lsproto::get_client_capabilities(ctx);
        let client_supports_link = caps.text_document.definition.link_support;

        let (program, file) = self.get_program_and_file(document_uri);
        // PORT: `positions` holds `SourceFileScript`s that borrow the node's
        // arena, so `nodes` must outlive the projection loop.
        let nodes = program.nodes(file.file_index());
        let positions = self.converters.from_lsp_position_for_source_file(
            file,
            &nodes,
            position,
            Feature::Definition,
        );
        let mut results: Vec<lsproto::DefinitionResponse> = Vec::with_capacity(positions.len());
        for mapped in &positions {
            if mapped.fidelity.is_single_segment() {
                results.push(self.provide_definition_at_position(
                    ctx,
                    &program,
                    mapped.script.file,
                    mapped.position,
                    client_supports_link,
                ));
            }
        }
        Ok(combine_definition_responses(results, client_supports_link))
    }

    /// `provideDefinitionAtPosition`.
    pub(crate) fn provide_definition_at_position(
        &self,
        ctx: &Context,
        program: &Rc<Program>,
        file: NodeId,
        text_pos: TextPos,
        client_supports_link: bool,
    ) -> lsproto::DefinitionResponse {
        let pos = text_pos;
        let node = {
            let mut nodes = program.nodes_mut(file.file_index());
            tsc_astnav::tokens::get_touching_property_name(&mut nodes, file, pos)
        }
        .expect("GetTouchingPropertyName should return a node");
        let reference = {
            let mut nodes = program.nodes_mut(file.file_index());
            get_reference_at_position(&mut nodes, file, pos, program)
        };

        let nodes = program.nodes(file.file_index());
        if ast::is_source_file(&nodes[node]) {
            return lsproto::LocationOrLocationsOrDefinitionLinksOrNull::default();
        }
        drop(nodes);

        let (origin_selection_range, _fidelity) = self.create_lsp_range_from_node(node, file);
        if let Some(reference) = reference.as_ref().filter(|r| r.file.is_some()) {
            return self.create_definition_locations(
                origin_selection_range,
                client_supports_link,
                &[],
                Some(reference),
                Feature::Definition,
            );
        }

        let (checker, done) = program.get_type_checker_for_file(ctx.clone(), file);
        let result = self.provide_definition_at_position_worker(
            &checker,
            program,
            node,
            file,
            origin_selection_range,
            client_supports_link,
            reference.as_ref(),
        );
        drop(checker);
        done();
        result
    }

    /// Body of `provideDefinitionAtPosition` after the checker checkout.
    fn provide_definition_at_position_worker(
        &self,
        checker: &Rc<RefCell<Checker>>,
        program: &Rc<Program>,
        node: NodeId,
        file: NodeId,
        origin_selection_range: lsproto::Range,
        client_supports_link: bool,
        reference: Option<&RefInfo>,
    ) -> lsproto::DefinitionResponse {
        let nodes = program.nodes(file.file_index());

        if nodes[node].kind == Kind::OverrideKeyword {
            if let Some(sym) =
                get_symbol_for_overridden_member(&mut checker.borrow_mut(), node, &nodes)
            {
                let declarations = checker.borrow().symbol_arena.borrow()[sym.index()]
                    .declarations
                    .clone();
                drop(nodes);
                return self.create_definition_locations(
                    origin_selection_range,
                    client_supports_link,
                    &declarations,
                    None,
                    Feature::Definition,
                );
            }
        }

        if is_jump_statement_target(node, &nodes) {
            if let Some(label) = nodes[node].parent.and_then(|p| {
                get_target_label(&nodes, Some(p), &nodes[node].text(&nodes))
            }) {
                drop(nodes);
                return self.create_definition_locations(
                    origin_selection_range,
                    client_supports_link,
                    &[label],
                    None,
                    Feature::Definition,
                );
            }
        }

        if nodes[node].kind == Kind::CaseKeyword
            || nodes[node].kind == Kind::DefaultKeyword
                && nodes[node]
                    .parent
                    .is_some_and(|p| ast::is_default_clause(&nodes[p]))
        {
            if let Some(stmt) = ast::find_ancestor(nodes[node].parent, &nodes, &mut |n, _ns| {
                ast::is_switch_statement(n)
            }) {
                let stmt_file = ast::get_source_file_of_node(Some(stmt), &nodes)
                    .expect("source file of switch statement");
                let range = {
                    let stmt_nodes = program.nodes(stmt_file.file_index());
                    scanner::get_range_of_token_at_position(
                        stmt_nodes[stmt_file].as_source_file(),
                        nodes[stmt].pos() as usize,
                    )
                };
                drop(nodes);
                return self.create_location_from_file_and_range(
                    stmt_file,
                    range,
                    Feature::Definition,
                );
            }
        }

        if nodes[node].kind == Kind::ReturnKeyword
            || nodes[node].kind == Kind::YieldKeyword
            || nodes[node].kind == Kind::AwaitKeyword
        {
            if let Some(fn_decl) = ast::find_ancestor(Some(node), &nodes, &mut |n, ns| {
                ast::is_function_like_declaration(Some(n.id), ns)
            }) {
                drop(nodes);
                return self.create_definition_locations(
                    origin_selection_range,
                    client_supports_link,
                    &[fn_decl],
                    None,
                    Feature::Definition,
                );
            }
        }
        drop(nodes);

        let mut declarations = get_declarations_from_location(program, checker, node);
        let called_declaration = try_get_signature_declaration(checker, node, program);
        let nodes = program.nodes(file.file_index());
        let node_parent_is_jsx = nodes[node]
            .parent
            .is_some_and(|p| ast::is_jsx_opening_like_element(&nodes[p]));
        drop(nodes);
        if let Some(called_declaration) = called_declaration {
            let called_nodes = program.arena_of(called_declaration);
            if !(node_parent_is_jsx && is_jsx_constructor_like(called_declaration, &called_nodes)) {
                let name_node = get_declaration_name_for_keyword(program, node);
                let symbol = checker.borrow_mut().get_symbol_at_location_api(name_node);
                let matches_signature = symbol.is_some_and(|symbol| {
                    checker.borrow_mut().get_root_symbols(symbol).iter().any(
                        |&root_symbol| {
                            symbol_matches_signature(
                                checker,
                                root_symbol,
                                called_declaration,
                                program,
                            )
                        },
                    )
                });
                if matches_signature {
                    if !ast::is_constructor_declaration(&called_nodes[called_declaration]) {
                        declarations = Vec::new();
                    } else {
                        declarations.retain(|&d| {
                            d != called_declaration && {
                                let d_nodes = program.arena_of(d);
                                ast::is_class_declaration(&d_nodes[d])
                                    || ast::is_class_expression(&d_nodes[d])
                            }
                        });
                    }
                } else {
                    declarations.retain(|&d| d != called_declaration);
                }
                declarations.push(called_declaration);
            }
        }
        self.create_definition_locations(
            origin_selection_range,
            client_supports_link,
            &declarations,
            reference,
            Feature::Definition,
        )
    }

    /// `ProvideTypeDefinition`.
    pub fn provide_type_definition(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
        position: lsproto::Position,
    ) -> Result<lsproto::TypeDefinitionResponse, Error> {
        let caps = lsproto::get_client_capabilities(ctx);
        let client_supports_link = caps.text_document.type_definition.link_support;

        let (program, file) = self.get_program_and_file(document_uri);
        let nodes = program.nodes(file.file_index());
        let positions = self.converters.from_lsp_position_for_source_file(
            file,
            &nodes,
            position,
            Feature::TypeDefinition,
        );
        let mut results: Vec<lsproto::TypeDefinitionResponse> =
            Vec::with_capacity(positions.len());
        for mapped in &positions {
            if mapped.fidelity.is_single_segment() {
                results.push(self.provide_type_definition_at_position(
                    ctx,
                    &program,
                    mapped.script.file,
                    mapped.position,
                    client_supports_link,
                ));
            }
        }
        Ok(combine_definition_responses(results, client_supports_link))
    }

    /// `provideTypeDefinitionAtPosition`.
    fn provide_type_definition_at_position(
        &self,
        ctx: &Context,
        program: &Rc<Program>,
        file: NodeId,
        text_pos: TextPos,
        client_supports_link: bool,
    ) -> lsproto::TypeDefinitionResponse {
        let node = {
            let mut nodes = program.nodes_mut(file.file_index());
            tsc_astnav::tokens::get_touching_property_name(&mut nodes, file, text_pos)
        }
        .expect("GetTouchingPropertyName should return a node");

        if ast::is_source_file(&program.nodes(file.file_index())[node]) {
            return lsproto::LocationOrLocationsOrDefinitionLinksOrNull::default();
        }
        let (origin_selection_range, _fidelity) = self.create_lsp_range_from_node(node, file);

        let (checker, done) = program.get_type_checker_for_file(ctx.clone(), file);
        let result =
            self.provide_type_definition_at_position_worker(&checker, program, node, file);
        drop(checker);
        done();

        match result {
            Some(declarations) => self.create_definition_locations(
                origin_selection_range,
                client_supports_link,
                &declarations,
                None,
                Feature::TypeDefinition,
            ),
            None => lsproto::LocationOrLocationsOrDefinitionLinksOrNull::default(),
        }
    }

    /// Body of `provideTypeDefinitionAtPosition` after the checker checkout.
    /// Returns the declaration list on success.
    fn provide_type_definition_at_position_worker(
        &self,
        checker: &Rc<RefCell<Checker>>,
        program: &Rc<Program>,
        node: NodeId,
        _file: NodeId,
    ) -> Option<Vec<NodeId>> {
        let node = get_declaration_name_for_keyword(program, node);

        let symbol = checker.borrow_mut().get_symbol_at_location_api(node)?;
        let symbol_type = get_type_of_symbol_at_location(checker, symbol, node, program);
        let mut declarations = get_declarations_from_type(checker, symbol_type);
        if let Some(type_argument) = checker
            .borrow_mut()
            .get_first_type_argument_from_known_type(symbol_type)
        {
            let mut argument_declarations =
                get_declarations_from_type(checker, type_argument);
            argument_declarations.extend(declarations);
            declarations = argument_declarations;
        }
        if !declarations.is_empty() {
            return Some(declarations);
        }
        let flags = checker.borrow().symbol_arena.borrow()[symbol.index()].flags;
        if !flags.intersects(SymbolFlags::VALUE) && flags.intersects(SymbolFlags::TYPE) {
            let declarations = checker.borrow().symbol_arena.borrow()[symbol.index()]
                .declarations
                .clone();
            return Some(declarations);
        }
        None
    }

    /// `createDefinitionLocations`.
    fn create_definition_locations(
        &self,
        origin_selection_range: lsproto::Range,
        client_supports_link: bool,
        declarations: &[NodeId],
        reference: Option<&RefInfo>,
        feature: Feature,
    ) -> lsproto::DefinitionResponse {
        let mut locations: Vec<lsproto::LocationLink> = Vec::new();
        // `fileRange{file, textRange}` dedup — `(NodeId, TextRange)` is `Eq+Hash`,
        // but a `Vec` scan is fine (declaration lists are small) and avoids a
        // `Hash` requirement on `NodeId`.
        let mut location_ranges: Vec<(NodeId, TextRange)> = Vec::new();

        if let Some(reference) = reference {
            let target_range = lsproto::Range {
                start: lsproto::Position {
                    line: 0,
                    character: 0,
                },
                end: lsproto::Position {
                    line: 0,
                    character: 0,
                },
            };
            locations.push(lsproto::LocationLink {
                origin_selection_range: Some(origin_selection_range.clone()),
                target_uri: tsc_lsconv::converters::file_name_to_document_uri(
                    &reference.file_name,
                ),
                target_range: target_range.clone(),
                target_selection_range: target_range,
                ..Default::default()
            });
        }

        for &decl in declarations {
            let decl_nodes = self.program.nodes(decl.file_index());
            let Some(file) = ast::get_source_file_of_node(Some(decl), &decl_nodes) else {
                continue;
            };
            let name =
                ast::get_name_of_declaration(Some(decl), &decl_nodes).unwrap_or(decl);
            let name_range = if decl_nodes[name].kind == Kind::EmptyStatement {
                TextRange::new(decl_nodes[name].pos(), decl_nodes[name].pos())
            } else {
                create_range_from_node(name, file, &decl_nodes)
            };
            if location_ranges.contains(&(file, name_range)) {
                continue;
            }
            location_ranges.push((file, name_range));
            let context_node = crate::findallreferences::get_context_node(decl, &decl_nodes)
                .unwrap_or(decl);
            let context_range = to_context_range(name_range, file, Some(context_node), &decl_nodes)
                .unwrap_or(name_range);
            let context_range = if !name_range.contained_by(&context_range) {
                let enclosing_range = TextRange::new(
                    name_range.pos().min(context_range.pos()),
                    name_range.end().max(context_range.end()),
                );
                enclosing_range
            } else {
                context_range
            };
            let (target_selection_loc, selection_fidelity) = self
                .source_file_range_to_lsp_location_for_feature(file, name_range, feature);
            if !selection_fidelity.is_single_segment() {
                continue;
            }
            let (mut target_loc, context_fidelity) =
                self.source_file_range_to_lsp_location(file, context_range);
            if context_fidelity.is_none()
                || target_loc.uri != target_selection_loc.uri
                || !lsp_range_contains(&target_loc.range, &target_selection_loc.range)
            {
                target_loc = target_selection_loc.clone();
            }
            locations.push(lsproto::LocationLink {
                origin_selection_range: Some(origin_selection_range.clone()),
                target_selection_range: target_selection_loc.range,
                target_uri: target_loc.uri,
                target_range: target_loc.range,
                ..Default::default()
            });
        }

        if client_supports_link {
            return lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
                definition_links: Some(locations),
                ..Default::default()
            };
        }
        create_locations_from_links(&locations)
    }

    /// `createLocationFromFileAndRange`.
    fn create_location_from_file_and_range(
        &self,
        file: NodeId,
        text_range: TextRange,
        feature: Feature,
    ) -> lsproto::DefinitionResponse {
        let (mut mapped_location, fidelity) =
            self.source_file_range_to_lsp_location_for_feature(file, text_range, feature);
        if fidelity.is_none() {
            mapped_location.range = lsproto::Range::default();
        }
        lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
            location: Some(mapped_location),
            ..Default::default()
        }
    }
}

/// `combineDefinitionResponses`.
pub(crate) fn combine_definition_responses(
    results: Vec<lsproto::DefinitionResponse>,
    links: bool,
) -> lsproto::DefinitionResponse {
    let mut locations: Vec<lsproto::Location> = Vec::new();
    let mut definition_links: Vec<lsproto::LocationLink> = Vec::new();
    // `collections.Set[lsproto.Location]` — `Location` is not `Hash`, so dedup
    // with a linear scan (result sets are small).
    let mut seen: Vec<lsproto::Location> = Vec::new();
    for result in &results {
        if let Some(links) = &result.definition_links {
            for link in links {
                let location = lsproto::Location {
                    uri: link.target_uri.clone(),
                    range: link.target_selection_range.clone(),
                };
                if !seen.contains(&location) {
                    seen.push(location.clone());
                    definition_links.push(link.clone());
                    locations.push(location);
                }
            }
        }
        if let Some(location) = &result.location {
            if !seen.contains(location) {
                seen.push(location.clone());
                locations.push(location.clone());
                definition_links.push(lsproto::LocationLink {
                    target_uri: location.uri.clone(),
                    target_range: location.range.clone(),
                    target_selection_range: location.range.clone(),
                    ..Default::default()
                });
            }
        }
        if let Some(result_locations) = &result.locations {
            for location in result_locations {
                if !seen.contains(location) {
                    seen.push(location.clone());
                    locations.push(location.clone());
                    definition_links.push(lsproto::LocationLink {
                        target_uri: location.uri.clone(),
                        target_range: location.range.clone(),
                        target_selection_range: location.range.clone(),
                        ..Default::default()
                    });
                }
            }
        }
    }
    if links {
        return lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
            definition_links: Some(definition_links),
            ..Default::default()
        };
    }
    lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
        locations: Some(locations),
        ..Default::default()
    }
}

/// `getDeclarationNameForKeyword` — canonical copy (Go: definition.go);
/// `hover.rs` has a sibling-owned duplicate.
pub(crate) fn get_declaration_name_for_keyword(program: &Rc<Program>, node: NodeId) -> NodeId {
    let nodes = program.arena_of(node);
    let kind = nodes[node].kind;
    if kind >= Kind::FIRST_KEYWORD && kind <= Kind::LAST_KEYWORD {
        if let Some(parent) = nodes[node].parent {
            if ast::is_variable_declaration_list(&nodes[parent]) {
                if let Some(decl) = nodes[parent]
                    .as_variable_declaration_list()
                    .declarations
                    .as_ref()
                    .and_then(|d| d.nodes().first())
                    .copied()
                {
                    if nodes[decl].name().is_some() {
                        return nodes[decl].name().expect("name");
                    }
                }
            } else if nodes[parent].declaration_data().is_some()
                && nodes[parent].name().is_some()
                && nodes[node].pos() < nodes[nodes[parent].name().expect("name")].pos()
            {
                return nodes[parent].name().expect("name");
            }
        }
    }
    node
}

/// `lspRangeContains`.
pub(crate) fn lsp_range_contains(outer: &lsproto::Range, inner: &lsproto::Range) -> bool {
    lsproto::compare_positions(&outer.start, &inner.start) <= 0
        && lsproto::compare_positions(&inner.end, &outer.end) <= 0
}

/// `createLocationsFromLinks`.
fn create_locations_from_links(
    links: &[lsproto::LocationLink],
) -> lsproto::DefinitionResponse {
    let locations: Vec<lsproto::Location> = links
        .iter()
        .map(|link| lsproto::Location {
            uri: link.target_uri.clone(),
            range: link.target_selection_range.clone(),
        })
        .collect();
    lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
        locations: Some(locations),
        ..Default::default()
    }
}

/// `getDeclarationsFromLocation` — canonical copy (Go: definition.go).
pub(crate) fn get_declarations_from_location(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    node: NodeId,
) -> Vec<NodeId> {
    {
        let nodes = program.arena_of(node);
        if ast::is_identifier(&nodes[node])
            && nodes[node]
                .parent
                .is_some_and(|p| ast::is_shorthand_property_assignment(&nodes[p]))
        {
            // Because name in short-hand property assignment has two different meanings: property name and property value,
            // using go-to-definition at such position should go to the variable declaration of the property value rather than
            // go to the declaration of the property name (in this case stay at the same position). However, if go-to-definition
            // is performed at the location of property access, we would like to go to definition of the property in the short-hand
            // assignment. This case and others are handled by the following code.
            // and the contextual type's property declarations
            drop(nodes);
            let shorthand_symbol = c.borrow_mut().get_resolved_symbol(node);
            // PORT: Go checks `shorthandSymbol != nil`; the Rust checker
            // returns `unknown_symbol` for a failed resolution instead.
            let mut declarations: Vec<NodeId> = if shorthand_symbol
                != c.borrow().get_unknown_symbol()
            {
                let arena = c.borrow().symbol_arena.clone();
                arena.borrow()[shorthand_symbol.index()].declarations.clone()
            } else {
                Vec::new()
            };
            let mut contextual_declarations =
                get_declarations_from_object_literal_element(program, c, node);
            declarations.append(&mut contextual_declarations);
            return declarations;
        }

        if ast::is_property_name(&nodes[node])
            && nodes[node]
                .parent
                .is_some_and(|p| ast::is_binding_element(&nodes[p]))
            && nodes[nodes[node].parent.expect("parent")]
                .parent
                .is_some_and(|p| ast::is_object_binding_pattern(&nodes[p]))
        {
            // If the node is the name of a BindingElement within an ObjectBindingPattern instead of just returning the
            // declaration of the symbol (which is itself), we should try to get to the original type of the
            // ObjectBindingPattern and return the property declaration for the referenced property.
            let parent = nodes[node].parent.expect("parent");
            let grandparent = nodes[parent].parent.expect("grandparent");
            let binding_el = &nodes[parent].as_binding_element();
            let binding_el_matches = binding_el.dot_dot_dot_token.is_none()
                && Some(node) == binding_el.property_name.or(nodes[parent].name());
            if binding_el_matches {
                if let Some(name) = ast::try_get_text_of_property_name(node, &nodes).0 {
                    drop(nodes);
                    let t = c.borrow_mut().get_type_at_location(grandparent);
                    let mut types = vec![t];
                    if c.borrow().types.get(t).is_union() {
                        types = c.borrow().types.get(t).types().to_vec();
                    }
                    let mut result = Vec::new();
                    for union_type in types {
                        if let Some(prop) =
                            c.borrow_mut().get_property_of_type(union_type, &name)
                        {
                            let arena = c.borrow().symbol_arena.clone();
                            result.extend(
                                arena.borrow()[prop.index()].declarations.iter().copied(),
                            );
                        }
                    }
                    return result;
                }
            }
        }
    }

    let node = get_declaration_name_for_keyword(program, node);
    if let Some(symbol) = c.borrow_mut().get_symbol_at_location_api(node) {
        let mut symbol = symbol;
        {
            let arena = c.borrow().symbol_arena.clone();
            let arena = arena.borrow();
            let flags = arena[symbol.index()].flags;
            if flags.intersects(SymbolFlags::CLASS)
                && !flags.intersects(SymbolFlags::FUNCTION | SymbolFlags::VARIABLE)
                && {
                    let nodes = program.arena_of(node);
                    nodes[node].kind == Kind::ConstructorKeyword
                }
            {
                if let Some(constructor) = arena[symbol.index()]
                    .members
                    .get(ast::INTERNAL_SYMBOL_NAME_CONSTRUCTOR)
                    .copied()
                {
                    symbol = constructor;
                }
            }
        }
        if c.borrow().symbol_arena.borrow()[symbol.index()]
            .flags
            .intersects(SymbolFlags::ALIAS)
        {
            if let Some(resolved) = c.borrow_mut().get_aliased_symbol(symbol) {
                symbol = resolved;
            }
        }
        let object_literal_element_declarations =
            get_declarations_from_object_literal_element(program, c, node);
        if !object_literal_element_declarations.is_empty() {
            return object_literal_element_declarations;
        }
        let declarations = {
            let arena = c.borrow().symbol_arena.clone();
            arena.borrow()[symbol.index()].declarations.clone()
        };
        if !declarations.is_empty() {
            return declarations;
        }
    }
    let index_infos = c.borrow_mut().get_index_signatures_at_location(node);
    if !index_infos.is_empty() {
        return index_infos;
    }
    Vec::new()
}

/// `getDeclarationsFromObjectLiteralElement` — returns declarations from the
/// contextual type of an object literal element, if available.
pub(crate) fn get_declarations_from_object_literal_element(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    node: NodeId,
) -> Vec<NodeId> {
    let Some(element) = ({
        let nodes = program.arena_of(node);
        get_containing_object_literal_element(node, &nodes)
    }) else {
        return Vec::new();
    };

    let element_parent = program.arena_of(element)[element].parent;
    let Some(element_parent) = element_parent else {
        return Vec::new();
    };
    let Some(contextual_type) = c
        .borrow_mut()
        .get_contextual_type_api(element_parent, ContextFlags::NONE)
    else {
        return Vec::new();
    };

    let mut properties = c.borrow_mut().get_property_symbols_from_contextual_type(
        element,
        contextual_type,
        false, /*unionSymbolOk*/
    );
    {
        let arena = c.borrow().symbol_arena.clone();
        let arena = arena.borrow();
        let found = properties.iter().any(|&p| {
            arena[p.index()].value_declaration.is_some_and(|vd| {
                let nodes = program.arena_of(vd);
                nodes[vd]
                    .parent
                    .is_some_and(|par| ast::is_object_literal_expression(&nodes[par]))
                    && ast::is_object_literal_element(&nodes[vd])
                    && nodes[vd].name() == Some(node)
            })
        });
        drop(arena);
        if found {
            if let Some(without_node_inferences_type) =
                c.borrow_mut().get_contextual_type_api(
                    element_parent,
                    ContextFlags::IGNORE_NODE_INFERENCES,
                )
            {
                let without_node_inferences_properties =
                    c.borrow_mut().get_property_symbols_from_contextual_type(
                        element,
                        without_node_inferences_type,
                        false, /*unionSymbolOk*/
                    );
                if !without_node_inferences_properties.is_empty() {
                    properties = without_node_inferences_properties;
                }
            }
        }
    }

    let mut result = Vec::new();
    {
        let arena = c.borrow().symbol_arena.clone();
        let arena = arena.borrow();
        for prop in properties {
            result.extend(arena[prop.index()].declarations.iter().copied());
        }
    }
    result
}

/// `getAncestorCallLikeExpression` — returns a CallLikeExpression where `node`
/// is the target being invoked.
fn get_ancestor_call_like_expression(
    node: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    let target = ast::find_ancestor(Some(node), nodes, &mut |n, ns| {
        !ast::is_right_side_of_property_access(n.id, ns)
    })?;
    let call_like = nodes[target].parent?;
    if ast::is_call_like_expression(&nodes[call_like], nodes)
        && ast::get_invoked_expression(&nodes[call_like], nodes) == Some(target)
    {
        return Some(call_like);
    }
    None
}

/// `tryGetSignatureDeclaration`.
pub(crate) fn try_get_signature_declaration(
    checker: &Rc<RefCell<Checker>>,
    node: NodeId,
    program: &Rc<Program>,
) -> Option<NodeId> {
    let call_like = {
        let nodes = program.arena_of(node);
        get_ancestor_call_like_expression(node, &nodes)
    };
    let signature =
        call_like.and_then(|call_like| checker.borrow_mut().get_resolved_signature_api(call_like));
    // Don't go to a function type, go to the value having that type.
    if let Some(signature) = signature {
        let declaration = checker.borrow().signature_arena.get(signature).declaration;
        if let Some(declaration) = declaration {
            let nodes = program.arena_of(declaration);
            if ast::is_function_like(Some(declaration), &nodes)
                && !ast::is_function_type_node(&nodes[declaration])
            {
                return Some(declaration);
            }
        }
    }
    None
}

/// `isJsxConstructorLike`.
fn is_jsx_constructor_like(node: NodeId, nodes: &[Node]) -> bool {
    ast::is_constructor_declaration(&nodes[node])
        || ast::is_constructor_type_node(&nodes[node])
        || ast::is_call_signature_declaration(&nodes[node])
        || ast::is_construct_signature_declaration(&nodes[node])
}

/// `symbolMatchesSignature`.
fn symbol_matches_signature(
    checker: &Rc<RefCell<Checker>>,
    symbol: SymbolId,
    called_declaration: NodeId,
    program: &Rc<Program>,
) -> bool {
    let nodes = program.arena_of(called_declaration);
    let called_symbol = nodes[called_declaration].symbol();
    if Some(symbol) == called_symbol {
        return true;
    }
    if let Some(called_symbol) = called_symbol {
        let called_parent = checker.borrow().symbol_arena.borrow()[called_symbol.index()].parent;
        if called_parent == Some(symbol) {
            return true;
        }
    }
    let Some(parent) = nodes[called_declaration].parent else {
        return false;
    };
    ast::is_assignment_expression(&nodes[parent], &nodes, false /*excludeCompoundAssignment*/)
        || !ast::is_call_like_expression(&nodes[parent], &nodes)
            && ast::can_have_symbol(&nodes[parent])
            && nodes[parent].symbol() == Some(symbol)
}

/// `getSymbolForOverriddenMember`.
fn get_symbol_for_overridden_member(
    checker: &mut Checker,
    node: NodeId,
    nodes: &[Node],
) -> Option<SymbolId> {
    let class_element =
        ast::find_ancestor(Some(node), nodes, &mut |n, _ns| ast::is_class_element(n))?;
    if nodes[class_element].name().is_none() {
        return None;
    }
    let base_declaration = ast::find_ancestor(
        Some(class_element),
        nodes,
        &mut |n, ns| ast::is_class_like(Some(n.id), ns),
    )?;
    let base_type_node =
        ast::get_class_extends_heritage_element(&nodes[base_declaration], nodes)?;
    let expression = ast::skip_parentheses(
        nodes[base_type_node]
            .expression()
            .expect("heritage element expression"),
        nodes,
    );
    let base = if ast::is_class_expression(&nodes[expression]) {
        nodes[expression].symbol()
    } else {
        checker.get_symbol_at_location_api(expression)
    }?;
    let name =
        ast::get_text_of_property_name(nodes[class_element].name()?, nodes);
    if ast::has_static_modifier(&nodes[class_element]) {
        let base_type = checker.get_type_of_symbol(base);
        checker.get_property_of_type(base_type, &name)
    } else {
        let base_type = checker.get_declared_type_of_symbol(base);
        checker.get_property_of_type(base_type, &name)
    }
}

/// `getTypeOfSymbolAtLocation`.
fn get_type_of_symbol_at_location(
    c: &Rc<RefCell<Checker>>,
    symbol: SymbolId,
    node: NodeId,
    program: &Rc<Program>,
) -> TypeId {
    let t = c.borrow_mut().get_type_of_symbol_at_location(symbol, Some(node));
    // If the type is just a function's inferred type, go-to-type should go to
    // the return type instead since go-to-definition takes you to the
    // function anyway.
    let t_symbol = c.borrow().types.get(t).symbol();
    let symbol_value_declaration = c.borrow().symbol_arena.borrow()[symbol.index()]
        .value_declaration;
    let inferred = t_symbol == Some(symbol)
        || t_symbol.is_some_and(|ts| {
            symbol_value_declaration.is_some_and(|vd| {
                let vd_nodes = program.arena_of(vd);
                ast::is_variable_declaration(&vd_nodes[vd])
                    && vd_nodes[vd].initializer()
                        == c.borrow().symbol_arena.borrow()[ts.index()].value_declaration
            })
        });
    if inferred {
        let sigs = c.borrow_mut().get_call_signatures(t);
        if sigs.len() == 1 {
            return c.borrow_mut().get_return_type_of_signature(sigs[0]);
        }
    }
    t
}

/// `getDeclarationsFromType`.
fn get_declarations_from_type(c: &Rc<RefCell<Checker>>, t: TypeId) -> Vec<NodeId> {
    let mut result: Vec<NodeId> = Vec::new();
    for t in c.borrow().types.get(t).distributed(t) {
        if let Some(symbol) = c.borrow().types.get(t).symbol() {
            let arena = c.borrow().symbol_arena.clone();
            for decl in arena.borrow()[symbol.index()].declarations.iter().copied() {
                if !result.contains(&decl) {
                    result.push(decl);
                }
            }
        }
    }
    result
}
