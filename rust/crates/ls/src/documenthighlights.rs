// Ported from tsc/internal/ls/documenthighlights.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
//
// - `*ast.Node`/`*ast.SourceFile` are `NodeId`s; every node access goes
//   through the file's arena (`program.nodes(file.file_index())`, or
//   `nodes_mut` for `get_children_from_non_jsdoc_node`/`get_first_token`/
//   `find_child_of_kind`, which need `&mut Vec<Node>`).
// - `getThrowStatementOwner`'s `child` sentinel is `Option<NodeId>`; the Go
//   "return child" for try-ownership is `Some(child)`.
// - `collections.Set[lsproto.Range]` dedup is a linear `Vec` scan (`Range`
//   is not `Hash`).
// - `useParent`/`highlightSpans`/`getFromAllDeclarations` become
//   `LanguageService` methods because they call
//   `create_lsp_range_from_node_for_feature`.

use std::rc::Rc;

use tsc_ast::{self as ast, FindAncestorResult, Kind, ModifierFlags, Node, NodeId};
use tsc_astnav::tokens;
use tsc_compiler::program::Program;
use tsc_collections::Set;
use tsc_core::context::Context;
use tsc_lsconv::converters;
use tsc_lsproto::{self as lsproto};
use tsc_lsutil::get_first_token;
use tsc_spanmap::Feature;
use tsc_tspath::RootedFilePath;

use crate::api::Error;
use crate::findallreferences::{
    EntryKind, RefOptions, ReferenceEntry, ReferenceUse, is_write_access_for_reference,
};
use crate::languageservice::LanguageService;
use crate::utilities::*;

impl<'h> LanguageService<'h> {
    /// `ProvideDocumentHighlights`.
    pub fn provide_document_highlights(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
        document_position: lsproto::Position,
    ) -> Result<lsproto::DocumentHighlightResponse, Error> {
        let result = self.provide_document_highlights_worker(
            ctx,
            document_uri,
            document_position,
            &[],
        )?;
        // Extract highlights for the current file only.
        let mut document_highlights: Vec<lsproto::DocumentHighlight> = Vec::new();
        if let Some(multi_highlights) = &result.multi_document_highlights {
            for mh in multi_highlights {
                if mh.uri == *document_uri {
                    if let Some(highlights) = &mh.highlights {
                        document_highlights.extend(highlights.iter().cloned());
                    }
                }
            }
        }
        Ok(lsproto::DocumentHighlightsOrNull {
            document_highlights: Some(document_highlights),
        })
    }

    /// `ProvideMultiDocumentHighlights`.
    pub fn provide_multi_document_highlights(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
        document_position: lsproto::Position,
        files_to_search: &[lsproto::DocumentUri],
    ) -> Result<lsproto::CustomMultiDocumentHighlightResponse, Error> {
        self.provide_document_highlights_worker(
            ctx,
            document_uri,
            document_position,
            files_to_search,
        )
    }

    /// `provideDocumentHighlightsWorker`.
    fn provide_document_highlights_worker(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
        document_position: lsproto::Position,
        files_to_search: &[lsproto::DocumentUri],
    ) -> Result<lsproto::MultiDocumentHighlightsOrNull, Error> {
        let (program, source_file) = self.get_program_and_file(document_uri);
        let nodes = program.nodes(source_file.file_index());
        let positions = self.converters.from_lsp_position_for_source_file(
            source_file,
            &nodes,
            document_position,
            Feature::DocumentHighlights,
        );
        let mut results: Vec<lsproto::MultiDocumentHighlightsOrNull> =
            Vec::with_capacity(positions.len());
        for mapped in &positions {
            if mapped.fidelity.is_single_segment() {
                results.push(self.provide_document_highlights_at_position(
                    ctx,
                    document_uri,
                    mapped.position,
                    &program,
                    mapped.script.file,
                    files_to_search,
                ));
            }
        }
        Ok(combine_multi_document_highlights(results))
    }

    /// `provideDocumentHighlightsAtPosition`.
    fn provide_document_highlights_at_position(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
        position: i32,
        program: &Rc<Program>,
        source_file: NodeId,
        files_to_search: &[lsproto::DocumentUri],
    ) -> lsproto::MultiDocumentHighlightsOrNull {
        let node = {
            let mut nodes = program.nodes_mut(source_file.file_index());
            tokens::get_touching_property_name(&mut nodes, source_file, position)
        }
        .expect("GetTouchingPropertyName should return a node");

        let nodes = program.nodes(source_file.file_index());

        // Cheap JSX check before resolving files to search.
        if let Some(parent) = nodes[node].parent {
            if nodes[parent].kind == Kind::JsxClosingElement
                || (nodes[parent].kind == Kind::JsxOpeningElement
                    && nodes[parent].tag_name() == Some(node))
            {
                let (opening_element, closing_element) = nodes[parent]
                    .parent
                    .map(|gp| {
                        if ast::is_jsx_element(&nodes[gp]) {
                            let jsx = nodes[gp].as_jsx_element();
                            (jsx.opening_element, jsx.closing_element)
                        } else {
                            (None, None)
                        }
                    })
                    .unwrap_or((None, None));
                let mut highlights: Vec<lsproto::DocumentHighlight> = Vec::new();
                let kind = lsproto::DocumentHighlightKind::Read;
                for element in [opening_element, closing_element].into_iter().flatten() {
                    let (lsp_range, fidelity) = self.create_lsp_range_from_node_for_feature(
                        element,
                        source_file,
                        Feature::DocumentHighlights,
                    );
                    if !fidelity.is_none() {
                        highlights.push(lsproto::DocumentHighlight {
                            range: lsp_range,
                            kind: Some(kind),
                            ..Default::default()
                        });
                    }
                }
                return lsproto::MultiDocumentHighlightsOrNull {
                    multi_document_highlights: Some(vec![lsproto::MultiDocumentHighlight {
                        uri: document_uri.clone(),
                        highlights: Some(highlights),
                        ..Default::default()
                    }]),
                    ..Default::default()
                };
            }
        }

        // Resolve the source files to search, deduplicating by file name.
        let mut source_files: Vec<NodeId> = Vec::new();
        let mut seen_files: Set<RootedFilePath> = Set::new();
        for uri in files_to_search {
            let file_name = uri.file_name();
            if !seen_files.add_if_absent(file_name.clone()) {
                continue;
            }
            if let Some(sf) = program.get_source_file(&file_name) {
                source_files.push(sf);
            }
        }
        if source_files.is_empty() {
            source_files = vec![source_file];
        }
        drop(nodes);

        let mut multi_highlights =
            self.get_semantic_document_highlights(ctx, position, node, program, &source_files);
        if multi_highlights.is_empty() {
            // Fall back to syntactic highlights for the current file only.
            let syntactic_highlights = self.get_syntactic_document_highlights(node, source_file);
            if !syntactic_highlights.is_empty() {
                multi_highlights = vec![lsproto::MultiDocumentHighlight {
                    uri: document_uri.clone(),
                    highlights: Some(syntactic_highlights),
                    ..Default::default()
                }];
            }
        }
        lsproto::MultiDocumentHighlightsOrNull {
            multi_document_highlights: Some(multi_highlights),
            ..Default::default()
        }
    }

    /// `getSemanticDocumentHighlights`.
    fn get_semantic_document_highlights(
        &self,
        ctx: &Context,
        position: i32,
        node: NodeId,
        program: &Rc<Program>,
        source_files: &[NodeId],
    ) -> Vec<lsproto::MultiDocumentHighlight> {
        let options = RefOptions {
            use_: ReferenceUse::None,
            ..Default::default()
        };
        let reference_entries = self.get_referenced_symbols_for_node(
            ctx,
            position,
            node,
            program,
            source_files,
            options,
        );
        if reference_entries.is_empty() {
            return Vec::new();
        }

        // Group highlights by file
        let mut file_highlights: std::collections::HashMap<String, Vec<lsproto::DocumentHighlight>> =
            std::collections::HashMap::new();
        for entry in &reference_entries {
            for ref_entry in &entry.borrow().references {
                let (file_name, highlight) = self.to_document_highlight(ref_entry);
                let Some(highlight) = highlight else {
                    continue;
                };
                file_highlights
                    .entry(file_name)
                    .or_default()
                    .push(highlight);
            }
        }

        let mut result: Vec<lsproto::MultiDocumentHighlight> = Vec::new();
        for &sf in source_files {
            let file_name = {
                let nodes = program.nodes(sf.file_index());
                nodes[sf].as_source_file().original_file_name(&nodes).clone()
            };
            if let Some(highlights) = file_highlights.get(file_name.as_string()) {
                result.push(lsproto::MultiDocumentHighlight {
                    uri: converters::file_name_to_document_uri(&file_name),
                    highlights: Some(highlights.clone()),
                    ..Default::default()
                });
            }
        }
        result
    }

    /// `toDocumentHighlight`.
    fn to_document_highlight(
        &self,
        entry: &Rc<std::cell::RefCell<ReferenceEntry>>,
    ) -> (String, Option<lsproto::DocumentHighlight>) {
        self.resolve_entry(entry);
        let (file_name, kind_is_range, node) = {
            let e = entry.borrow();
            let file_name = {
                let source_file = e.source_file.expect("source file");
                let nodes = self.program.nodes(source_file.file_index());
                nodes[source_file]
                    .as_source_file()
                    .original_file_name(&nodes)
                    .as_string()
                    .to_string()
            };
            (file_name, e.kind == EntryKind::Range, e.node)
        };

        let mut kind = lsproto::DocumentHighlightKind::Read;
        let (lsp_range, ok) =
            self.get_range_of_entry_for_feature(entry, Feature::DocumentHighlights);
        if !ok {
            return (file_name, None);
        }
        if kind_is_range {
            return (
                file_name,
                Some(lsproto::DocumentHighlight {
                    range: lsp_range,
                    kind: Some(kind),
                    ..Default::default()
                }),
            );
        }

        // Determine write access for node references.
        if let Some(node) = node {
            let nodes = self.program.nodes(node.file_index());
            if is_write_access_for_reference(node, &nodes) {
                kind = lsproto::DocumentHighlightKind::Write;
            }
        }

        (
            file_name,
            Some(lsproto::DocumentHighlight {
                range: lsp_range,
                kind: Some(kind),
                ..Default::default()
            }),
        )
    }

    /// `getSyntacticDocumentHighlights`.
    fn get_syntactic_document_highlights(
        &self,
        node: NodeId,
        source_file: NodeId,
    ) -> Vec<lsproto::DocumentHighlight> {
        let nodes = self.program.nodes(source_file.file_index());
        match nodes[node].kind {
            Kind::IfKeyword | Kind::ElseKeyword => {
                if let Some(parent) = nodes[node].parent {
                    if ast::is_if_statement(&nodes[parent]) {
                        drop(nodes);
                        return self.get_if_else_occurrences(parent, source_file);
                    }
                }
                Vec::new()
            }
            Kind::ReturnKeyword => self.use_parent(
                nodes[node].parent,
                &nodes,
                |n, _ns| ast::is_return_statement(n),
                get_return_occurrences,
                source_file,
            ),
            Kind::ThrowKeyword => self.use_parent(
                nodes[node].parent,
                &nodes,
                |n, _ns| ast::is_throw_statement(n),
                get_throw_occurrences,
                source_file,
            ),
            Kind::TryKeyword | Kind::CatchKeyword | Kind::FinallyKeyword => {
                let try_statement = if nodes[node].kind == Kind::CatchKeyword {
                    nodes[node].parent.and_then(|p| nodes[p].parent)
                } else {
                    nodes[node].parent
                };
                self.use_parent(
                    try_statement,
                    &nodes,
                    |n, _ns| ast::is_try_statement(n),
                    get_try_catch_finally_occurrences,
                    source_file,
                )
            }
            Kind::SwitchKeyword => self.use_parent(
                nodes[node].parent,
                &nodes,
                |n, _ns| ast::is_switch_statement(n),
                get_switch_case_default_occurrences,
                source_file,
            ),
            Kind::CaseKeyword | Kind::DefaultKeyword => {
                if let Some(parent) = nodes[node].parent {
                    if ast::is_default_clause(&nodes[parent])
                        || ast::is_case_clause(&nodes[parent])
                    {
                        let switch = nodes[parent].parent.and_then(|p| nodes[p].parent);
                        return self.use_parent(
                            switch,
                            &nodes,
                            |n, _ns| ast::is_switch_statement(n),
                            get_switch_case_default_occurrences,
                            source_file,
                        );
                    }
                }
                Vec::new()
            }
            Kind::BreakKeyword | Kind::ContinueKeyword => self.use_parent(
                nodes[node].parent,
                &nodes,
                |n, _ns| ast::is_break_or_continue_statement(n),
                get_break_or_continue_statement_occurrences,
                source_file,
            ),
            Kind::ForKeyword | Kind::WhileKeyword | Kind::DoKeyword => self.use_parent(
                nodes[node].parent,
                &nodes,
                |n, ns| ast::is_iteration_statement(n, ns, true),
                get_loop_break_continue_occurrences,
                source_file,
            ),
            Kind::ConstructorKeyword => self.get_from_all_declarations(
                |n, _ns| ast::is_constructor_declaration(n),
                &[Kind::ConstructorKeyword],
                node,
                source_file,
                &nodes,
            ),
            Kind::GetKeyword | Kind::SetKeyword => self.get_from_all_declarations(
                |n, _ns| ast::is_accessor(n),
                &[Kind::GetKeyword, Kind::SetKeyword],
                node,
                source_file,
                &nodes,
            ),
            Kind::AwaitKeyword => self.use_parent(
                nodes[node].parent,
                &nodes,
                |n, _ns| ast::is_await_expression(n),
                get_async_and_await_occurrences,
                source_file,
            ),
            Kind::AsyncKeyword => {
                let occurrences =
                    get_async_and_await_occurrences(node, source_file, &nodes, &self.program);
                self.highlight_spans(&occurrences, source_file)
            }
            Kind::YieldKeyword => {
                let occurrences =
                    get_yield_occurrences(node, source_file, &nodes, &self.program);
                self.highlight_spans(&occurrences, source_file)
            }
            Kind::InKeyword | Kind::OutKeyword => Vec::new(),
            _ => {
                if nodes[node].kind.is_modifier_kind()
                    && nodes[node].parent.is_some_and(|p| {
                        ast::is_declaration(&nodes[p])
                            || ast::is_variable_statement(&nodes[p])
                    })
                {
                    let parent = nodes[node].parent.expect("parent");
                    let occurrences = get_modifier_occurrences(
                        nodes[node].kind,
                        parent,
                        source_file,
                        &nodes,
                    );
                    self.highlight_spans(&occurrences, source_file)
                } else {
                    Vec::new()
                }
            }
        }
    }

    /// `useParent`.
    fn use_parent(
        &self,
        node: Option<NodeId>,
        nodes: &[Node],
        node_test: impl Fn(&Node, &[Node]) -> bool,
        get_nodes: fn(NodeId, NodeId, &[Node], &Rc<Program>) -> Vec<NodeId>,
        source_file: NodeId,
    ) -> Vec<lsproto::DocumentHighlight> {
        if let Some(node) = node {
            if node_test(&nodes[node], nodes) {
                let occurrences = get_nodes(node, source_file, nodes, &self.program);
                return self.highlight_spans(&occurrences, source_file);
            }
        }
        Vec::new()
    }

    /// `highlightSpans`.
    fn highlight_spans(
        &self,
        nodes: &[NodeId],
        source_file: NodeId,
    ) -> Vec<lsproto::DocumentHighlight> {
        if nodes.is_empty() {
            return Vec::new();
        }
        let mut highlights: Vec<lsproto::DocumentHighlight> = Vec::new();
        let kind = lsproto::DocumentHighlightKind::Read;
        for &node in nodes {
            let (lsp_range, fidelity) = self.create_lsp_range_from_node_for_feature(
                node,
                source_file,
                Feature::DocumentHighlights,
            );
            if !fidelity.is_none() {
                highlights.push(lsproto::DocumentHighlight {
                    range: lsp_range,
                    kind: Some(kind),
                    ..Default::default()
                });
            }
        }
        highlights
    }

    /// `getFromAllDeclarations`.
    fn get_from_all_declarations(
        &self,
        node_test: impl Fn(&Node, &[Node]) -> bool,
        keywords: &[Kind],
        node: NodeId,
        source_file: NodeId,
        nodes: &[Node],
    ) -> Vec<lsproto::DocumentHighlight> {
        let parent = nodes[node].parent;
        let Some(decl) = parent else {
            return Vec::new();
        };
        if !node_test(&nodes[decl], nodes) {
            return Vec::new();
        }
        let mut symbol_decls: Vec<NodeId> = Vec::new();
        if ast::can_have_symbol(&nodes[decl]) {
            if let Some(symbol) = nodes[decl].symbol() {
                let declarations = {
                    let symbols = self.program.symbols.clone();
                    symbols[symbol.index()].declarations.clone()
                };
                for d in declarations {
                    if node_test(&nodes[d], nodes) {
                        let children = {
                            let mut nodes_mut =
                                self.program.nodes_mut(source_file.file_index());
                            get_children_from_non_jsdoc_node(&mut nodes_mut, d, source_file)
                        };
                        let fresh = self.program.nodes(source_file.file_index());
                        'outer: for c in children {
                            for &k in keywords {
                                if fresh[c].kind == k {
                                    symbol_decls.push(c);
                                    break 'outer;
                                }
                            }
                        }
                    }
                }
            }
        }
        self.highlight_spans(&symbol_decls, source_file)
    }

    /// `getIfElseOccurrences`.
    fn get_if_else_occurrences(
        &self,
        if_statement: NodeId,
        source_file: NodeId,
    ) -> Vec<lsproto::DocumentHighlight> {
        let keywords = get_if_else_keywords(if_statement, source_file, &self.program);
        let kind = lsproto::DocumentHighlightKind::Read;
        let mut highlights: Vec<lsproto::DocumentHighlight> = Vec::new();

        // We'd like to highlight else/ifs together if they are only separated
        // by whitespace (i.e. the keywords are separated by no comments, no
        // newlines).
        let mut i = 0;
        while i < keywords.len() {
            let nodes = self.program.nodes(source_file.file_index());
            if nodes[keywords[i]].kind == Kind::ElseKeyword && i < keywords.len() - 1 {
                let else_keyword = keywords[i];
                let if_keyword = keywords[i + 1]; // this *should* always be an 'if' keyword.
                let mut should_combine = true;

                // Avoid recalculating getStart() by iterating backwards.
                let mut if_token_start = tsc_scanner::scanner::get_token_pos_of_node(
                    if_keyword,
                    nodes[source_file].as_source_file(),
                    false,
                    &nodes,
                );
                if if_token_start < 0 {
                    if_token_start = nodes[if_keyword].pos();
                }
                let text = nodes[source_file].as_source_file().text().to_string();
                let mut j = if_token_start - 1;
                while j >= nodes[else_keyword].end() {
                    let byte = text.as_bytes()[j as usize];
                    if !tsc_stringutil::is_white_space_single_line(byte as char) {
                        should_combine = false;
                        break;
                    }
                    j -= 1;
                }
                if should_combine {
                    let start = tsc_scanner::scanner::skip_trivia(
                        nodes[source_file].as_source_file().text(),
                        nodes[else_keyword].pos(),
                    );
                    let end = nodes[if_keyword].end();
                    drop(nodes);
                    let (lsp_range, fidelity) = self.create_lsp_range_from_bounds(
                        start,
                        end,
                        source_file,
                    );
                    if !fidelity.is_none() {
                        highlights.push(lsproto::DocumentHighlight {
                            range: lsp_range,
                            kind: Some(kind),
                            ..Default::default()
                        });
                    }
                    i += 2; // skip the next keyword
                    continue;
                }
            }
            let keyword = keywords[i];
            drop(nodes);
            let (lsp_range, fidelity) = self.create_lsp_range_from_node_for_feature(
                keyword,
                source_file,
                Feature::DocumentHighlights,
            );
            if !fidelity.is_none() {
                highlights.push(lsproto::DocumentHighlight {
                    range: lsp_range,
                    kind: Some(kind),
                    ..Default::default()
                });
            }
            i += 1;
        }
        highlights
    }
}

/// `combineMultiDocumentHighlights`.
fn combine_multi_document_highlights(
    results: Vec<lsproto::MultiDocumentHighlightsOrNull>,
) -> lsproto::MultiDocumentHighlightsOrNull {
    let mut by_uri: std::collections::HashMap<lsproto::DocumentUri, usize> =
        std::collections::HashMap::new();
    // `seen[uri] = Set[Range]` — linear scans (`Range` is not `Hash`).
    let mut seen: std::collections::HashMap<lsproto::DocumentUri, Vec<lsproto::Range>> =
        std::collections::HashMap::new();
    let mut combined_documents: Vec<lsproto::MultiDocumentHighlight> = Vec::new();
    for result in &results {
        let Some(documents) = &result.multi_document_highlights else {
            continue;
        };
        for document in documents {
            let idx = match by_uri.get(&document.uri) {
                Some(&idx) => idx,
                None => {
                    let idx = combined_documents.len();
                    combined_documents.push(lsproto::MultiDocumentHighlight {
                        uri: document.uri.clone(),
                        highlights: None,
                        ..Default::default()
                    });
                    by_uri.insert(document.uri.clone(), idx);
                    idx
                }
            };
            let ranges = seen.entry(document.uri.clone()).or_default();
            if let Some(highlights) = &document.highlights {
                for highlight in highlights {
                    if !ranges.contains(&highlight.range) {
                        ranges.push(highlight.range.clone());
                        combined_documents[idx]
                            .highlights
                            .get_or_insert_with(Vec::new)
                            .push(highlight.clone());
                    }
                }
            }
        }
    }
    lsproto::MultiDocumentHighlightsOrNull {
        multi_document_highlights: Some(combined_documents),
        ..Default::default()
    }
}

/// `getIfElseKeywords`.
fn get_if_else_keywords(
    if_statement: NodeId,
    source_file: NodeId,
    program: &Rc<Program>,
) -> Vec<NodeId> {
    let nodes = program.nodes(source_file.file_index());
    // We may be at an if statement like those in the range below:
    //
    //   ```
    //   if (...) {
    //   } else [|if (...) {}|]
    //   ````
    //
    // Traverse upwards through all parent if-statements linked by their
    // else-branches.
    let mut if_statement = if_statement;
    while nodes[if_statement]
        .parent
        .is_some_and(|p| ast::is_if_statement(&nodes[p]))
    {
        // See if the parent's `else` is actually the current `if` statement.
        let parenting_if = nodes[if_statement].parent.expect("if parent");
        let else_statement = nodes[parenting_if].as_if_statement().else_statement;
        if else_statement != Some(if_statement) {
            break;
        }
        if_statement = parenting_if;
    }

    let mut keywords: Vec<NodeId> = Vec::new();

    // Traverse back down through the else branches, aggregating if/else
    // keywords of if-statements.
    loop {
        let children = {
            let mut nodes_mut = program.nodes_mut(source_file.file_index());
            get_children_from_non_jsdoc_node(&mut nodes_mut, if_statement, source_file)
        };
        // `children` may include freshly created token nodes; re-fetch the
        // arena before indexing them.
        let nodes = program.nodes(source_file.file_index());
        if !children.is_empty() && nodes[children[0]].kind == Kind::IfKeyword {
            keywords.push(children[0]);
        }
        // Generally the 'else' keyword is second-to-last, so traverse
        // backwards.
        for c in children.iter().rev() {
            if nodes[*c].kind == Kind::ElseKeyword {
                keywords.push(*c);
                break;
            }
        }
        let else_statement = nodes[if_statement].as_if_statement().else_statement;
        match else_statement {
            Some(es) if ast::is_if_statement(&nodes[es]) => {
                if_statement = es;
            }
            _ => break,
        }
    }
    keywords
}

/// `getReturnOccurrences`.
fn get_return_occurrences(
    node: NodeId,
    source_file: NodeId,
    nodes: &[Node],
    program: &Rc<Program>,
) -> Vec<NodeId> {
    let Some(func_node) =
        ast::find_ancestor(nodes[node].parent, nodes, &mut |n, ns| {
            ast::is_function_like(Some(n.id), ns)
        })
    else {
        return Vec::new();
    };

    let mut keywords: Vec<NodeId> = Vec::new();
    if let Some(body) = nodes[func_node].body() {
        ast::for_each_return_statement(nodes, body, &mut |ret| {
            let mut nodes_mut = program.nodes_mut(source_file.file_index());
            if let Some(keyword) =
                tokens::find_child_of_kind(&mut nodes_mut, source_file, ret, Kind::ReturnKeyword)
            {
                keywords.push(keyword);
            }
            false // continue traversal
        });

        // Get all throw statements not in a try block
        let throw_statements = aggregate_owned_throw_statements(body, source_file, nodes, program);
        for throw in throw_statements {
            let mut nodes_mut = program.nodes_mut(source_file.file_index());
            if let Some(keyword) =
                tokens::find_child_of_kind(&mut nodes_mut, source_file, throw, Kind::ThrowKeyword)
            {
                keywords.push(keyword);
            }
        }
    }
    keywords
}

/// `aggregateOwnedThrowStatements`.
fn aggregate_owned_throw_statements(
    node: NodeId,
    source_file: NodeId,
    nodes: &[Node],
    program: &Rc<Program>,
) -> Vec<NodeId> {
    if ast::is_throw_statement(&nodes[node]) {
        return vec![node];
    }
    if ast::is_try_statement(&nodes[node]) {
        // Exceptions thrown within a try block lacking a catch clause are
        // "owned" in the current context.
        let statement = nodes[node].as_try_statement();
        let try_block = statement.try_block;
        let catch_clause = statement.catch_clause;
        let finally_block = statement.finally_block;

        let mut result = Vec::new();
        if let Some(catch_clause) = catch_clause {
            result = aggregate_owned_throw_statements(catch_clause, source_file, nodes, program);
        } else if let Some(try_block) = try_block {
            result = aggregate_owned_throw_statements(try_block, source_file, nodes, program);
        }
        if let Some(finally_block) = finally_block {
            result.extend(aggregate_owned_throw_statements(
                finally_block,
                source_file,
                nodes,
                program,
            ));
        }
        return result;
    }
    // Do not cross function boundaries.
    if ast::is_function_like(Some(node), nodes) {
        return Vec::new();
    }
    flat_map_children(node, source_file, nodes, program, aggregate_owned_throw_statements)
}

/// `flatMapChildren`.
fn flat_map_children(
    node: NodeId,
    _source_file: NodeId,
    nodes: &[Node],
    program: &Rc<Program>,
    cb: fn(NodeId, NodeId, &[Node], &Rc<Program>) -> Vec<NodeId>,
) -> Vec<NodeId> {
    let mut result = Vec::new();
    nodes[node].for_each_child(nodes, &mut |child| {
        let value = cb(child, _source_file, nodes, program);
        result.extend(value);
        false // continue traversal
    });
    result
}

/// `getThrowOccurrences`.
fn get_throw_occurrences(
    node: NodeId,
    source_file: NodeId,
    nodes: &[Node],
    program: &Rc<Program>,
) -> Vec<NodeId> {
    let Some(owner) = get_throw_statement_owner(node, nodes) else {
        return Vec::new();
    };

    let mut keywords: Vec<NodeId> = Vec::new();

    // Aggregate all throw statements "owned" by this owner.
    let throw_statements = aggregate_owned_throw_statements(owner, source_file, nodes, program);
    for throw in throw_statements {
        let mut nodes_mut = program.nodes_mut(source_file.file_index());
        if let Some(keyword) =
            tokens::find_child_of_kind(&mut nodes_mut, source_file, throw, Kind::ThrowKeyword)
        {
            keywords.push(keyword);
        }
    }

    // If the "owner" is a function, then we equate 'return' and 'throw'
    // statements in their ability to "jump out" of the function, and include
    // occurrences for both
    if ast::is_function_block(Some(owner), nodes) {
        ast::for_each_return_statement(nodes, owner, &mut |ret| {
            let mut nodes_mut = program.nodes_mut(source_file.file_index());
            if let Some(keyword) =
                tokens::find_child_of_kind(&mut nodes_mut, source_file, ret, Kind::ReturnKeyword)
            {
                keywords.push(keyword);
            }
            false // continue traversal
        });
    }

    keywords
}

/// `getThrowStatementOwner` — takes a throw statement and returns the nearest
/// ancestor that is a try-block (whose try statement has a catch clause),
/// function-block, or source file.
fn get_throw_statement_owner(throw_statement: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let mut child = throw_statement;
    while let Some(parent) = nodes[child].parent {
        if ast::is_function_block(Some(parent), nodes) || nodes[parent].kind == Kind::SourceFile {
            return Some(parent);
        }

        // A throw-statement is only owned by a try-statement if the
        // try-statement has a catch clause, and if the throw-statement occurs
        // within the try block.
        if ast::is_try_statement(&nodes[parent]) {
            let try_statement = nodes[parent].as_try_statement();
            if try_statement.try_block == Some(child) && try_statement.catch_clause.is_some() {
                return Some(child);
            }
        }

        child = parent;
    }
    None
}

/// `getTryCatchFinallyOccurrences`.
fn get_try_catch_finally_occurrences(
    node: NodeId,
    source_file: NodeId,
    nodes: &[Node],
    program: &Rc<Program>,
) -> Vec<NodeId> {
    let try_statement = nodes[node].as_try_statement();

    let mut keywords: Vec<NodeId> = Vec::new();
    let token = {
        let mut nodes_mut = program.nodes_mut(source_file.file_index());
        get_first_token(&mut nodes_mut, node, source_file)
    };
    if let Some(token) = token {
        // Tokens are appended by `get_first_token`; re-fetch the arena.
        let fresh = program.nodes(source_file.file_index());
        if fresh[token].kind == Kind::TryKeyword {
            keywords.push(token);
        }
    }

    if try_statement.catch_clause.is_some() {
        let mut nodes_mut = program.nodes_mut(source_file.file_index());
        if let Some(catch_token) =
            tokens::find_child_of_kind(&mut nodes_mut, source_file, node, Kind::CatchKeyword)
        {
            keywords.push(catch_token);
        }
    }

    if try_statement.finally_block.is_some() {
        let mut nodes_mut = program.nodes_mut(source_file.file_index());
        if let Some(finally_keyword) =
            tokens::find_child_of_kind(&mut nodes_mut, source_file, node, Kind::FinallyKeyword)
        {
            keywords.push(finally_keyword);
        }
    }

    keywords
}

/// `getSwitchCaseDefaultOccurrences`.
fn get_switch_case_default_occurrences(
    node: NodeId,
    source_file: NodeId,
    nodes: &[Node],
    program: &Rc<Program>,
) -> Vec<NodeId> {
    let switch_statement = nodes[node].as_switch_statement();

    let mut keywords: Vec<NodeId> = Vec::new();
    let token = {
        let mut nodes_mut = program.nodes_mut(source_file.file_index());
        get_first_token(&mut nodes_mut, node, source_file)
    };
    if let Some(token) = token {
        let fresh = program.nodes(source_file.file_index());
        if fresh[token].kind == Kind::SwitchKeyword {
            keywords.push(token);
        }
    }

    let clauses = nodes[switch_statement.case_block.expect("case block")]
        .as_case_block()
        .clauses
        .as_ref()
        .map(|c| c.nodes_rc())
        .unwrap_or_default();
    for clause in clauses.iter().copied() {
        let clause_token = {
            let mut nodes_mut = program.nodes_mut(source_file.file_index());
            get_first_token(&mut nodes_mut, clause, source_file)
        };
        if let Some(clause_token) = clause_token {
            let fresh = program.nodes(source_file.file_index());
            if fresh[clause_token].kind == Kind::CaseKeyword
                || fresh[clause_token].kind == Kind::DefaultKeyword
            {
                keywords.push(clause_token);
            }
        }

        let break_and_continue_statements =
            aggregate_all_break_and_continue_statements(clause, source_file, nodes, program);
        for statement in break_and_continue_statements {
            if nodes[statement].kind == Kind::BreakStatement
                && owns_break_or_continue_statement(node, statement, nodes)
            {
                let token = {
                    let mut nodes_mut = program.nodes_mut(source_file.file_index());
                    get_first_token(&mut nodes_mut, statement, source_file)
                };
                if let Some(token) = token {
                    keywords.push(token);
                }
            }
        }
    }

    keywords
}

/// `aggregateAllBreakAndContinueStatements`.
fn aggregate_all_break_and_continue_statements(
    node: NodeId,
    source_file: NodeId,
    nodes: &[Node],
    program: &Rc<Program>,
) -> Vec<NodeId> {
    if ast::is_break_or_continue_statement(&nodes[node]) {
        return vec![node];
    }
    if ast::is_function_like(Some(node), nodes) {
        return Vec::new();
    }
    flat_map_children(node, source_file, nodes, program, aggregate_all_break_and_continue_statements)
}

/// `ownsBreakOrContinueStatement`.
fn owns_break_or_continue_statement(
    owner: NodeId,
    statement: NodeId,
    nodes: &[Node],
) -> bool {
    get_break_or_continue_owner(statement, nodes) == Some(owner)
}

/// `getBreakOrContinueOwner`.
fn get_break_or_continue_owner(statement: NodeId, nodes: &[Node]) -> Option<NodeId> {
    ast::find_ancestor_or_quit(Some(statement), nodes, &mut |n, ns| {
        let is_loop = matches!(
            n.kind,
            Kind::ForStatement
                | Kind::ForInStatement
                | Kind::ForOfStatement
                | Kind::WhileStatement
                | Kind::DoStatement
        );
        if n.kind == Kind::SwitchStatement || is_loop {
            // `continue` statements are not owned by switch statements.
            if n.kind == Kind::SwitchStatement
                && nodes[statement].kind == Kind::ContinueStatement
            {
                return FindAncestorResult::False;
            }
            // If the statement is labeled, check if the node is labeled by
            // the statement's label.
            let labeled = match nodes[statement].label() {
                None => true,
                Some(label) => {
                    let label_text = nodes[label].text(ns).into_owned();
                    is_labeled_by(n.id, &label_text, ns)
                }
            };
            return if labeled {
                FindAncestorResult::True
            } else {
                FindAncestorResult::False
            };
        }
        // Don't cross function boundaries.
        if ast::is_function_like(Some(n.id), ns) {
            return FindAncestorResult::Quit;
        }
        FindAncestorResult::False
    })
}

/// `isLabeledBy` — whether `node` is preceded by a label of the given string.
/// Note: `node` cannot be a SourceFile.
fn is_labeled_by(node: NodeId, label_name: &str, nodes: &[Node]) -> bool {
    ast::find_ancestor_or_quit(nodes[node].parent, nodes, &mut |owner, _ns| {
        if !ast::is_labeled_statement(owner) {
            return FindAncestorResult::Quit;
        }
        if owner.label().is_some_and(|l| nodes[l].text(nodes).as_ref() == label_name) {
            return FindAncestorResult::True;
        }
        FindAncestorResult::False
    })
    .is_some()
}

/// `getBreakOrContinueStatementOccurrences`.
fn get_break_or_continue_statement_occurrences(
    node: NodeId,
    source_file: NodeId,
    nodes: &[Node],
    program: &Rc<Program>,
) -> Vec<NodeId> {
    if let Some(owner) = get_break_or_continue_owner(node, nodes) {
        match nodes[owner].kind {
            Kind::ForStatement
            | Kind::ForInStatement
            | Kind::ForOfStatement
            | Kind::DoStatement
            | Kind::WhileStatement => {
                return get_loop_break_continue_occurrences(owner, source_file, nodes, program)
            }
            Kind::SwitchStatement => {
                return get_switch_case_default_occurrences(owner, source_file, nodes, program)
            }
            _ => {}
        }
    }
    Vec::new()
}

/// `getLoopBreakContinueOccurrences`.
fn get_loop_break_continue_occurrences(
    node: NodeId,
    source_file: NodeId,
    nodes: &[Node],
    program: &Rc<Program>,
) -> Vec<NodeId> {
    let mut keywords: Vec<NodeId> = Vec::new();

    let token = {
        let mut nodes_mut = program.nodes_mut(source_file.file_index());
        get_first_token(&mut nodes_mut, node, source_file)
    };
    if let Some(token) = token {
        let fresh = program.nodes(source_file.file_index());
        if matches!(
            fresh[token].kind,
            Kind::ForKeyword | Kind::DoKeyword | Kind::WhileKeyword
        ) {
            keywords.push(token);
            if fresh[node].kind == Kind::DoStatement {
                let mut nodes_mut = program.nodes_mut(source_file.file_index());
                let loop_tokens =
                    get_children_from_non_jsdoc_node(&mut nodes_mut, node, source_file);
                drop(nodes_mut);
                let fresh = program.nodes(source_file.file_index());
                for loop_token in loop_tokens.iter().rev() {
                    if fresh[*loop_token].kind == Kind::WhileKeyword {
                        keywords.push(*loop_token);
                        break;
                    }
                }
            }
        }
    }

    let break_and_continue_statements =
        aggregate_all_break_and_continue_statements(node, source_file, nodes, program);
    for statement in break_and_continue_statements {
        let token = {
            let mut nodes_mut = program.nodes_mut(source_file.file_index());
            get_first_token(&mut nodes_mut, statement, source_file)
        };
        if owns_break_or_continue_statement(node, statement, nodes)
            && token.is_some_and(|t| {
                let fresh = program.nodes(source_file.file_index());
                matches!(fresh[t].kind, Kind::BreakKeyword | Kind::ContinueKeyword)
            })
        {
            keywords.push(token.expect("token"));
        }
    }

    keywords
}

/// `getAsyncAndAwaitOccurrences`.
fn get_async_and_await_occurrences(
    node: NodeId,
    source_file: NodeId,
    nodes: &[Node],
    program: &Rc<Program>,
) -> Vec<NodeId> {
    let Some(fun) = ast::get_containing_function(node, nodes) else {
        return Vec::new();
    };
    let _ = program;

    let mut keywords: Vec<NodeId> = Vec::new();

    if let Some(modifier_nodes) = nodes[fun].modifier_nodes() {
        for &modifier in modifier_nodes {
            if nodes[modifier].kind == Kind::AsyncKeyword {
                keywords.push(modifier);
            }
        }
    }

    nodes[fun].for_each_child(nodes, &mut |child| {
        traverse_without_crossing_function(child, source_file, nodes, &mut |child| {
            if ast::is_await_expression(&nodes[child]) {
                let mut nodes_mut = program.nodes_mut(source_file.file_index());
                if let Some(token) = get_first_token(&mut nodes_mut, child, source_file) {
                    drop(nodes_mut);
                    let fresh = program.nodes(source_file.file_index());
                    if fresh[token].kind == Kind::AwaitKeyword {
                        keywords.push(token);
                    }
                }
            }
        });
        false // continue traversal
    });

    keywords
}

/// `getYieldOccurrences`.
fn get_yield_occurrences(
    node: NodeId,
    source_file: NodeId,
    nodes: &[Node],
    program: &Rc<Program>,
) -> Vec<NodeId> {
    let Some(parent_func) =
        ast::find_ancestor(nodes[node].parent, nodes, &mut |n, ns| {
            ast::is_function_like(Some(n.id), ns)
        })
    else {
        return Vec::new();
    };

    let mut keywords: Vec<NodeId> = Vec::new();

    nodes[parent_func].for_each_child(nodes, &mut |child| {
        traverse_without_crossing_function(child, source_file, nodes, &mut |child| {
            if ast::is_yield_expression(&nodes[child]) {
                let mut nodes_mut = program.nodes_mut(source_file.file_index());
                if let Some(token) = get_first_token(&mut nodes_mut, child, source_file) {
                    drop(nodes_mut);
                    let fresh = program.nodes(source_file.file_index());
                    if fresh[token].kind == Kind::YieldKeyword {
                        keywords.push(token);
                    }
                }
            }
        });
        false // continue traversal
    });

    keywords
}

/// `traverseWithoutCrossingFunction`.
fn traverse_without_crossing_function(
    node: NodeId,
    source_file: NodeId,
    nodes: &[Node],
    cb: &mut dyn FnMut(NodeId),
) {
    let _ = source_file;
    cb(node);
    if !ast::is_function_like(Some(node), nodes)
        && !ast::is_class_like(Some(node), nodes)
        && !ast::is_interface_declaration(&nodes[node])
        && !ast::is_module_declaration(&nodes[node])
        && !ast::is_type_alias_declaration(&nodes[node])
        && !ast::is_type_node(&nodes[node])
    {
        nodes[node].for_each_child(nodes, &mut |child| {
            traverse_without_crossing_function(child, source_file, nodes, cb);
            false // continue traversal
        });
    }
}

/// `getModifierOccurrences`.
fn get_modifier_occurrences(
    kind: Kind,
    node: NodeId,
    source_file: NodeId,
    nodes: &[Node],
) -> Vec<NodeId> {
    let _ = source_file;
    let mut result: Vec<NodeId> = Vec::new();

    let nodes_to_search = get_nodes_to_search_for_modifier(node, ast::modifier_to_flag(kind), nodes);
    for n in nodes_to_search {
        if let Some(modifier) = find_modifier(n, kind, nodes) {
            result.push(modifier);
        }
    }
    result
}

/// `getNodesToSearchForModifier`.
fn get_nodes_to_search_for_modifier(
    declaration: NodeId,
    modifier_flag: ModifierFlags,
    nodes: &[Node],
) -> Vec<NodeId> {
    let mut result: Vec<NodeId> = Vec::new();

    let Some(container) = nodes[declaration].parent else {
        return Vec::new();
    };

    // Types of node whose children might have modifiers.
    match nodes[container].kind {
        Kind::ModuleBlock | Kind::SourceFile | Kind::Block | Kind::CaseClause
        | Kind::DefaultClause => {
            // Container is either a class declaration or the declaration is a
            // classDeclaration
            if modifier_flag.intersects(ModifierFlags::ABSTRACT)
                && ast::is_class_declaration(&nodes[declaration])
            {
                if let Some(members) = nodes[declaration].members() {
                    result.extend(members.iter().copied());
                }
                result.push(declaration);
                result
            } else {
                if let Some(statements) = nodes[container].statements() {
                    result.extend(statements.iter().copied());
                }
                result
            }
        }
        Kind::Constructor | Kind::MethodDeclaration | Kind::FunctionDeclaration => {
            // Parameters and, if inside a class, also class members
            if let Some(parameters) = nodes[container].parameters() {
                result.extend(parameters.iter().copied());
            }
            if let Some(container_parent) = nodes[container].parent {
                if ast::is_class_like(Some(container_parent), nodes) {
                    if let Some(members) = nodes[container_parent].members() {
                        result.extend(members.iter().copied());
                    }
                }
            }
            result
        }
        Kind::ClassDeclaration
        | Kind::ClassExpression
        | Kind::InterfaceDeclaration
        | Kind::TypeLiteral => {
            let member_list: Vec<NodeId> = nodes[container]
                .members()
                .map(|m| m.to_vec())
                .unwrap_or_default();
            result.extend(member_list.iter().copied());
            // If we're an accessibility modifier, we're in an instance member
            // and should search the constructor's parameter list for instance
            // members as well.
            if modifier_flag
                .intersects(ModifierFlags::ACCESSIBILITY_MODIFIER | ModifierFlags::READONLY)
            {
                let mut constructor = None;
                for &member in &member_list {
                    if ast::is_constructor_declaration(&nodes[member]) {
                        constructor = Some(member);
                        break;
                    }
                }
                if let Some(constructor) = constructor {
                    if let Some(parameters) = nodes[constructor].parameters() {
                        result.extend(parameters.iter().copied());
                    }
                }
            } else if modifier_flag.intersects(ModifierFlags::ABSTRACT) {
                result.push(container);
            }
            result
        }
        _ => {
            // Syntactically invalid positions or unsupported containers
            Vec::new()
        }
    }
}

/// `findModifier`.
fn find_modifier(node: NodeId, kind: Kind, nodes: &[Node]) -> Option<NodeId> {
    if let Some(modifier_nodes) = nodes[node].modifier_nodes() {
        for &modifier in modifier_nodes {
            if nodes[modifier].kind == kind {
                return Some(modifier);
            }
        }
    }
    None
}
