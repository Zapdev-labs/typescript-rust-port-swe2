// Ported from tsc/internal/ls/folding.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashSet;
use std::rc::Rc;

use tsc_ast::ast::{Node, NodeFactory, NodeFactoryHooks, NodeList};
use tsc_ast::kind_generated::Kind;
use tsc_ast::{self as ast, NodeFlags, NodeId};
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::text::{TextPos, TextRange};
use tsc_lsconv::converters::source_file_script;
use tsc_lsproto::{self as lsproto, FoldingRangeKind};
use tsc_spanmap::{Feature, Fidelity};

use crate::api::Error;
use crate::languageservice::LanguageService;
use crate::utilities::is_in_comment;

impl<'h> LanguageService<'h> {
    /// `ProvideFoldingRange`.
    pub fn provide_folding_range(
        &self,
        ctx: &Context,
        document_uri: lsproto::DocumentUri,
    ) -> Result<lsproto::FoldingRangeResponse, Error> {
        let (program, source_file) = self.get_program_and_file(&document_uri);
        let mut projections: Vec<NodeId> = vec![source_file];
        {
            let nodes = program.nodes(source_file.file_index());
            projections.extend_from_slice(
                nodes[source_file]
                    .as_source_file()
                    .supplemental_source_files(),
            );
        }
        let mut res: Vec<lsproto::FoldingRange> = Vec::new();
        for projection in projections {
            let mut ranges = self.add_node_outlining_spans(ctx, &program, projection);
            ranges.extend(self.add_region_outlining_spans(ctx, &program, projection));
            if lsproto::get_client_capabilities(ctx)
                .text_document
                .folding_range
                .line_folding_only
            {
                ranges = self.adjust_folding_end(&program, ranges, projection);
            }
            res.extend(ranges);
        }
        res.sort_by(|a, b| {
            a.start_line
                .cmp(&b.start_line)
                .then(a.start_character.cmp(&b.start_character))
                .then(a.end_line.cmp(&b.end_line))
                .then(a.end_character.cmp(&b.end_character))
        });
        let mut seen: HashSet<FoldingRangeKey> = HashSet::new();
        res.retain(|folding_range| seen.insert(key_for_folding_range(folding_range)));
        Ok(lsproto::FoldingRangesOrNull {
            folding_ranges: Some(res),
        })
    }

    /// `adjustFoldingEnd` adjusts the end line of folding ranges when the client signals lineFoldingOnly.
    /// This mirrors the behavior of VS Code's built-in TypeScript extension (workaround for vscode#47240).
    /// When lineFoldingOnly is true, we hide lines from startLine+1 to endLine. And to keep closing
    /// brackets/braces visible, we subtract 1 from endLine when the range ends with a closing pair character.
    fn adjust_folding_end(
        &self,
        program: &Rc<Program>,
        ranges: Vec<lsproto::FoldingRange>,
        source_file: NodeId,
    ) -> Vec<lsproto::FoldingRange> {
        let nodes = program.nodes(source_file.file_index());
        let source_text = nodes[source_file].as_source_file().text().to_string();
        let mut result: Vec<lsproto::FoldingRange> = Vec::with_capacity(ranges.len());
        for mut r in ranges {
            if let Some(end_character) = r.end_character
                && end_character > 0
            {
                let positions = self.converters.from_lsp_position_for_source_file(
                    source_file,
                    &nodes,
                    lsproto::Position {
                        line: r.end_line,
                        character: end_character,
                    },
                    Feature::FoldingRanges,
                );
                let mut position: Option<(NodeId, TextPos)> = None;
                for p in &positions {
                    if p.script.file == source_file && !p.fidelity.is_none() {
                        position = Some((p.script.file, p.position));
                        break;
                    }
                }
                if let Some((_, pos)) = position
                    && pos > 0
                    && pos as usize <= source_text.len()
                {
                    let end_offset = pos;
                    let fold_end_char = source_text.as_bytes()[end_offset as usize - 1];
                    if fold_end_char == b'}'
                        || fold_end_char == b']'
                        || fold_end_char == b')'
                        || fold_end_char == b'`'
                        || fold_end_char == b'>'
                    {
                        if r.end_line > r.start_line {
                            r.end_line -= 1;
                        }
                    }
                }
            }
            result.push(r);
        }
        result
    }

    /// `addNodeOutliningSpans`.
    fn add_node_outlining_spans(
        &self,
        ctx: &Context,
        program: &Rc<Program>,
        source_file: NodeId,
    ) -> Vec<lsproto::FoldingRange> {
        let depth_remaining: i32 = 40;
        let mut current: usize = 0;

        let statements = {
            let nodes = program.nodes(source_file.file_index());
            nodes[source_file]
                .as_source_file()
                .statements
                .clone()
                .expect("SourceFile should have statements")
        };
        let n = statements.nodes.len();
        let mut folding_range: Vec<lsproto::FoldingRange> = Vec::with_capacity(40);
        let mut nodes = program.nodes_mut(source_file.file_index());
        while current < n {
            while current < n
                && !ast::is_any_import_syntax(&nodes[statements.nodes[current]])
            {
                folding_range.extend(visit_node(
                    ctx,
                    self,
                    &mut nodes,
                    statements.nodes[current],
                    depth_remaining,
                    source_file,
                ));
                current += 1;
            }
            if current == n {
                break;
            }
            let first_import = current;
            while current < n
                && ast::is_any_import_syntax(&nodes[statements.nodes[current]])
            {
                folding_range.extend(visit_node(
                    ctx,
                    self,
                    &mut nodes,
                    statements.nodes[current],
                    depth_remaining,
                    source_file,
                ));
                current += 1;
            }
            let last_import = current - 1;
            if last_import != first_import {
                let folding_range_kind = FoldingRangeKind::Imports;
                let imports = {
                    let start = tsc_astnav::tokens::find_child_of_kind(
                        &mut nodes,
                        source_file,
                        statements.nodes[first_import],
                        Kind::ImportKeyword,
                    )
                    .map(|import_keyword| {
                        tsc_astnav::tokens::get_start_of_node(
                            &mut nodes,
                            source_file,
                            import_keyword,
                            false, /*includeJSDoc*/
                        )
                    });
                    start.and_then(|start| {
                        create_folding_range_from_bounds(
                            ctx,
                            self,
                            &nodes,
                            start,
                            nodes[statements.nodes[last_import]].end(),
                            folding_range_kind.clone(),
                            source_file,
                        )
                    })
                };
                if let Some(imports) = imports {
                    folding_range.push(imports);
                }
            }
        }

        // Visit the EOF Token so that comments which aren't attached to statements are included.
        let end_of_file_token = nodes[source_file]
            .as_source_file()
            .end_of_file_token;
        if let Some(end_of_file_token) = end_of_file_token {
            folding_range.extend(visit_node(
                ctx,
                self,
                &mut nodes,
                end_of_file_token,
                depth_remaining,
                source_file,
            ));
        }
        folding_range
    }

    /// `addRegionOutliningSpans`.
    fn add_region_outlining_spans(
        &self,
        ctx: &Context,
        program: &Rc<Program>,
        source_file: NodeId,
    ) -> Vec<lsproto::FoldingRange> {
        let mut regions: Vec<(i32, Option<String>)> = Vec::with_capacity(40);
        let mut out: Vec<lsproto::FoldingRange> = Vec::with_capacity(40);
        let mut nodes = program.nodes_mut(source_file.file_index());
        let source_text = nodes[source_file].as_source_file().text().to_string();
        let line_starts =
            tsc_scanner::scanner::get_ecma_line_starts(nodes[source_file].as_source_file());
        for current_line_start in line_starts {
            let line_end =
                get_line_end_of_position(&nodes, source_file, current_line_start);
            let line_text = &source_text[current_line_start as usize..line_end as usize];
            let result = parse_region_delimiter(line_text);
            let Some(result) = result else {
                continue;
            };
            let token_at_position = tsc_astnav::tokens::get_token_at_position(
                &mut nodes,
                source_file,
                current_line_start,
            );
            if is_in_comment(&mut nodes, source_file, current_line_start, token_at_position)
                .is_some()
            {
                continue;
            }

            if result.is_start {
                let position = line_text
                    .find("//")
                    .map(|i| i as i32)
                    .unwrap_or(-1)
                    + current_line_start;
                let mut region = (position, None);
                if supports_collapsed_text(ctx) {
                    let collapsed_text = if !result.name.is_empty() {
                        result.name
                    } else {
                        "#region".to_string()
                    };
                    region.1 = Some(collapsed_text);
                }
                regions.push(region);
            } else if let Some(region) = regions.pop() {
                let (text_range, fidelity) = self.create_folding_range_from_bounds(
                    &nodes,
                    region.0,
                    line_end,
                    source_file,
                );
                if fidelity.is_none() {
                    continue;
                }
                let mut folding_range = create_folding_range(
                    ctx,
                    text_range,
                    FoldingRangeKind::Region,
                    "",
                );
                folding_range.collapsed_text = region.1;
                out.push(folding_range);
            }
        }
        out
    }

    /// `createFoldingRangeFromBounds` (the `l.` receiver method).
    fn create_folding_range_from_bounds(
        &self,
        nodes: &[Node],
        start: i32,
        end: i32,
        source_file: NodeId,
    ) -> (lsproto::Range, Fidelity) {
        let script = source_file_script(source_file, nodes);
        self.converters.to_lsp_range_for_feature(
            &script,
            TextRange::new(start, end),
            Feature::FoldingRanges,
        )
    }
}

/// `foldingRangeKey` — `Option` fields collapse Go's `hasX` flag + value pairs.
#[derive(PartialEq, Eq, Hash)]
struct FoldingRangeKey {
    start_line: u32,
    start_character: Option<u32>,
    end_line: u32,
    end_character: Option<u32>,
    kind: Option<FoldingRangeKind>,
    collapsed_text: Option<String>,
}

/// `keyForFoldingRange`.
fn key_for_folding_range(folding_range: &lsproto::FoldingRange) -> FoldingRangeKey {
    FoldingRangeKey {
        start_line: folding_range.start_line,
        start_character: folding_range.start_character,
        end_line: folding_range.end_line,
        end_character: folding_range.end_character,
        kind: folding_range.kind.clone(),
        collapsed_text: folding_range.collapsed_text.clone(),
    }
}

/// `visitNode`.
fn visit_node(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    n: NodeId,
    mut depth_remaining: i32,
    source_file: NodeId,
) -> Vec<lsproto::FoldingRange> {
    if nodes[n].flags.intersects(NodeFlags::REPARSED)
        || depth_remaining == 0
        || ctx.is_cancelled()
    {
        return Vec::new();
    }
    let mut folding_range: Vec<lsproto::FoldingRange> = Vec::with_capacity(40);
    if (!ast::is_binary_expression(&nodes[n]) && ast::is_declaration(&nodes[n]))
        || ast::is_variable_statement(&nodes[n])
        || ast::is_return_statement(&nodes[n])
        || ast::is_call_or_new_expression(&nodes[n])
        || nodes[n].kind == Kind::EndOfFile
    {
        folding_range.extend(add_outlining_for_leading_comments_for_node(
            ctx,
            l,
            nodes,
            n,
            source_file,
        ));
    }
    if ast::is_function_like(Some(n), nodes)
        && nodes[n]
            .parent
            .is_some_and(|p| ast::is_binary_expression(&nodes[p]))
    {
        let parent = nodes[n].parent.expect("checked");
        let left = nodes[parent].as_binary_expression().left;
        if left.is_some_and(|left| ast::is_property_access_expression(&nodes[left])) {
            folding_range.extend(add_outlining_for_leading_comments_for_node(
                ctx,
                l,
                nodes,
                left.expect("checked"),
                source_file,
            ));
        }
    }
    if ast::is_block(&nodes[n]) {
        if let Some(statements) = &nodes[n].as_block().statements {
            let end = statements.end();
            folding_range.extend(add_outlining_for_leading_comments_for_pos(
                ctx,
                l,
                nodes,
                end,
                source_file,
            ));
        }
    }
    if ast::is_module_block(&nodes[n]) {
        if let Some(statements) = &nodes[n].as_module_block().statements {
            let end = statements.end();
            folding_range.extend(add_outlining_for_leading_comments_for_pos(
                ctx,
                l,
                nodes,
                end,
                source_file,
            ));
        }
    }
    if ast::is_class_like(Some(n), nodes) || ast::is_interface_declaration(&nodes[n]) {
        let members: Option<NodeList> = if ast::is_class_declaration(&nodes[n]) {
            nodes[n].as_class_declaration().class_like_base.members.clone()
        } else if ast::is_class_expression(&nodes[n]) {
            nodes[n].as_class_expression().class_like_base.members.clone()
        } else {
            nodes[n].as_interface_declaration().members.clone()
        };
        if let Some(members) = &members {
            let end = members.end();
            folding_range.extend(add_outlining_for_leading_comments_for_pos(
                ctx,
                l,
                nodes,
                end,
                source_file,
            ));
        }
    }

    if let Some(span) = get_outlining_span_for_node(ctx, l, nodes, n, source_file) {
        folding_range.push(span);
    }

    depth_remaining -= 1;
    if ast::is_call_expression(&nodes[n]) {
        depth_remaining += 1;
        if let Some(expression) = nodes[n].expression() {
            folding_range.extend(visit_node(
                ctx,
                l,
                nodes,
                expression,
                depth_remaining,
                source_file,
            ));
        }
        depth_remaining -= 1;
        let arguments = nodes[n].arguments().map(|a| a.to_vec()).unwrap_or_default();
        for arg in arguments {
            folding_range.extend(visit_node(ctx, l, nodes, arg, depth_remaining, source_file));
        }
        let type_arguments = nodes[n]
            .type_arguments()
            .map(|a| a.to_vec())
            .unwrap_or_default();
        for type_arg in type_arguments {
            folding_range.extend(visit_node(
                ctx,
                l,
                nodes,
                type_arg,
                depth_remaining,
                source_file,
            ));
        }
    } else if ast::is_if_statement(&nodes[n])
        && nodes[n]
            .as_if_statement()
            .else_statement
            .is_some_and(|e| ast::is_if_statement(&nodes[e]))
    {
        // Consider an 'else if' to be on the same depth as the 'if'.
        let (then_statement, else_statement) = {
            let if_statement = nodes[n].as_if_statement();
            (if_statement.then_statement, if_statement.else_statement)
        };
        if let Some(expression) = nodes[n].expression() {
            folding_range.extend(visit_node(
                ctx,
                l,
                nodes,
                expression,
                depth_remaining,
                source_file,
            ));
        }
        if let Some(then_statement) = then_statement {
            folding_range.extend(visit_node(
                ctx,
                l,
                nodes,
                then_statement,
                depth_remaining,
                source_file,
            ));
        }
        depth_remaining += 1;
        if let Some(else_statement) = else_statement {
            folding_range.extend(visit_node(
                ctx,
                l,
                nodes,
                else_statement,
                depth_remaining,
                source_file,
            ));
        }
        // PORT: Go's trailing `depthRemaining--` is dead code (the function
        // returns immediately); omitted to silence unused-assignment.
    } else {
        let mut children: Vec<NodeId> = Vec::new();
        nodes[n].for_each_child(nodes, &mut |child| {
            children.push(child);
            false
        });
        for child in children {
            folding_range.extend(visit_node(
                ctx,
                l,
                nodes,
                child,
                depth_remaining,
                source_file,
            ));
        }
    }
    folding_range
}

/// `addOutliningForLeadingCommentsForNode`.
fn add_outlining_for_leading_comments_for_node(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    n: NodeId,
    source_file: NodeId,
) -> Vec<lsproto::FoldingRange> {
    if ast::is_jsx_text(&nodes[n]) {
        return Vec::new();
    }
    add_outlining_for_leading_comments_for_pos(ctx, l, nodes, nodes[n].pos(), source_file)
}

/// `addOutliningForLeadingCommentsForPos`.
fn add_outlining_for_leading_comments_for_pos(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    pos: i32,
    source_file: NodeId,
) -> Vec<lsproto::FoldingRange> {
    let factory = NodeFactory::<'static>::new(NodeFactoryHooks::default());
    let mut folding_range: Vec<lsproto::FoldingRange> = Vec::with_capacity(40);
    let mut first_single_line_comment_start: i32 = -1;
    let mut last_single_line_comment_end: i32 = -1;
    let mut single_line_comment_count: i32 = 0;
    let folding_range_kind_comment = FoldingRangeKind::Comment;

    macro_rules! combine_and_add_multiple_single_line_comments {
        () => {
            // Only outline spans of two or more consecutive single line comments
            if single_line_comment_count > 1 {
                create_folding_range_from_bounds(
                    ctx,
                    l,
                    nodes,
                    first_single_line_comment_start,
                    last_single_line_comment_end,
                    folding_range_kind_comment.clone(),
                    source_file,
                )
            } else {
                None
            }
        };
    }

    let source_text = nodes[source_file].as_source_file().text().to_string();
    for comment in tsc_scanner::scanner::get_leading_comment_ranges(
        &factory,
        &source_text,
        pos,
    ) {
        let comment_pos = comment.text_range.pos();
        let comment_end = comment.text_range.end();

        if ctx.is_cancelled() {
            return Vec::new();
        }
        match comment.kind {
            Kind::SingleLineCommentTrivia => {
                // never fold region delimiters into single-line comment regions
                let comment_text = &source_text[comment_pos as usize..comment_end as usize];
                if parse_region_delimiter(comment_text).is_some() {
                    if let Some(comments) = combine_and_add_multiple_single_line_comments!() {
                        folding_range.push(comments);
                    }
                    single_line_comment_count = 0;
                    break;
                }

                // For single line comments, combine consecutive ones (2 or more) into
                // a single span from the start of the first till the end of the last
                if single_line_comment_count == 0 {
                    first_single_line_comment_start = comment_pos;
                }
                last_single_line_comment_end = comment_end;
                single_line_comment_count += 1;
            }
            Kind::MultiLineCommentTrivia => {
                if let Some(comments) = combine_and_add_multiple_single_line_comments!() {
                    folding_range.push(comments);
                }
                if let Some(comment) = create_folding_range_from_bounds(
                    ctx,
                    l,
                    nodes,
                    comment_pos,
                    comment_end,
                    folding_range_kind_comment.clone(),
                    source_file,
                ) {
                    folding_range.push(comment);
                }
                single_line_comment_count = 0;
            }
            _ => unreachable!("unexpected comment kind"),
        }
    }
    if let Some(added_comments) = combine_and_add_multiple_single_line_comments!() {
        folding_range.push(added_comments);
    }
    folding_range
}

/// `regionDelimiterResult`.
struct RegionDelimiterResult {
    is_start: bool,
    name: String,
}

/// `parseRegionDelimiter`.
fn parse_region_delimiter(line_text: &str) -> Option<RegionDelimiterResult> {
    // We trim the leading whitespace and // without the regex since the
    // multiple potential whitespace matches can make for some gnarly backtracking behavior
    let line_text = line_text.trim_start_matches(char::is_whitespace);
    if !line_text.starts_with("//") {
        return None;
    }
    let mut line_text = line_text[2..].trim();
    if let Some(stripped) = line_text.strip_suffix('\r') {
        line_text = stripped;
    }
    if !line_text.starts_with('#') {
        return None;
    }
    let mut line_text = &line_text[1..];
    let mut is_start = true;
    if let Some(rest) = line_text.strip_prefix("end") {
        is_start = false;
        line_text = rest;
    }
    if !line_text.starts_with("region") {
        return None;
    }
    let line_text = &line_text[6..];
    Some(RegionDelimiterResult {
        is_start,
        name: line_text.trim().to_string(),
    })
}

/// `getOutliningSpanForNode`.
fn get_outlining_span_for_node(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    n: NodeId,
    source_file: NodeId,
) -> Option<lsproto::FoldingRange> {
    match nodes[n].kind {
        Kind::Block => {
            if ast::is_function_like(nodes[n].parent, nodes) {
                return function_span(ctx, l, nodes, nodes[n].parent.expect("function-like"), n, source_file);
            }
            // Check if the block is standalone, or 'attached' to some parent statement.
            // If the latter, we want to collapse the block, but consider its hint span
            // to be the entire span of the parent.
            let parent_kind = nodes[n].parent.map(|p| nodes[p].kind);
            match parent_kind {
                Some(
                    Kind::DoStatement
                    | Kind::ForInStatement
                    | Kind::ForOfStatement
                    | Kind::ForStatement
                    | Kind::IfStatement
                    | Kind::WhileStatement
                    | Kind::WithStatement
                    | Kind::CatchClause,
                ) => {
                    return span_for_node(
                        ctx,
                        l,
                        nodes,
                        n,
                        Kind::OpenBraceToken,
                        true, /*useFullStart*/
                        source_file,
                    );
                }
                Some(Kind::TryStatement) => {
                    // Could be the try-block, or the finally-block.
                    let try_statement = nodes[nodes[n].parent.expect("parent")].as_try_statement();
                    if try_statement.try_block == Some(n) {
                        return span_for_node(
                            ctx,
                            l,
                            nodes,
                            n,
                            Kind::OpenBraceToken,
                            true, /*useFullStart*/
                            source_file,
                        );
                    } else if try_statement.finally_block == Some(n) {
                        if let Some(span) = span_for_node(
                            ctx,
                            l,
                            nodes,
                            n,
                            Kind::OpenBraceToken,
                            true, /*useFullStart*/
                            source_file,
                        ) {
                            return Some(span);
                        }
                    }
                    // fallthrough
                }
                _ => {}
            }
            // Block was a standalone block.  In this case we want to only collapse
            // the span of the block, independent of any parent span.
            let (text_range, fidelity) =
                l.create_lsp_range_from_node_for_feature(n, source_file, Feature::FoldingRanges);
            if fidelity.is_none() {
                return None;
            }
            Some(create_folding_range(ctx, text_range, FoldingRangeKind::default(), ""))
        }
        Kind::ModuleBlock => span_for_node(
            ctx,
            l,
            nodes,
            n,
            Kind::OpenBraceToken,
            true, /*useFullStart*/
            source_file,
        ),
        Kind::ClassDeclaration
        | Kind::ClassExpression
        | Kind::InterfaceDeclaration
        | Kind::EnumDeclaration
        | Kind::CaseBlock
        | Kind::TypeLiteral
        | Kind::ObjectBindingPattern => span_for_node(
            ctx,
            l,
            nodes,
            n,
            Kind::OpenBraceToken,
            true, /*useFullStart*/
            source_file,
        ),
        Kind::TupleType => span_for_node(
            ctx,
            l,
            nodes,
            n,
            Kind::OpenBracketToken,
            !nodes[n]
                .parent
                .is_some_and(|p| ast::is_tuple_type_node(&nodes[p])), /*useFullStart*/
            source_file,
        ),
        Kind::CaseClause | Kind::DefaultClause => {
            let statements = nodes[n].as_case_or_default_clause().statements.clone();
            span_for_node_array(ctx, l, nodes, statements.as_ref(), source_file)
        }
        Kind::ObjectLiteralExpression => span_for_node(
            ctx,
            l,
            nodes,
            n,
            Kind::OpenBraceToken,
            !nodes[n]
                .parent
                .is_some_and(|p| ast::is_array_literal_expression(&nodes[p]))
                && !nodes[n]
                    .parent
                    .is_some_and(|p| ast::is_call_expression(&nodes[p])), /*useFullStart*/
            source_file,
        ),
        Kind::ArrayLiteralExpression => span_for_node(
            ctx,
            l,
            nodes,
            n,
            Kind::OpenBracketToken,
            !nodes[n]
                .parent
                .is_some_and(|p| ast::is_array_literal_expression(&nodes[p]))
                && !nodes[n]
                    .parent
                    .is_some_and(|p| ast::is_call_expression(&nodes[p])), /*useFullStart*/
            source_file,
        ),
        Kind::JsxElement | Kind::JsxFragment => span_for_jsx_element(ctx, l, nodes, n, source_file),
        Kind::JsxSelfClosingElement | Kind::JsxOpeningElement => {
            span_for_jsx_attributes(ctx, l, nodes, n, source_file)
        }
        Kind::TemplateExpression | Kind::NoSubstitutionTemplateLiteral => {
            span_for_template_literal(ctx, l, nodes, n, source_file)
        }
        Kind::ArrayBindingPattern => span_for_node(
            ctx,
            l,
            nodes,
            n,
            Kind::OpenBracketToken,
            !nodes[n]
                .parent
                .is_some_and(|p| ast::is_binding_element(&nodes[p])), /*useFullStart*/
            source_file,
        ),
        Kind::ArrowFunction => span_for_arrow_function(ctx, l, nodes, n, source_file),
        Kind::CallExpression => span_for_call_expression(ctx, l, nodes, n, source_file),
        Kind::ParenthesizedExpression => {
            span_for_parenthesized_expression(ctx, l, nodes, n, source_file)
        }
        Kind::NamedImports | Kind::NamedExports | Kind::ImportAttributes => {
            span_for_import_export_elements(ctx, l, nodes, n, source_file)
        }
        _ => None,
    }
}

/// `spanForImportExportElements`.
fn span_for_import_export_elements(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    node: NodeId,
    source_file: NodeId,
) -> Option<lsproto::FoldingRange> {
    let elements: Option<NodeList> = match nodes[node].kind {
        Kind::NamedImports => nodes[node].as_named_imports().elements.clone(),
        Kind::NamedExports => nodes[node].as_named_exports().elements.clone(),
        Kind::ImportAttributes => nodes[node].as_import_attributes().attributes.clone(),
        _ => None,
    };
    if elements.as_ref().is_none_or(|e| e.nodes.is_empty()) {
        return None;
    }
    let open_token = tsc_astnav::tokens::find_child_of_kind(
        nodes,
        source_file,
        node,
        Kind::OpenBraceToken,
    );
    let close_token = tsc_astnav::tokens::find_child_of_kind(
        nodes,
        source_file,
        node,
        Kind::CloseBraceToken,
    );
    if open_token.is_none()
        || close_token.is_none()
        || positions_are_on_same_line(
            nodes[open_token.expect("checked")].pos(),
            nodes[close_token.expect("checked")].pos(),
            source_file,
            nodes,
        )
    {
        return None;
    }
    range_between_tokens(
        ctx,
        l,
        nodes,
        open_token.expect("checked"),
        close_token.expect("checked"),
        source_file,
        false, /*useFullStart*/
    )
}

/// `spanForParenthesizedExpression`.
fn span_for_parenthesized_expression(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    node: NodeId,
    source_file: NodeId,
) -> Option<lsproto::FoldingRange> {
    let start = tsc_astnav::tokens::get_start_of_node(
        nodes,
        source_file,
        node,
        false, /*includeJSDoc*/
    );
    if positions_are_on_same_line(start, nodes[node].end(), source_file, nodes) {
        return None;
    }
    let (text_range, fidelity) = l.create_folding_range_from_bounds(
        nodes,
        start,
        nodes[node].end(),
        source_file,
    );
    if fidelity.is_none() {
        return None;
    }
    Some(create_folding_range(ctx, text_range, FoldingRangeKind::default(), ""))
}

/// `spanForCallExpression`.
fn span_for_call_expression(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    node: NodeId,
    source_file: NodeId,
) -> Option<lsproto::FoldingRange> {
    if nodes[node]
        .as_call_expression()
        .arguments
        .as_ref()
        .is_none_or(|a| a.nodes.is_empty())
    {
        return None;
    }
    let open_token =
        tsc_astnav::tokens::find_child_of_kind(nodes, source_file, node, Kind::OpenParenToken);
    let close_token =
        tsc_astnav::tokens::find_child_of_kind(nodes, source_file, node, Kind::CloseParenToken);
    if open_token.is_none()
        || close_token.is_none()
        || positions_are_on_same_line(
            nodes[open_token.expect("checked")].pos(),
            nodes[close_token.expect("checked")].pos(),
            source_file,
            nodes,
        )
    {
        return None;
    }

    range_between_tokens(
        ctx,
        l,
        nodes,
        open_token.expect("checked"),
        close_token.expect("checked"),
        source_file,
        true, /*useFullStart*/
    )
}

/// `spanForArrowFunction`.
fn span_for_arrow_function(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    node: NodeId,
    source_file: NodeId,
) -> Option<lsproto::FoldingRange> {
    let body = nodes[node].body();
    if body.is_some_and(|b| ast::is_block(&nodes[b]))
        || body.is_some_and(|b| ast::is_parenthesized_expression(&nodes[b]))
        || body.is_some_and(|b| {
            positions_are_on_same_line(nodes[b].pos(), nodes[b].end(), source_file, nodes)
        })
    {
        return None;
    }
    let body = body.expect("arrow function body");
    let (text_range, fidelity) = l.create_folding_range_from_bounds(
        nodes,
        nodes[body].pos(),
        nodes[body].end(),
        source_file,
    );
    if fidelity.is_none() {
        return None;
    }
    Some(create_folding_range(ctx, text_range, FoldingRangeKind::default(), ""))
}

/// `spanForTemplateLiteral`.
fn span_for_template_literal(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    node: NodeId,
    source_file: NodeId,
) -> Option<lsproto::FoldingRange> {
    if nodes[node].kind == Kind::NoSubstitutionTemplateLiteral
        && nodes[node].text(nodes).is_empty()
    {
        return None;
    }
    let start = tsc_astnav::tokens::get_start_of_node(
        nodes,
        source_file,
        node,
        false, /*includeJSDoc*/
    );
    create_folding_range_from_bounds(
        ctx,
        l,
        nodes,
        start,
        nodes[node].end(),
        FoldingRangeKind::default(),
        source_file,
    )
}

/// `spanForJSXElement`.
fn span_for_jsx_element(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    node: NodeId,
    source_file: NodeId,
) -> Option<lsproto::FoldingRange> {
    if nodes[node].kind == Kind::JsxElement {
        let (opening_element, closing_element) = {
            let jsx_element = nodes[node].as_jsx_element();
            (jsx_element.opening_element, jsx_element.closing_element)
        };
        let start = tsc_astnav::tokens::get_start_of_node(
            nodes,
            source_file,
            opening_element.expect("openingElement"),
            false, /*includeJSDoc*/
        );
        let (text_range, fidelity) = l.create_folding_range_from_bounds(
            nodes,
            start,
            nodes[closing_element.expect("closingElement")].end(),
            source_file,
        );
        if fidelity.is_none() {
            return None;
        }
        let tag_name = tsc_scanner::utilities::get_text_of_node(
            nodes[opening_element.expect("openingElement")]
                .tag_name()
                .expect("tagName"),
            nodes,
        );
        let banner_text = format!("<{tag_name}>...</{tag_name}>");
        return Some(create_folding_range(
            ctx,
            text_range,
            FoldingRangeKind::default(),
            &banner_text,
        ));
    }
    // JsxFragment
    let (opening_fragment, closing_fragment) = {
        let jsx_fragment = nodes[node].as_jsx_fragment();
        (jsx_fragment.opening_fragment, jsx_fragment.closing_fragment)
    };
    let start = tsc_astnav::tokens::get_start_of_node(
        nodes,
        source_file,
        opening_fragment.expect("openingFragment"),
        false, /*includeJSDoc*/
    );
    let (text_range, fidelity) = l.create_folding_range_from_bounds(
        nodes,
        start,
        nodes[closing_fragment.expect("closingFragment")].end(),
        source_file,
    );
    if fidelity.is_none() {
        return None;
    }
    Some(create_folding_range(
        ctx,
        text_range,
        FoldingRangeKind::default(),
        "<>...</>",
    ))
}

/// `spanForJSXAttributes`.
fn span_for_jsx_attributes(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    node: NodeId,
    source_file: NodeId,
) -> Option<lsproto::FoldingRange> {
    let attributes = if nodes[node].kind == Kind::JsxSelfClosingElement {
        nodes[node].as_jsx_self_closing_element().attributes
    } else {
        nodes[node].as_jsx_opening_element().attributes
    };
    let attributes = attributes.expect("JSX attributes");
    if nodes[attributes]
        .properties()
        .is_none_or(|p| p.is_empty())
    {
        return None;
    }
    let start = tsc_astnav::tokens::get_start_of_node(
        nodes,
        source_file,
        node,
        false, /*includeJSDoc*/
    );
    create_folding_range_from_bounds(
        ctx,
        l,
        nodes,
        start,
        nodes[node].end(),
        FoldingRangeKind::default(),
        source_file,
    )
}

/// `spanForNodeArray`.
fn span_for_node_array(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    statements: Option<&NodeList>,
    source_file: NodeId,
) -> Option<lsproto::FoldingRange> {
    if let Some(statements) = statements
        && !statements.nodes.is_empty()
    {
        let (text_range, fidelity) = l.create_folding_range_from_bounds(
            nodes,
            statements.pos(),
            statements.end(),
            source_file,
        );
        if fidelity.is_none() {
            return None;
        }
        return Some(create_folding_range(
            ctx,
            text_range,
            FoldingRangeKind::default(),
            "",
        ));
    }
    None
}

/// `spanForNode`.
fn span_for_node(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    node: NodeId,
    open: Kind,
    use_full_start: bool,
    source_file: NodeId,
) -> Option<lsproto::FoldingRange> {
    let close = if open != Kind::OpenBraceToken {
        Kind::CloseBracketToken
    } else {
        Kind::CloseBraceToken
    };
    let open_token = tsc_astnav::tokens::find_child_of_kind(nodes, source_file, node, open);
    let close_token = tsc_astnav::tokens::find_child_of_kind(nodes, source_file, node, close);
    if let (Some(open_token), Some(close_token)) = (open_token, close_token) {
        return range_between_tokens(
            ctx,
            l,
            nodes,
            open_token,
            close_token,
            source_file,
            use_full_start,
        );
    }
    None
}

/// `rangeBetweenTokens`.
fn range_between_tokens(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    open_token: NodeId,
    close_token: NodeId,
    source_file: NodeId,
    use_full_start: bool,
) -> Option<lsproto::FoldingRange> {
    let (text_range, fidelity) = if use_full_start {
        l.create_folding_range_from_bounds(
            nodes,
            nodes[open_token].pos(),
            nodes[close_token].end(),
            source_file,
        )
    } else {
        let start = tsc_astnav::tokens::get_start_of_node(
            nodes,
            source_file,
            open_token,
            false, /*includeJSDoc*/
        );
        l.create_folding_range_from_bounds(
            nodes,
            start,
            nodes[close_token].end(),
            source_file,
        )
    };
    if fidelity.is_none() {
        return None;
    }
    Some(create_folding_range(ctx, text_range, FoldingRangeKind::default(), ""))
}

/// `supportsCollapsedText`.
fn supports_collapsed_text(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .folding_range
        .folding_range
        .collapsed_text
}

/// `createFoldingRange`.
fn create_folding_range(
    ctx: &Context,
    text_range: lsproto::Range,
    folding_range_kind: FoldingRangeKind,
    collapsed_text: &str,
) -> lsproto::FoldingRange {
    let kind = if folding_range_kind.as_str().is_empty() {
        None
    } else {
        Some(folding_range_kind)
    };
    let mut result = lsproto::FoldingRange {
        start_line: text_range.start.line,
        start_character: Some(text_range.start.character),
        end_line: text_range.end.line,
        end_character: Some(text_range.end.character),
        kind,
        ..Default::default()
    };
    if !collapsed_text.is_empty() && supports_collapsed_text(ctx) {
        result.collapsed_text = Some(collapsed_text.to_string());
    }
    result
}

/// `createFoldingRangeFromBounds` (free function).
fn create_folding_range_from_bounds(
    ctx: &Context,
    l: &LanguageService,
    nodes: &[Node],
    pos: i32,
    end: i32,
    folding_range_kind: FoldingRangeKind,
    source_file: NodeId,
) -> Option<lsproto::FoldingRange> {
    let (text_range, fidelity) =
        l.create_folding_range_from_bounds(nodes, pos, end, source_file);
    if fidelity.is_none() {
        return None;
    }
    Some(create_folding_range(ctx, text_range, folding_range_kind, ""))
}

/// `functionSpan`.
fn function_span(
    ctx: &Context,
    l: &LanguageService,
    nodes: &mut Vec<Node>,
    node: NodeId,
    body: NodeId,
    source_file: NodeId,
) -> Option<lsproto::FoldingRange> {
    let open_token = try_get_function_open_token(nodes, node, body, source_file);
    let close_token =
        tsc_astnav::tokens::find_child_of_kind(nodes, source_file, body, Kind::CloseBraceToken);
    if let (Some(open_token), Some(close_token)) = (open_token, close_token) {
        return range_between_tokens(
            ctx,
            l,
            nodes,
            open_token,
            close_token,
            source_file,
            true, /*useFullStart*/
        );
    }
    None
}

/// `tryGetFunctionOpenToken`.
fn try_get_function_open_token(
    nodes: &mut Vec<Node>,
    node: NodeId,
    body: NodeId,
    source_file: NodeId,
) -> Option<NodeId> {
    if is_node_array_multi_line(nodes[node].parameters(), source_file, nodes) {
        let open_paren_token = tsc_astnav::tokens::find_child_of_kind(
            nodes,
            source_file,
            node,
            Kind::OpenParenToken,
        );
        if open_paren_token.is_some() {
            return open_paren_token;
        }
    }
    tsc_astnav::tokens::find_child_of_kind(nodes, source_file, body, Kind::OpenBraceToken)
}

/// `isNodeArrayMultiLine`.
fn is_node_array_multi_line(
    list: Option<&[NodeId]>,
    source_file: NodeId,
    nodes: &[Node],
) -> bool {
    let Some(list) = list else {
        return false;
    };
    if list.is_empty() {
        return false;
    }
    !positions_are_on_same_line(
        nodes[list[0]].pos(),
        nodes[list[list.len() - 1]].end(),
        source_file,
        nodes,
    )
}

/// `printer.PositionsAreOnSameLine` — `pub(crate)` in `tsc_printer`, so it is
/// reimplemented here over `ecma_line_map` + `compute_line_of_position`,
/// matching `getLinesBetweenPositions(pos1, pos2, sourceFile) == 0`.
fn positions_are_on_same_line(pos1: i32, pos2: i32, source_file: NodeId, nodes: &[Node]) -> bool {
    if pos1 == pos2 {
        return true;
    }
    let line_starts = tsc_ast::SourceFileLike::ecma_line_map(nodes[source_file].as_source_file());
    let lower = if pos1 < pos2 { pos1 } else { pos2 };
    let upper = if pos1 < pos2 { pos2 } else { pos1 };
    let lower_line = tsc_scanner::scanner::compute_line_of_position(line_starts, lower);
    let upper_line = lower_line
        + tsc_scanner::scanner::compute_line_of_position(
            &line_starts[lower_line as usize..],
            upper,
        );
    lower_line == upper_line
}

/// `getLineEndOfPosition` — local copy of the private helper in
/// `completions.rs` (sibling-owned file).
fn get_line_end_of_position(nodes: &[Node], file: NodeId, position: TextPos) -> TextPos {
    let source_file = nodes[file].as_source_file();
    let line = tsc_scanner::scanner::get_ecma_line_of_position(source_file, position);
    let line_starts = tsc_scanner::scanner::get_ecma_line_starts(source_file);
    let last_char_pos = if (line as usize) + 1 >= line_starts.len() {
        nodes[file].end()
    } else {
        line_starts[line as usize + 1] - 1
    };
    let full_text = source_file.text.as_bytes();
    if last_char_pos > 0
        && (last_char_pos as usize) < full_text.len()
        && full_text[last_char_pos as usize] == b'\n'
        && full_text[last_char_pos as usize - 1] == b'\r'
    {
        return last_char_pos - 1;
    }
    last_char_pos
}
