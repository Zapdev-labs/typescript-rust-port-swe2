// Ported from tsc/internal/ls/jsdoc_snippet.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
//
// - `*ast.Node` is `NodeId`; `*ast.SourceFile` is the file `NodeId` indexed
//   through its arena (`nodes: &[Node]` / `&mut Vec<Node>`). Node parent links
//   are followed via `nodes[n].parent`.
// - `getDocCommentTemplateAtPosition` needs mutable arena access both for
//   `GetTokenAtPosition` (which may synthesize nodes) and for `node.JSDoc(file)`
//   lazy JSDoc parsing (`ast::js_doc`). The recursive reparse case allocates a
//   fresh arena via `tsc_parser::parse_source_file` and recurses on it.
// - Go's `(*commentOwnerInfo, bool quit)` is `(Option<CommentOwnerInfo>, bool)`.
// - Go's `clientSupportsItem*` helpers live in `completions.rs` and are reused
//   via `pub(crate)` re-exports; `getLineEndOfPosition` is duplicated here (the
//   same private copy exists in `folding.rs`).

use tsc_ast::{self as ast, Kind, Node, NodeId};
use tsc_core::text::TextPos;
use tsc_lsproto as lsproto;
use tsc_stringutil as stringutil;

use crate::completions::{
    CompletionItem, CompletionList, client_supports_item_commit_characters,
    client_supports_item_insert_replace, client_supports_item_snippet,
};
use crate::languageservice::LanguageService;

/// `docCommentTemplate`.
struct DocCommentTemplate {
    /// `newText`.
    new_text: String,
}

/// `commentOwnerInfo`.
#[derive(Default)]
struct CommentOwnerInfo {
    /// `commentOwner`.
    comment_owner: NodeId,
    /// `parameters` — `[]*ast.ParameterDeclarationNode` in Go (may be empty).
    parameters: Vec<NodeId>,
    /// `hasReturn`.
    has_return: bool,
}

/// `isPotentiallyValidJSDocSnippetCompletionPosition` — whether a `*` trigger
/// at `position` could start a JSDoc snippet completion.
pub(crate) fn is_potentially_valid_jsdoc_snippet_completion_position(
    nodes: &[Node],
    file: NodeId,
    position: TextPos,
) -> bool {
    let text = &nodes[file].as_source_file().text;
    let line_start = tsc_format::get_line_start_position_for_position(position, file, nodes);
    let prefix = &text[line_start as usize..position as usize];
    if !is_jsdoc_snippet_prefix(prefix) {
        return false;
    }

    let line_end = get_line_end_of_position(nodes, file, position);
    let suffix = &text[position as usize..line_end as usize];
    is_jsdoc_snippet_suffix(suffix)
}

impl LanguageService<'_> {
    /// `getJSDocSnippetCompletion`.
    pub(crate) fn get_js_doc_snippet_completion(
        &self,
        ctx: &tsc_core::context::Context,
        file: NodeId,
        position: TextPos,
    ) -> Option<CompletionList> {
        if self.user_preferences().complete_jsdocs.is_false() {
            return None;
        }
        {
            let nodes = self.program.nodes(file.file_index());
            if !is_potentially_valid_jsdoc_snippet_completion_position(&nodes, file, position) {
                return None;
            }
        }
        let mut new_line = self
            .format_options()
            .editor_settings
            .new_line_character
            .clone();
        if new_line.is_empty() {
            new_line = "\n".to_string();
        }
        let template = {
            let mut nodes = self.program.nodes_mut(file.file_index());
            get_doc_comment_template_at_position(
                &mut nodes,
                file,
                position,
                self.user_preferences().generate_return_in_doc_template.is_true(),
                &new_line,
            )?
        };

        let mut insert_text = template.new_text;
        let mut insert_text_format: Option<lsproto::InsertTextFormat> = None;
        if client_supports_item_snippet(ctx) {
            insert_text = template_to_snippet(&insert_text, &new_line);
            insert_text_format = Some(lsproto::InsertTextFormat::Snippet);
        }

        let edit_range = self.get_jsdoc_snippet_completion_range(ctx, file, position, &insert_text);
        let mut commit_characters: Option<Vec<String>> = None;
        if client_supports_item_commit_characters(ctx) {
            commit_characters = Some(Vec::new());
        }
        let item = CompletionItem {
            item: lsproto::CompletionItem {
                label: "/** */".to_string(),
                kind: Some(lsproto::CompletionItemKind::Text),
                detail: Some(
                    tsc_diagnostics::JSDoc_comment
                        .localize(&tsc_locale::from_context(ctx), &[""; 0]),
                ),
                sort_text: Some("\0".to_string()),
                insert_text_format,
                text_edit: edit_range,
                commit_characters,
                ..Default::default()
            },
            symbol: None,
        };
        Some(CompletionList {
            is_incomplete: false,
            items: vec![Some(item)],
            ..Default::default()
        })
    }

    /// `getJSDocSnippetCompletionRange`.
    fn get_jsdoc_snippet_completion_range(
        &self,
        ctx: &tsc_core::context::Context,
        file: NodeId,
        position: TextPos,
        new_text: &str,
    ) -> Option<lsproto::TextEditOrInsertReplaceEdit> {
        let nodes = self.program.nodes(file.file_index());
        let text = &nodes[file].as_source_file().text;
        let line_start = tsc_format::get_line_start_position_for_position(position, file, &nodes);
        let prefix = &text[line_start as usize..position as usize];
        let mut start = position;
        if let Some(prefix_start) = get_jsdoc_snippet_prefix_start(prefix) {
            start = line_start + prefix_start as TextPos;
        }

        let line_end = get_line_end_of_position(&nodes, file, position);
        let suffix = &text[position as usize..line_end as usize];
        let mut end = position;
        // Go: `if suffixEnd, ok := getJSDocSnippetSuffixEnd(suffix); ok` — the
        // bool is `hasClosing`; the end is extended only when a `/` closer
        // was found.
        let (suffix_end, has_closing) = get_jsdoc_snippet_suffix_end(suffix);
        if has_closing {
            end += suffix_end as TextPos;
        }

        let (replacement_range, fidelity) = self.create_lsp_range_from_bounds(start, end, file);
        if !fidelity.is_exact() {
            return None;
        }
        if client_supports_item_insert_replace(ctx) {
            return Some(lsproto::TextEditOrInsertReplaceEdit {
                insert_replace_edit: Some(lsproto::InsertReplaceEdit {
                    new_text: new_text.to_string(),
                    insert: replacement_range.clone(),
                    replace: replacement_range,
                }),
                ..Default::default()
            });
        }
        Some(lsproto::TextEditOrInsertReplaceEdit {
            text_edit: Some(lsproto::TextEdit {
                new_text: new_text.to_string(),
                range: replacement_range,
            }),
            ..Default::default()
        })
    }
}

/// `getDocCommentTemplateAtPosition`.
fn get_doc_comment_template_at_position(
    nodes: &mut Vec<Node>,
    file: NodeId,
    position: TextPos,
    generate_return_in_doc_template: bool,
    new_line: &str,
) -> Option<DocCommentTemplate> {
    let mut token_at_pos = tsc_astnav::tokens::get_token_at_position(nodes, file, position)?;

    let existing_doc_comment =
        ast::find_ancestor(Some(token_at_pos), nodes, &mut |n, _| ast::is_js_doc(n));
    let (doc_comment_end, has_doc_comment_at_position, has_closing_doc_comment_at_position) =
        get_doc_comment_end_at_position(nodes, file, position);
    let is_in_empty_doc_comment = existing_doc_comment.is_some() || has_doc_comment_at_position;
    if is_non_empty_jsdoc(existing_doc_comment, nodes)
        && has_doc_comment_at_position
        && !has_closing_doc_comment_at_position
    {
        let text = nodes[file].as_source_file().text.clone();
        let reparse_text = format!(
            "{} */{}",
            &text[..position as usize],
            &text[position as usize..]
        );
        let source_file = nodes[file].as_source_file();
        let parse_options = source_file.parse_options.clone();
        let script_kind = source_file.script_kind;
        let (reparse_file, mut reparse_nodes) =
            tsc_parser::parse_source_file(parse_options, &reparse_text, script_kind);
        return get_doc_comment_template_at_position(
            &mut reparse_nodes,
            reparse_file,
            position,
            generate_return_in_doc_template,
            new_line,
        );
    }
    if is_non_empty_jsdoc(existing_doc_comment, nodes) {
        return None;
    }
    if existing_doc_comment.is_none() && has_doc_comment_at_position {
        token_at_pos = tsc_astnav::tokens::get_token_at_position(
            nodes,
            file,
            skip_whitespace(&nodes[file].as_source_file().text, doc_comment_end),
        )?;
    }
    let token_start = tsc_astnav::tokens::get_start_of_node(nodes, file, token_at_pos, false);
    if !is_in_empty_doc_comment && token_start < position {
        return None;
    }

    let comment_owner_info =
        get_comment_owner_info(token_at_pos, nodes, generate_return_in_doc_template)?;
    let comment_owner = comment_owner_info.comment_owner;
    let last_jsdoc = ast::js_doc(nodes, comment_owner, Some(file)).last().copied();
    let comment_owner_start =
        tsc_astnav::tokens::get_start_of_node(nodes, file, comment_owner, false);
    if comment_owner_start < position
        || (last_jsdoc.is_some()
            && existing_doc_comment.is_some()
            && last_jsdoc != existing_doc_comment)
    {
        return None;
    }

    let indentation = get_indentation_string_at_position(nodes, file, position);
    let mut tags = parameter_doc_comments(
        &comment_owner_info.parameters,
        ast::is_source_file_js(nodes[file].as_source_file()),
        &indentation,
        new_line,
        nodes,
    );
    if comment_owner_info.has_return {
        tags.push_str(&returns_doc_comment(&indentation, new_line));
    }

    if !tags.is_empty() && !has_jsdoc_tags(comment_owner, nodes, file) {
        let preamble = format!("/**{}{} * ", new_line, indentation);
        let mut end_line = String::new();
        if token_start == position {
            end_line = format!("{}{}", new_line, indentation);
        }
        return Some(DocCommentTemplate {
            new_text: format!(
                "{}{}{}{} */{}",
                preamble, new_line, tags, indentation, end_line
            ),
        });
    }
    Some(DocCommentTemplate {
        new_text: "/** */".to_string(),
    })
}

/// `getDocCommentEndAtPosition` — returns `(end, ok, hasClosing)`.
fn get_doc_comment_end_at_position(
    nodes: &[Node],
    file: NodeId,
    position: TextPos,
) -> (TextPos, bool, bool) {
    let text = &nodes[file].as_source_file().text;
    let line_start = tsc_format::get_line_start_position_for_position(position, file, nodes);
    let line_end = get_line_end_of_position(nodes, file, position);
    let prefix = &text[line_start as usize..position as usize];
    let suffix = &text[position as usize..line_end as usize];
    if !trim_right_single_line_whitespace(prefix).ends_with("/**") {
        return (0, false, false);
    }
    let (suffix_end, has_closing) = get_jsdoc_snippet_suffix_end(suffix);
    (position + suffix_end as TextPos, true, has_closing)
}

/// `skipWhitespace`.
fn skip_whitespace(text: &str, mut position: TextPos) -> TextPos {
    let bytes = text.as_bytes();
    while (position as usize) < bytes.len() {
        let (ch, size) = stringutil::decode_js_string_rune(&bytes[position as usize..]);
        if size == 0 {
            break;
        }
        if !char::from_u32(ch as u32).is_some_and(stringutil::is_white_space_like) {
            break;
        }
        position += size as TextPos;
    }
    position
}

/// `getCommentOwnerInfo`.
fn get_comment_owner_info(
    token_at_pos: NodeId,
    nodes: &[Node],
    generate_return_in_doc_template: bool,
) -> Option<CommentOwnerInfo> {
    let mut node = Some(token_at_pos);
    while let Some(n) = node {
        let (info, quit) = get_comment_owner_info_worker(Some(n), nodes, generate_return_in_doc_template);
        if info.is_some() || quit {
            return info;
        }
        node = nodes[n].parent;
    }
    None
}

/// `getCommentOwnerInfoWorker` — returns `(info, quit)`.
fn get_comment_owner_info_worker(
    comment_owner: Option<NodeId>,
    nodes: &[Node],
    generate_return_in_doc_template: bool,
) -> (Option<CommentOwnerInfo>, bool) {
    let Some(owner) = comment_owner else {
        return (None, false);
    };
    let parameters_of = |node: NodeId| -> Vec<NodeId> {
        nodes[node].parameters().map(|p| p.to_vec()).unwrap_or_default()
    };
    match nodes[owner].kind {
        Kind::FunctionDeclaration
        | Kind::FunctionExpression
        | Kind::MethodDeclaration
        | Kind::Constructor
        | Kind::MethodSignature
        | Kind::ArrowFunction => (
            Some(CommentOwnerInfo {
                comment_owner: owner,
                parameters: parameters_of(owner),
                has_return: has_return(nodes, owner, generate_return_in_doc_template),
            }),
            false,
        ),
        Kind::PropertyAssignment => get_comment_owner_info_worker(
            nodes[owner].as_property_assignment().initializer,
            nodes,
            generate_return_in_doc_template,
        ),
        Kind::ClassDeclaration
        | Kind::InterfaceDeclaration
        | Kind::EnumDeclaration
        | Kind::EnumMember
        | Kind::TypeAliasDeclaration => (
            Some(CommentOwnerInfo {
                comment_owner: owner,
                ..Default::default()
            }),
            false,
        ),
        Kind::PropertySignature => {
            if let Some(type_node) = nodes[owner].as_property_signature_declaration().type_ {
                if ast::is_function_type_node(&nodes[type_node]) {
                    return (
                        Some(CommentOwnerInfo {
                            comment_owner: owner,
                            parameters: parameters_of(type_node),
                            has_return: has_return(nodes, type_node, generate_return_in_doc_template),
                        }),
                        false,
                    );
                }
            }
            (
                Some(CommentOwnerInfo {
                    comment_owner: owner,
                    ..Default::default()
                }),
                false,
            )
        }
        Kind::VariableStatement => {
            let declarations = nodes[owner]
                .as_variable_statement()
                .declaration_list
                .and_then(|dl| {
                    nodes[dl]
                        .as_variable_declaration_list()
                        .declarations
                        .as_ref()
                        .map(|l| l.nodes_rc())
                })
                .unwrap_or_default();
            if declarations.len() == 1 {
                if let Some(initializer) =
                    nodes[declarations[0]].as_variable_declaration().initializer
                {
                    if let Some(host) = get_right_hand_side_of_assignment(nodes, Some(initializer)) {
                        return (
                            Some(CommentOwnerInfo {
                                comment_owner: owner,
                                parameters: parameters_of(host),
                                has_return: has_return(nodes, host, generate_return_in_doc_template),
                            }),
                            false,
                        );
                    }
                }
            }
            (
                Some(CommentOwnerInfo {
                    comment_owner: owner,
                    ..Default::default()
                }),
                false,
            )
        }
        Kind::SourceFile => (None, true),
        Kind::ModuleDeclaration => {
            if nodes[owner]
                .parent
                .is_some_and(|p| nodes[p].kind == Kind::ModuleDeclaration)
            {
                return (None, false);
            }
            (
                Some(CommentOwnerInfo {
                    comment_owner: owner,
                    ..Default::default()
                }),
                false,
            )
        }
        Kind::ExpressionStatement => get_comment_owner_info_worker(
            nodes[owner].as_expression_statement().expression,
            nodes,
            generate_return_in_doc_template,
        ),
        Kind::BinaryExpression => {
            let binary_expression = nodes[owner].as_binary_expression();
            if ast::get_assignment_declaration_kind(owner, nodes) == ast::JsDeclarationKind::None {
                return (None, true);
            }
            if let Some(right) = binary_expression.right {
                if ast::is_function_like(Some(right), nodes) {
                    return (
                        Some(CommentOwnerInfo {
                            comment_owner: owner,
                            parameters: parameters_of(right),
                            has_return: has_return(nodes, right, generate_return_in_doc_template),
                        }),
                        false,
                    );
                }
            }
            (
                Some(CommentOwnerInfo {
                    comment_owner: owner,
                    ..Default::default()
                }),
                false,
            )
        }
        Kind::PropertyDeclaration => {
            if let Some(initializer) = nodes[owner].as_property_declaration().initializer {
                if ast::is_function_expression_or_arrow_function(&nodes[initializer]) {
                    return (
                        Some(CommentOwnerInfo {
                            comment_owner: owner,
                            parameters: parameters_of(initializer),
                            has_return: has_return(
                                nodes,
                                initializer,
                                generate_return_in_doc_template,
                            ),
                        }),
                        false,
                    );
                }
            }
            (None, false)
        }
        _ => (None, false),
    }
}

/// `hasReturn`.
fn has_return(nodes: &[Node], node: NodeId, generate_return_in_doc_template: bool) -> bool {
    if !generate_return_in_doc_template {
        return false;
    }
    if ast::is_function_type_node(&nodes[node]) {
        return true;
    }
    if ast::is_arrow_function(&nodes[node]) {
        if let Some(body) = nodes[node].body() {
            if ast::is_expression(&nodes[body], nodes) {
                return true;
            }
        }
    }
    ast::is_function_like_declaration(Some(node), nodes)
        && nodes[node].body().is_some_and(|b| {
            ast::is_block(&nodes[b]) && ast::for_each_return_statement(nodes, b, &mut |_| true)
        })
}

/// `getRightHandSideOfAssignment`.
fn get_right_hand_side_of_assignment(nodes: &[Node], right_hand_side: Option<NodeId>) -> Option<NodeId> {
    let mut right_hand_side = right_hand_side?;
    while nodes[right_hand_side].kind == Kind::ParenthesizedExpression {
        right_hand_side = nodes[right_hand_side]
            .as_parenthesized_expression()
            .expression?;
    }
    match nodes[right_hand_side].kind {
        Kind::FunctionExpression | Kind::ArrowFunction => Some(right_hand_side),
        Kind::ClassExpression => nodes[right_hand_side]
            .members()?
            .iter()
            .find(|m| ast::is_constructor_declaration(&nodes[**m]))
            .copied(),
        _ => None,
    }
}

/// `parameterDocComments`.
fn parameter_doc_comments(
    parameters: &[NodeId],
    is_java_script_file: bool,
    indentation: &str,
    new_line: &str,
    nodes: &[Node],
) -> String {
    let mut b = String::new();
    for (i, parameter) in parameters.iter().enumerate() {
        let mut param_name = format!("param{}", i);
        if let Some(name) = nodes[*parameter].name() {
            if ast::is_identifier(&nodes[name]) {
                param_name = nodes[name].text(nodes).into_owned();
            }
        }
        let mut param_type = "";
        if is_java_script_file {
            if nodes[*parameter]
                .as_parameter_declaration()
                .dot_dot_dot_token
                .is_some()
            {
                param_type = "{...any} ";
            } else {
                param_type = "{any} ";
            }
        }
        b.push_str(indentation);
        b.push_str(" * @param ");
        b.push_str(param_type);
        b.push_str(&param_name);
        b.push_str(new_line);
    }
    b
}

/// `returnsDocComment`.
fn returns_doc_comment(indentation: &str, new_line: &str) -> String {
    format!("{} * @returns{}", indentation, new_line)
}

/// `getIndentationStringAtPosition`.
fn get_indentation_string_at_position(nodes: &[Node], file: NodeId, position: TextPos) -> String {
    let text = &nodes[file].as_source_file().text;
    let line_start = tsc_format::get_line_start_position_for_position(position, file, nodes);
    let mut pos = line_start as usize;
    let bytes = text.as_bytes();
    while pos < position as usize {
        let (ch, size) = stringutil::decode_js_string_rune(&bytes[pos..]);
        if size == 0 {
            break;
        }
        if !char::from_u32(ch as u32).is_some_and(stringutil::is_white_space_single_line) {
            break;
        }
        pos += size;
    }
    text[line_start as usize..pos].to_string()
}

/// `isNonEmptyJSDoc`.
fn is_non_empty_jsdoc(jsdoc: Option<NodeId>, nodes: &[Node]) -> bool {
    let Some(jsdoc) = jsdoc else {
        return false;
    };
    let data = nodes[jsdoc].as_js_doc();
    data.comment.as_ref().is_some_and(|c| !c.nodes().is_empty())
        || data.tags.as_ref().is_some_and(|t| !t.nodes().is_empty())
}

/// `hasJSDocTags` — needs `&mut Vec<Node>` for lazy JSDoc parsing.
fn has_jsdoc_tags(node: NodeId, nodes: &mut Vec<Node>, file: NodeId) -> bool {
    let jsdocs = ast::js_doc(nodes, node, Some(file));
    let Some(last) = jsdocs.last() else {
        return false;
    };
    nodes[*last]
        .as_js_doc()
        .tags
        .as_ref()
        .is_some_and(|t| !t.nodes().is_empty())
}

/// `templateToSnippet`.
fn template_to_snippet(template: &str, new_line: &str) -> String {
    if template == "/** */" {
        return format!("/**{} * $0{} */", new_line, new_line);
    }

    let mut snippet_index = 1;
    let template = escape_snippet_text(template);
    let template = strip_jsdoc_template_indentation(&template, new_line);
    transform_jsdoc_template_lines(&template, new_line, &mut snippet_index)
}

/// `escapeSnippetText` — private copy; canonical version lives in
/// `completions.rs`.
fn escape_snippet_text(text: &str) -> String {
    text.replace('$', "\\$")
}

/// `stripJSDocTemplateIndentation`.
fn strip_jsdoc_template_indentation(template: &str, new_line: &str) -> String {
    let mut lines: Vec<String> = template.split(new_line).map(|l| l.to_string()).collect();
    for line in lines.iter_mut() {
        let trimmed = line.trim_start_matches([' ', '\t']);
        if trimmed.starts_with('/') {
            *line = trimmed.to_string();
        } else if trimmed.starts_with('*') {
            *line = format!(" {}", trimmed);
        }
    }
    lines.join(new_line)
}

/// `transformJSDocTemplateLines`.
fn transform_jsdoc_template_lines(template: &str, new_line: &str, snippet_index: &mut i32) -> String {
    let mut lines: Vec<String> = template.split(new_line).map(|l| l.to_string()).collect();
    for i in 0..lines.len() {
        if i > 0 && lines[i - 1].starts_with("/**") && line_has_only_jsdoc_asterisk(&lines[i]) {
            lines[i] = format!("{}$0", lines[i]);
            continue;
        }
        if let Some(transformed) = transform_jsdoc_param_line(&lines[i], snippet_index) {
            lines[i] = transformed;
            continue;
        }
        if let Some(transformed) = transform_jsdoc_returns_line(&lines[i], snippet_index) {
            lines[i] = transformed;
        }
    }
    lines.join(new_line)
}

/// `lineHasOnlyJSDocAsterisk`.
fn line_has_only_jsdoc_asterisk(line: &str) -> bool {
    let line = line.trim_start_matches([' ', '\t']);
    line.starts_with('*') && is_only_spaces_or_tabs(&line[1..])
}

/// `transformJSDocParamLine` — returns the transformed line on success.
fn transform_jsdoc_param_line(line: &str, snippet_index: &mut i32) -> Option<String> {
    let mut prefix = "";
    let mut rest = line;
    if let Some(r) = rest.strip_prefix(' ') {
        prefix = " ";
        rest = r;
    }
    rest = rest.strip_prefix("* @param")?;
    if !starts_with_single_line_whitespace(rest) {
        return None;
    }
    rest = rest.trim_start_matches([' ', '\t']);

    let mut type_text = String::new();
    if rest.starts_with('{') {
        let close_brace = rest.find('}')?;
        type_text = format!(" {}", &rest[..close_brace + 1]);
        rest = &rest[close_brace + 1..];
        if !starts_with_single_line_whitespace(rest) {
            return None;
        }
        rest = rest.trim_start_matches([' ', '\t']);
    }

    let (param_name, rest, ok) = scan_non_whitespace(rest);
    if !ok || !is_only_spaces_or_tabs(rest) {
        return None;
    }

    let mut out = format!("{}* @param ", prefix);
    if type_text == " {any}" || type_text == " {*}" {
        out.push_str(&format!("{{${{{}:*}}}} ", *snippet_index));
        *snippet_index += 1;
    } else if !type_text.is_empty() {
        out.push_str(&type_text);
        out.push(' ');
    }
    out.push_str(&format!("{} ${{{}}}", param_name, *snippet_index));
    *snippet_index += 1;
    Some(out)
}

/// `transformJSDocReturnsLine`.
fn transform_jsdoc_returns_line(line: &str, snippet_index: &mut i32) -> Option<String> {
    let mut prefix = "";
    let mut rest = line;
    if let Some(r) = rest.strip_prefix(' ') {
        prefix = " ";
        rest = r;
    }
    if !rest.starts_with("* @returns") || !is_only_spaces_or_tabs(&rest["* @returns".len()..]) {
        return None;
    }
    let text = format!("{}* @returns ${{{}}}", prefix, *snippet_index);
    *snippet_index += 1;
    Some(text)
}

/// `scanNonWhitespace` — returns `(word, rest, ok)`.
fn scan_non_whitespace(text: &str) -> (&str, &str, bool) {
    if text.is_empty() {
        return ("", "", false);
    }
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let (ch, size) = stringutil::decode_js_string_rune(&bytes[i..]);
        if size == 0 || char::from_u32(ch as u32).is_some_and(stringutil::is_white_space_like) {
            if i == 0 {
                return ("", "", false);
            }
            return (&text[..i], &text[i..], true);
        }
        i += size;
    }
    (text, "", true)
}

/// `isJSDocSnippetPrefix`.
fn is_jsdoc_snippet_prefix(prefix: &str) -> bool {
    let trimmed = trim_right_single_line_whitespace(prefix);
    if trimmed.ends_with("/**") {
        return true;
    }
    let start = skip_single_line_whitespace(prefix, 0);
    let trimmed_bytes = trimmed.as_bytes();
    if start >= trimmed.len() || trimmed_bytes[start] != b'/' {
        return false;
    }
    if start + 3 > trimmed.len() {
        return false;
    }
    for i in start + 1..trimmed.len() {
        if trimmed_bytes[i] != b'*' {
            return false;
        }
    }
    trimmed.len() - start >= 3
}

/// `getJSDocSnippetPrefixStart` — returns the start offset on success.
fn get_jsdoc_snippet_prefix_start(prefix: &str) -> Option<usize> {
    let trimmed = trim_right_single_line_whitespace(prefix);
    let bytes = trimmed.as_bytes();
    let mut i = trimmed.len() as i64 - 1;
    while i >= 0 && bytes[i as usize] == b'*' {
        if i > 0 && bytes[i as usize - 1] == b'/' {
            return Some(i as usize - 1);
        }
        i -= 1;
    }
    if trimmed.ends_with('/') {
        return Some(trimmed.len() - 1);
    }
    None
}

/// `isJSDocSnippetSuffix`.
fn is_jsdoc_snippet_suffix(suffix: &str) -> bool {
    let trimmed = trim_right_single_line_whitespace(&suffix[skip_single_line_whitespace(suffix, 0)..]);
    if trimmed.is_empty() {
        return true;
    }
    if !trimmed.ends_with('/') {
        return false;
    }
    let bytes = trimmed.as_bytes();
    for i in 0..trimmed.len() - 1 {
        if bytes[i] != b'*' {
            return false;
        }
    }
    true
}

/// `getJSDocSnippetSuffixEnd` — returns `(end, hasClosing)`; `end` is applied
/// by callers regardless of `hasClosing` (mirroring the Go tuple return).
fn get_jsdoc_snippet_suffix_end(suffix: &str) -> (usize, bool) {
    let mut pos = skip_single_line_whitespace(suffix, 0);
    let bytes = suffix.as_bytes();
    while pos < bytes.len() && bytes[pos] == b'*' {
        pos += 1;
    }
    if pos < bytes.len() && bytes[pos] == b'/' {
        return (pos + 1, true);
    }
    (0, false)
}

/// `trimRightSingleLineWhitespace`.
fn trim_right_single_line_whitespace(text: &str) -> &str {
    let bytes = text.as_bytes();
    let mut end = 0;
    let mut pos = 0;
    while pos < bytes.len() {
        let (ch, size) = stringutil::decode_js_string_rune(&bytes[pos..]);
        if size == 0 {
            break;
        }
        pos += size;
        if !char::from_u32(ch as u32).is_some_and(stringutil::is_white_space_single_line) {
            end = pos;
        }
    }
    &text[..end]
}

/// `skipSingleLineWhitespace`.
fn skip_single_line_whitespace(text: &str, mut pos: usize) -> usize {
    let bytes = text.as_bytes();
    while pos < bytes.len() {
        let (ch, size) = stringutil::decode_js_string_rune(&bytes[pos..]);
        if size == 0
            || !char::from_u32(ch as u32).is_some_and(stringutil::is_white_space_single_line)
        {
            break;
        }
        pos += size;
    }
    pos
}

/// `startsWithSingleLineWhitespace`.
fn starts_with_single_line_whitespace(text: &str) -> bool {
    if text.is_empty() {
        return false;
    }
    let (ch, size) = stringutil::decode_js_string_rune(text.as_bytes());
    size != 0 && char::from_u32(ch as u32).is_some_and(stringutil::is_white_space_single_line)
}

/// `isOnlySpacesOrTabs`.
fn is_only_spaces_or_tabs(text: &str) -> bool {
    text.bytes().all(|b| b == b' ' || b == b'\t')
}

/// `getLineOfPosition` — private copy (see `completions.rs`/`folding.rs`).
fn get_line_of_position(nodes: &[Node], file: NodeId, position: TextPos) -> TextPos {
    tsc_scanner::scanner::get_ecma_line_of_position(nodes[file].as_source_file(), position)
}

/// `getLineEndOfPosition` — private copy (see `completions.rs`/`folding.rs`).
fn get_line_end_of_position(nodes: &[Node], file: NodeId, position: TextPos) -> TextPos {
    let source_file = nodes[file].as_source_file();
    let line = get_line_of_position(nodes, file, position);
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
