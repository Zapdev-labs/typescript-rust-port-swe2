// Ported from tsc/internal/format/indent.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::NodeFactoryHooks;
use tsc_ast::ast::{CommentRange, Node, NodeFactory, NodeList};
use tsc_ast::ids::NodeId;
use tsc_ast::kind_generated::Kind;
use tsc_astnav::tokens::{
    find_next_token, find_preceding_token, find_preceding_token_ex, get_token_at_position,
};
use tsc_core::text::TextRange;
use tsc_lsutil::{FormatCodeSettings, IndentStyle, position_belongs_to_node};
use tsc_scanner::scanner::{
    get_leading_comment_ranges, get_scanner_for_source_file, get_token_pos_of_node,
    get_trailing_comment_ranges, skip_trivia,
};
use tsc_stringutil::{is_white_space_like, is_white_space_single_line};

use crate::span::is_string_or_regular_expression_or_template_literal;
use crate::util::{
    get_line_start_position_for_position, line_and_byte_offset_of_position, line_map,
    line_of_position, position_of_line_and_byte_offset, range_is_on_one_line,
};

/// `GetIndentationForNode`
pub fn get_indentation_for_node(
    n: NodeId,
    ignore_actual_indentation_range: Option<&TextRange>,
    source_file: NodeId,
    options: &FormatCodeSettings,
    nodes: &mut Vec<Node>,
) -> i32 {
    let (startline, startpos) = line_and_byte_offset_of_position(
        nodes,
        source_file,
        get_token_pos_of_node(n, nodes[source_file].as_source_file(), false, nodes),
    );
    get_indentation_for_node_worker(
        n,
        startline,
        startpos,
        ignore_actual_indentation_range, /*indentationDelta*/
        0,
        source_file, /*isNextChild*/
        false,
        options,
        nodes,
    )
}

/// `GetIndentation` — computes the expected indentation for a position in a source file.
/// This is the Go port of SmartIndenter.getIndentation from TypeScript.
pub fn get_indentation(
    position: i32,
    source_file: NodeId,
    options: &FormatCodeSettings,
    assume_new_line_before_close_brace: bool,
    nodes: &mut Vec<Node>,
) -> i32 {
    if position > nodes[source_file].as_source_file().text.len() as i32 {
        return options.editor_settings.base_indent_size; // past EOF
    }

    // no indentation when the indent style is set to none,
    // so we can return fast
    if options.editor_settings.indent_style == IndentStyle::NONE {
        return 0;
    }

    let preceding_token = find_preceding_token_ex(
        nodes,
        source_file,
        position,
        None, /*startNode*/
        true, /*excludeJSDoc*/
    );

    let enclosing_comment_range =
        get_range_of_enclosing_comment(source_file, position, preceding_token, nodes);
    if let Some(comment_range) = enclosing_comment_range {
        if comment_range.kind == Kind::MultiLineCommentTrivia {
            return get_comment_indent(source_file, position, options, &comment_range, nodes);
        }
    }

    let Some(preceding_token) = preceding_token else {
        return options.editor_settings.base_indent_size;
    };

    // no indentation in string/regex/template literals
    if is_string_or_regular_expression_or_template_literal(nodes[preceding_token].kind) {
        let token_start = get_token_pos_of_node(
            preceding_token,
            nodes[source_file].as_source_file(),
            false,
            nodes,
        );
        if token_start <= position && position < nodes[preceding_token].end() {
            return 0;
        }
    }

    let line_at_position = line_of_position(nodes, source_file, position);

    // indentation is first non-whitespace character in a previous line
    // for block indentation, we should look for a line which contains something that's not
    // whitespace.
    let current_token =
        get_token_at_position(nodes, source_file, position).expect("token at position");
    // For object literals, we want indentation to work just like with blocks.
    // If the `{` starts in any position (even in the middle of a line), then
    // the following indentation should treat `{` as the start of that line (including leading whitespace).
    let is_object_literal = nodes[current_token].kind == Kind::OpenBraceToken
        && nodes[current_token]
            .parent
            .is_some_and(|p| nodes[p].kind == Kind::ObjectLiteralExpression);
    if options.editor_settings.indent_style == IndentStyle::BLOCK || is_object_literal {
        return get_block_indent(source_file, position, options, nodes);
    }

    if nodes[preceding_token].kind == Kind::CommaToken
        && nodes[preceding_token]
            .parent
            .is_some_and(|p| nodes[p].kind != Kind::BinaryExpression)
    {
        // previous token is comma that separates items in list - find the previous item and try to derive indentation from it
        let actual_indentation = get_actual_indentation_for_list_item_before_comma(
            preceding_token,
            source_file,
            options,
            nodes,
        );
        if actual_indentation != -1 {
            return actual_indentation;
        }
    }

    let container_list =
        get_list_by_position(position, nodes[preceding_token].parent, source_file, nodes);
    // use list position if the preceding token is before any list items
    if let Some(container_list) = container_list {
        if !nodes[preceding_token].loc.contained_by(&container_list.loc) {
            let use_the_same_base_indentation = nodes[current_token].parent.is_some_and(|p| {
                nodes[p].kind == Kind::FunctionExpression || nodes[p].kind == Kind::ArrowFunction
            });
            let mut indent_size = 0;
            if !use_the_same_base_indentation {
                indent_size = options.editor_settings.indent_size;
            }
            let res = get_actual_indentation_for_list_start_line(
                &container_list,
                source_file,
                options,
                nodes,
            );
            if res == -1 {
                return indent_size;
            }
            return res + indent_size;
        }
    }

    get_smart_indent(
        source_file,
        position,
        preceding_token,
        line_at_position,
        assume_new_line_before_close_brace,
        options,
        nodes,
    )
}

/// `getCommentIndent`
fn get_comment_indent(
    source_file: NodeId,
    position: i32,
    options: &FormatCodeSettings,
    enclosing_comment_range: &CommentRange,
    nodes: &mut Vec<Node>,
) -> i32 {
    let previous_line = line_of_position(nodes, source_file, position) - 1;
    let comment_start_line =
        line_of_position(nodes, source_file, enclosing_comment_range.text_range.pos());

    debug_assert!(comment_start_line >= 0, "commentStartLine >= 0");

    if previous_line <= comment_start_line {
        let line_starts = line_map(nodes, source_file);
        return find_first_non_whitespace_column(
            line_starts[comment_start_line as usize],
            position,
            source_file,
            options,
            nodes,
        );
    }

    let line_starts = line_map(nodes, source_file);
    let start_position_of_line = line_starts[previous_line as usize];
    let (character, column) = find_first_non_whitespace_character_and_column(
        start_position_of_line,
        position,
        source_file,
        options,
        nodes,
    );

    if column == 0 {
        return column;
    }

    let first_non_whitespace_character_code = nodes[source_file].as_source_file().text.as_bytes()
        [(start_position_of_line + character) as usize];
    if first_non_whitespace_character_code == b'*' {
        return column - 1;
    }
    column
}

/// `getLeadingCommentRangesOfNode`
fn get_leading_comment_ranges_of_node(
    node: NodeId,
    file: NodeId,
    nodes: &[Node],
) -> Vec<CommentRange> {
    if nodes[node].kind == Kind::JsxText {
        return Vec::new();
    }
    let factory = NodeFactory::<'static>::new(NodeFactoryHooks::default());
    get_leading_comment_ranges(
        &factory,
        &nodes[file].as_source_file().text,
        nodes[node].pos(),
    )
}

/// `getRangeOfEnclosingComment`
fn get_range_of_enclosing_comment(
    source_file: NodeId,
    position: i32,
    preceding_token: Option<NodeId>,
    nodes: &mut Vec<Node>,
) -> Option<CommentRange> {
    let mut token_at_position =
        get_token_at_position(nodes, source_file, position).expect("token at position");
    let jsdoc = tsc_ast::find_ancestor(Some(token_at_position), nodes, &mut |n, _nodes| {
        tsc_ast::is_js_doc(n)
    });
    if let Some(jsdoc) = jsdoc {
        token_at_position = nodes[jsdoc].parent.expect("JSDoc parent");
    }
    let token_start = tsc_astnav::tokens::get_start_of_node(
        nodes,
        source_file,
        token_at_position,
        false, /*includeJSDoc*/
    );
    if token_start <= position && position < nodes[token_at_position].end() {
        return None;
    }

    // Between two consecutive tokens, all comments are either trailing on the former
    // or leading on the latter (and none are in both lists).
    let mut comment_ranges: Vec<CommentRange> = Vec::new();
    if let Some(preceding_token) = preceding_token {
        let factory = NodeFactory::<'static>::new(NodeFactoryHooks::default());
        comment_ranges.extend(get_trailing_comment_ranges(
            &factory,
            &nodes[source_file].as_source_file().text,
            nodes[preceding_token].end(),
        ));
    }
    comment_ranges.extend(get_leading_comment_ranges_of_node(
        token_at_position,
        source_file,
        nodes,
    ));

    for comment_range in comment_ranges {
        if comment_range.text_range.contains_exclusive(position)
            || (position == comment_range.text_range.end()
                && (comment_range.kind == Kind::SingleLineCommentTrivia
                    || position == nodes[source_file].as_source_file().text.len() as i32))
        {
            return Some(comment_range);
        }
    }
    None
}

/// `getBlockIndent`
fn get_block_indent(
    source_file: NodeId,
    position: i32,
    options: &FormatCodeSettings,
    nodes: &mut Vec<Node>,
) -> i32 {
    // move backwards until we find a line with a non-whitespace character,
    // then find the first non-whitespace character for that line.
    let mut current = position;
    let text = &nodes[source_file].as_source_file().text;
    while current > 0 {
        let (ch, size) = decode_rune_in_string(&text.as_bytes()[current as usize..]);
        if !is_white_space_like(ch) {
            break;
        }
        current -= size as i32;
    }

    let line_start = get_line_start_position_for_position(current, source_file, nodes);
    find_first_non_whitespace_column(line_start, current, source_file, options, nodes)
}

/// `getActualIndentationForListItemBeforeComma`
fn get_actual_indentation_for_list_item_before_comma(
    comma_token: NodeId,
    source_file: NodeId,
    options: &FormatCodeSettings,
    nodes: &mut Vec<Node>,
) -> i32 {
    // previous token is comma that separates items in list - find the previous item and try to derive indentation from it
    if nodes[comma_token].parent.is_none() {
        return -1;
    }
    let Some(containing_list) = get_containing_list(comma_token, source_file, nodes) else {
        return -1;
    };
    let comma_index = containing_list.nodes.iter().position(|&n| n == comma_token);
    if let Some(comma_index) = comma_index {
        if comma_index > 0 {
            return derive_actual_indentation_from_list(
                &containing_list,
                comma_index as i32 - 1,
                source_file,
                options,
                nodes,
            );
        }
    }
    -1
}

/// `type nextTokenKind int`
#[derive(Clone, Copy, PartialEq, Eq)]
enum NextTokenKind {
    Unknown = 0,
    OpenBrace = 1,
    CloseBrace = 2,
}

/// `nextTokenIsCurlyBraceOnSameLineAsCursor`
fn next_token_is_curly_brace_on_same_line_as_cursor(
    preceding_token: NodeId,
    current: NodeId,
    line_at_position: i32,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> NextTokenKind {
    let Some(next_token) = find_next_token(nodes, source_file, preceding_token, current) else {
        return NextTokenKind::Unknown;
    };

    if nodes[next_token].kind == Kind::OpenBraceToken {
        // open braces are always indented at the parent level
        NextTokenKind::OpenBrace
    } else if nodes[next_token].kind == Kind::CloseBraceToken {
        // close braces are indented at the parent level if they are located on the same line with cursor
        let next_token_start_line = get_start_line_for_node(next_token, source_file, nodes);
        if line_at_position == next_token_start_line {
            return NextTokenKind::CloseBrace;
        }
        NextTokenKind::Unknown
    } else {
        NextTokenKind::Unknown
    }
}

/// `getSmartIndent`
fn get_smart_indent(
    source_file: NodeId,
    position: i32,
    preceding_token: NodeId,
    line_at_position: i32,
    assume_new_line_before_close_brace: bool,
    options: &FormatCodeSettings,
    nodes: &mut Vec<Node>,
) -> i32 {
    // try to find node that can contribute to indentation and includes 'position' starting from 'precedingToken'
    // if such node is found - compute initial indentation for 'position' inside this node
    let mut previous: Option<NodeId> = None;
    let mut current = Some(preceding_token);

    while let Some(cur) = current {
        if position_belongs_to_node(nodes, cur, position, source_file)
            && should_indent_child_node(options, cur, previous, Some(source_file), true, nodes)
        {
            let (current_start_line, current_start_char) =
                get_start_line_and_character_for_node(cur, source_file, nodes);
            let ntk = next_token_is_curly_brace_on_same_line_as_cursor(
                preceding_token,
                cur,
                line_at_position,
                source_file,
                nodes,
            );
            let mut indentation_delta = 0;
            if ntk != NextTokenKind::Unknown {
                // handle cases when codefix is about to be inserted before the close brace
                if assume_new_line_before_close_brace && ntk == NextTokenKind::CloseBrace {
                    indentation_delta = options.editor_settings.indent_size;
                }
                // else 0
            } else {
                if line_at_position != current_start_line {
                    indentation_delta = options.editor_settings.indent_size;
                }
            }
            return get_indentation_for_node_worker(
                cur,
                current_start_line,
                current_start_char,
                None,
                indentation_delta,
                source_file,
                true,
                options,
                nodes,
            );
        }

        // check if current node is a list item - if yes, take indentation from it
        // do not consider parent-child line sharing yet:
        // function foo(a
        //    | preceding node 'a' does share line with its parent but indentation is expected
        let actual_indentation = get_actual_indentation_for_list_item(
            cur,
            source_file,
            options,
            true, /*listIndentsChild*/
            nodes,
        );
        if actual_indentation != -1 {
            return actual_indentation;
        }

        previous = Some(cur);
        current = nodes[cur].parent;
    }
    // no parent was found - return the base indentation of the SourceFile
    options.editor_settings.base_indent_size
}

/// `getIndentationForNodeWorker`
#[allow(clippy::too_many_arguments)]
fn get_indentation_for_node_worker(
    current: NodeId,
    current_start_line: i32,
    current_start_character: i32,
    ignore_actual_indentation_range: Option<&TextRange>,
    indentation_delta: i32,
    source_file: NodeId,
    is_next_child: bool,
    options: &FormatCodeSettings,
    nodes: &mut Vec<Node>,
) -> i32 {
    let mut current = current;
    let mut current_start_line = current_start_line;
    let mut current_start_character = current_start_character;
    let mut indentation_delta = indentation_delta;
    let mut parent = nodes[current].parent;

    // Walk up the tree and collect indentation for parent-child node pairs. Indentation is not added if
    // * parent and child nodes start on the same line, or
    // * parent is an IfStatement and child starts on the same line as an 'else clause'.
    while let Some(p) = parent {
        let mut use_actual_indentation = true;
        if let Some(ignore) = ignore_actual_indentation_range {
            let start =
                get_token_pos_of_node(current, nodes[source_file].as_source_file(), false, nodes);
            use_actual_indentation = start < ignore.pos() || start > ignore.end();
        }

        let (containing_list_or_parent_start_line, containing_list_or_parent_start_character) =
            get_containing_list_or_parent_start(p, current, source_file, nodes);
        let parent_and_child_share_line = containing_list_or_parent_start_line
            == current_start_line
            || child_starts_on_the_same_line_with_else_in_if_statement(
                p,
                current,
                current_start_line,
                source_file,
                nodes,
            );

        if use_actual_indentation {
            // check if current node is a list item - if yes, take indentation from it
            let containing_list = get_containing_list(current, source_file, nodes);
            let first_list_child = containing_list
                .as_ref()
                .and_then(|l| l.nodes.first().copied());
            // A list indents its children if the children begin on a later line than the list itself:
            //
            // f1(               L0 - List start
            //   {               L1 - First child start: indented, along with all other children
            //     prop: 0
            //   },
            //   {
            //     prop: 1
            //   }
            // )
            //
            // f2({             L0 - List start and first child start: children are not indented.
            //   prop: 0             Object properties are indented only one level, because the list
            // }, {                  itself contributes nothing.
            //   prop: 1        L3 - The indentation of the second object literal is best understood by
            // })                    looking at the relationship between the list and *first* list item.
            let mut list_indents_child = false;
            if let Some(first_list_child) = first_list_child {
                let list_line = get_start_line_for_node(first_list_child, source_file, nodes);
                list_indents_child = list_line > containing_list_or_parent_start_line;
            }
            let actual_indentation = get_actual_indentation_for_list_item(
                current,
                source_file,
                options,
                list_indents_child,
                nodes,
            );
            if actual_indentation != -1 {
                return actual_indentation + indentation_delta;
            }

            // try to fetch actual indentation for current node from source text
            let actual_indentation = get_actual_indentation_for_node(
                current,
                p,
                current_start_line,
                current_start_character,
                parent_and_child_share_line,
                source_file,
                options,
                nodes,
            );
            if actual_indentation != -1 {
                return actual_indentation + indentation_delta;
            }
        }

        // increase indentation if parent node wants its content to be indented and parent and child nodes don't start on the same line
        if should_indent_child_node(
            options,
            p,
            Some(current),
            Some(source_file),
            is_next_child,
            nodes,
        ) && !parent_and_child_share_line
        {
            indentation_delta += options.editor_settings.indent_size;
        }

        // In our AST, a call argument's `parent` is the call-expression, not the argument list.
        // We would like to increase indentation based on the relationship between an argument and its argument-list,
        // so we spoof the starting position of the (parent) call-expression to match the (non-parent) argument-list.
        // But, the spoofed start-value could then cause a problem when comparing the start position of the call-expression
        // to *its* parent (in the case of an iife, an expression statement), adding an extra level of indentation.
        //
        // Instead, when at an argument, we unspoof the starting position of the enclosing call expression
        // *after* applying indentation for the argument.

        let use_true_start = is_argument_and_start_line_overlaps_expression_being_called(
            p,
            current,
            current_start_line,
            source_file,
            nodes,
        );

        current = p;
        parent = nodes[current].parent;

        if use_true_start {
            let (l, c) = line_and_byte_offset_of_position(
                nodes,
                source_file,
                get_token_pos_of_node(current, nodes[source_file].as_source_file(), false, nodes),
            );
            current_start_line = l;
            current_start_character = c;
        } else {
            current_start_line = containing_list_or_parent_start_line;
            current_start_character = containing_list_or_parent_start_character;
        }
    }

    indentation_delta + options.editor_settings.base_indent_size
}

/*
* Function returns -1 if actual indentation for node should not be used (i.e because node is nested expression)
 */
/// `getActualIndentationForNode`
#[allow(clippy::too_many_arguments)]
fn get_actual_indentation_for_node(
    current: NodeId,
    parent: NodeId,
    cuurent_line: i32,
    current_char: i32,
    parent_and_child_share_line: bool,
    source_file: NodeId,
    options: &FormatCodeSettings,
    nodes: &mut Vec<Node>,
) -> i32 {
    // actual indentation is used for statements\declarations if one of cases below is true:
    // - parent is SourceFile - by default immediate children of SourceFile are not indented except when user indents them manually
    // - parent and child are not on the same line
    let use_actual_indentation = (tsc_ast::is_declaration(&nodes[current])
        || tsc_ast::is_statement_but_not_declaration(&nodes[current]))
        && (nodes[parent].kind == Kind::SourceFile || !parent_and_child_share_line);

    if !use_actual_indentation {
        return -1;
    }

    find_column_for_first_non_whitespace_character_in_line(
        cuurent_line,
        current_char,
        source_file,
        options,
        nodes,
    )
}

/// `isArgumentAndStartLineOverlapsExpressionBeingCalled`
fn is_argument_and_start_line_overlaps_expression_being_called(
    parent: NodeId,
    child: NodeId,
    child_start_line: i32,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> bool {
    if !(tsc_ast::is_call_expression(&nodes[parent])
        && nodes[parent]
            .arguments()
            .is_some_and(|a| a.contains(&child)))
    {
        return false;
    }
    let expression_of_call_expression_end =
        nodes[nodes[parent].expression().expect("call expression")].end();
    let expression_of_call_expression_end_line =
        line_of_position(nodes, source_file, expression_of_call_expression_end);
    expression_of_call_expression_end_line == child_start_line
}

/// `getActualIndentationForListItem`
fn get_actual_indentation_for_list_item(
    node: NodeId,
    source_file: NodeId,
    options: &FormatCodeSettings,
    list_indents_child: bool,
    nodes: &mut Vec<Node>,
) -> i32 {
    if nodes[node]
        .parent
        .is_some_and(|p| nodes[p].kind == Kind::VariableDeclarationList)
    {
        // VariableDeclarationList has no wrapping tokens
        return -1;
    }
    if let Some(containing_list) = get_containing_list(node, source_file, nodes) {
        let index = containing_list.nodes.iter().position(|&e| e == node);
        if let Some(index) = index {
            let result = derive_actual_indentation_from_list(
                &containing_list,
                index as i32,
                source_file,
                options,
                nodes,
            );
            if result != -1 {
                return result;
            }
        }
        let mut delta = 0;
        if list_indents_child {
            delta = options.editor_settings.indent_size;
        }
        let res = get_actual_indentation_for_list_start_line(
            &containing_list,
            source_file,
            options,
            nodes,
        );
        if res == -1 {
            return delta;
        }
        return res + delta;
    }
    -1
}

/// `getActualIndentationForListStartLine`
fn get_actual_indentation_for_list_start_line(
    list: &NodeList,
    source_file: NodeId,
    options: &FormatCodeSettings,
    nodes: &mut Vec<Node>,
) -> i32 {
    let (line, char) = line_and_byte_offset_of_position(nodes, source_file, list.loc.pos());
    find_column_for_first_non_whitespace_character_in_line(line, char, source_file, options, nodes)
}

/// `deriveActualIndentationFromList`
fn derive_actual_indentation_from_list(
    list: &NodeList,
    index: i32,
    source_file: NodeId,
    options: &FormatCodeSettings,
    nodes: &mut Vec<Node>,
) -> i32 {
    debug_assert!(index >= 0 && (index as usize) < list.nodes.len());

    let node = list.nodes[index as usize];

    // walk toward the start of the list starting from current node and check if the line is the same for all items.
    // if end line for item [i - 1] differs from the start line for item [i] - find column of the first non-whitespace character on the line of item [i]

    let (mut line, mut char) = get_start_line_and_character_for_node(node, source_file, nodes);

    let mut i = index;
    while i >= 0 {
        if nodes[list.nodes[i as usize]].kind == Kind::CommaToken {
            i -= 1;
            continue;
        }
        // skip list items that ends on the same line with the current list element
        let prev_end_line =
            line_of_position(nodes, source_file, nodes[list.nodes[i as usize]].end());
        if prev_end_line != line {
            return find_column_for_first_non_whitespace_character_in_line(
                line,
                char,
                source_file,
                options,
                nodes,
            );
        }

        let (l, c) =
            get_start_line_and_character_for_node(list.nodes[i as usize], source_file, nodes);
        line = l;
        char = c;
        i -= 1;
    }
    -1
}

/// `findColumnForFirstNonWhitespaceCharacterInLine`
fn find_column_for_first_non_whitespace_character_in_line(
    line: i32,
    char: i32,
    source_file: NodeId,
    options: &FormatCodeSettings,
    nodes: &mut Vec<Node>,
) -> i32 {
    let line_start = position_of_line_and_byte_offset(nodes, source_file, line, 0);
    find_first_non_whitespace_column(line_start, line_start + char, source_file, options, nodes)
}

/// `FindFirstNonWhitespaceColumn`
pub fn find_first_non_whitespace_column(
    start_pos: i32,
    end_pos: i32,
    source_file: NodeId,
    options: &FormatCodeSettings,
    nodes: &[Node],
) -> i32 {
    let (_, col) = find_first_non_whitespace_character_and_column(
        start_pos,
        end_pos,
        source_file,
        options,
        nodes,
    );
    col
}

/**
* Character is the actual index of the character since the beginning of the line.
* Column - position of the character after expanding tabs to spaces.
* "0\t2$"
* value of 'character' for '$' is 3
* value of 'column' for '$' is 6 (assuming that tab size is 4)
 */
/// `findFirstNonWhitespaceCharacterAndColumn`
pub(crate) fn find_first_non_whitespace_character_and_column(
    start_pos: i32,
    end_pos: i32,
    source_file: NodeId,
    options: &FormatCodeSettings,
    nodes: &[Node],
) -> (i32, i32) {
    let mut column = 0;
    let text = &nodes[source_file].as_source_file().text;
    let mut pos = start_pos;
    while pos < end_pos {
        let (ch, size) = decode_rune_in_string(&text.as_bytes()[pos as usize..]);
        if !is_white_space_single_line(ch) {
            break;
        }

        if ch == '\t' {
            if options.editor_settings.tab_size > 0 {
                column +=
                    options.editor_settings.tab_size + (column % options.editor_settings.tab_size);
            }
        } else {
            column += 1;
        }

        pos += size as i32;
    }
    (pos - start_pos, column)
}

/// `childStartsOnTheSameLineWithElseInIfStatement`
pub(crate) fn child_starts_on_the_same_line_with_else_in_if_statement(
    parent: NodeId,
    child: NodeId,
    child_start_line: i32,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> bool {
    if nodes[parent].kind == Kind::IfStatement
        && nodes[parent].as_if_statement().else_statement == Some(child)
    {
        let else_keyword = find_preceding_token(nodes, source_file, nodes[child].pos());
        debug_assert!(else_keyword.is_some());
        let else_keyword_start_line =
            get_start_line_for_node(else_keyword.unwrap(), source_file, nodes);
        return else_keyword_start_line == child_start_line;
    }
    false
}

/// `getStartLineAndCharacterForNode`
fn get_start_line_and_character_for_node(
    n: NodeId,
    source_file: NodeId,
    nodes: &[Node],
) -> (i32, i32) {
    line_and_byte_offset_of_position(
        nodes,
        source_file,
        get_token_pos_of_node(n, nodes[source_file].as_source_file(), false, nodes),
    )
}

/// `getStartLineForNode`
fn get_start_line_for_node(n: NodeId, source_file: NodeId, nodes: &[Node]) -> i32 {
    line_of_position(
        nodes,
        source_file,
        get_token_pos_of_node(n, nodes[source_file].as_source_file(), false, nodes),
    )
}

/// `GetContainingList`
pub fn get_containing_list(
    node: NodeId,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> Option<NodeList> {
    nodes[node].parent?;
    get_list_by_range(
        get_token_pos_of_node(node, nodes[source_file].as_source_file(), false, nodes),
        nodes[node].end(),
        nodes[node].parent.unwrap(),
        source_file,
        nodes,
    )
}

/// `getListByPosition`
fn get_list_by_position(
    pos: i32,
    node: Option<NodeId>,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> Option<NodeList> {
    let node = node?;
    get_list_by_range(pos, pos, node, source_file, nodes)
}

/// `getListByRange`
fn get_list_by_range(
    start: i32,
    end: i32,
    node: NodeId,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> Option<NodeList> {
    let r = TextRange::new(start, end);
    match nodes[node].kind {
        Kind::TypeReference => get_list(
            nodes[node].type_argument_list().cloned(),
            r,
            node,
            source_file,
            nodes,
        ),
        Kind::ObjectLiteralExpression => get_list(
            nodes[node].property_list().cloned(),
            r,
            node,
            source_file,
            nodes,
        ),
        Kind::ArrayLiteralExpression => get_list(
            nodes[node].element_list().cloned(),
            r,
            node,
            source_file,
            nodes,
        ),
        Kind::TypeLiteral => get_list(
            nodes[node].member_list().cloned(),
            r,
            node,
            source_file,
            nodes,
        ),
        Kind::FunctionDeclaration
        | Kind::FunctionExpression
        | Kind::ArrowFunction
        | Kind::MethodDeclaration
        | Kind::MethodSignature
        | Kind::CallSignature
        | Kind::Constructor
        | Kind::ConstructorType
        | Kind::ConstructSignature => {
            if let Some(tpl) = get_list(
                nodes[node].type_parameter_list().cloned(),
                r,
                node,
                source_file,
                nodes,
            ) {
                return Some(tpl);
            }
            get_list(
                nodes[node].parameter_list().cloned(),
                r,
                node,
                source_file,
                nodes,
            )
        }
        Kind::GetAccessor => get_list(
            nodes[node].parameter_list().cloned(),
            r,
            node,
            source_file,
            nodes,
        ),
        Kind::ClassDeclaration
        | Kind::ClassExpression
        | Kind::InterfaceDeclaration
        | Kind::TypeAliasDeclaration
        | Kind::JSDocTemplateTag => get_list(
            nodes[node].type_parameter_list().cloned(),
            r,
            node,
            source_file,
            nodes,
        ),
        Kind::NewExpression | Kind::CallExpression => {
            if let Some(l) = get_list(
                nodes[node].type_argument_list().cloned(),
                r,
                node,
                source_file,
                nodes,
            ) {
                return Some(l);
            }
            get_list(
                nodes[node].argument_list().cloned(),
                r,
                node,
                source_file,
                nodes,
            )
        }
        Kind::VariableDeclarationList => get_list(
            nodes[node]
                .as_variable_declaration_list()
                .declarations
                .clone(),
            r,
            node,
            source_file,
            nodes,
        ),
        Kind::ObjectBindingPattern
        | Kind::ArrayBindingPattern
        | Kind::NamedImports
        | Kind::NamedExports => get_list(
            nodes[node].element_list().cloned(),
            r,
            node,
            source_file,
            nodes,
        ),
        _ => None, // TODO: should this be a panic? It isn't in strada.
    }
}

/// `getList`
fn get_list(
    list: Option<NodeList>,
    r: TextRange,
    node: NodeId,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> Option<NodeList> {
    let list = list?;
    if r.contained_by(&get_visual_list_range(node, list.loc, source_file, nodes)) {
        return Some(list);
    }
    None
}

/// `getVisualListRange`
fn get_visual_list_range(
    _node: NodeId,
    list: TextRange,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> TextRange {
    // In strada, this relied on the services .getChildren method, which manifested synthetic token nodes
    // _however_, the logic boils down to "find the child with the matching span and adjust its start to the
    // previous (possibly token) child's end and its end to the token start of the following element" - basically
    // expanding the range to encompass all the neighboring non-token trivia
    // Now, we perform that logic with the scanner instead
    let prior = find_preceding_token(nodes, source_file, list.pos());
    let prior_end = prior.map_or(list.pos(), |p| nodes[p].end());
    // Find the token that starts at or after list.End() using the scanner
    let next_start = {
        let sf = nodes[source_file].as_source_file();
        let scan = get_scanner_for_source_file(sf, list.end() as usize);
        if scan.token() == Kind::EndOfFile {
            list.end()
        } else {
            scan.token_start() as i32
        }
    };
    TextRange::new(prior_end, next_start)
}

/// `getContainingListOrParentStart`
fn get_containing_list_or_parent_start(
    parent: NodeId,
    child: NodeId,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> (i32, i32) {
    let containing_list = get_containing_list(child, source_file, nodes);
    let start_pos = containing_list.map_or_else(
        || get_token_pos_of_node(parent, nodes[source_file].as_source_file(), false, nodes),
        |l| l.loc.pos(),
    );
    line_and_byte_offset_of_position(nodes, source_file, start_pos)
}

/// `isControlFlowEndingStatement`
fn is_control_flow_ending_statement(kind: Kind, parent_kind: Kind) -> bool {
    match kind {
        Kind::ReturnStatement
        | Kind::ThrowStatement
        | Kind::ContinueStatement
        | Kind::BreakStatement => parent_kind != Kind::Block,
        _ => false,
    }
}

/**
* True when the parent node should indent the given child by an explicit rule.
* @param is_next_child If true, we are judging indent of a hypothetical child *after* this one, not the current child.
 */
/// `ShouldIndentChildNode`
pub fn should_indent_child_node(
    settings: &FormatCodeSettings,
    parent: NodeId,
    child: Option<NodeId>,
    source_file: Option<NodeId>,
    is_next_child: bool,
    nodes: &mut Vec<Node>,
) -> bool {
    node_will_indent_child(settings, parent, child, source_file, false, nodes)
        && !(is_next_child
            && child.is_some_and(|c| {
                is_control_flow_ending_statement(nodes[c].kind, nodes[parent].kind)
            }))
}

/// `NodeWillIndentChild`
pub fn node_will_indent_child(
    settings: &FormatCodeSettings,
    parent: NodeId,
    child: Option<NodeId>,
    source_file: Option<NodeId>,
    indent_by_default: bool,
    nodes: &mut Vec<Node>,
) -> bool {
    let child_kind = child.map_or(Kind::Unknown, |c| nodes[c].kind);

    match nodes[parent].kind {
        Kind::ExpressionStatement
        | Kind::ClassDeclaration
        | Kind::ClassExpression
        | Kind::InterfaceDeclaration
        | Kind::EnumDeclaration
        | Kind::TypeAliasDeclaration
        | Kind::ArrayLiteralExpression
        | Kind::Block
        | Kind::ModuleBlock
        | Kind::ObjectLiteralExpression
        | Kind::TypeLiteral
        | Kind::MappedType
        | Kind::TupleType
        | Kind::ParenthesizedExpression
        | Kind::PropertyAccessExpression
        | Kind::CallExpression
        | Kind::NewExpression
        | Kind::VariableStatement
        | Kind::ExportAssignment
        | Kind::ReturnStatement
        | Kind::ConditionalExpression
        | Kind::ArrayBindingPattern
        | Kind::ObjectBindingPattern
        | Kind::JsxOpeningElement
        | Kind::JsxOpeningFragment
        | Kind::JsxSelfClosingElement
        | Kind::JsxExpression
        | Kind::MethodSignature
        | Kind::CallSignature
        | Kind::ConstructSignature
        | Kind::Parameter
        | Kind::FunctionType
        | Kind::ConstructorType
        | Kind::ParenthesizedType
        | Kind::TaggedTemplateExpression
        | Kind::AwaitExpression
        | Kind::NamedExports
        | Kind::NamedImports
        | Kind::ExportSpecifier
        | Kind::ImportSpecifier
        | Kind::PropertyDeclaration
        | Kind::CaseClause
        | Kind::DefaultClause => true,
        Kind::CaseBlock => settings.indent_switch_case.is_true_or_unknown(),
        Kind::VariableDeclaration | Kind::PropertyAssignment | Kind::BinaryExpression => {
            if settings
                .indent_multi_line_object_literal_beginning_on_blank_line
                .is_false_or_unknown()
                && source_file.is_some()
                && child_kind == Kind::ObjectLiteralExpression
            {
                return range_is_on_one_line(
                    nodes[child.unwrap()].loc,
                    source_file.unwrap(),
                    nodes,
                );
            }
            if nodes[parent].kind == Kind::BinaryExpression
                && source_file.is_some()
                && child_kind == Kind::JsxElement
            {
                let sf = source_file.unwrap();
                let parent_start_line = line_of_position(
                    nodes,
                    sf,
                    skip_trivia(&nodes[sf].as_source_file().text, nodes[parent].pos()),
                );
                let child_start_line = line_of_position(
                    nodes,
                    sf,
                    skip_trivia(
                        &nodes[sf].as_source_file().text,
                        nodes[child.unwrap()].pos(),
                    ),
                );
                return parent_start_line != child_start_line;
            }
            if nodes[parent].kind != Kind::BinaryExpression {
                return true;
            }
            indent_by_default
        }
        Kind::DoStatement
        | Kind::WhileStatement
        | Kind::ForInStatement
        | Kind::ForOfStatement
        | Kind::ForStatement
        | Kind::IfStatement
        | Kind::FunctionDeclaration
        | Kind::FunctionExpression
        | Kind::MethodDeclaration
        | Kind::Constructor
        | Kind::GetAccessor
        | Kind::SetAccessor => child_kind != Kind::Block,
        Kind::ArrowFunction => {
            if source_file.is_some() && child_kind == Kind::ParenthesizedExpression {
                return range_is_on_one_line(
                    nodes[child.unwrap()].loc,
                    source_file.unwrap(),
                    nodes,
                );
            }
            child_kind != Kind::Block
        }
        Kind::ExportDeclaration => child_kind != Kind::NamedExports,
        Kind::ImportDeclaration => {
            child_kind != Kind::ImportClause
                || (nodes[child.unwrap()]
                    .as_import_clause()
                    .named_bindings
                    .is_some_and(|nb| nodes[nb].kind != Kind::NamedImports))
        }
        Kind::JsxElement => child_kind != Kind::JsxClosingElement,
        Kind::JsxFragment => child_kind != Kind::JsxClosingFragment,
        Kind::IntersectionType | Kind::UnionType | Kind::SatisfiesExpression => {
            if child_kind == Kind::TypeLiteral
                || child_kind == Kind::TupleType
                || child_kind == Kind::MappedType
            {
                return false;
            }
            indent_by_default
        }
        Kind::TryStatement => {
            if child_kind == Kind::Block {
                return false;
            }
            indent_by_default
        }
        _ => indent_by_default,
    }
}

// A multiline conditional typically increases the indentation of its whenTrue and whenFalse children:
//
// condition
//
//	? whenTrue
//	: whenFalse;
//
// However, that indentation does not apply if the subexpressions themselves span multiple lines,
// applying their own indentation:
//
//	(() => {
//	  return complexCalculationForCondition();
//	})() ? {
//
//	  whenTrue: 'multiline object literal'
//	} : (
//
//	whenFalse('multiline parenthesized expression')
//
// );
//
// In these cases, we must discard the indentation increase that would otherwise be applied to the
// whenTrue and whenFalse children to avoid double-indenting their contents. To identify this scenario,
// we check for the whenTrue branch beginning on the line that the condition ends, and the whenFalse
// branch beginning on the line that the whenTrue branch ends.

/// `childIsUnindentedBranchOfConditionalExpression`
pub(crate) fn child_is_unindented_branch_of_conditional_expression(
    parent: NodeId,
    child: NodeId,
    child_start_line: i32,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> bool {
    if nodes[parent].kind == Kind::ConditionalExpression {
        let cond = nodes[parent].as_conditional_expression();
        let when_true = cond.when_true;
        let when_false = cond.when_false;
        let condition = cond.condition;
        if Some(child) == when_true || Some(child) == when_false {
            let condition_end_line = line_of_position(
                nodes,
                source_file,
                nodes[condition.expect("condition")].end(),
            );
            if Some(child) == when_true {
                return child_start_line == condition_end_line;
            } else {
                // On the whenFalse side, we have to look at the whenTrue side, because if that one was
                // indented, whenFalse must also be indented:
                //
                // const y = true
                //   ? 1 : (          L1: whenTrue indented because it's on a new line
                //     0              L2: indented two stops, one because whenTrue was indented
                //   );                   and one because of the parentheses spanning multiple lines
                let true_start_line =
                    get_start_line_for_node(when_true.unwrap(), source_file, nodes);
                let true_end_line =
                    line_of_position(nodes, source_file, nodes[when_true.unwrap()].end());
                return condition_end_line == true_start_line && true_end_line == child_start_line;
            }
        }
    }
    false
}

/// `argumentStartsOnSameLineAsPreviousArgument`
pub(crate) fn argument_starts_on_same_line_as_previous_argument(
    parent: NodeId,
    child: NodeId,
    child_start_line: i32,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> bool {
    if tsc_ast::is_call_expression(&nodes[parent]) || tsc_ast::is_new_expression(&nodes[parent]) {
        let Some(arguments) = nodes[parent].arguments() else {
            return false;
        };
        if arguments.is_empty() {
            return false;
        }
        let Some(current_index) = arguments.iter().position(|&n| n == child) else {
            // If it's not one of the arguments, don't look past this
            return false;
        };
        if current_index == 0 {
            return false; // Can't look at previous node if first
        }

        let previous_node = arguments[current_index - 1];
        let line_of_previous_node =
            line_of_position(nodes, source_file, nodes[previous_node].end());
        if child_start_line == line_of_previous_node {
            return true;
        }
    }
    false
}

/// `utf8.DecodeRuneInString` for byte slices — returns `(rune, size)`; `size`
/// is 0 for an empty slice and 1 for an invalid leading byte (Go `RuneError`
/// semantics). The input may start mid-UTF-8-sequence since callers scan
/// backwards byte-by-byte like Go does.
pub(crate) fn decode_rune_in_string(bytes: &[u8]) -> (char, usize) {
    if bytes.is_empty() {
        return ('\u{FFFD}', 0);
    }
    let first = bytes[0];
    if first < 0x80 {
        return (first as char, 1);
    }
    // try up to 4 bytes for a multi-byte sequence
    let n = bytes.len().min(4);
    match std::str::from_utf8(&bytes[..n]) {
        Ok(s) => {
            let ch = s.chars().next().unwrap();
            (ch, ch.len_utf8())
        }
        Err(e) if e.valid_up_to() > 0 => {
            let ch = std::str::from_utf8(&bytes[..e.valid_up_to()])
                .unwrap()
                .chars()
                .next()
                .unwrap();
            (ch, ch.len_utf8())
        }
        Err(_) => ('\u{FFFD}', 1),
    }
}
