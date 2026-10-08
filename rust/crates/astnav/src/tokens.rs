// Ported from tsc/internal/astnav/tokens.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `*ast.Node` is `NodeId` and `*ast.SourceFile` is the arena `NodeId` of the
//   file; file data is reached via `nodes[file].as_source_file()`. Public
//   functions take the arena (`&mut Vec<Node>`) first, then the file id.
// - Go `int` positions are `TextPos` (`i32`) so the `-1` sentinel in
//   `findRightmostValidToken` stays representable; the scanner works in
//   `usize`, so conversions happen at the `Scanner` boundary.
// - `Scanner<'a>` borrows `&'a str`. It cannot borrow `SourceFile::text` out
//   of `nodes` because `get_or_create_token`/`js_doc` need `&mut Vec<Node>`
//   while a scanner is alive. Each public entry point therefore clones the
//   file text once and scanners are built on the clone, playing the role of
//   `scanner.GetScannerForSourceFile`.
// - Go's `getNodeVisitor`/`VisitEachChildAndJSDoc` run on the *transform*
//   visitor (`NodeVisitor`/`visit_each_child`), because the algorithm needs
//   `NodeList`-level callbacks (list `pos`/`end` + binary searches) that the
//   flattened `for_each_child` traversal cannot express. The visitor's visit
//   callback is the identity, so no node is ever rebuilt; a throwaway
//   `NodeFactory` satisfies `VisitorCx`.
// - `NodeVisitor` hooks are `Fn`, not `FnMut`, so the cursors Go mutates
//   through closure captures (`next`, `left`, `prevChild`, ...) live in
//   `Cell`s/`RefCell`s shared by the closures.
// - `get_token_pos_of_node` is reimplemented locally: tsc-scanner's version
//   defers the `includeJSDoc` hop because it needs `&mut Vec<Node>` for the
//   lazy `js_doc` resolution.
// - `IsJSDocSingleCommentNodeList` in tsc-ast compares `&NodeList` pointers,
//   but `visit_each_child` hands hooks *cloned* lists, so the wrapper here
//   compares the parent's stored comment list by value.
//
// PORT(deferred): `tokens_test.go` is driven by the parser + jstest harness;
// `tsc-parser` is still being ported, so no tests are ported here yet.

use std::cell::{Cell, RefCell};

use tsc_ast::ast::{self, ModifierList, Node, NodeFactory, NodeFactoryHooks, NodeList};
use tsc_ast::ast_generated::is_private_identifier;
use tsc_ast::ids::NodeId;
use tsc_ast::kind_generated::Kind;
use tsc_ast::nodeflags::NodeFlags;
use tsc_ast::utilities::{
    find_last_visible_node, is_js_doc_kind, is_js_doc_link_like, is_js_doc_node,
    is_js_doc_single_comment_node, is_js_doc_single_comment_node_comment, is_js_doc_tag,
    is_jsx_child, is_non_whitespace_token, is_property_name_literal, is_whitespace_only_jsx_text,
    node_is_missing,
};
use tsc_ast::visitor::{
    NodeVisitor, NodeVisitorHooks, VisitModifiersHook, VisitNodeHook, VisitNodesHook, VisitorCx,
};
use tsc_core::binarysearch::binary_search_unique_func;
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::text::TextPos;
use tsc_scanner::scanner::{Scanner, SkipTriviaOptions, skip_trivia_ex};

const COMPARISON_LESS_THAN: i32 = -1;
const COMPARISON_EQUAL_TO: i32 = 0;
const COMPARISON_GREATER_THAN: i32 = 1;

/// Per-call context: the source file plus the cloned text that scanners
/// borrow from (see the file header note).
struct NavCtx<'a> {
    file: NodeId,
    text: &'a str,
    language_variant: LanguageVariant,
}

/// Go `int` → scanner `usize`. Go panics on negative positions (slice OOB);
/// `expect` mirrors that.
fn to_scanner_pos(pos: TextPos) -> usize {
    usize::try_from(pos).expect("astnav: negative position cannot be scanned")
}

/// `scanner.GetScannerForSourceFile(sourceFile, pos)` built on the cloned
/// text (`NavCtx::text` instead of `sourceFile.Text()`).
fn nav_scanner<'a>(ctx: &NavCtx<'a>, pos: TextPos) -> Scanner<'a> {
    let mut s = Scanner::new();
    s.set_text(ctx.text);
    s.set_language_variant(ctx.language_variant);
    s.reset_pos(to_scanner_pos(pos));
    s.scan();
    s
}

/// `shouldRescanLessThanLessThanToken(s, containingNode, token)` — Go's
/// scanner argument is unused.
fn should_rescan_less_than_less_than_token(containing_node: &Node, token: Kind) -> bool {
    token == Kind::LessThanLessThanToken && is_jsx_child(containing_node)
}

/// `scanNavigationToken(s, containingNode)`.
fn scan_navigation_token(s: &mut Scanner<'_>, nodes: &[Node], containing_node: NodeId) -> Kind {
    let token = s.token();
    if should_rescan_less_than_less_than_token(&nodes[containing_node], token) {
        return s.rescan_jsx_token(true /* allowMultilineJsxText */);
    }
    token
}

/// `GetTokenPosOfNode(node, sourceFile, includeJSDoc)` — ported locally
/// because tsc-scanner's version defers the `includeJSDoc` hop (lazy `js_doc`
/// resolution needs `&mut Vec<Node>`; see its PORT note).
fn get_token_pos_of_node(
    nodes: &mut Vec<Node>,
    ctx: &NavCtx<'_>,
    node: NodeId,
    include_jsdoc: bool,
) -> TextPos {
    // With nodes that have no width (i.e. 'Missing' nodes), we actually *don't*
    // want to skip trivia because this will launch us forward to the next token.
    if node_is_missing(Some(node), nodes) {
        return nodes[node].pos();
    }
    if is_js_doc_node(&nodes[node]) || nodes[node].kind == Kind::JsxText {
        // JsxText cannot actually contain comments, even though the scanner
        // will think it sees comments.
        return skip_trivia_ex(
            ctx.text,
            nodes[node].pos(),
            Some(&SkipTriviaOptions {
                stop_at_comments: true,
                ..Default::default()
            }),
        );
    }
    if include_jsdoc {
        let jsdocs = ast::js_doc(nodes, node, Some(ctx.file));
        if let Some(&first) = jsdocs.first() {
            return get_token_pos_of_node(nodes, ctx, first, false /* includeJSDoc */);
        }
    }
    skip_trivia_ex(
        ctx.text,
        nodes[node].pos(),
        Some(&SkipTriviaOptions {
            in_jsdoc: nodes[node].flags.intersects(NodeFlags::JSDOC),
            ..Default::default()
        }),
    )
}

/// `GetStartOfNode(node, file, includeJSDoc)` on a `VisitorCx` (internal;
/// the exported wrapper is `get_start_of_node` below).
fn start_of_node(
    cx: &mut VisitorCx<'_, '_>,
    ctx: &NavCtx<'_>,
    node: NodeId,
    include_jsdoc: bool,
) -> TextPos {
    get_token_pos_of_node(cx.nodes, ctx, node, include_jsdoc)
}

/// `getPosition(node, sourceFile, allowPositionInLeadingTrivia)`.
fn get_position(
    cx: &mut VisitorCx<'_, '_>,
    ctx: &NavCtx<'_>,
    node: NodeId,
    allow_position_in_leading_trivia: bool,
) -> TextPos {
    if allow_position_in_leading_trivia {
        return cx.nodes[node].pos();
    }
    get_token_pos_of_node(cx.nodes, ctx, node, true /* includeJSDoc */)
}

/// `sourceFile.EndOfFileToken.End()` — Go nil-derefs when unset.
fn eof_end(nodes: &[Node], file: NodeId) -> TextPos {
    let eof = nodes[file]
        .as_source_file()
        .end_of_file_token
        .expect("SourceFile.EndOfFileToken is not set");
    nodes[eof].end()
}

/// `IsJSDocSingleCommentNodeList(nodeList)` — tsc-ast's
/// `is_js_doc_single_comment_node_list` compares `&NodeList` pointers, but
/// `visit_each_child` hands hooks cloned lists; compare the parent's stored
/// comment list by value instead.
fn is_jsdoc_single_comment_node_list(node_list: Option<&NodeList>, nodes: &[Node]) -> bool {
    let Some(node_list) = node_list else {
        return false;
    };
    let Some(&first) = node_list.nodes().first() else {
        return false;
    };
    let Some(parent) = nodes[first].parent else {
        return false;
    };
    is_js_doc_single_comment_node(&nodes[parent], nodes)
        && nodes[parent]
            .comment_list()
            .is_some_and(|c| c.loc == node_list.loc && c.nodes() == node_list.nodes())
}

/// The `IsJSDocSingleCommentNodeComment` wrapper from `getNodeVisitor`.
fn wrap_visit_node<'a>(f: &'a VisitNodeHook<'a>) -> Box<VisitNodeHook<'a>> {
    Box::new(
        move |cx: &mut VisitorCx<'_, '_>, n: NodeId, v: &NodeVisitor<'a>| {
            if is_js_doc_single_comment_node_comment(Some(n), cx.nodes) {
                return Some(n);
            }
            f(cx, n, v)
        },
    )
}

/// The `IsJSDocSingleCommentNodeList` wrapper from `getNodeVisitor`.
fn wrap_visit_nodes<'a>(f: &'a VisitNodesHook<'a>) -> Box<VisitNodesHook<'a>> {
    Box::new(
        move |cx: &mut VisitorCx<'_, '_>, n: Option<NodeList>, v: &NodeVisitor<'a>| {
            if is_jsdoc_single_comment_node_list(n.as_ref(), cx.nodes) {
                return n;
            }
            f(cx, n, v)
        },
    )
}

/// `getNodeVisitor(visitNode, visitNodes)` — builds a `NodeVisitor` whose
/// `visit` is `core.Identity` and whose hooks run the given callbacks behind
/// the JSDoc-single-comment skips.
fn get_node_visitor<'a>(
    visit_node: Option<&'a VisitNodeHook<'a>>,
    visit_nodes: Option<&'a VisitNodesHook<'a>>,
) -> NodeVisitor<'a> {
    let wrapped_visit_node: Option<Box<VisitNodeHook<'a>>> = visit_node.map(wrap_visit_node);
    // Go: `VisitToken: wrappedVisitNode` — the same wrapper, built twice
    // (token children never reach `visitToken` in the generated dispatch
    // anyway, exactly like Go).
    let wrapped_visit_token: Option<Box<VisitNodeHook<'a>>> = visit_node.map(wrap_visit_node);
    let wrapped_visit_nodes: Option<Box<VisitNodesHook<'a>>> = visit_nodes.map(wrap_visit_nodes);
    let wrapped_visit_modifiers: Option<Box<VisitModifiersHook<'a>>> = visit_nodes.map(|f| {
        Box::new(
            move |cx: &mut VisitorCx<'_, '_>,
                  modifiers: Option<ModifierList>,
                  v: &NodeVisitor<'a>| {
                if let Some(mods) = modifiers.as_ref() {
                    let list = mods.as_node_list();
                    if !is_jsdoc_single_comment_node_list(Some(&list), cx.nodes) {
                        let _ = f(cx, Some(list), v);
                    }
                }
                modifiers
            },
        ) as Box<VisitModifiersHook<'a>>
    });
    NodeVisitor::new(
        Box::new(|_v: &NodeVisitor<'_>, _cx: &mut VisitorCx<'_, '_>, node: NodeId| Some(node)),
        NodeVisitorHooks {
            visit_node: wrapped_visit_node,
            visit_token: wrapped_visit_token,
            visit_nodes: wrapped_visit_nodes,
            visit_modifiers: wrapped_visit_modifiers,
            ..Default::default()
        },
    )
}

/// `VisitEachChildAndJSDoc(node, sourceFile, visitNode, visitNodes)`.
pub fn visit_each_child_and_jsdoc<'a>(
    nodes: &mut Vec<Node>,
    file: NodeId,
    node: NodeId,
    visit_node: Option<&'a VisitNodeHook<'a>>,
    visit_nodes: Option<&'a VisitNodesHook<'a>>,
) {
    let mut factory = NodeFactory::<'static>::new(NodeFactoryHooks::default());
    let mut cx = VisitorCx {
        nodes,
        factory: &mut factory,
    };
    visit_each_child_and_jsdoc_impl(&mut cx, file, node, visit_node, visit_nodes);
}

/// `VisitEachChildAndJSDoc` on an existing `VisitorCx`.
fn visit_each_child_and_jsdoc_impl<'a>(
    cx: &mut VisitorCx<'_, '_>,
    file: NodeId,
    node: NodeId,
    visit_node: Option<&'a VisitNodeHook<'a>>,
    visit_nodes: Option<&'a VisitNodesHook<'a>>,
) {
    let visitor = get_node_visitor(visit_node, visit_nodes);
    for jsdoc in ast::js_doc(cx.nodes, node, Some(file)) {
        if let Some(hook) = visitor.hooks.visit_node.as_deref() {
            let _ = hook(cx, jsdoc, &visitor);
        } else {
            let _ = visitor.visit_node(cx, Some(jsdoc));
        }
    }
    let _ = visitor.visit_each_child(cx, node);
}

/// `shouldSkipChild(node)`.
fn should_skip_child(node: &Node) -> bool {
    node.kind == Kind::JSDoc
        || node.kind == Kind::JSDocText
        || node.kind == Kind::JSDocTypeLiteral
        || node.kind == Kind::JSDocSignature
        || is_js_doc_link_like(node)
        || is_js_doc_tag(node)
}

/// The include-callback type for `getTokenAtPosition`
/// (`func(node *ast.Node) bool`).
type IncludePreceding<'a> = dyn Fn(&[Node], NodeId) -> bool + 'a;

/// `GetTouchingPropertyName(sourceFile, position)`.
pub fn get_touching_property_name(
    nodes: &mut Vec<Node>,
    file: NodeId,
    position: TextPos,
) -> Option<NodeId> {
    let mut factory = NodeFactory::<'static>::new(NodeFactoryHooks::default());
    let mut cx = VisitorCx {
        nodes,
        factory: &mut factory,
    };
    let text = cx.nodes[file].as_source_file().text.clone();
    let ctx = NavCtx {
        file,
        text: &text,
        language_variant: cx.nodes[file].as_source_file().language_variant,
    };
    let include = |nodes: &[Node], node: NodeId| {
        is_property_name_literal(&nodes[node])
            || nodes[node].kind.is_keyword_kind()
            || is_private_identifier(&nodes[node])
    };
    get_token_at_position_impl(
        &mut cx,
        &ctx,
        position,
        false, /* allowPositionInLeadingTrivia */
        Some(&include),
    )
}

/// `GetTouchingToken(sourceFile, position)`.
pub fn get_touching_token(
    nodes: &mut Vec<Node>,
    file: NodeId,
    position: TextPos,
) -> Option<NodeId> {
    let mut factory = NodeFactory::<'static>::new(NodeFactoryHooks::default());
    let mut cx = VisitorCx {
        nodes,
        factory: &mut factory,
    };
    let text = cx.nodes[file].as_source_file().text.clone();
    let ctx = NavCtx {
        file,
        text: &text,
        language_variant: cx.nodes[file].as_source_file().language_variant,
    };
    get_token_at_position_impl(
        &mut cx, &ctx, position, false, /* allowPositionInLeadingTrivia */
        None,
    )
}

/// `GetTokenAtPosition(sourceFile, position)`.
pub fn get_token_at_position(
    nodes: &mut Vec<Node>,
    file: NodeId,
    position: TextPos,
) -> Option<NodeId> {
    let mut factory = NodeFactory::<'static>::new(NodeFactoryHooks::default());
    let mut cx = VisitorCx {
        nodes,
        factory: &mut factory,
    };
    let text = cx.nodes[file].as_source_file().text.clone();
    let ctx = NavCtx {
        file,
        text: &text,
        language_variant: cx.nodes[file].as_source_file().language_variant,
    };
    get_token_at_position_impl(
        &mut cx, &ctx, position, true, /* allowPositionInLeadingTrivia */
        None,
    )
}

/// `getTokenAtPosition(sourceFile, position, allowPositionInLeadingTrivia,
/// includePrecedingTokenAtEndPosition)` — returns a token at `position`,
/// either a real node or a synthesized token from the file's token cache.
fn get_token_at_position_impl(
    cx: &mut VisitorCx<'_, '_>,
    ctx: &NavCtx<'_>,
    position: TextPos,
    allow_position_in_leading_trivia: bool,
    include_preceding_token_at_end_position: Option<&IncludePreceding<'_>>,
) -> Option<NodeId> {
    // `next` tracks the node whose children will be visited on the next
    // iteration. `prevSubtree` is a node whose end position is equal to the
    // target position, only if `includePrecedingTokenAtEndPosition` is
    // provided. Once set, the next iteration of the loop will test the
    // rightmost token of `prevSubtree` to see if it should be returned.
    let next = Cell::new(Option::<NodeId>::None);
    let prev_subtree = Cell::new(Option::<NodeId>::None);
    let mut current = ctx.file;
    // `left` tracks the lower boundary of the node/token that could be
    // returned, and is eventually the scanner's start position, if the
    // scanner is used.
    let left = Cell::new(0 as TextPos);
    // `nodeAfterLeft` tracks the first node we visit after visiting the node
    // that advances `left`. When scanning in between nodes for token, we
    // should only scan up to the start of `nodeAfterLeft`.
    let node_after_left = Cell::new(Option::<NodeId>::None);

    let get_included_preceding_token =
        |cx: &mut VisitorCx<'_, '_>, subtree: NodeId| -> Option<NodeId> {
            let child = find_preceding_token_ex_impl(cx, ctx, position, Some(subtree), false);
            if let Some(child) = child {
                if cx.nodes[child].end() == position {
                    if let Some(f) = include_preceding_token_at_end_position {
                        if f(cx.nodes, child) {
                            return Some(child);
                        }
                    }
                }
            }
            None
        };

    let test_node = |cx: &mut VisitorCx<'_, '_>, node: NodeId| -> i32 {
        let (kind, end, reparsed) = {
            let n = &cx.nodes[node];
            (n.kind, n.end(), n.flags.intersects(NodeFlags::REPARSED))
        };
        if kind != Kind::EndOfFile
            && end == position
            && include_preceding_token_at_end_position.is_some()
            && !reparsed
        {
            if let Some(ps) = prev_subtree.get() {
                if get_included_preceding_token(cx, ps).is_some() {
                    return COMPARISON_EQUAL_TO;
                }
            }
            prev_subtree.set(Some(node));
        }

        // A node "contains" the position if position < end, except nodes at
        // the file end treat end as inclusive (there's nowhere else to
        // look). This applies to the EOF token itself, and to JSDoc nodes
        // reaching EOF (e.g. unterminated JSDoc comments).
        if end < position
            || (end == position
                && kind != Kind::EndOfFile
                && (!is_js_doc_kind(kind) || end != eof_end(cx.nodes, ctx.file)))
        {
            return COMPARISON_LESS_THAN;
        }
        let node_pos = get_position(cx, ctx, node, allow_position_in_leading_trivia);
        if node_pos > position {
            return COMPARISON_GREATER_THAN;
        }
        COMPARISON_EQUAL_TO
    };

    // We zero in on the node that contains the target position by visiting
    // each child and JSDoc comment of the current node. Node children are
    // walked in order, while node lists are binary searched.
    let visit_node =
        |cx: &mut VisitorCx<'_, '_>, node: NodeId, _v: &NodeVisitor<'_>| -> Option<NodeId> {
            // We can't abort visiting children, so once a match is found, we set
            // `next` and do nothing on subsequent visits.
            if cx.nodes[node].flags.intersects(NodeFlags::REPARSED) {
                return None;
            }
            if node_after_left.get().is_none() {
                node_after_left.set(Some(node));
            }
            if next.get().is_none() {
                match test_node(cx, node) {
                    COMPARISON_LESS_THAN => {
                        if !is_js_doc_kind(cx.nodes[node].kind) {
                            // We can't move the left boundary into or beyond
                            // JSDoc, because we may end up returning the token
                            // after this JSDoc, constructing it with the scanner,
                            // and we need to include all its leading trivia in
                            // its position.
                            left.set(cx.nodes[node].end());
                        }
                        node_after_left.set(None);
                    }
                    COMPARISON_EQUAL_TO => next.set(Some(node)),
                    _ => {}
                }
            }
            Some(node)
        };

    let visit_nodes = |cx: &mut VisitorCx<'_, '_>,
                       node_list: Option<NodeList>,
                       _v: &NodeVisitor<'_>|
     -> Option<NodeList> {
        let Some(list) = node_list.as_ref() else {
            return node_list;
        };
        if list.nodes.is_empty() {
            return node_list;
        }
        if node_after_left.get().is_none() {
            for &node in list.nodes.iter() {
                if !cx.nodes[node].flags.intersects(NodeFlags::REPARSED) {
                    node_after_left.set(Some(node));
                    break;
                }
            }
        }
        if next.get().is_none() {
            if list.end() == position && include_preceding_token_at_end_position.is_some() {
                left.set(list.end());
                node_after_left.set(None);
                for &v in list.nodes.iter().rev() {
                    if !cx.nodes[v].flags.intersects(NodeFlags::REPARSED) {
                        prev_subtree.set(Some(v));
                        break;
                    }
                }
            } else if list.end() <= position {
                left.set(list.end());
                node_after_left.set(None);
            } else if list.pos() <= position {
                let slice: &[NodeId] = &list.nodes;
                let (mut index, mut found) = binary_search_unique_func(slice, |middle, &node| {
                    if cx.nodes[node].flags.intersects(NodeFlags::REPARSED) {
                        return COMPARISON_EQUAL_TO;
                    }
                    let cmp = test_node(cx, node);
                    if cmp < 0 {
                        left.set(cx.nodes[node].end());
                        node_after_left.set(None);
                        for i in (middle + 1)..slice.len() {
                            if !cx.nodes[slice[i]].flags.intersects(NodeFlags::REPARSED) {
                                node_after_left.set(Some(slice[i]));
                                break;
                            }
                        }
                    }
                    cmp
                });
                let mut filtered: Option<Vec<NodeId>> = None;
                if found && cx.nodes[slice[index]].flags.intersects(NodeFlags::REPARSED) {
                    // filter and search again
                    let f: Vec<NodeId> = slice
                        .iter()
                        .copied()
                        .filter(|&node| !cx.nodes[node].flags.intersects(NodeFlags::REPARSED))
                        .collect();
                    let r = binary_search_unique_func(&f, |middle, &node| {
                        let cmp = test_node(cx, node);
                        if cmp < 0 {
                            left.set(cx.nodes[node].end());
                            node_after_left.set(f.get(middle + 1).copied());
                        }
                        cmp
                    });
                    index = r.0;
                    found = r.1;
                    filtered = Some(f);
                }
                if found {
                    let hit = match &filtered {
                        Some(f) => f[index],
                        None => slice[index],
                    };
                    next.set(Some(hit));
                }
            }
        }
        node_list
    };

    loop {
        visit_each_child_and_jsdoc_impl(
            cx,
            ctx.file,
            current,
            Some(&visit_node),
            Some(&visit_nodes),
        );
        // If prevSubtree was set on the last iteration, it ends at the
        // target position. Check if the rightmost token of prevSubtree
        // should be returned based on the
        // `includePrecedingTokenAtEndPosition` callback.
        if let Some(ps) = prev_subtree.get() {
            if let Some(child) = get_included_preceding_token(cx, ps) {
                // Optimization: includePrecedingTokenAtEndPosition only ever
                // returns true for real AST nodes, so we don't run the
                // scanner here.
                return Some(child);
            }
            prev_subtree.set(None);
        }

        // No node was found that contains the target position, so we've gone
        // as deep as we can in the AST. We've either found a token, or we
        // need to run the scanner to construct one that isn't stored in the
        // AST.
        if next.get().is_none() {
            if cx.nodes[current].kind.is_token_kind() || should_skip_child(&cx.nodes[current]) {
                return Some(current);
            }
            let mut scanner = nav_scanner(ctx, left.get());
            let mut end = cx.nodes[current].end();
            // We should only scan up to the start of the next node in the
            // AST after the node ending at position `left`. It is necessary
            // to enforce this invariant in cases where `position` occurs in
            // between two node/tokens, such that we would not find a token
            // in the loop below before we reach the next node.
            // We can fall into this case when `allowPositionInLeadingTrivia`
            // is false and `position` is in a leading trivia, or when
            // `position` would be in the leading trivia of a node but this
            // node is inside JSDoc:
            // ```
            // /**
            //  * @type {{
            //  */*$*/ identifier: boolean;
            //  * }}
            //  */
            // ```
            // The position of marker '$' falls in between the asterisk token
            // and the identifier token, but is not part of the leading
            // trivia for `identifier`.
            if let Some(nal) = node_after_left.get() {
                end = cx.nodes[nal].pos();
            }
            let mut left = left.get();
            while left < end {
                let token = scan_navigation_token(&mut scanner, cx.nodes, current);
                let token_full_start = scanner.token_full_start() as TextPos;
                let token_start = if allow_position_in_leading_trivia {
                    token_full_start
                } else {
                    scanner.token_start() as TextPos
                };
                let token_end = scanner.token_end() as TextPos;
                let flags = scanner.token_flags();
                if token_end > end {
                    break;
                }
                if token_start <= position && position < token_end {
                    if token == Kind::Identifier || !token.is_token_kind() {
                        if is_js_doc_kind(cx.nodes[current].kind) {
                            return Some(current);
                        }
                        panic!(
                            "did not expect {} to have {} in its trivia",
                            cx.nodes[current].kind_string(),
                            token.kind_string()
                        );
                    }
                    return Some(ast::get_or_create_token(
                        cx.nodes,
                        ctx.file,
                        token,
                        token_full_start,
                        token_end,
                        current,
                        flags,
                    ));
                }
                if include_preceding_token_at_end_position.is_some() && token_end == position {
                    let prev_token = ast::get_or_create_token(
                        cx.nodes,
                        ctx.file,
                        token,
                        token_full_start,
                        token_end,
                        current,
                        flags,
                    );
                    if let Some(f) = include_preceding_token_at_end_position {
                        if f(cx.nodes, prev_token) {
                            return Some(prev_token);
                        }
                    }
                }
                left = token_end;
                scanner.scan();
            }
            return Some(current);
        }
        current = next.get().unwrap();
        left.set(cx.nodes[current].pos());
        node_after_left.set(None);
        next.set(None);
    }
}

/// `findRightmostNode(node)` — finds the rightmost child/descendant. Unused
/// in `tokens.go` itself (Go keeps it as a package-private helper). Note Go
/// uses plain `VisitEachChild` (no JSDoc children).
#[allow(dead_code)]
fn find_rightmost_node(cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
    let next = Cell::new(Option::<NodeId>::None);
    let mut current = node;
    let visit_node =
        |_cx: &mut VisitorCx<'_, '_>, node: NodeId, _v: &NodeVisitor<'_>| -> Option<NodeId> {
            next.set(Some(node));
            Some(node)
        };
    let visit_nodes = |cx: &mut VisitorCx<'_, '_>,
                       node_list: Option<NodeList>,
                       _v: &NodeVisitor<'_>|
     -> Option<NodeList> {
        if let Some(list) = node_list.as_ref() {
            if let Some(rightmost) = find_last_visible_node(&list.nodes, cx.nodes) {
                next.set(Some(rightmost));
            }
        }
        node_list
    };
    let visitor = get_node_visitor(Some(&visit_node), Some(&visit_nodes));
    loop {
        let _ = visitor.visit_each_child(cx, current);
        match next.get() {
            None => return current,
            Some(n) => {
                current = n;
                next.set(None);
            }
        }
    }
}

/// `FindPrecedingToken(sourceFile, position)` — finds the leftmost token
/// satisfying `position < token.End()`. If the leftmost token satisfying
/// `position < token.End()` is invalid, or if position is in the trivia of
/// that leftmost token, we will find the rightmost valid token with
/// `token.End() <= position`.
pub fn find_preceding_token(
    nodes: &mut Vec<Node>,
    file: NodeId,
    position: TextPos,
) -> Option<NodeId> {
    find_preceding_token_ex(nodes, file, position, None, false)
}

/// `FindPrecedingTokenEx(sourceFile, position, startNode, excludeJSDoc)`.
pub fn find_preceding_token_ex(
    nodes: &mut Vec<Node>,
    file: NodeId,
    position: TextPos,
    start_node: Option<NodeId>,
    exclude_jsdoc: bool,
) -> Option<NodeId> {
    let mut factory = NodeFactory::<'static>::new(NodeFactoryHooks::default());
    let mut cx = VisitorCx {
        nodes,
        factory: &mut factory,
    };
    let text = cx.nodes[file].as_source_file().text.clone();
    let ctx = NavCtx {
        file,
        text: &text,
        language_variant: cx.nodes[file].as_source_file().language_variant,
    };
    find_preceding_token_ex_impl(&mut cx, &ctx, position, start_node, exclude_jsdoc)
}

fn find_preceding_token_ex_impl(
    cx: &mut VisitorCx<'_, '_>,
    ctx: &NavCtx<'_>,
    position: TextPos,
    start_node: Option<NodeId>,
    exclude_jsdoc: bool,
) -> Option<NodeId> {
    let node = start_node.unwrap_or(ctx.file);
    let result = preceding_token_find(cx, ctx, position, node, exclude_jsdoc);
    if let Some(result) = result {
        if is_whitespace_only_jsx_text(&cx.nodes[result]) {
            panic!("Expected result to be a non-whitespace token.");
        }
    }
    result
}

/// The `find` closure inside `FindPrecedingTokenEx` — recursive, so a
/// module-level fn taking the same context.
fn preceding_token_find(
    cx: &mut VisitorCx<'_, '_>,
    ctx: &NavCtx<'_>,
    position: TextPos,
    n: NodeId,
    exclude_jsdoc: bool,
) -> Option<NodeId> {
    if is_non_whitespace_token(&cx.nodes[n]) && cx.nodes[n].kind != Kind::EndOfFile {
        return Some(n);
    }

    // `foundChild` is the leftmost node that contains the target position.
    // `prevChild` is the last visited child of the current node.
    let found_child = Cell::new(Option::<NodeId>::None);
    let prev_child = Cell::new(Option::<NodeId>::None);
    let visit_node =
        |cx: &mut VisitorCx<'_, '_>, node: NodeId, _v: &NodeVisitor<'_>| -> Option<NodeId> {
            // skip synthesized nodes (that will exist now because of jsdoc
            // handling)
            if cx.nodes[node].flags.intersects(NodeFlags::REPARSED) {
                return Some(node);
            }
            if found_child.get().is_some() {
                // We cannot abort visiting children, so once the desired child
                // is found, we do nothing.
                return Some(node);
            }
            if position < cx.nodes[node].end()
                && prev_child
                    .get()
                    .map_or(true, |p| cx.nodes[p].end() <= position)
            {
                found_child.set(Some(node));
            } else {
                prev_child.set(Some(node));
            }
            Some(node)
        };
    let visit_nodes = |cx: &mut VisitorCx<'_, '_>,
                       node_list: Option<NodeList>,
                       _v: &NodeVisitor<'_>|
     -> Option<NodeList> {
        if found_child.get().is_some() {
            return node_list;
        }
        if let Some(list) = node_list.as_ref() {
            if !list.nodes.is_empty() {
                let slice: &[NodeId] = &list.nodes;
                let (index, found) = binary_search_unique_func(slice, |middle, _| {
                    // synthetic jsdoc nodes should have
                    // jsdocNode.End() <= n.Pos()
                    if cx.nodes[slice[middle]]
                        .flags
                        .intersects(NodeFlags::REPARSED)
                    {
                        return COMPARISON_LESS_THAN;
                    }
                    if position < cx.nodes[slice[middle]].end() {
                        if middle == 0 || position >= cx.nodes[slice[middle - 1]].end() {
                            return COMPARISON_EQUAL_TO;
                        }
                        return COMPARISON_GREATER_THAN;
                    }
                    COMPARISON_LESS_THAN
                });
                if found {
                    found_child.set(Some(slice[index]));
                }

                let valid_lookup_index: i64 = if found {
                    index as i64 - 1
                } else {
                    slice.len() as i64 - 1
                };
                let mut i = valid_lookup_index;
                while i >= 0 {
                    let node = slice[i as usize];
                    if !cx.nodes[node].flags.intersects(NodeFlags::REPARSED) {
                        if prev_child.get().is_none() {
                            prev_child.set(Some(node));
                        }
                    }
                    i -= 1;
                }
            }
        }
        node_list
    };
    visit_each_child_and_jsdoc_impl(cx, ctx.file, n, Some(&visit_node), Some(&visit_nodes));

    if let Some(fc) = found_child.get() {
        // Note that the span of a node's tokens is
        // [getStartOfNode(node, ...), node.end). Given that
        // `position < child.end` and child has constituent tokens, we
        // distinguish these cases:
        // 1) `position` precedes `child`'s tokens or `child` has no tokens
        //    (ie: in a comment or whitespace preceding `child`): we need to
        //    find the last token in a previous child node or child tokens.
        // 2) `position` is within the same span: we recurse on `child`.
        let start = start_of_node(cx, ctx, fc, !exclude_jsdoc /* includeJSDoc */);
        let look_in_previous_child = start >= position || !is_valid_preceding_node(cx, ctx, fc);
        if look_in_previous_child {
            if position >= cx.nodes[fc].pos() {
                // Find jsdoc preceding the foundChild.
                let mut jsdoc_opt: Option<NodeId> = None;
                let node_jsdoc = ast::js_doc(cx.nodes, n, Some(ctx.file));
                for &jd in node_jsdoc.iter().rev() {
                    if cx.nodes[jd].pos() >= cx.nodes[fc].pos() {
                        jsdoc_opt = Some(jd);
                        break;
                    }
                }
                if let Some(jd) = jsdoc_opt {
                    if !exclude_jsdoc && position < cx.nodes[jd].end() {
                        return preceding_token_find(cx, ctx, position, jd, exclude_jsdoc);
                    }
                    return find_rightmost_valid_token(
                        cx,
                        ctx,
                        cx.nodes[jd].end(),
                        n,
                        position,
                        exclude_jsdoc,
                    );
                }
                return find_rightmost_valid_token(
                    cx,
                    ctx,
                    cx.nodes[fc].pos(),
                    n,
                    -1, /* position */
                    exclude_jsdoc,
                );
            }
            // Answer is in tokens between two visited children.
            return find_rightmost_valid_token(
                cx,
                ctx,
                cx.nodes[fc].pos(),
                n,
                position,
                exclude_jsdoc,
            );
        }
        // position is in [foundChild.getStart(), foundChild.End): recur.
        return preceding_token_find(cx, ctx, position, fc, exclude_jsdoc);
    }

    // We have two cases here: either the position is at the end of the file,
    // or the desired token is in the unvisited trailing tokens of the
    // current node.
    if position >= cx.nodes[n].end() {
        return find_rightmost_valid_token(cx, ctx, cx.nodes[n].end(), n, -1, exclude_jsdoc);
    }
    find_rightmost_valid_token(cx, ctx, cx.nodes[n].end(), n, position, exclude_jsdoc)
}

/// `isValidPrecedingNode(node, sourceFile)`.
fn is_valid_preceding_node(cx: &mut VisitorCx<'_, '_>, ctx: &NavCtx<'_>, node: NodeId) -> bool {
    if cx.nodes[node].kind == Kind::EndOfFile {
        return !ast::js_doc(cx.nodes, node, Some(ctx.file)).is_empty();
    }
    let start = start_of_node(cx, ctx, node, false /* includeJSDoc */);
    let width = cx.nodes[node].end() - start;
    !(is_whitespace_only_jsx_text(&cx.nodes[node]) || width == 0)
}

/// `GetStartOfNode(node, file, includeJSDoc)` — exported helper.
pub fn get_start_of_node(
    nodes: &mut Vec<Node>,
    file: NodeId,
    node: NodeId,
    include_jsdoc: bool,
) -> TextPos {
    let text = nodes[file].as_source_file().text.clone();
    let ctx = NavCtx {
        file,
        text: &text,
        language_variant: nodes[file].as_source_file().language_variant,
    };
    get_token_pos_of_node(nodes, &ctx, node, include_jsdoc)
}

/// `findRightmostValidToken(endPos, sourceFile, containingNode, position,
/// excludeJSDoc)` — looks for the rightmost valid token in the range
/// `[startPos, endPos)`. If `position` is >= 0, looks for the rightmost valid
/// token that precedes or touches that position (`-1` is Go's nil-sentinel
/// for "use `containingNode.End()`").
fn find_rightmost_valid_token(
    cx: &mut VisitorCx<'_, '_>,
    ctx: &NavCtx<'_>,
    end_pos: TextPos,
    containing_node: NodeId,
    position: TextPos,
    exclude_jsdoc: bool,
) -> Option<NodeId> {
    let position = if position == -1 {
        cx.nodes[containing_node].end()
    } else {
        position
    };
    rightmost_valid_find(
        cx,
        ctx,
        Some(containing_node),
        end_pos,
        containing_node,
        position,
        exclude_jsdoc,
    )
}

/// The `find` closure inside `findRightmostValidToken` — recursive, so a
/// module-level fn.
#[allow(clippy::too_many_arguments)]
fn rightmost_valid_find(
    cx: &mut VisitorCx<'_, '_>,
    ctx: &NavCtx<'_>,
    n: Option<NodeId>,
    end_pos: TextPos,
    containing_node: NodeId,
    position: TextPos,
    exclude_jsdoc: bool,
) -> Option<NodeId> {
    let n = n?;
    if is_non_whitespace_token(&cx.nodes[n]) {
        return Some(n);
    }

    let rightmost_valid_node = Cell::new(Option::<NodeId>::None);
    // Nodes after the last valid node.
    let rightmost_visited_nodes: RefCell<Vec<NodeId>> = RefCell::new(Vec::with_capacity(1));
    let has_children = Cell::new(false);
    let should_visit_node = |cx: &mut VisitorCx<'_, '_>, node: NodeId| -> bool {
        // Node is synthetic or out of the desired range: don't visit it.
        !(cx.nodes[node].flags.intersects(NodeFlags::REPARSED)
            || cx.nodes[node].end() > end_pos
            || start_of_node(cx, ctx, node, !exclude_jsdoc /* includeJSDoc */) >= position)
    };
    let visit_node =
        |cx: &mut VisitorCx<'_, '_>, node: NodeId, _v: &NodeVisitor<'_>| -> Option<NodeId> {
            if cx.nodes[node].flags.intersects(NodeFlags::REPARSED) {
                return Some(node);
            }
            has_children.set(true);
            if !should_visit_node(cx, node) {
                return Some(node);
            }
            rightmost_visited_nodes.borrow_mut().push(node);
            if is_valid_preceding_node(cx, ctx, node) {
                rightmost_valid_node.set(Some(node));
                rightmost_visited_nodes.borrow_mut().clear();
            }
            Some(node)
        };
    let visit_nodes = |cx: &mut VisitorCx<'_, '_>,
                       node_list: Option<NodeList>,
                       _v: &NodeVisitor<'_>|
     -> Option<NodeList> {
        if let Some(list) = node_list.as_ref() {
            if !list.nodes.is_empty() {
                has_children.set(true);
                let slice: &[NodeId] = &list.nodes;
                let (index, _) = binary_search_unique_func(slice, |_middle, &node| {
                    if cx.nodes[node].end() > end_pos {
                        return COMPARISON_GREATER_THAN;
                    }
                    COMPARISON_LESS_THAN
                });
                let mut valid_index: i64 = -1;
                for i in (0..index).rev() {
                    if !should_visit_node(cx, slice[i]) {
                        continue;
                    }
                    if is_valid_preceding_node(cx, ctx, slice[i]) {
                        valid_index = i as i64;
                        rightmost_valid_node.set(Some(slice[i]));
                        break;
                    }
                }
                let mut i = valid_index + 1;
                while (i as usize) < index {
                    if should_visit_node(cx, slice[i as usize]) {
                        rightmost_visited_nodes.borrow_mut().push(slice[i as usize]);
                    }
                    i += 1;
                }
            }
        }
        node_list
    };
    visit_each_child_and_jsdoc_impl(cx, ctx.file, n, Some(&visit_node), Some(&visit_nodes));

    // Three cases:
    // 1. The answer is a token of `rightmostValidNode`.
    // 2. The answer is one of the unvisited tokens that occur after the
    //    rightmost valid node.
    // 3. The current node is a childless, token-less node. The answer is the
    //    current node.

    // Case 2: Look at unvisited trailing tokens that occur in between the
    // rightmost visited nodes.
    if !should_skip_child(&cx.nodes[n]) {
        // JSDoc nodes don't include trivia tokens as children.
        let mut start_pos = match rightmost_valid_node.get() {
            Some(rvn) => cx.nodes[rvn].end(),
            None => cx.nodes[n].pos(),
        };
        let mut scanner = nav_scanner(ctx, start_pos);
        let mut tokens: Vec<NodeId> = Vec::new();
        let visited: Vec<NodeId> = rightmost_visited_nodes.borrow().clone();
        for visited_node in visited {
            // Trailing tokens that occur before this node.
            let limit = cx.nodes[visited_node].pos().min(position);
            while start_pos < limit {
                let token = scan_navigation_token(&mut scanner, cx.nodes, n);
                let token_start = scanner.token_start() as TextPos;
                if token_start >= limit {
                    break;
                }
                let token_full_start = scanner.token_full_start() as TextPos;
                let token_end = scanner.token_end() as TextPos;
                start_pos = token_end;
                let flags = scanner.token_flags();
                tokens.push(ast::get_or_create_token(
                    cx.nodes,
                    ctx.file,
                    token,
                    token_full_start,
                    token_end,
                    n,
                    flags,
                ));
                scanner.scan();
            }
            start_pos = cx.nodes[visited_node].end();
            scanner.reset_pos(to_scanner_pos(start_pos));
            scanner.scan();
        }
        // Trailing tokens after last visited node.
        let limit = end_pos.min(position);
        while start_pos < limit {
            let token = scan_navigation_token(&mut scanner, cx.nodes, n);
            let token_start = scanner.token_start() as TextPos;
            if token_start >= limit {
                break;
            }
            let token_full_start = scanner.token_full_start() as TextPos;
            let token_end = scanner.token_end() as TextPos;
            start_pos = token_end;
            let flags = scanner.token_flags();
            tokens.push(ast::get_or_create_token(
                cx.nodes,
                ctx.file,
                token,
                token_full_start,
                token_end,
                n,
                flags,
            ));
            scanner.scan();
        }

        // Find preceding valid token.
        for &t in tokens.iter().rev() {
            if !is_whitespace_only_jsx_text(&cx.nodes[t]) {
                return Some(t);
            }
        }
    }

    // Case 3: childless node.
    if !has_children.get() {
        if n != containing_node {
            return Some(n);
        }
        return None;
    }
    // Case 1: recur on rightmostValidNode.
    let rvn = rightmost_valid_node.get();
    let end_pos = match rvn {
        Some(r) => cx.nodes[r].end(),
        None => end_pos,
    };
    rightmost_valid_find(
        cx,
        ctx,
        rvn,
        end_pos,
        containing_node,
        position,
        exclude_jsdoc,
    )
}

/// `FindNextToken(previousToken, parent, file)`.
pub fn find_next_token(
    nodes: &mut Vec<Node>,
    file: NodeId,
    previous_token: NodeId,
    parent: NodeId,
) -> Option<NodeId> {
    let mut factory = NodeFactory::<'static>::new(NodeFactoryHooks::default());
    let mut cx = VisitorCx {
        nodes,
        factory: &mut factory,
    };
    let text = cx.nodes[file].as_source_file().text.clone();
    let ctx = NavCtx {
        file,
        text: &text,
        language_variant: cx.nodes[file].as_source_file().language_variant,
    };
    next_token_find(&mut cx, &ctx, previous_token, parent)
}

/// The `find` closure inside `FindNextToken` — recursive, so a module-level
/// fn.
fn next_token_find(
    cx: &mut VisitorCx<'_, '_>,
    ctx: &NavCtx<'_>,
    previous_token: NodeId,
    n: NodeId,
) -> Option<NodeId> {
    let prev_end = cx.nodes[previous_token].end();
    let prev_pos = cx.nodes[previous_token].pos();
    if cx.nodes[n].kind.is_token_kind() && cx.nodes[n].pos() == prev_end {
        // this is token that starts at the end of previous token - return it
        return Some(n);
    }
    // Node that contains `previousToken` or occurs immediately after it.
    let found_node = Cell::new(Option::<NodeId>::None);
    let visit_node =
        |cx: &mut VisitorCx<'_, '_>, node: NodeId, _v: &NodeVisitor<'_>| -> Option<NodeId> {
            if !cx.nodes[node].flags.intersects(NodeFlags::REPARSED)
                && cx.nodes[node].pos() <= prev_end
                && cx.nodes[node].end() > prev_end
            {
                found_node.set(Some(node));
            }
            Some(node)
        };
    let visit_nodes = |cx: &mut VisitorCx<'_, '_>,
                       node_list: Option<NodeList>,
                       _v: &NodeVisitor<'_>|
     -> Option<NodeList> {
        if let Some(list) = node_list.as_ref() {
            if !list.nodes.is_empty() && found_node.get().is_none() {
                let slice: &[NodeId] = &list.nodes;
                let (index, found) = binary_search_unique_func(slice, |_middle, &node| {
                    if cx.nodes[node].flags.intersects(NodeFlags::REPARSED) {
                        return COMPARISON_LESS_THAN;
                    }
                    if cx.nodes[node].pos() > prev_end {
                        return COMPARISON_GREATER_THAN;
                    }
                    if cx.nodes[node].end() <= prev_pos {
                        return COMPARISON_LESS_THAN;
                    }
                    COMPARISON_EQUAL_TO
                });
                if found {
                    found_node.set(Some(slice[index]));
                }
            }
        }
        node_list
    };
    visit_each_child_and_jsdoc_impl(cx, ctx.file, n, Some(&visit_node), Some(&visit_nodes));
    // Cases:
    // 1. no answer exists
    // 2. answer is an unvisited token
    // 3. answer is in the visited found node

    // Case 3: look for the next token inside the found node.
    if let Some(found) = found_node.get() {
        return next_token_find(cx, ctx, previous_token, found);
    }
    let start_pos = prev_end;
    // Case 2: look for the next token directly.
    if start_pos >= cx.nodes[n].pos() && start_pos < cx.nodes[n].end() {
        let scanner = &mut nav_scanner(ctx, start_pos);
        let token = scanner.token();
        let token_full_start = scanner.token_full_start() as TextPos;
        let token_end = scanner.token_end() as TextPos;
        let flags = scanner.token_flags();
        // Use tokenFullStart (which includes leading trivia) to match TS's
        // findNextToken behavior where `n.pos === previousToken.end` is
        // checked (TS's pos includes trivia, same as Go's
        // Pos()/tokenFullStart).
        if token_full_start == prev_end {
            return Some(ast::get_or_create_token(
                cx.nodes,
                ctx.file,
                token,
                token_full_start,
                token_end,
                n,
                flags,
            ));
        }
        panic!(
            "Expected to find next token at {}, got token {} at {}",
            prev_end,
            token.kind_string(),
            token_full_start
        );
    }
    // Case 3: no answer.
    None
}

/// `FindChildOfKind(containingNode, kind, sourceFile)` — searches for a child
/// node or token of the specified kind within a containing node. Scans
/// through both AST nodes and intervening tokens to find the first match.
pub fn find_child_of_kind(
    nodes: &mut Vec<Node>,
    file: NodeId,
    containing_node: NodeId,
    kind: Kind,
) -> Option<NodeId> {
    let text = nodes[file].as_source_file().text.clone();
    let ctx = NavCtx {
        file,
        text: &text,
        language_variant: nodes[file].as_source_file().language_variant,
    };
    let mut last_node_pos = nodes[containing_node].pos();
    let mut scan = nav_scanner(&ctx, last_node_pos);

    // `ForEachChildAndJSDoc` — JSDoc children first, then `ForEachChild`'s
    // flattened child walk. The children are collected up front because the
    // visitor body below mutates the arena (`get_or_create_token`).
    let mut children: Vec<NodeId> = ast::js_doc(nodes, containing_node, Some(file));
    nodes[containing_node].for_each_child(nodes, &mut |child| {
        children.push(child);
        false
    });

    let mut found_child: Option<NodeId> = None;
    'visit: for node in children {
        if nodes[node].flags.intersects(NodeFlags::REPARSED) {
            continue;
        }
        // Look for child in preceding tokens.
        let mut start_pos = last_node_pos;
        while start_pos < nodes[node].pos() {
            let token_kind = scan.token();
            let token_end = scan.token_end() as TextPos;
            if token_kind == kind {
                let token_full_start = scan.token_full_start() as TextPos;
                let flags = scan.token_flags();
                found_child = Some(ast::get_or_create_token(
                    nodes,
                    file,
                    token_kind,
                    token_full_start,
                    token_end,
                    containing_node,
                    flags,
                ));
                break 'visit;
            }
            start_pos = token_end;
            scan.scan();
        }

        if nodes[node].kind == kind {
            found_child = Some(node);
            break;
        }

        last_node_pos = nodes[node].end();
        scan.reset_pos(to_scanner_pos(last_node_pos));
    }

    if let Some(found) = found_child {
        return Some(found);
    }

    // Look for child in trailing tokens.
    let mut start_pos = last_node_pos;
    while start_pos < nodes[containing_node].end() {
        let token_kind = scan.token();
        let token_end = scan.token_end() as TextPos;
        if token_kind == kind {
            let token_full_start = scan.token_full_start() as TextPos;
            let flags = scan.token_flags();
            return Some(ast::get_or_create_token(
                nodes,
                file,
                token_kind,
                token_full_start,
                token_end,
                containing_node,
                flags,
            ));
        }
        start_pos = token_end;
        scan.scan();
    }
    None
}
