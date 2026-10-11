// Ported from tsc/internal/ls/jsdoc.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
//
// - `*ast.Symbol`/`*ast.Node` are `SymbolId`/`NodeId`. Symbol fields are read
//   via `c.symbol_arena.borrow()`; node fields via `program.arena_of(id)`
//   snapshots because a declaration may live in another file's arena.
// - `node.JSDoc(nil)` → `ast::js_doc(&mut nodes, node, file)`, which can
//   trigger lazy JSDoc parsing and therefore needs a mutable arena guard
//   (`program.nodes_mut`). Guards are scoped so they never overlap a checker
//   call, which may itself read arenas.
// - `GetSymbolJSDocTags` returns `Option<Vec<JSDocTagInfo>>` to preserve Go's
//   nil slice (`None`) when the symbol is nil or yields no tags.

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::{self as ast, Kind, Node, NodeFlags, NodeId, SymbolId};
use tsc_checker::checker_core::Checker;
use tsc_collections::Set;
use tsc_compiler::program::Program;
use tsc_lsproto as lsproto;
use tsc_scanner::utilities::{get_text_of_jsdoc_comment, get_text_of_node};

/// `JSDocTagInfo` mirrors Strada's `JSDocTagInfo`, but renders the tag's text
/// as a plain string instead of `SymbolDisplayPart[]`.
pub struct JSDocTagInfo {
    /// `Name`.
    pub name: String,
    /// `Text`.
    pub text: String,
}

/// `GetSymbolDocumentationComment` renders a symbol's documentation comment
/// as plain text. It backs the API's Symbol.getDocumentationComment and
/// mirrors Strada's getJsDocCommentsFromDeclarations: comments are gathered
/// from each unique declaration, deduplicated, and joined with line breaks.
/// Like Strada, it does not resolve aliases — consumers resolve aliases
/// themselves (via getAliasedSymbol) and re-query if desired.
pub fn get_symbol_documentation_comment(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    symbol: Option<SymbolId>,
) -> String {
    let Some(symbol) = symbol else {
        return String::new();
    };
    let declarations = {
        let arena = c.borrow().symbol_arena.clone();
        arena.borrow()[symbol.index()].declarations.clone()
    };
    let mut parts: Vec<String> = Vec::new();
    let mut seen: Set<NodeId> = Set::new();
    for decl in declarations {
        if !seen.add_if_absent(decl) {
            continue;
        }
        let doc = crate::hover::get_documentation_from_declaration(
            &crate::hover::no_mapped_location,
            program,
            c,
            Some(symbol),
            Some(decl),
            decl,
            lsproto::MarkupKind::PlainText,
            true, /*commentOnly*/
        );
        if !doc.is_empty() && !parts.contains(&doc) {
            parts.push(doc);
        }
    }
    parts.join("\n")
}

/// `GetSymbolJSDocTags` collects a symbol's JSDoc tags. It backs the API's
/// Symbol.getJsDocTags and mirrors Strada's getJsDocTagsFromDeclarations,
/// except each tag's text is rendered as a plain string rather than
/// SymbolDisplayPart[]. Tags with no text have an empty `text` field.
///
/// Returns `None` when `symbol` is `None` or produces no tags (Go nil slice).
pub fn get_symbol_js_doc_tags(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    symbol: Option<SymbolId>,
) -> Option<Vec<JSDocTagInfo>> {
    let symbol = symbol?;
    let declarations = {
        let arena = c.borrow().symbol_arena.clone();
        arena.borrow()[symbol.index()].declarations.clone()
    };
    let mut infos: Vec<JSDocTagInfo> = Vec::new();
    let mut seen: Set<NodeId> = Set::new();
    for decl in declarations {
        if !seen.add_if_absent(decl) {
            continue;
        }
        let tags = declaration_js_doc_tags(program, decl);
        // Skip comments containing @typedef/@callback since they're not associated with a
        // particular declaration, unless they also carry @param/@return (treated as local docs).
        let has_typedef = tags.iter().copied().any(|t| {
            let kind = program.arena_of(t)[t].kind;
            kind == Kind::JSDocTypedefTag || kind == Kind::JSDocCallbackTag
        });
        let has_param_or_return = tags.iter().copied().any(|t| {
            let kind = program.arena_of(t)[t].kind;
            kind == Kind::JSDocParameterTag || kind == Kind::JSDocReturnTag
        });
        if has_typedef && !has_param_or_return {
            continue;
        }
        for tag in tags {
            let nodes = program.arena_of(tag);
            let name = nodes[tag]
                .tag_name()
                .map(|n| nodes[n].text(&nodes).into_owned())
                .unwrap_or_default();
            let text = get_js_doc_tag_text(&nodes, tag);
            infos.push(JSDocTagInfo { name, text });
        }
    }
    if infos.is_empty() {
        None
    } else {
        Some(infos)
    }
}

/// `declarationJSDocTags` returns the JSDoc tags associated with a
/// declaration, walking the JSDoc comment location chain like the checker's
/// getAllJSDocTags.
fn declaration_js_doc_tags(program: &Rc<Program>, node: NodeId) -> Vec<NodeId> {
    if program.arena_of(node)[node].flags.intersects(NodeFlags::JSDOC) {
        return Vec::new();
    }
    let mut nodes = program.nodes_mut(node.file_index());
    let file = ast::get_source_file_of_node(Some(node), &nodes);
    let mut current = Some(node);
    while let Some(cur) = current {
        let jsdocs = ast::js_doc(&mut nodes, cur, file);
        if !jsdocs.is_empty() {
            let last_jsdoc = *jsdocs.last().expect("last jsdoc");
            if let Some(tags) = nodes[last_jsdoc].as_js_doc().tags.as_ref() {
                return tags.nodes().to_vec();
            }
        }
        current = ast::get_next_js_doc_comment_location(cur, &nodes);
    }
    Vec::new()
}

/// `getJSDocTagText` renders the text of a single JSDoc tag as a plain string,
/// mirroring Strada's getCommentDisplayParts collapsed from
/// SymbolDisplayPart[] to a string.
fn get_js_doc_tag_text(nodes: &[Node], tag: NodeId) -> String {
    let comment = get_text_of_jsdoc_comment(nodes[tag].comment_list(), nodes);
    let add_comment = |s: String| -> String {
        if comment.is_empty() {
            s
        } else {
            format!("{} {}", s, comment)
        }
    };
    match nodes[tag].kind {
        Kind::JSDocThrowsTag => {
            if let Some(te) = nodes[tag].as_js_doc_throws_tag().type_expression {
                return add_comment(get_text_of_node(te, nodes));
            }
            comment
        }
        Kind::JSDocImplementsTag => {
            if let Some(class_name) = nodes[tag].as_js_doc_implements_tag().class_name {
                return add_comment(get_text_of_node(class_name, nodes));
            }
            comment
        }
        Kind::JSDocAugmentsTag => {
            if let Some(class_name) = nodes[tag].as_js_doc_augments_tag().class_name {
                return add_comment(get_text_of_node(class_name, nodes));
            }
            comment
        }
        Kind::JSDocTemplateTag => {
            let template_tag = nodes[tag].as_js_doc_template_tag();
            let mut b = String::new();
            if let Some(constraint) = template_tag.constraint {
                b.push_str(&get_text_of_node(constraint, nodes));
            }
            if let Some(type_parameters) = template_tag.type_parameters.as_ref() {
                for (i, &tp) in type_parameters.nodes.iter().enumerate() {
                    if i == 0 && !b.is_empty() {
                        b.push(' ');
                    }
                    if i != 0 {
                        b.push_str(", ");
                    }
                    b.push_str(&get_text_of_node(tp, nodes));
                }
            }
            if !comment.is_empty() {
                if !b.is_empty() {
                    b.push(' ');
                }
                b.push_str(&comment);
            }
            b
        }
        Kind::JSDocTypeTag => {
            if let Some(te) = nodes[tag].as_js_doc_type_tag().type_expression {
                return add_comment(get_text_of_node(te, nodes));
            }
            comment
        }
        Kind::JSDocSatisfiesTag => {
            if let Some(te) = nodes[tag].as_js_doc_satisfies_tag().type_expression {
                return add_comment(get_text_of_node(te, nodes));
            }
            comment
        }
        Kind::JSDocSeeTag => {
            if let Some(ne) = nodes[tag].as_js_doc_see_tag().name_expression {
                return add_comment(get_text_of_node(ne, nodes));
            }
            comment
        }
        Kind::JSDocParameterTag | Kind::JSDocPropertyTag => {
            if let Some(name) = nodes[tag].name() {
                return add_comment(get_text_of_node(name, nodes));
            }
            comment
        }
        _ => comment,
    }
}

/// `getJSDoc` — the last JSDoc node attached to `node` (`core.LastOrNil(node.JSDoc(nil))`).
fn get_jsdoc(program: &Rc<Program>, node: NodeId) -> Option<NodeId> {
    let mut nodes = program.nodes_mut(node.file_index());
    ast::js_doc(&mut nodes, node, None).last().copied()
}

/// `getJSDocOrTag` — looks through declaration locations for a JSDoc node or
/// a matching JSDoc tag (parameter, type parameter, binding element,
/// inherited member docs). `seen_symbols` guards against cycles in the
/// class/interface inheritance walk.
pub(crate) fn get_jsdoc_or_tag(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    node: Option<NodeId>,
    seen_symbols: &mut Set<SymbolId>,
) -> Option<NodeId> {
    let node = node?;
    if let Some(jsdoc) = get_jsdoc(program, node) {
        return Some(jsdoc);
    }
    let nodes = program.arena_of(node);
    let parent = nodes[node].parent;
    if ast::is_parameter_declaration(&nodes[node]) {
        let name = nodes[node].name();
        if name.is_some_and(|n| ast::is_binding_pattern(&nodes[n])) {
            // For binding patterns, match JSDoc @param tags by position rather than by name
            drop(nodes);
            return get_jsdoc_parameter_tag_by_position(program, c, node);
        }
        let text = name
            .map(|n| nodes[n].text(&nodes).into_owned())
            .unwrap_or_default();
        drop(nodes);
        return get_matching_jsdoc_tag(
            program,
            c,
            parent,
            &text,
            is_matching_parameter_tag,
            seen_symbols,
        );
    }
    if ast::is_type_parameter_declaration(&nodes[node]) {
        let text = nodes[node]
            .name()
            .map(|n| nodes[n].text(&nodes).into_owned())
            .unwrap_or_default();
        drop(nodes);
        return get_matching_jsdoc_tag(
            program,
            c,
            parent,
            &text,
            is_matching_template_tag,
            seen_symbols,
        );
    }
    if ast::is_variable_declaration(&nodes[node])
        && parent.is_some_and(|p| {
            ast::is_variable_declaration_list(&nodes[p])
                && nodes[p]
                    .as_variable_declaration_list()
                    .declarations
                    .as_ref()
                    .and_then(|d| d.nodes().first().copied())
                    == Some(node)
        })
    {
        let grandparent = parent.and_then(|p| nodes[p].parent);
        drop(nodes);
        return get_jsdoc_or_tag(program, c, grandparent, seen_symbols);
    }
    if (ast::is_function_expression_or_arrow_function(&nodes[node])
        || ast::is_class_expression(&nodes[node]))
        && parent.is_some_and(|p| {
            ast::is_variable_declaration(&nodes[p])
                || ast::is_property_declaration(&nodes[p])
                || ast::is_property_assignment(&nodes[p])
        })
        && parent.is_some_and(|p| nodes[p].initializer() == Some(node))
    {
        drop(nodes);
        return get_jsdoc_or_tag(program, c, parent, seen_symbols);
    }
    if ast::is_binding_element(&nodes[node])
        && parent.is_some_and(|p| ast::is_object_binding_pattern(&nodes[p]))
    {
        if let Some(name) = nodes[node].property_name_or_name() {
            if ast::is_identifier(&nodes[name]) {
                let text = nodes[name].text(&nodes).into_owned();
                let object_pattern = parent.expect("object binding pattern");
                drop(nodes);
                let object_type = c.borrow_mut().get_type_at_location(object_pattern);
                if let Some(prop) = c.borrow_mut().get_property_of_type(object_type, &text) {
                    let prop_declarations = {
                        let arena = c.borrow().symbol_arena.clone();
                        arena.borrow()[prop.index()].declarations.clone()
                    };
                    for d in prop_declarations {
                        if let Some(jsdoc) = get_jsdoc(program, d) {
                            return Some(jsdoc);
                        }
                    }
                }
            }
        }
    }
    let nodes = program.arena_of(node);
    let symbol = nodes[node].symbol();
    // PORT: `nodes` is an immutable `Rc<Vec<Node>>` snapshot — holding it
    // across checker calls is safe (only `nodes_mut` guards conflict).
    if let (Some(symbol), Some(parent)) = (symbol, nodes[node].parent) {
        if ast::is_function_declaration(&nodes[node])
            || ast::is_method_declaration(&nodes[node])
            || ast::is_method_signature_declaration(&nodes[node])
            || ast::is_constructor_declaration(&nodes[node])
            || ast::is_construct_signature_declaration(&nodes[node])
        {
            let first_signature = {
                let arena = c.borrow().symbol_arena.clone();
                arena.borrow()[symbol.index()]
                    .declarations
                    .iter()
                    .copied()
                    .find(|&d| {
                        let dnodes = program.arena_of(d);
                        ast::is_function_like(Some(d), &dnodes)
                    })
            };
            if let Some(first_signature) = first_signature {
                if node != first_signature {
                    if let Some(jsdoc) =
                        get_jsdoc_or_tag(program, c, Some(first_signature), seen_symbols)
                    {
                        return Some(jsdoc);
                    }
                }
            }
        }
        if ast::is_class_or_interface_like(Some(parent), &nodes) {
            let is_static = ast::has_static_modifier(&nodes[node]);
            let symbol_name = {
                let arena = c.borrow().symbol_arena.clone();
                arena.borrow()[symbol.index()].name.clone()
            };
            if let Some(parent_symbol) = nodes[parent].symbol() {
                let class_type = c.borrow_mut().get_declared_type_of_symbol(parent_symbol);
                if is_static {
                    // For static members, use the checker's base constructor type resolution.
                    // This correctly handles intersection constructor types from mixins
                    // (e.g., typeof MixinClass & T) by preserving the full intersection.
                    let base_ctor =
                        c.borrow_mut().get_base_constructor_type_of_class(class_type);
                    let static_base_type = c.borrow_mut().get_apparent_type(base_ctor);
                    let prop =
                        c.borrow_mut().get_property_of_type(static_base_type, &symbol_name);
                    if let Some(jsdoc) = jsdoc_from_base_prop(
                        program, c, prop, seen_symbols,
                    ) {
                        return Some(jsdoc);
                    }
                } else {
                    for base_type in c.borrow_mut().get_base_types(class_type) {
                        let prop = c.borrow_mut().get_property_of_type(base_type, &symbol_name);
                        if let Some(jsdoc) = jsdoc_from_base_prop(
                            program, c, prop, seen_symbols,
                        ) {
                            return Some(jsdoc);
                        }
                    }
                }
            }
        }
    }
    None
}

/// The `prop != nil && prop.ValueDeclaration != nil &&
/// seenSymbols.AddIfAbsent(prop)` body shared by the static/instance base
/// walks of `getJSDocOrTag`.
fn jsdoc_from_base_prop(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    prop: Option<SymbolId>,
    seen_symbols: &mut Set<SymbolId>,
) -> Option<NodeId> {
    let prop = prop?;
    let value_declaration = {
        let arena = c.borrow().symbol_arena.clone();
        arena.borrow()[prop.index()].value_declaration
    }?;
    if !seen_symbols.add_if_absent(prop) {
        return None;
    }
    get_jsdoc_or_tag(program, c, Some(value_declaration), seen_symbols)
}

/// `getMatchingJSDocTag`.
fn get_matching_jsdoc_tag(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    node: Option<NodeId>,
    name: &str,
    match_fn: fn(&[Node], NodeId, &str) -> bool,
    seen_symbols: &mut Set<SymbolId>,
) -> Option<NodeId> {
    let jsdoc = get_jsdoc_or_tag(program, c, node, seen_symbols)?;
    let nodes = program.arena_of(jsdoc);
    if nodes[jsdoc].kind == Kind::JSDoc {
        if let Some(tags) = nodes[jsdoc].as_js_doc().tags.as_ref() {
            for &tag in &tags.nodes {
                if match_fn(&nodes, tag, name) {
                    return Some(tag);
                }
            }
        }
    }
    None
}

/// `getJSDocParameterTagByPosition` finds a JSDoc @param tag for a binding
/// pattern parameter by position. Since binding patterns don't have a simple
/// name, we match the @param tag at the same index as the parameter.
fn get_jsdoc_parameter_tag_by_position(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    param: NodeId,
) -> Option<NodeId> {
    let (parent, param_index) = {
        let nodes = program.arena_of(param);
        let parent = nodes[param].parent?;
        // Find the parameter's index in the parent's parameters list
        let param_index = nodes[parent]
            .parameters()
            .and_then(|params| params.iter().position(|&p| p == param))?;
        (parent, param_index)
    };

    // Get the JSDoc for the parent function/method
    let jsdoc = get_jsdoc_or_tag(program, c, Some(parent), &mut Set::new())?;
    let nodes = program.arena_of(jsdoc);
    if nodes[jsdoc].kind != Kind::JSDoc {
        return None;
    }

    // Collect all @param tags in order
    let tags = nodes[jsdoc].as_js_doc().tags.as_ref()?;
    let mut param_tag_index = 0;
    for &tag in &tags.nodes {
        if nodes[tag].kind == Kind::JSDocParameterTag {
            if param_tag_index == param_index {
                return Some(tag);
            }
            param_tag_index += 1;
        }
    }
    None
}

/// `isMatchingParameterTag`.
fn is_matching_parameter_tag(nodes: &[Node], tag: NodeId, name: &str) -> bool {
    nodes[tag].kind == Kind::JSDocParameterTag && is_node_with_name(nodes, tag, name)
}

/// `isMatchingTemplateTag`.
fn is_matching_template_tag(nodes: &[Node], tag: NodeId, name: &str) -> bool {
    nodes[tag].kind == Kind::JSDocTemplateTag
        && nodes[tag]
            .type_parameters()
            .is_some_and(|tps| tps.iter().any(|&tp| is_node_with_name(nodes, tp, name)))
}

/// `isNodeWithName`.
fn is_node_with_name(nodes: &[Node], node: NodeId, name: &str) -> bool {
    let Some(node_name) = nodes[node].name() else {
        return false;
    };
    ast::is_identifier(&nodes[node_name]) && nodes[node_name].text(nodes) == name
}
