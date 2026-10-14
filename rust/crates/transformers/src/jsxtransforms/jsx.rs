// Ported from tsc/internal/transformers/jsxtransforms/jsx.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `JSXTransformer` — lowers JSX elements/fragments to `createElement` (classic
// runtime) or `jsx`/`jsxs`/`jsxDEV` calls (automatic runtime), including the
// implicit-runtime import bookkeeping, development `__source`/`__self`
// arguments, spread-attribute object merging, JSX child whitespace fixups and
// HTML entity decoding.
//
// PORT notes:
//   - The Go `JSXTransformer` struct embeds `transformers.Transformer` so its
//     methods can reach `tx.Visitor()`/`tx.Factory()`/`tx.EmitContext()`. Here
//     the transformer state lives in a struct with interior-mutable fields
//     owned by the single visit closure; the running visitor arrives as the
//     callback's first parameter, `tx.Factory()` maps to `self.factory()`
//     (a `RefMut` into the emit-context factory — the borrow ends with each
//     statement), and `tx.EmitContext()` maps to `self.ec.borrow()`.
//   - `*ast.Node` → `NodeId`, `*ast.JsxChild` → `NodeId`, `*ast.NodeList` →
//     `Option<NodeList>`, `[]*ast.Node` → `Vec<NodeId>`,
//     `collections.OrderedMap[string, map[string]*ast.Node]` →
//     `OrderedMap<String, HashMap<String, NodeId>>`, `map[string]*ast.Node`
//     → `HashMap<String, NodeId>` (iterations are always sorted before use).
//   - `decodeEntities` builds WTF-8/CESU-8 bytes so surrogate entities keep
//     their `encode_js_string_rune` sentinels; the `String` boundary uses
//     `String::from_utf8_lossy`, matching the scanner's convention
//     (`scanner.rs` `token_value` decoding).
//   - Go's `printer.EmitResolver` interface embeds the reference resolver;
//     in Rust `EmitResolver`/`ReferenceResolver` are separate traits, so
//     `create_react_namespace` reads `opts.resolver` + `opts.symbols`
//     (PORT: when either is absent the namespace-substitution lookup is
//     skipped — equivalent to the lookup finding no export container;
//     Go would nil-panic on a nil resolver anyway).
//   - Go's generic `insertStatementAfterPrologue` is instantiated exactly
//     once (with `isAnyPrologueDirective`); it is monomorphic here.

use std::cell::{Cell, RefCell, RefMut};
use std::collections::HashMap;
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeId, NodeList, SymbolArena};
use tsc_binder::referenceresolver::ReferenceResolver;
use tsc_collections::OrderedMap;
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::options_generated::{CompilerOptions, JsxEmit, ScriptTarget};
use tsc_core::text::TextRange;
use tsc_printer::{
    AutoGenerateOptions, EmitFlags, EmitResolver, GeneratedIdentifierFlags, NodeFactory,
};
use tsc_scanner::scanner::{get_ecma_line_and_utf16_character_of_position, skip_trivia};
use tsc_scanner::utilities::{is_identifier_text, is_intrinsic_jsx_name};
use tsc_stringutil as stringutil;
use tsc_stringutil::COMPARISON_EQUAL;

use crate::chain::TransformOptions;
use crate::estransforms::{Ec, make_transformer, visit as raw_visit, visit_each_child};
use crate::transformer::Transformer;

/// `type JSXTransformer struct`.
pub struct JsxTransformer<'a> {
    compiler_options: &'a CompilerOptions,
    emit_resolver: Rc<RefCell<dyn EmitResolver + 'a>>,
    /// `opts.Resolver`/`opts.Symbols` — needed by `get_referenced_export_container`
    /// (PORT: Go's emit-resolver interface embeds the reference resolver;
    /// see header note).
    resolver: Option<Rc<RefCell<dyn ReferenceResolver + 'a>>>,
    symbols: Option<&'a SymbolArena>,
    ec: Ec,

    import_specifier: RefCell<String>,
    filename_declaration: Cell<Option<NodeId>>,
    utilized_implicit_runtime_imports: RefCell<OrderedMap<String, HashMap<String, NodeId>>>,
    in_jsx_child: Cell<bool>,

    current_source_file: Cell<Option<NodeId>>,
}

/// `NewJSXTransformer`.
pub fn new_jsx_transformer<'a>(opts: &TransformOptions<'a>) -> Option<Transformer<'a>> {
    let compiler_options = opts
        .compiler_options
        .expect("jsxTransformer requires compiler options");
    let emit_resolver = opts
        .emit_resolver
        .clone()
        .expect("jsxTransformer requires an emit resolver");
    let resolver = opts.resolver.clone();
    let symbols = opts.symbols;
    make_transformer(opts, move |ec| {
        let tx = JsxTransformer {
            compiler_options,
            emit_resolver,
            resolver,
            symbols,
            ec,
            import_specifier: RefCell::new(String::new()),
            filename_declaration: Cell::new(None),
            utilized_implicit_runtime_imports: RefCell::new(OrderedMap::new()),
            in_jsx_child: Cell::new(false),
            current_source_file: Cell::new(None),
        };
        Box::new(move |v, cx, node| tx.visit(v, cx, node))
    })
}

impl<'a> JsxTransformer<'a> {
    /// `tx.Factory()` — a `RefMut` into the emit-context factory; the borrow
    /// lasts one statement (never across a `v.visit_*` call).
    #[inline]
    fn factory(&self) -> RefMut<'_, NodeFactory> {
        RefMut::map(self.ec.borrow_mut(), |ec| &mut ec.factory)
    }

    /// `getCurrentFileNameExpression`.
    fn get_current_file_name_expression(&self, cx: &mut VisitorCx<'_, '_>) -> NodeId {
        if let Some(d) = self.filename_declaration.get() {
            return cx.nodes[d].as_variable_declaration().name.unwrap();
        }
        let name = self.factory().new_unique_name_ex(
            cx.nodes,
            "_jsxFileName",
            &AutoGenerateOptions {
                flags: GeneratedIdentifierFlags::OPTIMISTIC | GeneratedIdentifierFlags::FILE_LEVEL,
                ..Default::default()
            },
        );
        let initializer = {
            let file_name = cx.nodes[self.current_source_file.get().unwrap()]
                .as_source_file()
                .file_name()
                .as_string()
                .to_string();
            self.factory()
                .new_string_literal(cx.nodes, &file_name, ast::TokenFlags::NONE)
        };
        let d = self.factory().new_variable_declaration(
            cx.nodes,
            Some(name),
            None,
            None,
            Some(initializer),
        );
        self.filename_declaration.set(Some(d));
        cx.nodes[d].as_variable_declaration().name.unwrap()
    }

    /// `getJsxFactoryCalleePrimitive`.
    fn get_jsx_factory_callee_primitive(&self, is_static_children: bool) -> &'static str {
        if self.compiler_options.jsx == JsxEmit::ReactJSXDev {
            return "jsxDEV";
        }
        if is_static_children {
            return "jsxs";
        }
        "jsx"
    }

    /// `getJsxFactoryCallee`.
    fn get_jsx_factory_callee(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        is_static_children: bool,
    ) -> NodeId {
        let t = self.get_jsx_factory_callee_primitive(is_static_children);
        self.get_implicit_import_for_name(cx, t)
    }

    /// `getImplicitJsxFragmentReference`.
    fn get_implicit_jsx_fragment_reference(&self, cx: &mut VisitorCx<'_, '_>) -> NodeId {
        self.get_implicit_import_for_name(cx, "Fragment")
    }

    /// `getImplicitImportForName`.
    fn get_implicit_import_for_name(&self, cx: &mut VisitorCx<'_, '_>, name: &str) -> NodeId {
        let mut import_source = self.import_specifier.borrow().clone();
        if name != "createElement" {
            import_source = ast::get_jsx_runtime_import(&import_source, self.compiler_options);
        }
        {
            let utilized = self.utilized_implicit_runtime_imports.borrow();
            if let Some(existing) = utilized.get(&import_source)
                && let Some(elem) = existing.get(name)
            {
                return cx.nodes[*elem].as_import_specifier().name.unwrap();
            }
        }

        let generated_name = self.factory().new_unique_name_ex(
            cx.nodes,
            &format!("_{}", name),
            &AutoGenerateOptions {
                flags: GeneratedIdentifierFlags::OPTIMISTIC
                    | GeneratedIdentifierFlags::FILE_LEVEL
                    | GeneratedIdentifierFlags::ALLOW_NAME_SUBSTITUTION,
                ..Default::default()
            },
        );
        let property_name = self.factory().new_identifier(cx.nodes, name);
        let specifier = self.factory().new_import_specifier(
            cx.nodes,
            false,
            Some(property_name),
            Some(generated_name),
        );
        self.emit_resolver
            .borrow_mut()
            .set_referenced_import_declaration(generated_name, Some(specifier), cx.nodes);
        // `getOrInsert(importSource, map[string]*ast.Node{})` — insertion
        // order is preserved by OrderedMap either way, so inserting the key
        // after creating the specifier is equivalent.
        {
            let mut utilized = self.utilized_implicit_runtime_imports.borrow_mut();
            if let Some(existing) = utilized.get_mut(&import_source) {
                existing.insert(name.to_string(), specifier);
            } else {
                let mut m = HashMap::new();
                m.insert(name.to_string(), specifier);
                utilized.set(import_source, m);
            }
        }
        cx.nodes[specifier].name().unwrap()
    }

    /// `setInChild`.
    fn set_in_child(&self, v: bool) {
        self.in_jsx_child.set(v);
    }

    /// `(tx *JSXTransformer) visit`.
    fn visit(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if !cx.nodes[node]
            .subtree_facts(cx.nodes)
            .intersects(ast::SubtreeFacts::CONTAINS_JSX)
        {
            return Some(node);
        }
        match cx.nodes[node].kind {
            Kind::SourceFile => {
                self.set_in_child(false);
                self.visit_source_file(v, cx, node)
            }
            Kind::JsxElement => self.visit_jsx_element(v, cx, node),
            Kind::JsxSelfClosingElement => self.visit_jsx_self_closing_element(v, cx, node),
            Kind::JsxFragment => self.visit_jsx_fragment(v, cx, node),
            Kind::JsxOpeningElement => {
                panic!("JsxOpeningElement should not be visited, handled in visitJsxElement")
            }
            Kind::JsxOpeningFragment => {
                panic!("JsxOpeningFragment should not be visited, handled in visitJsxFragment")
            }
            Kind::JsxText => {
                self.set_in_child(false);
                self.visit_jsx_text(cx, node)
            }
            Kind::JsxExpression => {
                self.set_in_child(false);
                self.visit_jsx_expression(v, cx, node)
            }
            _ => {
                self.set_in_child(false);
                Some(visit_each_child(v, cx, node)) // by default, do nothing
            }
        }
    }

    /// `shouldUseCreateElement`.
    fn should_use_create_element(&self, nodes: &[ast::Node], node: NodeId) -> bool {
        self.import_specifier.borrow().is_empty() || has_key_after_props_spread(nodes, node)
    }

    /// `isAnyPrologueDirective`.
    fn is_any_prologue_directive(&self, nodes: &[ast::Node], node: NodeId) -> bool {
        ast::is_prologue_directive(&nodes[node], nodes)
            || self
                .ec
                .borrow()
                .emit_flags(node)
                .has(EmitFlags::CUSTOM_PROLOGUE)
    }

    /// `insertStatementAfterCustomPrologue` — the sole instantiation of Go's
    /// generic `insertStatementAfterPrologue` (see header note).
    fn insert_statement_after_custom_prologue(
        &self,
        nodes: &[ast::Node],
        mut to: Vec<NodeId>,
        statement: NodeId,
    ) -> Vec<NodeId> {
        let mut statement_idx = 0;
        // skip all prologue directives to insert at the correct position
        while statement_idx < to.len() {
            if !self.is_any_prologue_directive(nodes, to[statement_idx]) {
                break;
            }
            statement_idx += 1;
        }
        to.insert(statement_idx, statement);
        to
    }

    /// `visitSourceFile`.
    fn visit_source_file(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if cx.nodes[node].as_source_file().is_declaration_file {
            return Some(node);
        }

        self.current_source_file.set(Some(node));
        *self.import_specifier.borrow_mut() = ast::get_jsx_implicit_import_base(
            self.compiler_options,
            Some(cx.nodes[node].as_source_file()),
        );
        self.filename_declaration.set(None);
        self.utilized_implicit_runtime_imports.borrow_mut().clear();

        let mut visited = visit_each_child(v, cx, node);
        let helpers = self.ec.borrow_mut().read_emit_helpers();
        self.ec.borrow().add_emit_helper(visited, &helpers[..]);
        let mut statements: Vec<NodeId> = cx.nodes[visited]
            .statements()
            .map(<[_]>::to_vec)
            .unwrap_or_default();
        let mut statements_updated = false;
        if let Some(filename_declaration) = self.filename_declaration.get() {
            let declaration_list = self.factory().new_node_list(vec![filename_declaration]);
            let decl_list = self.factory().new_variable_declaration_list(
                cx.nodes,
                Some(declaration_list),
                ast::NodeFlags::CONST,
            );
            let stmt = self
                .factory()
                .new_variable_statement(cx.nodes, None, Some(decl_list));
            statements = self.insert_statement_after_custom_prologue(cx.nodes, statements, stmt);
            statements_updated = true;
        }

        if self.utilized_implicit_runtime_imports.borrow().size() > 0 {
            if ast::is_external_module(cx.nodes[node].as_source_file()) {
                statements_updated = true;
                let mut new_statements =
                    Vec::with_capacity(self.utilized_implicit_runtime_imports.borrow().size());
                let imports = self.utilized_implicit_runtime_imports.borrow();
                for (import_source, import_specifiers_map) in imports.entries() {
                    let specifiers = get_sorted_specifiers(cx.nodes, import_specifiers_map);
                    let elements = self.factory().new_node_list(specifiers);
                    let named_imports = self.factory().new_named_imports(cx.nodes, Some(elements));
                    let clause = self.factory().new_import_clause(
                        cx.nodes,
                        Kind::Unknown,
                        None,
                        Some(named_imports),
                    );
                    let module_specifier = self.factory().new_string_literal(
                        cx.nodes,
                        import_source,
                        ast::TokenFlags::NONE,
                    );
                    let s = self.factory().new_import_declaration(
                        cx.nodes,
                        None,
                        Some(clause),
                        Some(module_specifier),
                        None,
                    );
                    ast::set_parent_in_children(cx.nodes, s);
                    new_statements.push(s);
                }
                drop(imports);
                for e in new_statements {
                    statements =
                        self.insert_statement_after_custom_prologue(cx.nodes, statements, e);
                }
            } else if ast::is_external_or_commonjs_module(cx.nodes[node].as_source_file()) {
                statements_updated = true;
                let mut new_statements =
                    Vec::with_capacity(self.utilized_implicit_runtime_imports.borrow().size());
                let imports = self.utilized_implicit_runtime_imports.borrow();
                for (import_source, import_specifiers_map) in imports.entries() {
                    let sorted = get_sorted_specifiers(cx.nodes, import_specifiers_map);
                    let mut as_binding_elems = Vec::with_capacity(sorted.len());
                    for elem in sorted {
                        let property_name = cx.nodes[elem].property_name();
                        let name = cx.nodes[elem].as_import_specifier().name;
                        as_binding_elems.push(self.factory().new_binding_element(
                            cx.nodes,
                            None,
                            property_name,
                            name,
                            None,
                        ));
                    }
                    let elements = self.factory().new_node_list(as_binding_elems);
                    let pattern = self.factory().new_binding_pattern(
                        cx.nodes,
                        Kind::ObjectBindingPattern,
                        Some(elements),
                    );
                    let arg_literal = self.factory().new_string_literal(
                        cx.nodes,
                        import_source,
                        ast::TokenFlags::NONE,
                    );
                    let args = self.factory().new_node_list(vec![arg_literal]);
                    let require = self.factory().new_identifier(cx.nodes, "require");
                    let call = self.factory().new_call_expression(
                        cx.nodes,
                        Some(require),
                        None,
                        None,
                        Some(args),
                        ast::NodeFlags::NONE,
                    );
                    let declaration = self.factory().new_variable_declaration(
                        cx.nodes,
                        Some(pattern),
                        None,
                        None,
                        Some(call),
                    );
                    let declarations = self.factory().new_node_list(vec![declaration]);
                    let decl_list = self.factory().new_variable_declaration_list(
                        cx.nodes,
                        Some(declarations),
                        ast::NodeFlags::CONST,
                    );
                    let s = self
                        .factory()
                        .new_variable_statement(cx.nodes, None, Some(decl_list));
                    ast::set_parent_in_children(cx.nodes, s);
                    new_statements.push(s);
                }
                drop(imports);
                for e in new_statements {
                    statements =
                        self.insert_statement_after_custom_prologue(cx.nodes, statements, e);
                }
            } else {
                // Do nothing (script file) - consider an error in the checker?
            }
        }

        if statements_updated {
            let statements_list = self.factory().new_node_list(statements);
            visited = self
                .factory()
                .update_source_file(
                    cx.nodes,
                    node,
                    Some(statements_list),
                    cx.nodes[node].as_source_file().end_of_file_token,
                )
                .unwrap_or(node);
        }

        self.current_source_file.set(None);
        *self.import_specifier.borrow_mut() = String::new();
        self.filename_declaration.set(None);
        self.utilized_implicit_runtime_imports.borrow_mut().clear();

        Some(visited)
    }

    /// `visitJsxElement`.
    fn visit_jsx_element(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let use_create_element = self.should_use_create_element(cx.nodes, node);
        let (opening_element, children) = {
            let d = cx.nodes[node].as_jsx_element();
            (d.opening_element.unwrap(), d.children.clone())
        };
        let location = TextRange::new(
            skip_trivia(
                &cx.nodes[self.current_source_file.get().unwrap()]
                    .as_source_file()
                    .text,
                cx.nodes[node].pos(),
            ),
            cx.nodes[node].end(),
        );
        if use_create_element {
            self.visit_jsx_opening_like_element_create_element(
                v,
                cx,
                opening_element,
                children,
                location,
            )
        } else {
            self.visit_jsx_opening_like_element_jsx(v, cx, opening_element, children, location)
        }
    }

    /// `visitJsxSelfClosingElement`.
    fn visit_jsx_self_closing_element(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let use_create_element = self.should_use_create_element(cx.nodes, node);
        let location = TextRange::new(
            skip_trivia(
                &cx.nodes[self.current_source_file.get().unwrap()]
                    .as_source_file()
                    .text,
                cx.nodes[node].pos(),
            ),
            cx.nodes[node].end(),
        );
        if use_create_element {
            self.visit_jsx_opening_like_element_create_element(v, cx, node, None, location)
        } else {
            self.visit_jsx_opening_like_element_jsx(v, cx, node, None, location)
        }
    }

    /// `visitJsxFragment`.
    fn visit_jsx_fragment(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let (opening_fragment, children) = {
            let d = cx.nodes[node].as_jsx_fragment();
            (d.opening_fragment.unwrap(), d.children.clone())
        };
        let location = TextRange::new(
            skip_trivia(
                &cx.nodes[self.current_source_file.get().unwrap()]
                    .as_source_file()
                    .text,
                cx.nodes[node].pos(),
            ),
            cx.nodes[node].end(),
        );
        if self.import_specifier.borrow().is_empty() {
            self.visit_jsx_opening_fragment_create_element(
                v,
                cx,
                opening_fragment,
                children,
                location,
            )
        } else {
            self.visit_jsx_opening_fragment_jsx(v, cx, opening_fragment, children, location)
        }
    }

    /// `convertJsxChildrenToChildrenPropObject`.
    fn convert_jsx_children_to_children_prop_object(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        children: &[NodeId],
    ) -> Option<NodeId> {
        let prop = self.convert_jsx_children_to_children_prop_assignment(v, cx, children)?;
        let members = self.factory().new_node_list(vec![prop]);
        Some(
            self.factory()
                .new_object_literal_expression(cx.nodes, Some(members), false),
        )
    }

    /// `transformJsxChildToExpression`.
    fn transform_jsx_child_to_expression(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let prev = self.in_jsx_child.get();
        self.set_in_child(true);
        let result = raw_visit(v, cx, node);
        self.set_in_child(prev);
        result
    }

    /// `convertJsxChildrenToChildrenPropAssignment`.
    fn convert_jsx_children_to_children_prop_assignment(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        children: &[NodeId],
    ) -> Option<NodeId> {
        let non_whitespace_children = ast::get_semantic_jsx_children(children, cx.nodes);
        if non_whitespace_children.len() == 1
            && (cx.nodes[non_whitespace_children[0]].kind != Kind::JsxExpression
                || cx.nodes[non_whitespace_children[0]]
                    .as_jsx_expression()
                    .dot_dot_dot_token
                    .is_none())
        {
            let result =
                self.transform_jsx_child_to_expression(v, cx, non_whitespace_children[0])?;
            let name = self.factory().new_identifier(cx.nodes, "children");
            return Some(self.factory().new_property_assignment(
                cx.nodes,
                None,
                Some(name),
                None,
                None,
                Some(result),
            ));
        }
        // For multiple children in the children property array, don't set
        // StartOnNewLine on child elements — the array literal is single-line.
        let mut results = Vec::with_capacity(non_whitespace_children.len());
        for &child in &non_whitespace_children {
            let Some(res) = self.transform_jsx_child_to_expression(v, cx, child) else {
                continue;
            };
            let flags = self.ec.borrow().emit_flags(res);
            self.ec
                .borrow()
                .set_emit_flags(res, flags & !EmitFlags::START_ON_NEW_LINE);
            results.push(res);
        }
        if results.is_empty() {
            return None;
        }
        let elements = self.factory().new_node_list(results);
        let array = self
            .factory()
            .new_array_literal_expression(cx.nodes, Some(elements), false);
        let name = self.factory().new_identifier(cx.nodes, "children");
        Some(self.factory().new_property_assignment(
            cx.nodes,
            None,
            Some(name),
            None,
            None,
            Some(array),
        ))
    }

    /// `getTagName`.
    fn get_tag_name(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        match cx.nodes[node].kind {
            Kind::JsxElement => {
                let opening = cx.nodes[node].as_jsx_element().opening_element.unwrap();
                self.get_tag_name(cx, opening)
            }
            _ if ast::is_jsx_opening_like_element(&cx.nodes[node]) => {
                let tag_name = cx.nodes[node].tag_name().unwrap();
                if ast::is_identifier(&cx.nodes[tag_name])
                    && is_intrinsic_jsx_name(&cx.nodes[tag_name].text(cx.nodes))
                {
                    let text = cx.nodes[tag_name].text(cx.nodes).to_string();
                    self.factory()
                        .new_string_literal(cx.nodes, &text, ast::TokenFlags::NONE)
                } else if ast::is_jsx_namespaced_name(&cx.nodes[tag_name]) {
                    let text = {
                        let d = cx.nodes[tag_name].as_jsx_namespaced_name();
                        format!(
                            "{}:{}",
                            cx.nodes[d.namespace.unwrap()].text(cx.nodes),
                            cx.nodes[d.name.unwrap()].text(cx.nodes)
                        )
                    };
                    self.factory()
                        .new_string_literal(cx.nodes, &text, ast::TokenFlags::NONE)
                } else {
                    self.factory()
                        .create_expression_from_entity_name(cx.nodes, tag_name)
                }
            }
            _ => panic!(
                "unhandled node kind passed to getTagName: {}",
                cx.nodes[node].kind_string()
            ),
        }
    }

    /// `visitJsxOpeningLikeElementJSX`.
    fn visit_jsx_opening_like_element_jsx(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        element: NodeId,
        children: Option<NodeList>,
        location: TextRange,
    ) -> Option<NodeId> {
        let tag_name = self.get_tag_name(cx, element);
        let mut children_prop = None;
        if let Some(children) = &children
            && !children.nodes.is_empty()
        {
            children_prop =
                self.convert_jsx_children_to_children_prop_assignment(v, cx, &children.nodes);
        }
        let mut key_attr = None;
        let mut attrs: Vec<NodeId> = cx.nodes[cx.nodes[element].attributes().unwrap()]
            .properties()
            .unwrap_or(&[])
            .to_vec();
        for (i, &p) in attrs.iter().enumerate() {
            if cx.nodes[p].kind == Kind::JsxAttribute
                && let Some(name) = cx.nodes[p].name()
                && ast::is_identifier(&cx.nodes[name])
                && &*cx.nodes[name].text(cx.nodes) == "key"
            {
                key_attr = Some(p);
                attrs.remove(i);
                break;
            }
        }
        let object;
        if !attrs.is_empty() {
            object = self.transform_jsx_attributes_to_object_props(v, cx, &attrs, children_prop);
        } else {
            let mut object_children = Vec::new();
            if let Some(children_prop) = children_prop {
                object_children.push(children_prop);
            }
            let members = self.factory().new_node_list(object_children);
            object = self
                .factory()
                .new_object_literal_expression(cx.nodes, Some(members), false);
        }
        Some(self.visit_jsx_opening_like_element_or_fragment_jsx(
            v, cx, tag_name, object, key_attr, children, location,
        ))
    }

    /// `transformJsxAttributesToObjectProps`.
    fn transform_jsx_attributes_to_object_props(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        attrs: &[NodeId],
        children_prop: Option<NodeId>,
    ) -> NodeId {
        let target = self.compiler_options.get_emit_script_target();
        if target >= ScriptTarget::ES2018 {
            // target has object spreads, can keep as-is
            let props = self.transform_jsx_attributes_to_props(v, cx, attrs, children_prop);
            let members = self.factory().new_node_list(props);
            return self
                .factory()
                .new_object_literal_expression(cx.nodes, Some(members), false);
        }
        self.transform_jsx_attributes_to_expression(v, cx, attrs, children_prop)
    }

    /// `transformJsxAttributesToExpression`.
    fn transform_jsx_attributes_to_expression(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        attrs: &[NodeId],
        children_prop: Option<NodeId>,
    ) -> NodeId {
        let mut expressions: Vec<NodeId> = Vec::with_capacity(2);
        let mut properties: Vec<NodeId> = Vec::with_capacity(attrs.len());

        for &attr in attrs {
            if ast::is_jsx_spread_attribute(&cx.nodes[attr]) {
                // as an optimization we try to flatten the first level of
                // spread inline object as if its props would be passed as JSX
                // attributes
                let expression = cx.nodes[attr].expression().unwrap();
                if ast::is_object_literal_expression(&cx.nodes[expression])
                    && !has_proto(
                        cx.nodes[expression].as_object_literal_expression(),
                        cx.nodes,
                    )
                {
                    for &prop in cx.nodes[expression]
                        .properties()
                        .unwrap_or(&[])
                        .to_vec()
                        .iter()
                    {
                        if ast::is_spread_assignment(&cx.nodes[prop]) {
                            combine_properties_into_new_expression(
                                &mut self.factory(),
                                cx,
                                &mut expressions,
                                &mut properties,
                            );
                            let expr = cx.nodes[prop].expression().unwrap();
                            expressions.push(raw_visit(v, cx, expr).unwrap_or(expr));
                            continue;
                        }
                        properties.push(raw_visit(v, cx, prop).unwrap_or(prop));
                    }
                    continue;
                }
                combine_properties_into_new_expression(
                    &mut self.factory(),
                    cx,
                    &mut expressions,
                    &mut properties,
                );
                expressions.push(raw_visit(v, cx, expression).unwrap_or(expression));
                continue;
            }
            properties.push(self.transform_jsx_attribute_to_object_literal_element(v, cx, attr));
        }

        if let Some(children_prop) = children_prop {
            properties.push(children_prop);
        }

        combine_properties_into_new_expression(
            &mut self.factory(),
            cx,
            &mut expressions,
            &mut properties,
        );

        if !expressions.is_empty() && !ast::is_object_literal_expression(&cx.nodes[expressions[0]])
        {
            // We must always emit at least one object literal before a spread
            // attribute as the JSX always factory expects a fresh object, so
            // we need to make a copy here we also avoid mutating an external
            // reference by doing this (first expression is used as assign's
            // target)
            let empty = self.factory().new_node_list(Vec::new());
            let obj = self
                .factory()
                .new_object_literal_expression(cx.nodes, Some(empty), false);
            expressions.insert(0, obj);
        }

        if expressions.len() == 1 {
            return expressions[0];
        }
        self.factory().new_assign_helper(
            cx.nodes,
            expressions,
            self.compiler_options.get_emit_script_target(),
        )
    }

    /// `transformJsxAttributesToProps`.
    fn transform_jsx_attributes_to_props(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        attrs: &[NodeId],
        children_prop: Option<NodeId>,
    ) -> Vec<NodeId> {
        let mut props = Vec::with_capacity(attrs.len());
        for &attr in attrs {
            if cx.nodes[attr].kind == Kind::JsxSpreadAttribute {
                let res = self.transform_jsx_spread_attributes_to_props(v, cx, attr);
                props.extend(res);
            } else {
                props.push(self.transform_jsx_attribute_to_object_literal_element(v, cx, attr));
            }
        }
        if let Some(children_prop) = children_prop {
            props.push(children_prop);
        }
        props
    }

    /// `transformJsxSpreadAttributesToProps`.
    fn transform_jsx_spread_attributes_to_props(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Vec<NodeId> {
        let expression = cx.nodes[node].as_jsx_spread_attribute().expression.unwrap();
        if ast::is_object_literal_expression(&cx.nodes[expression])
            && !has_proto(
                cx.nodes[expression].as_object_literal_expression(),
                cx.nodes,
            )
        {
            let props = cx.nodes[expression]
                .as_object_literal_expression()
                .properties
                .clone();
            return v
                .visit_nodes(cx, props)
                .map(|l| l.nodes.to_vec())
                .unwrap_or_default();
        }
        let visited = raw_visit(v, cx, expression).unwrap_or(expression);
        vec![
            self.factory()
                .new_spread_assignment(cx.nodes, Some(visited)),
        ]
    }

    /// `transformJsxAttributeToObjectLiteralElement`.
    fn transform_jsx_attribute_to_object_literal_element(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let name = self.get_attribute_name(cx, node);
        let initializer = cx.nodes[node].as_jsx_attribute().initializer;
        let expression = self.transform_jsx_attribute_initializer(v, cx, initializer);
        self.factory().new_property_assignment(
            cx.nodes,
            None,
            Some(name),
            None,
            None,
            Some(expression),
        )
    }

    /// `getAttributeName`.
    fn get_attribute_name(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        let name = cx.nodes[node].name().unwrap();
        if ast::is_identifier(&cx.nodes[name]) {
            let text = cx.nodes[name].text(cx.nodes).to_string();
            if is_identifier_text(&text, LanguageVariant::Standard) {
                return name;
            }
            return self
                .factory()
                .new_string_literal(cx.nodes, &text, ast::TokenFlags::NONE);
        }
        // must be jsx namespace
        let text = {
            let d = cx.nodes[name].as_jsx_namespaced_name();
            format!(
                "{}:{}",
                cx.nodes[d.namespace.unwrap()].text(cx.nodes),
                cx.nodes[d.name.unwrap()].text(cx.nodes)
            )
        };
        self.factory()
            .new_string_literal(cx.nodes, &text, ast::TokenFlags::NONE)
    }

    /// `transformJsxAttributeInitializer`.
    fn transform_jsx_attribute_initializer(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: Option<NodeId>,
    ) -> NodeId {
        let Some(node) = node else {
            return self.factory().new_true_expression(cx.nodes);
        };
        match cx.nodes[node].kind {
            Kind::StringLiteral => {
                // Always recreate the literal to escape any escape sequences
                // or newlines which may be in the original jsx string and
                // which need to be escaped to be handled correctly in a normal
                // string
                let text = cx.nodes[node].text(cx.nodes).to_string();
                let token_flags = cx.nodes[node]
                    .as_string_literal()
                    .literal_expression_base
                    .literal_like_node_base
                    .token_flags;
                let res = self.factory().new_string_literal(
                    cx.nodes,
                    &decode_entities(&text),
                    token_flags,
                );
                cx.nodes[res].loc = cx.nodes[node].loc;
                // Preserve the original quote style (single vs double quotes)
                let flags = cx.nodes[node]
                    .as_string_literal()
                    .literal_expression_base
                    .literal_like_node_base
                    .token_flags;
                cx.nodes[res]
                    .as_string_literal_mut()
                    .literal_expression_base
                    .literal_like_node_base
                    .token_flags = flags;
                res
            }
            Kind::JsxExpression => {
                let Some(expression) = cx.nodes[node].expression() else {
                    return self.factory().new_true_expression(cx.nodes);
                };
                raw_visit(v, cx, expression).unwrap_or(expression)
            }
            _ if ast::is_jsx_element(&cx.nodes[node])
                || ast::is_jsx_self_closing_element(&cx.nodes[node])
                || ast::is_jsx_fragment(&cx.nodes[node]) =>
            {
                self.set_in_child(false);
                raw_visit(v, cx, node).unwrap_or(node)
            }
            _ => panic!(
                "Unhandled node kind found in jsx initializer: {}",
                cx.nodes[node].kind_string()
            ),
        }
    }

    /// `visitJsxOpeningLikeElementOrFragmentJSX`.
    fn visit_jsx_opening_like_element_or_fragment_jsx(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        tag_name: NodeId,
        object: NodeId,
        key_attr: Option<NodeId>,
        children: Option<NodeList>,
        location: TextRange,
    ) -> NodeId {
        let mut non_whitespace_children = Vec::new();
        if let Some(children) = &children {
            non_whitespace_children = ast::get_semantic_jsx_children(&children.nodes, cx.nodes);
        }
        let is_static_children = non_whitespace_children.len() > 1
            || (non_whitespace_children.len() == 1
                && ast::is_jsx_expression(&cx.nodes[non_whitespace_children[0]])
                && cx.nodes[non_whitespace_children[0]]
                    .as_jsx_expression()
                    .dot_dot_dot_token
                    .is_some());
        let mut args = Vec::with_capacity(3);
        args.push(tag_name);
        args.push(object);
        // function jsx(type, config, maybeKey) {}
        // "maybeKey" is optional. It is acceptable to use "_jsx" without a
        // third argument
        if let Some(key_attr) = key_attr {
            let initializer = cx.nodes[key_attr].as_jsx_attribute().initializer;
            args.push(self.transform_jsx_attribute_initializer(v, cx, initializer));
        }

        if self.compiler_options.jsx == JsxEmit::ReactJSXDev {
            let original_file = self
                .ec
                .borrow()
                .most_original(self.current_source_file.get());
            if let Some(original_file) = original_file
                && cx.nodes[original_file].kind == Kind::SourceFile
            {
                // "maybeKey" has to be replaced with "void 0" to not break the
                // jsxDEV signature
                if key_attr.is_none() {
                    args.push(self.factory().new_void_zero_expression(cx.nodes));
                }
                // isStaticChildren development flag
                if is_static_children {
                    args.push(self.factory().new_true_expression(cx.nodes));
                } else {
                    args.push(self.factory().new_false_expression(cx.nodes));
                }
                // __source development flag
                let (line, col) = get_ecma_line_and_utf16_character_of_position(
                    cx.nodes[original_file].as_source_file(),
                    location.pos(),
                );
                let file_name = self.get_current_file_name_expression(cx);
                let file_name_prop = {
                    let name = self.factory().new_identifier(cx.nodes, "fileName");
                    self.factory().new_property_assignment(
                        cx.nodes,
                        None,
                        Some(name),
                        None,
                        None,
                        Some(file_name),
                    )
                };
                let line_prop = {
                    let name = self.factory().new_identifier(cx.nodes, "lineNumber");
                    let lit = self.factory().new_numeric_literal(
                        cx.nodes,
                        &(line + 1).to_string(),
                        ast::TokenFlags::NONE,
                    );
                    self.factory().new_property_assignment(
                        cx.nodes,
                        None,
                        Some(name),
                        None,
                        None,
                        Some(lit),
                    )
                };
                let col_prop = {
                    let name = self.factory().new_identifier(cx.nodes, "columnNumber");
                    let lit = self.factory().new_numeric_literal(
                        cx.nodes,
                        &(col + 1).to_string(),
                        ast::TokenFlags::NONE,
                    );
                    self.factory().new_property_assignment(
                        cx.nodes,
                        None,
                        Some(name),
                        None,
                        None,
                        Some(lit),
                    )
                };
                let members =
                    self.factory()
                        .new_node_list(vec![file_name_prop, line_prop, col_prop]);
                args.push(self.factory().new_object_literal_expression(
                    cx.nodes,
                    Some(members),
                    false,
                ));
                // __self development flag
                args.push(self.factory().new_this_expression(cx.nodes));
            }
        }

        let callee = self.get_jsx_factory_callee(cx, is_static_children);
        let args = self.factory().new_node_list(args);
        let element = self.factory().new_call_expression(
            cx.nodes,
            Some(callee),
            None,
            None,
            Some(args),
            ast::NodeFlags::NONE,
        );
        cx.nodes[element].loc = location;

        if self.in_jsx_child.get() {
            self.ec
                .borrow()
                .add_emit_flags(element, EmitFlags::START_ON_NEW_LINE);
        }

        element
    }

    /// `visitJsxOpeningFragmentJSX`.
    fn visit_jsx_opening_fragment_jsx(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        fragment: NodeId,
        children: Option<NodeList>,
        location: TextRange,
    ) -> Option<NodeId> {
        let _ = fragment;
        let mut children_props = None;
        if let Some(children) = &children
            && !children.nodes.is_empty()
        {
            children_props =
                self.convert_jsx_children_to_children_prop_object(v, cx, &children.nodes);
        }
        if children_props.is_none() {
            let empty = self.factory().new_node_list(Vec::new());
            children_props = Some(self.factory().new_object_literal_expression(
                cx.nodes,
                Some(empty),
                false,
            ));
        }
        let tag_name = self.get_implicit_jsx_fragment_reference(cx);
        Some(self.visit_jsx_opening_like_element_or_fragment_jsx(
            v,
            cx,
            tag_name,
            children_props.unwrap(),
            None,
            children,
            location,
        ))
    }

    /// `createReactNamespace`.
    fn create_react_namespace(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        react_namespace: &str,
        parent: NodeId,
    ) -> NodeId {
        // To ensure the emit resolver can properly resolve the namespace, we
        // need to treat this identifier as if it were a source tree node by
        // clearing the `Synthesized` flag and setting a parent node. TODO: Is
        // this still true? The emit resolver is supposed to be hardened
        // against this, so long as the node retains original node pointers
        // back to a parsed node
        let react_namespace = if react_namespace.is_empty() {
            "React"
        } else {
            react_namespace
        };
        let react = self.factory().new_identifier(cx.nodes, react_namespace);
        cx.nodes[react].flags &= !ast::NodeFlags::SYNTHESIZED;

        // Set the parent that is in parse tree
        // this makes sure that parent chain is intact for checker to traverse
        // complete scope tree
        // PORT: `ParseNode` mirrors `react.Parent = c.ParseNode(parent)`
        // (Go: parent intentionally wired to a parse-tree node for resolver
        // traversal).
        cx.nodes[react].parent = self.ec.borrow().parse_node(cx.nodes, parent);

        // If the identifier refers to an exported member of a namespace,
        // substitute with a qualified namespace property access (e.g.,
        // `React` -> `M.React`). See also:
        // RuntimeSyntaxTransformer.visitExpressionIdentifier in
        // runtimesyntax.go
        // PORT: Go calls `emitResolver.GetReferencedExportContainer`; in Rust
        // that lives on the `ReferenceResolver` trait and needs the shared
        // symbol arena. Absent resolver/symbols, skip the substitution.
        let container = match (&self.resolver, self.symbols) {
            (Some(resolver), Some(symbols)) => {
                resolver.borrow_mut().get_referenced_export_container(
                    react,
                    false, /*prefixLocals*/
                    cx.nodes,
                    symbols,
                )
            }
            _ => None,
        };
        if let Some(container) = container
            && cx.nodes[container].kind == Kind::ModuleDeclaration
        {
            let container_name = self
                .factory()
                .new_generated_name_for_node(cx.nodes, container);
            return self.factory().new_property_access_expression(
                cx.nodes,
                Some(container_name),
                None,
                Some(react),
                ast::NodeFlags::NONE,
            );
        }

        react
    }

    /// `createJsxFactoryExpressionFromEntityName`.
    fn create_jsx_factory_expression_from_entity_name(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        e: NodeId,
        parent: NodeId,
    ) -> NodeId {
        // PORT: `e` lives in the checker's file arena — `entity_name_texts`
        // resolves it there and flattens the qualified-name chain
        // (Go's recursion reads `e.Left`/`e.Right` through pointers).
        let parts = self.emit_resolver.borrow().entity_name_texts(e, cx.nodes);
        let mut it = parts.iter();
        let Some(first) = it.next() else {
            return self.create_react_namespace(cx, "", parent);
        };
        let mut expr = self.create_react_namespace(cx, first, parent);
        for part in it {
            let right = self.factory().new_identifier(cx.nodes, part);
            expr = self.factory().new_property_access_expression(
                cx.nodes,
                Some(expr),
                None,
                Some(right),
                ast::NodeFlags::NONE,
            );
        }
        expr
    }

    /// `createJsxPseudoFactoryExpression`.
    fn create_jsx_pseudo_factory_expression(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        parent: NodeId,
        e: Option<NodeId>,
        target: &str,
    ) -> NodeId {
        if let Some(e) = e {
            return self.create_jsx_factory_expression_from_entity_name(cx, e, parent);
        }
        let namespace =
            self.create_react_namespace(cx, &self.compiler_options.react_namespace, parent);
        let target_id = self.factory().new_identifier(cx.nodes, target);
        self.factory().new_property_access_expression(
            cx.nodes,
            Some(namespace),
            None,
            Some(target_id),
            ast::NodeFlags::NONE,
        )
    }

    /// `createJsxFactoryExpression`.
    fn create_jsx_factory_expression(&self, cx: &mut VisitorCx<'_, '_>, parent: NodeId) -> NodeId {
        let e = self
            .emit_resolver
            .borrow()
            .get_jsx_factory_entity(self.current_source_file.get().unwrap(), cx.nodes);
        self.create_jsx_pseudo_factory_expression(cx, parent, e, "createElement")
    }

    /// `createJsxFragmentFactoryExpression`.
    fn create_jsx_fragment_factory_expression(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        parent: NodeId,
    ) -> NodeId {
        let e = self
            .emit_resolver
            .borrow()
            .get_jsx_fragment_factory_entity(self.current_source_file.get().unwrap(), cx.nodes);
        self.create_jsx_pseudo_factory_expression(cx, parent, e, "Fragment")
    }

    /// `visitJsxOpeningLikeElementCreateElement`.
    fn visit_jsx_opening_like_element_create_element(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        element: NodeId,
        children: Option<NodeList>,
        location: TextRange,
    ) -> Option<NodeId> {
        let tag_name = self.get_tag_name(cx, element);
        let attrs: Vec<NodeId> = cx.nodes[cx.nodes[element].attributes().unwrap()]
            .properties()
            .unwrap_or(&[])
            .to_vec();
        let object_properties;
        if !attrs.is_empty() {
            object_properties = self.transform_jsx_attributes_to_object_props(v, cx, &attrs, None);
        } else {
            // When there are no attributes, React wants "null"
            object_properties = self
                .factory()
                .new_keyword_expression(cx.nodes, Kind::NullKeyword);
        }

        let callee;
        if self.import_specifier.borrow().is_empty() {
            callee = self.create_jsx_factory_expression(cx, element);
        } else {
            callee = self.get_implicit_import_for_name(cx, "createElement");
        }

        let mut new_children = Vec::new();
        if let Some(children) = &children {
            for &c in children.nodes.iter() {
                if let Some(res) = self.transform_jsx_child_to_expression(v, cx, c) {
                    new_children.push(res);
                }
            }
        }

        // Add StartOnNewLine flag only if there are multiple actual children
        // (after filtering)
        if new_children.len() > 1 {
            for &child in &new_children {
                self.ec
                    .borrow()
                    .add_emit_flags(child, EmitFlags::START_ON_NEW_LINE);
            }
        }

        let mut args = Vec::with_capacity(new_children.len() + 2);
        args.push(tag_name);
        args.push(object_properties);
        args.extend(new_children);

        let args = self.factory().new_node_list(args);
        let result = self.factory().new_call_expression(
            cx.nodes,
            Some(callee),
            None,
            None,
            Some(args),
            ast::NodeFlags::NONE,
        );
        cx.nodes[result].loc = location;

        if self.in_jsx_child.get() {
            self.ec
                .borrow()
                .add_emit_flags(result, EmitFlags::START_ON_NEW_LINE);
        }
        Some(result)
    }

    /// `visitJsxOpeningFragmentCreateElement`.
    fn visit_jsx_opening_fragment_create_element(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        fragment: NodeId,
        children: Option<NodeList>,
        location: TextRange,
    ) -> Option<NodeId> {
        let tag_name = self.create_jsx_fragment_factory_expression(cx, fragment);
        let callee = self.create_jsx_factory_expression(cx, fragment);

        let mut new_children = Vec::new();
        if let Some(children) = &children {
            for &c in children.nodes.iter() {
                if let Some(res) = self.transform_jsx_child_to_expression(v, cx, c) {
                    new_children.push(res);
                }
            }
        }

        // Add StartOnNewLine flag only if there are multiple actual children
        // (after filtering)
        if new_children.len() > 1 {
            for &child in &new_children {
                self.ec
                    .borrow()
                    .add_emit_flags(child, EmitFlags::START_ON_NEW_LINE);
            }
        }

        let mut args = Vec::with_capacity(new_children.len() + 2);
        args.push(tag_name);
        args.push(
            self.factory()
                .new_keyword_expression(cx.nodes, Kind::NullKeyword),
        );
        args.extend(new_children);

        let args = self.factory().new_node_list(args);
        let result = self.factory().new_call_expression(
            cx.nodes,
            Some(callee),
            None,
            None,
            Some(args),
            ast::NodeFlags::NONE,
        );
        cx.nodes[result].loc = location;

        if self.in_jsx_child.get() {
            self.ec
                .borrow()
                .add_emit_flags(result, EmitFlags::START_ON_NEW_LINE);
        }
        Some(result)
    }

    /// `visitJsxText`.
    fn visit_jsx_text(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> Option<NodeId> {
        // Go reads `(*JsxText).Text` (LiteralLikeNodeBase.text), not
        // `Node.Text()` — JsxText is not in the `Node.Text` kind switch.
        let text = cx.nodes[node].as_jsx_text().literal_like_node_base.text.clone();
        let fixed = fixup_whitespace_and_decode_entities(&text);
        if fixed.is_empty() {
            return None;
        }
        Some(
            self.factory()
                .new_string_literal(cx.nodes, &fixed, ast::TokenFlags::NONE),
        )
    }

    /// `visitJsxExpression`.
    fn visit_jsx_expression(
        &self,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let expression = cx.nodes[node].as_jsx_expression().expression;
        let e = expression.and_then(|e| raw_visit(v, cx, e));
        if cx.nodes[node]
            .as_jsx_expression()
            .dot_dot_dot_token
            .is_some()
        {
            return Some(self.factory().new_spread_element(cx.nodes, e));
        }
        e
    }
}

/// `hasKeyAfterPropsSpread` — the react jsx/jsxs transform falls back to
/// `createElement` when an explicit `key` argument comes after a spread.
fn has_key_after_props_spread(nodes: &[ast::Node], node: NodeId) -> bool {
    let mut spread = false;
    let mut opener = node;
    if nodes[node].kind == Kind::JsxElement {
        opener = nodes[node].as_jsx_element().opening_element.unwrap();
    } // otherwise self-closing
    for &elem in nodes[nodes[opener].attributes().unwrap()]
        .properties()
        .unwrap_or(&[])
        .iter()
    {
        if ast::is_jsx_spread_attribute(&nodes[elem]) {
            let expression = nodes[elem].expression().unwrap();
            if !ast::is_object_literal_expression(&nodes[expression])
                || nodes[expression]
                    .properties()
                    .unwrap_or(&[])
                    .iter()
                    .any(|&p| ast::is_spread_assignment(&nodes[p]))
            {
                spread = true;
            }
        } else if spread
            && ast::is_jsx_attribute(&nodes[elem])
            && let Some(name) = nodes[elem].name()
            && ast::is_identifier(&nodes[name])
            && nodes[name].text(nodes) == "key"
        {
            return true;
        }
    }
    false
}

/// `sortImportSpecifiers`.
fn sort_import_specifiers(nodes: &[ast::Node], a: &NodeId, b: &NodeId) -> std::cmp::Ordering {
    let a_property = nodes[nodes[*a].property_name().unwrap()].text(nodes);
    let b_property = nodes[nodes[*b].property_name().unwrap()].text(nodes);
    let res =
        stringutil::compare_strings_case_sensitive(a_property.as_bytes(), b_property.as_bytes());
    if res != COMPARISON_EQUAL {
        return res.cmp(&0);
    }
    let a_name = nodes[nodes[*a].as_import_specifier().name.unwrap()].text(nodes);
    let b_name = nodes[nodes[*b].as_import_specifier().name.unwrap()].text(nodes);
    let res = stringutil::compare_strings_case_sensitive(a_name.as_bytes(), b_name.as_bytes());
    res.cmp(&0)
}

/// `getSortedSpecifiers`.
fn get_sorted_specifiers(nodes: &[ast::Node], m: &HashMap<String, NodeId>) -> Vec<NodeId> {
    let mut res: Vec<NodeId> = m.values().copied().collect();
    res.sort_by(|a, b| sort_import_specifiers(nodes, a, b));
    res
}

/// `combinePropertiesIntoNewExpression`.
fn combine_properties_into_new_expression(
    factory: &mut RefMut<'_, NodeFactory>,
    cx: &mut VisitorCx<'_, '_>,
    expressions: &mut Vec<NodeId>,
    props: &mut Vec<NodeId>,
) {
    if props.is_empty() {
        return;
    }
    let members = factory.new_node_list(std::mem::take(props));
    let new_obj = factory.new_object_literal_expression(cx.nodes, Some(members), false);
    expressions.push(new_obj);
}

/// `hasProto`.
fn has_proto(obj: &ast::ObjectLiteralExpression, nodes: &[ast::Node]) -> bool {
    for &p in obj.properties.iter().flat_map(|l| l.nodes.iter()) {
        if ast::is_property_assignment(&nodes[p])
            && let Some(name) = nodes[p].name()
            && (ast::is_string_literal(&nodes[name]) || ast::is_identifier(&nodes[name]))
            && &*nodes[name].text(nodes) == "__proto__"
        {
            return true;
        }
    }
    false
}

/// `addLineOfJsxText`.
fn add_line_of_jsx_text(b: &mut Vec<u8>, trimmed_line: &str, is_initial: bool) {
    // We do not escape the string here as that is handled by the printer
    // when it emits the literal. We do, however, need to decode JSX entities.
    let decoded = decode_entities(trimmed_line);
    if !is_initial {
        b.extend_from_slice(b" ");
    }
    b.extend_from_slice(decoded.as_bytes());
}

/// `fixupWhitespaceAndDecodeEntities` — JSX trims whitespace at the end and
/// beginning of lines, except that the start/end of a tag is considered a
/// start/end of a line only if that line is on the same line as the closing
/// tag. See examples in
/// tests/cases/conformance/jsx/tsxReactEmitWhitespace.tsx and
/// https://www.w3.org/TR/html4/struct/text.html#h-9.1 and
/// https://www.w3.org/TR/CSS2/text.html#white-space-model
fn fixup_whitespace_and_decode_entities(text: &str) -> String {
    let mut acc = Vec::new();
    let mut initial = true;
    // First non-whitespace character on this line.
    let mut first_non_whitespace: isize = 0;
    // End byte position of the last non-whitespace character on this line.
    let mut last_non_whitespace_end: isize = -1;
    // These initial values are special because the first line is:
    // firstNonWhitespace = 0 to indicate that we want leading whitespace,
    // but lastNonWhitespaceEnd = -1 as a special flag to indicate that we
    // *don't* include the line if it's all whitespace.
    let bytes = text.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        let (c, size) = {
            let c = text[i..].chars().next().unwrap();
            (c, c.len_utf8())
        };
        if stringutil::is_line_break(c) {
            // If we've seen any non-whitespace characters on this line, add
            // the 'trim' of the line.
            // (lastNonWhitespaceEnd === -1 is a special flag to detect whether
            // the first line is all whitespace.)
            if first_non_whitespace != -1 && last_non_whitespace_end != -1 {
                add_line_of_jsx_text(
                    &mut acc,
                    &text[first_non_whitespace as usize..last_non_whitespace_end as usize + 1],
                    initial,
                );
                initial = false;
            }

            // Reset firstNonWhitespace for the next line.
            // Don't bother to reset lastNonWhitespaceEnd because we ignore it
            // if firstNonWhitespace = -1.
            first_non_whitespace = -1;
        } else if !stringutil::is_white_space_single_line(c) {
            last_non_whitespace_end = i as isize + size as isize - 1; // Store the end byte position of the character
            if first_non_whitespace == -1 {
                first_non_whitespace = i as isize;
            }
        }

        i += size;
    }

    if first_non_whitespace != -1 {
        // Last line had a non-whitespace character. Emit the 'trimLeft',
        // meaning keep trailing whitespace.
        add_line_of_jsx_text(&mut acc, &text[first_non_whitespace as usize..], initial);
    }
    // PORT: `new_string_literal` stores a `String`; lone-surrogate sentinel
    // bytes collapse to U+FFFD here (same trade the scanner makes with
    // `from_utf8_lossy` on `token_value`).
    String::from_utf8_lossy(&acc).into_owned()
}

/// `decodeEntities` — replaces entities like "&nbsp;", "&#123;", and
/// "&#xDEADBEEF;" with the characters they encode.
/// See https://en.wikipedia.org/wiki/List_of_XML_and_HTML_character_entity_references
fn decode_entities(text: &str) -> String {
    let Some(mut i) = text.find('&') else {
        return text.to_string();
    };

    let mut result: Vec<u8> = Vec::with_capacity(text.len());
    let mut text = text;
    loop {
        result.extend_from_slice(&text.as_bytes()[..i]);
        text = &text[i..];

        let Some(mut semi) = text.find(';') else {
            break;
        };

        // Skip past any intervening '&' characters between the current '&'
        // and the ';'. Each such '&' is not part of a valid entity, so emit
        // it (and any text before the next '&') as literals.
        loop {
            let Some(next_amp) = text[1..semi].find('&') else {
                break;
            };
            result.extend_from_slice(&text.as_bytes()[..next_amp + 1]);
            text = &text[next_amp + 1..];
            semi -= next_amp + 1;
        }

        let entity = &text[1..semi];
        if let Some(decoded) = decode_entity(entity) {
            // Use the JS-string encoder so lone surrogates (e.g. "&#xD800;")
            // are preserved rather than being lost to U+FFFD by WriteRune.
            result.extend_from_slice(&stringutil::encode_js_string_rune(decoded));
        } else {
            result.extend_from_slice(&text.as_bytes()[..semi + 1]);
        }
        text = &text[semi + 1..];

        let Some(next) = text.find('&') else {
            break;
        };
        i = next;
    }
    result.extend_from_slice(text.as_bytes());
    // See the note in fixup_whitespace_and_decode_entities for the
    // `String` conversion.
    String::from_utf8_lossy(&result).into_owned()
}

/// `decodeEntity` — returns the decoded code point (Go `rune`; `i32` so lone
/// surrogates round-trip through `encode_js_string_rune`).
fn decode_entity(entity: &str) -> Option<i32> {
    if entity.is_empty() {
        return None;
    }

    let mut entity = entity;
    if entity.as_bytes()[0] == b'#' {
        entity = &entity[1..];
        if entity.is_empty() {
            return None;
        }

        let mut base = 10;
        if entity.as_bytes()[0] == b'x' {
            base = 16;
            entity = &entity[1..];
        }

        if entity.is_empty() {
            return None;
        }

        for c in entity.chars() {
            if base == 16 && !stringutil::is_hex_digit(c) {
                return None;
            }
            if base == 10 && !stringutil::is_digit(c) {
                return None;
            }
        }

        let parsed = i32::from_str_radix(entity, base).ok()?;
        return Some(parsed);
    }

    lookup_entity(entity)
}
/// The HTML named-entity table (Go: `var entities = map[string]rune{...}`).
/// Values are code points; lone surrogates are stored as `i32` and are
/// encoded via `stringutil::encode_js_string_rune` (CESU-8/WTF-8 sentinel).
fn lookup_entity(entity: &str) -> Option<i32> {
    Some(match entity {
        "quot" => 0x0022,
        "amp" => 0x0026,
        "apos" => 0x0027,
        "lt" => 0x003C,
        "gt" => 0x003E,
        "nbsp" => 0x00A0,
        "iexcl" => 0x00A1,
        "cent" => 0x00A2,
        "pound" => 0x00A3,
        "curren" => 0x00A4,
        "yen" => 0x00A5,
        "brvbar" => 0x00A6,
        "sect" => 0x00A7,
        "uml" => 0x00A8,
        "copy" => 0x00A9,
        "ordf" => 0x00AA,
        "laquo" => 0x00AB,
        "not" => 0x00AC,
        "shy" => 0x00AD,
        "reg" => 0x00AE,
        "macr" => 0x00AF,
        "deg" => 0x00B0,
        "plusmn" => 0x00B1,
        "sup2" => 0x00B2,
        "sup3" => 0x00B3,
        "acute" => 0x00B4,
        "micro" => 0x00B5,
        "para" => 0x00B6,
        "middot" => 0x00B7,
        "cedil" => 0x00B8,
        "sup1" => 0x00B9,
        "ordm" => 0x00BA,
        "raquo" => 0x00BB,
        "frac14" => 0x00BC,
        "frac12" => 0x00BD,
        "frac34" => 0x00BE,
        "iquest" => 0x00BF,
        "Agrave" => 0x00C0,
        "Aacute" => 0x00C1,
        "Acirc" => 0x00C2,
        "Atilde" => 0x00C3,
        "Auml" => 0x00C4,
        "Aring" => 0x00C5,
        "AElig" => 0x00C6,
        "Ccedil" => 0x00C7,
        "Egrave" => 0x00C8,
        "Eacute" => 0x00C9,
        "Ecirc" => 0x00CA,
        "Euml" => 0x00CB,
        "Igrave" => 0x00CC,
        "Iacute" => 0x00CD,
        "Icirc" => 0x00CE,
        "Iuml" => 0x00CF,
        "ETH" => 0x00D0,
        "Ntilde" => 0x00D1,
        "Ograve" => 0x00D2,
        "Oacute" => 0x00D3,
        "Ocirc" => 0x00D4,
        "Otilde" => 0x00D5,
        "Ouml" => 0x00D6,
        "times" => 0x00D7,
        "Oslash" => 0x00D8,
        "Ugrave" => 0x00D9,
        "Uacute" => 0x00DA,
        "Ucirc" => 0x00DB,
        "Uuml" => 0x00DC,
        "Yacute" => 0x00DD,
        "THORN" => 0x00DE,
        "szlig" => 0x00DF,
        "agrave" => 0x00E0,
        "aacute" => 0x00E1,
        "acirc" => 0x00E2,
        "atilde" => 0x00E3,
        "auml" => 0x00E4,
        "aring" => 0x00E5,
        "aelig" => 0x00E6,
        "ccedil" => 0x00E7,
        "egrave" => 0x00E8,
        "eacute" => 0x00E9,
        "ecirc" => 0x00EA,
        "euml" => 0x00EB,
        "igrave" => 0x00EC,
        "iacute" => 0x00ED,
        "icirc" => 0x00EE,
        "iuml" => 0x00EF,
        "eth" => 0x00F0,
        "ntilde" => 0x00F1,
        "ograve" => 0x00F2,
        "oacute" => 0x00F3,
        "ocirc" => 0x00F4,
        "otilde" => 0x00F5,
        "ouml" => 0x00F6,
        "divide" => 0x00F7,
        "oslash" => 0x00F8,
        "ugrave" => 0x00F9,
        "uacute" => 0x00FA,
        "ucirc" => 0x00FB,
        "uuml" => 0x00FC,
        "yacute" => 0x00FD,
        "thorn" => 0x00FE,
        "yuml" => 0x00FF,
        "OElig" => 0x0152,
        "oelig" => 0x0153,
        "Scaron" => 0x0160,
        "scaron" => 0x0161,
        "Yuml" => 0x0178,
        "fnof" => 0x0192,
        "circ" => 0x02C6,
        "tilde" => 0x02DC,
        "Alpha" => 0x0391,
        "Beta" => 0x0392,
        "Gamma" => 0x0393,
        "Delta" => 0x0394,
        "Epsilon" => 0x0395,
        "Zeta" => 0x0396,
        "Eta" => 0x0397,
        "Theta" => 0x0398,
        "Iota" => 0x0399,
        "Kappa" => 0x039A,
        "Lambda" => 0x039B,
        "Mu" => 0x039C,
        "Nu" => 0x039D,
        "Xi" => 0x039E,
        "Omicron" => 0x039F,
        "Pi" => 0x03A0,
        "Rho" => 0x03A1,
        "Sigma" => 0x03A3,
        "Tau" => 0x03A4,
        "Upsilon" => 0x03A5,
        "Phi" => 0x03A6,
        "Chi" => 0x03A7,
        "Psi" => 0x03A8,
        "Omega" => 0x03A9,
        "alpha" => 0x03B1,
        "beta" => 0x03B2,
        "gamma" => 0x03B3,
        "delta" => 0x03B4,
        "epsilon" => 0x03B5,
        "zeta" => 0x03B6,
        "eta" => 0x03B7,
        "theta" => 0x03B8,
        "iota" => 0x03B9,
        "kappa" => 0x03BA,
        "lambda" => 0x03BB,
        "mu" => 0x03BC,
        "nu" => 0x03BD,
        "xi" => 0x03BE,
        "omicron" => 0x03BF,
        "pi" => 0x03C0,
        "rho" => 0x03C1,
        "sigmaf" => 0x03C2,
        "sigma" => 0x03C3,
        "tau" => 0x03C4,
        "upsilon" => 0x03C5,
        "phi" => 0x03C6,
        "chi" => 0x03C7,
        "psi" => 0x03C8,
        "omega" => 0x03C9,
        "thetasym" => 0x03D1,
        "upsih" => 0x03D2,
        "piv" => 0x03D6,
        "ensp" => 0x2002,
        "emsp" => 0x2003,
        "thinsp" => 0x2009,
        "zwnj" => 0x200C,
        "zwj" => 0x200D,
        "lrm" => 0x200E,
        "rlm" => 0x200F,
        "ndash" => 0x2013,
        "mdash" => 0x2014,
        "lsquo" => 0x2018,
        "rsquo" => 0x2019,
        "sbquo" => 0x201A,
        "ldquo" => 0x201C,
        "rdquo" => 0x201D,
        "bdquo" => 0x201E,
        "dagger" => 0x2020,
        "Dagger" => 0x2021,
        "bull" => 0x2022,
        "hellip" => 0x2026,
        "permil" => 0x2030,
        "prime" => 0x2032,
        "Prime" => 0x2033,
        "lsaquo" => 0x2039,
        "rsaquo" => 0x203A,
        "oline" => 0x203E,
        "frasl" => 0x2044,
        "euro" => 0x20AC,
        "image" => 0x2111,
        "weierp" => 0x2118,
        "real" => 0x211C,
        "trade" => 0x2122,
        "alefsym" => 0x2135,
        "larr" => 0x2190,
        "uarr" => 0x2191,
        "rarr" => 0x2192,
        "darr" => 0x2193,
        "harr" => 0x2194,
        "crarr" => 0x21B5,
        "lArr" => 0x21D0,
        "uArr" => 0x21D1,
        "rArr" => 0x21D2,
        "dArr" => 0x21D3,
        "hArr" => 0x21D4,
        "forall" => 0x2200,
        "part" => 0x2202,
        "exist" => 0x2203,
        "empty" => 0x2205,
        "nabla" => 0x2207,
        "isin" => 0x2208,
        "notin" => 0x2209,
        "ni" => 0x220B,
        "prod" => 0x220F,
        "sum" => 0x2211,
        "minus" => 0x2212,
        "lowast" => 0x2217,
        "radic" => 0x221A,
        "prop" => 0x221D,
        "infin" => 0x221E,
        "ang" => 0x2220,
        "and" => 0x2227,
        "or" => 0x2228,
        "cap" => 0x2229,
        "cup" => 0x222A,
        "int" => 0x222B,
        "there4" => 0x2234,
        "sim" => 0x223C,
        "cong" => 0x2245,
        "asymp" => 0x2248,
        "ne" => 0x2260,
        "equiv" => 0x2261,
        "le" => 0x2264,
        "ge" => 0x2265,
        "sub" => 0x2282,
        "sup" => 0x2283,
        "nsub" => 0x2284,
        "sube" => 0x2286,
        "supe" => 0x2287,
        "oplus" => 0x2295,
        "otimes" => 0x2297,
        "perp" => 0x22A5,
        "sdot" => 0x22C5,
        "lceil" => 0x2308,
        "rceil" => 0x2309,
        "lfloor" => 0x230A,
        "rfloor" => 0x230B,
        "lang" => 0x2329,
        "rang" => 0x232A,
        "loz" => 0x25CA,
        "spades" => 0x2660,
        "clubs" => 0x2663,
        "hearts" => 0x2665,
        "diams" => 0x2666,
        _ => return None,
    })
}
