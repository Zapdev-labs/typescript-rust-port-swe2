// Ported from tsc/internal/transformers/moduletransforms/commonjsmodule.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The CommonJS module transform: top-level import/export lowering,
// `exports.x` live bindings, `export =`, dynamic-import lowering, and
// imported/exported identifier rewriting.
//
// PORT notes specific to this file:
//   - Go's `tx.topLevelVisitor`/`topLevelNestedVisitor`/
//     `discardedValueVisitor`/`assignmentPatternVisitor` are sibling
//     `NodeVisitor`s created through `emitContext.NewNodeVisitor` (see the
//     `CjsVisitors` docs below). `tx.Visitor()` (the main visitor) is
//     likewise re-created as `visitors.main` with the same visit function —
//     the transform cannot reach the visitor its own visit closure is
//     installed on.
//   - `pushNode`/`popNode` ancestor tracking is `Cell`-backed state on the
//     shared struct with an RAII [`PopGuard`] restoring `parentNode`/
//     `currentNode` on scope exit (Go `defer`).
//   - `tx.EmitContext().VisitIterationBody` /
//     `tx.topLevelNestedVisitor.VisitEmbeddedStatement` map to
//     `ec_visit_iteration_body` / `NodeVisitor::visit_embedded_statement`,
//     which do not borrow the `EmitContext` `RefCell` (see `estransforms`).

use std::cell::{Cell, Ref, RefCell, RefMut};
use std::rc::{Rc, Weak};

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, Node, NodeId, SubtreeFacts, Symbol};
use tsc_binder::referenceresolver::ReferenceResolver;
use tsc_collections::Set;
use tsc_core::options_generated::{CompilerOptions, ModuleKind, ScriptTarget};
use tsc_core::text::TextRange;
use tsc_printer::{AutoGenerateOptions, EmitFlags, GeneratedIdentifierFlags};

use super::externalmoduleinfo::{
    ExternalModuleInfo, collect_external_module_info,
    create_external_helpers_import_declaration_if_needed, get_export_needs_import_star_helper,
    get_import_needs_import_default_helper, get_import_needs_import_star_helper,
};
use super::utilities::{
    get_external_module_name_literal, is_declaration_name_of_enum_or_namespace,
    is_file_level_reserved_generated_identifier, is_simple_inlineable_expression,
    rewrite_module_specifier,
};
use crate::chain::{GetEmitModuleFormatOfFile, TransformOptions};
use crate::destructuring::{
    CreateAssignmentCallback, FlattenLevel, flatten_destructuring_assignment,
};
use crate::estransforms::{
    Ec, ec_visit_iteration_body, make_transformer, subtree_facts, tx_adapter, visit_each_child,
};
use crate::modifier_visitor::extract_modifiers;
use crate::transformer::Transformer;
use crate::{
    convert_variable_declaration_to_assignment_expression, is_export_name, is_generated_identifier,
    is_helper_name, is_identifier_reference, is_local_name, single_or_many,
};

/// The sibling visitors Go constructs in `NewCommonJSModuleTransformer` via
/// `emitContext.NewNodeVisitor`. Each visit closure re-enters the shared
/// [`CommonJsModuleTransformer`] state through a `Weak`.
///
/// `main` re-creates `tx.Visitor()` — the same visit function and
/// emit-context hooks as the real `Transformer` visitor, which the state
/// struct cannot reach from within its own visit callback.
struct CjsVisitors<'a> {
    /// `tx.Visitor()` — proxy of the transformer's main visitor.
    main: NodeVisitor<'a>,
    /// `tx.topLevelVisitor` — visits statements at top level of a module.
    top_level: NodeVisitor<'a>,
    /// `tx.topLevelNestedVisitor` — visits nested statements at top level of a module.
    top_level_nested: NodeVisitor<'a>,
    /// `tx.discardedValueVisitor` — visits expressions whose values would be discarded at runtime.
    discarded_value: NodeVisitor<'a>,
    /// `tx.assignmentPatternVisitor` — visits assignment patterns in a destructuring assignment.
    assignment_pattern: NodeVisitor<'a>,
}

/// `type CommonJSModuleTransformer struct`.
struct CommonJsModuleTransformer<'a> {
    compiler_options: &'a CompilerOptions,
    resolver: Option<Rc<RefCell<dyn ReferenceResolver + 'a>>>,
    get_emit_module_format_of_file: Option<&'a GetEmitModuleFormatOfFile<'a>>,
    symbols: Option<&'a RefCell<Vec<Symbol>>>,
    module_kind: ModuleKind,
    language_version: ScriptTarget,
    /// `currentSourceFile`
    current_source_file: Cell<Option<NodeId>>,
    /// `currentModuleInfo`
    current_module_info: RefCell<Option<ExternalModuleInfo>>,
    /// `parentNode` — used for ancestor tracking via pushNode/popNode to
    /// detect expression identifiers.
    parent_node: Cell<Option<NodeId>>,
    /// `currentNode`
    current_node: Cell<Option<NodeId>>,
    /// The sibling visitors, installed after construction.
    visitors: RefCell<Option<CjsVisitors<'a>>>,
    /// `Weak` self-reference used to build the destructuring-flattening
    /// assignment callback (`Box<CreateAssignmentCallback<'a>>` cannot
    /// capture `&self`).
    self_ref: RefCell<Weak<Self>>,
}

/// RAII equivalent of Go's `grandparentNode := tx.pushNode(node); defer
/// tx.popNode(grandparentNode)`.
struct PopGuard<'s, 'a> {
    tx: &'s CommonJsModuleTransformer<'a>,
    grandparent: Option<NodeId>,
}

impl Drop for PopGuard<'_, '_> {
    fn drop(&mut self) {
        self.tx.current_node.set(self.tx.parent_node.get());
        self.tx.parent_node.set(self.grandparent);
    }
}

/// `NewCommonJSModuleTransformer`.
pub fn new_common_js_module_transformer<'a>(
    opts: &'a TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    let compiler_options = opts
        .compiler_options
        .expect("NewCommonJSModuleTransformer requires opts.CompilerOptions");
    make_transformer(opts, |ec| {
        let tx = Rc::new(CommonJsModuleTransformer {
            compiler_options,
            resolver: opts.resolver.clone(),
            get_emit_module_format_of_file: opts.get_emit_module_format_of_file,
            symbols: opts.symbols,
            module_kind: compiler_options.get_emit_module_kind(),
            language_version: compiler_options.get_emit_script_target(),
            current_source_file: Cell::new(None),
            current_module_info: RefCell::new(None),
            parent_node: Cell::new(None),
            current_node: Cell::new(None),
            visitors: RefCell::new(None),
            self_ref: RefCell::new(Weak::new()),
        });
        *tx.self_ref.borrow_mut() = Rc::downgrade(&tx);
        let weak = Rc::downgrade(&tx);

        // `emitContext.NewNodeVisitor` — each sibling visitor's visit
        // closure re-enters the shared state through `Weak` so the visitors
        // can be stored on the state itself.
        fn make_visitor<'a>(
            weak: &Weak<CommonJsModuleTransformer<'a>>,
            ec: &Ec,
            f: fn(
                &CommonJsModuleTransformer<'a>,
                &Ec,
                &mut VisitorCx<'_, '_>,
                NodeId,
            ) -> Option<NodeId>,
        ) -> NodeVisitor<'a> {
            let weak = weak.clone();
            let ec2 = ec.clone();
            ec.borrow().new_node_visitor(Box::new(move |_v, cx, node| {
                let tx = weak
                    .upgrade()
                    .expect("transformer state dropped during visit");
                f(&tx, &ec2, cx, node)
            }))
        }

        let visitors = CjsVisitors {
            main: make_visitor(&weak, &ec, |t, e, cx, n| t.visit(e, cx, n)),
            top_level: make_visitor(&weak, &ec, |t, e, cx, n| t.visit_top_level(e, cx, n)),
            top_level_nested: make_visitor(&weak, &ec, |t, e, cx, n| {
                t.visit_top_level_nested(e, cx, n)
            }),
            discarded_value: make_visitor(&weak, &ec, |t, e, cx, n| {
                t.visit_discarded_value(e, cx, n)
            }),
            assignment_pattern: make_visitor(&weak, &ec, |t, e, cx, n| {
                t.visit_assignment_pattern(e, cx, n)
            }),
        };
        *tx.visitors.borrow_mut() = Some(visitors);
        Box::new(move |_v, cx, node| tx.visit(&ec, cx, node))
    })
}

/// Runs `f` against the emit-context `printer::NodeFactory` (`tx.Factory()`)
/// without leaking the `RefCell` borrow.
fn fac<R>(
    ec: &Ec,
    nodes: &mut Vec<Node>,
    f: impl FnOnce(&mut tsc_printer::NodeFactory, &mut Vec<Node>) -> R,
) -> R {
    let mut e = ec.borrow_mut();
    f(&mut e.factory, nodes)
}

impl<'a> CommonJsModuleTransformer<'a> {
    /// `tx.pushNode(node)` — returns a guard performing `popNode` on drop.
    fn push_node(&self, node: NodeId) -> PopGuard<'_, 'a> {
        let grandparent = self.parent_node.replace(self.current_node.get());
        self.current_node.set(Some(node));
        PopGuard {
            tx: self,
            grandparent,
        }
    }

    /// `tx.Visitor()` / `tx.topLevelVisitor` / etc.
    fn visitors(&self) -> Ref<'_, CjsVisitors<'a>> {
        Ref::map(self.visitors.borrow(), |v| {
            v.as_ref().expect("sibling visitors not installed")
        })
    }

    fn resolver(&self) -> RefMut<'_, dyn ReferenceResolver + 'a> {
        self.resolver
            .as_ref()
            .expect("opts.Resolver is required by the CommonJS transform")
            .borrow_mut()
    }

    fn symbols(&self) -> RefMut<'_, Vec<Symbol>> {
        self.symbols
            .expect("opts.symbols (the binder symbol arena) is required alongside opts.Resolver")
            .borrow_mut()
    }

    /// `tx.getEmitModuleFormatOfFile(file)` — `file` must be a `SourceFile`.
    fn emit_module_format(&self, cx: &VisitorCx<'_, '_>, file: NodeId) -> ModuleKind {
        (self
            .get_emit_module_format_of_file
            .expect("opts.GetEmitModuleFormatOfFile is required by the module transforms"))(
            cx.nodes[file].as_source_file(),
        )
    }

    fn module_info<R>(&self, f: impl FnOnce(&ExternalModuleInfo) -> R) -> R {
        f(self
            .current_module_info
            .borrow()
            .as_ref()
            .expect("currentModuleInfo is nil outside a source file visit"))
    }

    /// `tx.Visitor().VisitNode(node)` — the main visitor.
    fn main_visit_node(&self, cx: &mut VisitorCx<'_, '_>, node: Option<NodeId>) -> Option<NodeId> {
        self.visitors().main.visit_node(cx, node)
    }

    /// `tx.Visitor().VisitEachChild(node)` — returns `node` when unchanged
    /// (Go returns the input pointer).
    fn main_visit_each_child(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        visit_each_child(&self.visitors().main, cx, node)
    }

    // Visits a node at the top level of the source file.
    fn visit_top_level(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> Option<NodeId> {
        let _guard = self.push_node(node);
        match cx.nodes[node].kind {
            Kind::ImportDeclaration => self.visit_top_level_import_declaration(ec, cx, node),
            Kind::ImportEqualsDeclaration => {
                self.visit_top_level_import_equals_declaration(ec, cx, node)
            }
            Kind::ExportDeclaration => self.visit_top_level_export_declaration(ec, cx, node),
            Kind::ExportAssignment => self.visit_top_level_export_assignment(ec, cx, node),
            Kind::FunctionDeclaration => {
                Some(self.visit_top_level_function_declaration(ec, cx, node))
            }
            Kind::ClassDeclaration => self.visit_top_level_class_declaration(ec, cx, node),
            Kind::VariableStatement => self.visit_top_level_variable_statement(ec, cx, node),
            _ => Some(self.visit_top_level_nested_no_stack(ec, cx, node)),
        }
    }

    /// Visits nested elements at the top-level of a module.
    fn visit_top_level_nested(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let _guard = self.push_node(node);
        Some(self.visit_top_level_nested_no_stack(ec, cx, node))
    }

    /// Visits nested elements at the top-level of a module without ancestor tracking.
    fn visit_top_level_nested_no_stack(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        match cx.nodes[node].kind {
            Kind::VariableStatement => self
                .visit_top_level_variable_statement(ec, cx, node)
                .unwrap_or(node),
            Kind::ForStatement => self.visit_top_level_nested_for_statement(ec, cx, node),
            Kind::ForInStatement | Kind::ForOfStatement => {
                self.visit_top_level_nested_for_in_or_of_statement(ec, cx, node)
            }
            Kind::DoStatement => self.visit_top_level_nested_do_statement(ec, cx, node),
            Kind::WhileStatement => self.visit_top_level_nested_while_statement(ec, cx, node),
            Kind::LabeledStatement => self.visit_top_level_nested_labeled_statement(ec, cx, node),
            Kind::WithStatement => self.visit_top_level_nested_with_statement(ec, cx, node),
            Kind::IfStatement => self.visit_top_level_nested_if_statement(ec, cx, node),
            Kind::SwitchStatement => self.visit_top_level_nested_switch_statement(ec, cx, node),
            Kind::CaseBlock => self.visit_top_level_nested_case_block(cx, node),
            Kind::CaseClause | Kind::DefaultClause => {
                self.visit_top_level_nested_case_or_default_clause(ec, cx, node)
            }
            Kind::TryStatement => self.visit_top_level_nested_try_statement(cx, node),
            Kind::CatchClause => self.visit_top_level_nested_catch_clause(ec, cx, node),
            Kind::Block => self.visit_top_level_nested_block(cx, node),
            _ => self.visit_no_stack(ec, cx, node, false /* resultIsDiscarded */),
        }
    }

    /// Visits source elements that are not top-level or top-level nested statements.
    fn visit(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> Option<NodeId> {
        let _guard = self.push_node(node);
        Some(self.visit_no_stack(ec, cx, node, false /* resultIsDiscarded */))
    }

    /// Visits source elements that are not top-level or top-level nested
    /// statements without ancestor tracking.
    fn visit_no_stack(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        result_is_discarded: bool,
    ) -> NodeId {
        // This visitor does not need to descend into the tree if there are no dynamic imports or identifiers in the subtree
        if !ast::is_source_file(&cx.nodes[node])
            && !subtree_facts(cx, node).intersects(
                SubtreeFacts::CONTAINS_DYNAMIC_IMPORT | SubtreeFacts::CONTAINS_IDENTIFIER,
            )
        {
            return node;
        }

        match cx.nodes[node].kind {
            Kind::SourceFile => self.visit_source_file(ec, cx, node),
            Kind::ForStatement => self.visit_for_statement(ec, cx, node),
            Kind::ForInStatement | Kind::ForOfStatement => {
                self.visit_for_in_or_of_statement(ec, cx, node)
            }
            Kind::ExpressionStatement => self.visit_expression_statement(cx, node),
            Kind::VoidExpression => self.visit_void_expression(cx, node),
            Kind::ParenthesizedExpression => {
                self.visit_parenthesized_expression(ec, cx, node, result_is_discarded)
            }
            Kind::PartiallyEmittedExpression => {
                self.visit_partially_emitted_expression(ec, cx, node, result_is_discarded)
            }
            Kind::CallExpression => self.visit_call_expression(ec, cx, node),
            Kind::TaggedTemplateExpression => self.visit_tagged_template_expression(ec, cx, node),
            Kind::BinaryExpression => {
                self.visit_binary_expression(ec, cx, node, result_is_discarded)
            }
            Kind::PrefixUnaryExpression => {
                self.visit_prefix_unary_expression(ec, cx, node, result_is_discarded)
            }
            Kind::PostfixUnaryExpression => {
                self.visit_postfix_unary_expression(ec, cx, node, result_is_discarded)
            }
            Kind::ShorthandPropertyAssignment => {
                self.visit_shorthand_property_assignment(ec, cx, node)
            }
            Kind::Identifier => self.visit_identifier(ec, cx, node),
            _ => self.main_visit_each_child(cx, node),
        }
    }

    /// Visits source elements whose value is discarded if they are expressions.
    fn visit_discarded_value(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let _guard = self.push_node(node);
        Some(self.visit_no_stack(ec, cx, node, true /* resultIsDiscarded */))
    }

    /// `tx.visitAssignmentPattern`
    fn visit_assignment_pattern(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let _guard = self.push_node(node);
        Some(self.visit_assignment_pattern_no_stack(ec, cx, node))
    }

    /// `tx.visitAssignmentPatternNoStack`
    fn visit_assignment_pattern_no_stack(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        match cx.nodes[node].kind {
            // AssignmentPattern
            Kind::ObjectLiteralExpression | Kind::ArrayLiteralExpression => {
                visit_each_child(&self.visitors().assignment_pattern, cx, node)
            }

            // AssignmentProperty
            Kind::PropertyAssignment => self.visit_assignment_property(ec, cx, node),
            Kind::ShorthandPropertyAssignment => {
                self.visit_shorthand_assignment_property(ec, cx, node)
            }

            // AssignmentRestProperty
            Kind::SpreadAssignment => self.visit_assignment_rest_property(ec, cx, node),

            // AssignmentRestElement
            Kind::SpreadElement => self.visit_assignment_rest_element(ec, cx, node),

            // AssignmentElement
            _ => {
                if ast::is_expression(&cx.nodes[node], cx.nodes) {
                    self.visit_assignment_element(ec, cx, node)
                } else {
                    self.visit_no_stack(ec, cx, node, false /* resultIsDiscarded */)
                }
            }
        }
    }

    /// `tx.visitSourceFile` — `node` must be a `SourceFile`.
    fn visit_source_file(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        let (is_declaration_file, is_effective, has_dynamic_import) = {
            let sf = cx.nodes[node].as_source_file();
            (
                sf.is_declaration_file,
                ast::is_effective_external_module(sf, self.compiler_options),
                subtree_facts(cx, node).intersects(SubtreeFacts::CONTAINS_DYNAMIC_IMPORT),
            )
        };
        if is_declaration_file || !(is_effective || has_dynamic_import) {
            return node;
        }

        self.current_source_file.set(Some(node));
        *self.current_module_info.borrow_mut() = Some(collect_external_module_info(
            node,
            self.compiler_options,
            ec,
            self.resolver.as_ref(),
            self.symbols,
            cx.nodes,
        ));
        let updated = self.transform_common_js_module(ec, cx, node);
        self.current_source_file.set(None);
        *self.current_module_info.borrow_mut() = None;
        updated
    }

    /// `tx.shouldEmitUnderscoreUnderscoreESModule`
    fn should_emit_underscore_underscore_es_module(&self, nodes: &[Node]) -> bool {
        let current_source_file = self
            .current_source_file
            .get()
            .expect("currentSourceFile is nil");
        {
            let sf = nodes[current_source_file].as_source_file();
            if sf
                .file_name()
                .extension_is_one_of(tsc_tspath::SUPPORTED_JS_EXTENSIONS_FLAT)
                && sf.common_js_module_indicator.is_some()
                && sf
                    .external_module_indicator
                    .is_none_or(|i| nodes[i].kind == ast::Kind::SourceFile)
            {
                return false;
            }
        }
        self.module_info(|i| i.export_equals.is_none())
            && ast::is_external_module(nodes[current_source_file].as_source_file())
    }

    /// `tx.createUnderscoreUnderscoreESModule`
    fn create_underscore_underscore_es_module(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
    ) -> NodeId {
        let statement = fac(ec, cx.nodes, |f, nodes| {
            let object_ident = f.new_identifier(nodes, "Object");
            let define_property = f.new_identifier(nodes, "defineProperty");
            let callee = f.new_property_access_expression(
                nodes,
                Some(object_ident),
                None, /* questionDotToken */
                Some(define_property),
                ast::NodeFlags::NONE,
            );
            let exports = f.new_identifier(nodes, "exports");
            let es_module = f.new_string_literal(nodes, "__esModule", ast::TokenFlags::NONE);
            let value_ident = f.new_identifier(nodes, "value");
            let true_expr = f.new_true_expression(nodes);
            let value_assignment = f.new_property_assignment(
                nodes,
                None, /* modifiers */
                Some(value_ident),
                None, /* postfixToken */
                None, /* typeNode */
                Some(true_expr),
            );
            let props_list = f.new_node_list(vec![value_assignment]);
            let object_literal = f.new_object_literal_expression(
                nodes,
                Some(props_list),
                false, /* multiLine */
            );
            let args = f.new_node_list(vec![exports, es_module, object_literal]);
            let call = f.new_call_expression(
                nodes,
                Some(callee),
                None, /* questionDotToken */
                None, /* typeArguments */
                Some(args),
                ast::NodeFlags::NONE,
            );
            f.new_expression_statement(nodes, Some(call))
        });
        ec.borrow()
            .set_emit_flags(statement, EmitFlags::CUSTOM_PROLOGUE);
        statement
    }

    /// `tx.transformCommonJSModule` — `node` must be a `SourceFile`.
    fn transform_common_js_module(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        ec.borrow_mut().start_variable_environment();

        // emit standard prologue directives (e.g. "use strict")
        let (source, statements_loc, end_of_file_token) = {
            let sf = cx.nodes[node].as_source_file();
            (
                sf.statements
                    .as_ref()
                    .map(|l| l.nodes.iter().copied().collect::<Vec<_>>())
                    .unwrap_or_default(),
                sf.statements.as_ref().map(|l| l.loc).unwrap_or_default(),
                sf.end_of_file_token,
            )
        };
        let (prologue, rest) = ec
            .borrow()
            .factory
            .split_standard_prologue(cx.nodes, &source);
        let mut statements: Vec<NodeId> = prologue.to_vec();

        // emit custom prologues from other transformations
        let (custom, rest) = ec.borrow().factory.split_custom_prologue(cx.nodes, rest);
        statements.extend(
            self.visitors()
                .top_level
                .visit_slice(cx, custom)
                .unwrap_or_else(|| custom.to_vec()),
        );

        // emits `Object.defineProperty(exports, "__esModule", { value: true });` at the top of the file
        if self.should_emit_underscore_underscore_es_module(cx.nodes) {
            statements.push(self.create_underscore_underscore_es_module(ec, cx));
        }

        // initialize all exports to `undefined`, e.g.:
        //  exports.a = exports.b = void 0;
        let exported_names = self.module_info(|i| i.exported_names.clone());
        if !exported_names.is_empty() {
            const CHUNK_SIZE: usize = 50;
            for chunk in exported_names.chunks(CHUNK_SIZE) {
                let mut right = fac(ec, cx.nodes, |f, nodes| f.new_void_zero_expression(nodes));
                for &next_id in chunk {
                    let left = if cx.nodes[next_id].kind == Kind::StringLiteral {
                        fac(ec, cx.nodes, |f, nodes| {
                            let exports = f.new_identifier(nodes, "exports");
                            let name = f.new_string_literal_from_node(nodes, next_id);
                            f.new_element_access_expression(
                                nodes,
                                Some(exports),
                                None, /* questionDotToken */
                                Some(name),
                                ast::NodeFlags::NONE,
                            )
                        })
                    } else {
                        let (name, left) = fac(ec, cx.nodes, |f, nodes| {
                            let name = f.clone_node(nodes, next_id);
                            let exports = f.new_identifier(nodes, "exports");
                            let left = f.new_property_access_expression(
                                nodes,
                                Some(exports),
                                None, /* questionDotToken */
                                Some(name),
                                ast::NodeFlags::NONE,
                            );
                            (name, left)
                        });
                        ec.borrow().set_emit_flags(
                            name,
                            EmitFlags::NO_SOURCE_MAP | EmitFlags::NO_COMMENTS,
                        );
                        left
                    };
                    right = fac(ec, cx.nodes, |f, nodes| {
                        f.new_assignment_expression(nodes, left, right)
                    });
                }
                let statement = fac(ec, cx.nodes, |f, nodes| {
                    f.new_expression_statement(nodes, Some(right))
                });
                ec.borrow()
                    .add_emit_flags(statement, EmitFlags::CUSTOM_PROLOGUE);
                statements.push(statement);
            }
        }

        // initialize exports for function declarations, e.g.:
        //  exports.f = f;
        //  function f() {}
        // These are marked as custom prologue so they are ordered before the external helpers
        // import declaration (e.g., `const tslib_1 = require("tslib")`), matching TypeScript's emit order.
        let exported_functions_start = statements.len();
        let exported_functions =
            self.module_info(|i| i.exported_functions.values().copied().collect::<Vec<_>>());
        for func in exported_functions {
            statements =
                self.append_exports_of_class_or_function_declaration(ec, cx, statements, func);
        }
        for &s in &statements[exported_functions_start..] {
            ec.borrow().add_emit_flags(s, EmitFlags::CUSTOM_PROLOGUE);
        }

        // visit the remaining statements in the source file
        statements.extend(
            self.visitors()
                .top_level
                .visit_slice(cx, rest)
                .unwrap_or_else(|| rest.to_vec()),
        );

        // emit `module.exports = ...` if needed
        statements = self.append_export_equals_if_needed(ec, cx, statements);

        // merge temp variables into the statement list
        statements = ec
            .borrow_mut()
            .end_and_merge_variable_environment(cx.nodes, &statements);

        let mut result = {
            let mut e = ec.borrow_mut();
            let mut statement_list = e.factory.new_node_list(statements);
            statement_list.loc = statements_loc;
            e.factory
                .update_source_file(cx.nodes, node, Some(statement_list), end_of_file_token)
                .unwrap_or(node)
        };
        let helpers = ec.borrow_mut().read_emit_helpers();
        ec.borrow().add_emit_helper(result, &helpers);

        let external_helpers_import_declaration = {
            let file_module_kind = self.emit_module_format(cx, node);
            create_external_helpers_import_declaration_if_needed(
                &mut ec.borrow_mut(),
                cx.nodes,
                result,
                self.compiler_options,
                file_module_kind,
                false, /* hasExportStarsToExportValues */
                false, /* hasImportStar */
                false, /* hasImportDefault */
            )
        };
        if let Some(decl) = external_helpers_import_declaration {
            let (source, statements_loc) = {
                let sf = cx.nodes[result].as_source_file();
                (
                    sf.statements
                        .as_ref()
                        .map(|l| l.nodes.iter().copied().collect::<Vec<_>>())
                        .unwrap_or_default(),
                    sf.statements.as_ref().map(|l| l.loc).unwrap_or_default(),
                )
            };
            let (prologue, rest) = ec
                .borrow()
                .factory
                .split_standard_prologue(cx.nodes, &source);
            let (custom, rest) = ec.borrow().factory.split_custom_prologue(cx.nodes, rest);
            let mut statements: Vec<NodeId> = prologue.to_vec();
            statements.extend_from_slice(custom);
            if let Some(visited) = self.visitors().top_level.visit_node(cx, Some(decl)) {
                statements.push(visited);
            }
            statements.extend_from_slice(rest);
            result = {
                let mut e = ec.borrow_mut();
                let mut statement_list = e.factory.new_node_list(statements);
                statement_list.loc = statements_loc;
                e.factory
                    .update_source_file(cx.nodes, result, Some(statement_list), end_of_file_token)
                    .unwrap_or(result)
            };
        }

        result
    }

    /// Adds the down-level representation of `export=` to the statement list
    /// if one exists in the source file.
    fn append_export_equals_if_needed(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut statements: Vec<NodeId>,
    ) -> Vec<NodeId> {
        let export_equals = self.module_info(|i| i.export_equals);
        if let Some(export_equals) = export_equals {
            if let Some(expression_result) = self.visit_export_equals(cx, export_equals) {
                let statement = fac(ec, cx.nodes, |f, nodes| {
                    let module = f.new_identifier(nodes, "module");
                    let exports = f.new_identifier(nodes, "exports");
                    let left = f.new_property_access_expression(
                        nodes,
                        Some(module),
                        None, /* questionDotToken */
                        Some(exports),
                        ast::NodeFlags::NONE,
                    );
                    let assignment = f.new_assignment_expression(nodes, left, expression_result);
                    f.new_expression_statement(nodes, Some(assignment))
                });
                ec.borrow().assign_comment_and_source_map_ranges(
                    cx.nodes,
                    statement,
                    export_equals,
                );
                ec.borrow()
                    .add_emit_flags(statement, EmitFlags::NO_COMMENTS);
                statements.push(statement);
            }
        }
        statements
    }

    /// `tx.visitExportEquals` — `node` must be an `ExportAssignment`.
    fn visit_export_equals(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> Option<NodeId> {
        let _guard = self.push_node(node);
        let expression = cx.nodes[node].as_export_assignment().expression;
        self.main_visit_node(cx, expression)
    }

    /// Appends the exports of an ImportDeclaration to a statement list.
    fn append_exports_of_import_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut statements: Vec<NodeId>,
        decl: NodeId,
    ) -> Vec<NodeId> {
        if self.module_info(|i| i.export_equals.is_some()) {
            return statements;
        }

        let Some(import_clause) = cx.nodes[decl].as_import_declaration().import_clause else {
            return statements;
        };

        let mut seen: Set<String> = Set::default();
        if cx.nodes[import_clause].name().is_some() {
            statements = self.append_exports_of_declaration(
                ec,
                cx,
                statements,
                import_clause,
                Some(&mut seen),
                false, /* liveBinding */
            );
        }

        if let Some(named_bindings) = cx.nodes[import_clause].as_import_clause().named_bindings {
            match cx.nodes[named_bindings].kind {
                Kind::NamespaceImport => {
                    statements = self.append_exports_of_declaration(
                        ec,
                        cx,
                        statements,
                        named_bindings,
                        Some(&mut seen),
                        false, /* liveBinding */
                    );
                }
                Kind::NamedImports => {
                    let elements: Vec<NodeId> = cx.nodes[named_bindings]
                        .elements()
                        .map(|e| e.to_vec())
                        .unwrap_or_default();
                    for import_binding in elements {
                        statements = self.append_exports_of_declaration(
                            ec,
                            cx,
                            statements,
                            import_binding,
                            Some(&mut seen),
                            true, /* liveBinding */
                        );
                    }
                }
                _ => {}
            }
        }

        statements
    }

    /// Appends the exports of a VariableStatement to a statement list.
    fn append_exports_of_variable_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        statements: Vec<NodeId>,
        node: NodeId,
    ) -> Vec<NodeId> {
        let Some(declaration_list) = cx.nodes[node].as_variable_statement().declaration_list else {
            return statements;
        };
        self.append_exports_of_variable_declaration_list(
            ec,
            cx,
            statements,
            declaration_list,
            false, /* isForInOrOfInitializer */
        )
    }

    /// Appends the exports of a VariableDeclarationList to a statement list.
    fn append_exports_of_variable_declaration_list(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut statements: Vec<NodeId>,
        node: NodeId,
        is_for_in_or_of_initializer: bool,
    ) -> Vec<NodeId> {
        if self.module_info(|i| i.export_equals.is_some()) {
            return statements;
        }

        let declarations: Vec<NodeId> = cx.nodes[node]
            .as_variable_declaration_list()
            .declarations
            .as_ref()
            .map(|d| d.nodes.iter().copied().collect())
            .unwrap_or_default();
        for decl in declarations {
            statements = self.append_exports_of_binding_element(
                ec,
                cx,
                statements,
                decl,
                is_for_in_or_of_initializer,
            );
        }

        statements
    }

    /// Appends the exports of a VariableDeclaration or BindingElement to a
    /// statement list.
    fn append_exports_of_binding_element(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut statements: Vec<NodeId>,
        decl: NodeId, /* VariableDeclaration | BindingElement */
        is_for_in_or_of_initializer: bool,
    ) -> Vec<NodeId> {
        let Some(name) = cx.nodes[decl].name() else {
            return statements;
        };
        if self.module_info(|i| i.export_equals.is_some()) {
            return statements;
        }

        if ast::is_binding_pattern(&cx.nodes[name]) {
            let elements: Vec<NodeId> = cx.nodes[name]
                .elements()
                .map(|e| e.to_vec())
                .unwrap_or_default();
            for element in elements {
                if !ast::is_omitted_expression(&cx.nodes[element]) {
                    statements = self.append_exports_of_binding_element(
                        ec,
                        cx,
                        statements,
                        element,
                        is_for_in_or_of_initializer,
                    );
                }
            }
        } else if !is_generated_identifier(&ec.borrow(), name)
            && (!ast::is_variable_declaration(&cx.nodes[decl])
                || cx.nodes[decl].initializer().is_some()
                || is_for_in_or_of_initializer)
        {
            statements = self.append_exports_of_declaration(
                ec, cx, statements, decl, None,  /* seen */
                false, /* liveBinding */
            );
        }

        statements
    }

    /// Appends the exports of a ClassDeclaration or FunctionDeclaration to a
    /// statement list.
    fn append_exports_of_class_or_function_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut statements: Vec<NodeId>,
        decl: NodeId,
    ) -> Vec<NodeId> {
        if self.module_info(|i| i.export_equals.is_some()) {
            return statements;
        }

        let mut seen: Set<String> = Set::default();
        if ast::has_syntactic_modifier(&cx.nodes[decl], ast::ModifierFlags::EXPORT) {
            let has_default =
                ast::has_syntactic_modifier(&cx.nodes[decl], ast::ModifierFlags::DEFAULT);
            let decl_loc = cx.nodes[decl].loc;
            let (export_name, export_value) = fac(ec, cx.nodes, |f, nodes| {
                let export_name = if has_default {
                    f.new_identifier(nodes, "default")
                } else {
                    f.get_declaration_name(nodes, Some(decl))
                };
                let export_value = f.get_local_name(nodes, Some(decl));
                (export_name, export_value)
            });
            statements = self.append_export_statement(
                ec,
                cx,
                statements,
                &mut seen,
                export_name,
                export_value,
                Some(&decl_loc),
                false, /* allowComments */
                false, /* liveBinding */
            );
        }

        if cx.nodes[decl].name().is_some() {
            return self.append_exports_of_declaration(
                ec,
                cx,
                statements,
                decl,
                Some(&mut seen),
                false, /* liveBinding */
            );
        }

        statements
    }

    /// Appends the exports of a declaration to a statement list.
    fn append_exports_of_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut statements: Vec<NodeId>,
        decl: NodeId,
        seen: Option<&mut Set<String>>,
        live_binding: bool,
    ) -> Vec<NodeId> {
        if self.module_info(|i| i.export_equals.is_some()) {
            return statements;
        }

        let mut owned_seen = Set::default();
        let seen: &mut Set<String> = match seen {
            Some(s) => s,
            None => &mut owned_seen,
        };

        let has_export_specifiers = self.module_info(|i| !i.export_specifiers.is_empty());
        if let Some(name) = cx.nodes[decl].name()
            && has_export_specifiers
            && ast::is_identifier(&cx.nodes[name])
        {
            let name = fac(ec, cx.nodes, |f, nodes| {
                f.get_declaration_name(nodes, Some(decl))
            });
            let name_text = cx.nodes[name].text(cx.nodes).into_owned();
            let export_specifiers =
                self.module_info(|i| i.export_specifiers.get(&name_text).to_vec());
            if !export_specifiers.is_empty() {
                let export_value = self.visit_expression_identifier(ec, cx, name);
                for export_specifier in export_specifiers {
                    let specifier_name = cx.nodes[export_specifier].name();
                    let specifier_loc = specifier_name.map(|n| cx.nodes[n].loc);
                    statements = self.append_export_statement(
                        ec,
                        cx,
                        statements,
                        seen,
                        specifier_name.expect("export specifier has no name"),
                        export_value,
                        specifier_loc.as_ref(),
                        false, /* allowComments */
                        live_binding,
                    );
                }
            }
        }

        statements
    }

    /// Appends the down-level representation of an export to a statement list.
    #[allow(clippy::too_many_arguments)]
    fn append_export_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut statements: Vec<NodeId>,
        seen: &mut Set<String>,
        export_name: NodeId, /* ModuleExportName */
        expression: NodeId,
        location: Option<&TextRange>,
        allow_comments: bool,
        live_binding: bool,
    ) -> Vec<NodeId> {
        if cx.nodes[export_name].kind != Kind::StringLiteral {
            let text = cx.nodes[export_name].text(cx.nodes).into_owned();
            if seen.has(&text) {
                return statements;
            }
            seen.add(text);
        }
        statements.push(self.create_export_statement(
            ec,
            cx,
            export_name,
            expression,
            location,
            allow_comments,
            live_binding,
        ));
        statements
    }

    /// Creates a call to the current file's export function to export a value.
    fn create_export_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId, /* ModuleExportName */
        value: NodeId,
        location: Option<&TextRange>,
        allow_comments: bool,
        live_binding: bool,
    ) -> NodeId {
        let statement = {
            let expression = self.create_export_expression(ec, cx, name, value, None, live_binding);
            fac(ec, cx.nodes, |f, nodes| {
                f.new_expression_statement(nodes, Some(expression))
            })
        };
        if let Some(location) = location {
            ec.borrow().set_comment_range(statement, *location);
        }
        ec.borrow()
            .add_emit_flags(statement, EmitFlags::START_ON_NEW_LINE);
        if !allow_comments {
            ec.borrow()
                .add_emit_flags(statement, EmitFlags::NO_COMMENTS);
        }
        statement
    }

    /// Creates a call to the current file's export function to export a value.
    fn create_export_expression(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId, /* ModuleExportName */
        value: NodeId,
        location: Option<&TextRange>,
        live_binding: bool,
    ) -> NodeId {
        let expression = if live_binding {
            // For a live binding we emit a getter on `exports` that returns the value:
            //  Object.defineProperty(exports, "<name>", { enumerable: true, get: function () { return <value>; } });
            fac(ec, cx.nodes, |f, nodes| {
                let object_ident = f.new_identifier(nodes, "Object");
                let define_property = f.new_identifier(nodes, "defineProperty");
                let callee = f.new_property_access_expression(
                    nodes,
                    Some(object_ident),
                    None, /* questionDotToken */
                    Some(define_property),
                    ast::NodeFlags::NONE,
                );
                let exports = f.new_identifier(nodes, "exports");
                let name_literal = f.new_string_literal_from_node(nodes, name);
                let enumerable_ident = f.new_identifier(nodes, "enumerable");
                let true_expr = f.new_true_expression(nodes);
                let enumerable_prop = f.new_property_assignment(
                    nodes,
                    None, /* modifiers */
                    Some(enumerable_ident),
                    None, /* postfixToken */
                    None, /* typeNode */
                    Some(true_expr),
                );
                let get_ident = f.new_identifier(nodes, "get");
                let return_stmt = f.new_return_statement(nodes, Some(value));
                let block_stmts = f.new_node_list(vec![return_stmt]);
                let block = f.new_block(nodes, Some(block_stmts), false /* multiLine */);
                let params = f.new_node_list(vec![]);
                let function = f.new_function_expression(
                    nodes,
                    None, /* modifiers */
                    None, /* asteriskToken */
                    None, /* name */
                    None, /* typeParameters */
                    Some(params),
                    None, /* type */
                    None, /* fullSignature */
                    Some(block),
                );
                let get_prop = f.new_property_assignment(
                    nodes,
                    None, /* modifiers */
                    Some(get_ident),
                    None, /* postfixToken */
                    None, /* typeNode */
                    Some(function),
                );
                let props = f.new_node_list(vec![enumerable_prop, get_prop]);
                let object_literal =
                    f.new_object_literal_expression(nodes, Some(props), false /* multiLine */);
                let args = f.new_node_list(vec![exports, name_literal, object_literal]);
                f.new_call_expression(
                    nodes,
                    Some(callee),
                    None, /* questionDotToken */
                    None, /* typeArguments */
                    Some(args),
                    ast::NodeFlags::NONE,
                )
            })
        } else {
            // Otherwise, we emit a simple property assignment.
            let name_is_string_literal = cx.nodes[name].kind == Kind::StringLiteral;
            let left = fac(ec, cx.nodes, |f, nodes| {
                if name_is_string_literal {
                    // emits:
                    //  exports["<name>"] = <value>;
                    let exports = f.new_identifier(nodes, "exports");
                    let name_literal = f.new_string_literal_from_node(nodes, name);
                    f.new_element_access_expression(
                        nodes,
                        Some(exports),
                        None, /* questionDotToken */
                        Some(name_literal),
                        ast::NodeFlags::NONE,
                    )
                } else {
                    // emits:
                    //  exports.<name> = <value>;
                    let exports = f.new_identifier(nodes, "exports");
                    let name = f.clone_node(nodes, name);
                    f.new_property_access_expression(
                        nodes,
                        Some(exports),
                        None, /* questionDotToken */
                        Some(name),
                        ast::NodeFlags::NONE,
                    )
                }
            });
            fac(ec, cx.nodes, |f, nodes| {
                f.new_assignment_expression(nodes, left, value)
            })
        };
        if let Some(location) = location {
            ec.borrow().set_comment_range(expression, *location);
        }
        expression
    }

    /// Creates a `require()` call to import an external module.
    /// `node` must be an `ImportDeclaration`, `ImportEqualsDeclaration`, or
    /// `ExportDeclaration`.
    fn create_require_call(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        let mut args: Vec<NodeId> = Vec::new();
        let module_name = fac(ec, cx.nodes, |f, nodes| {
            get_external_module_name_literal(
                f,
                nodes,
                node,
                self.current_source_file.get(),
                None, /* host */
                None, /* resolver */
                self.compiler_options,
            )
        });
        if let Some(module_name) = module_name {
            if let Some(rewritten) = rewrite_module_specifier(
                &mut ec.borrow_mut(),
                cx.nodes,
                Some(module_name),
                self.compiler_options,
            ) {
                args.push(rewritten);
            }
        }
        fac(ec, cx.nodes, |f, nodes| {
            let require = f.new_identifier(nodes, "require");
            let arg_list = f.new_node_list(args);
            f.new_call_expression(
                nodes,
                Some(require),
                None, /* questionDotToken */
                None, /* typeArguments */
                Some(arg_list),
                ast::NodeFlags::NONE,
            )
        })
    }

    /// `tx.getHelperExpressionForExport` — `node` must be an
    /// `ExportDeclaration`.
    fn get_helper_expression_for_export(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        inner_expr: NodeId,
    ) -> NodeId {
        if get_export_needs_import_star_helper(cx.nodes, node) {
            let helper = fac(ec, cx.nodes, |f, nodes| {
                f.new_import_star_helper(nodes, inner_expr)
            });
            return self
                .main_visit_node(cx, Some(helper))
                .expect("visitor returned nil for ImportStarHelper");
        }
        inner_expr
    }

    /// `tx.getHelperExpressionForImport` — `node` must be an
    /// `ImportDeclaration`.
    fn get_helper_expression_for_import(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        inner_expr: NodeId,
    ) -> NodeId {
        if get_import_needs_import_star_helper(cx.nodes, node) {
            let helper = fac(ec, cx.nodes, |f, nodes| {
                f.new_import_star_helper(nodes, inner_expr)
            });
            return self
                .main_visit_node(cx, Some(helper))
                .expect("visitor returned nil for ImportStarHelper");
        }
        if get_import_needs_import_default_helper(cx.nodes, node) {
            let helper = fac(ec, cx.nodes, |f, nodes| {
                f.new_import_default_helper(nodes, inner_expr)
            });
            return self
                .main_visit_node(cx, Some(helper))
                .expect("visitor returned nil for ImportDefaultHelper");
        }
        inner_expr
    }

    /// `tx.visitTopLevelImportDeclaration` — `node` must be an
    /// `ImportDeclaration`.
    fn visit_top_level_import_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if cx.nodes[node]
            .as_import_declaration()
            .import_clause
            .is_none()
        {
            // import "mod";
            let require = self.create_require_call(ec, cx, node);
            let statement = fac(ec, cx.nodes, |f, nodes| {
                f.new_expression_statement(nodes, Some(require))
            });
            ec.borrow().set_original(statement, node);
            ec.borrow()
                .assign_comment_and_source_map_ranges(cx.nodes, statement, node);
            return Some(statement);
        }

        let mut statements: Vec<NodeId> = Vec::new();
        let mut variables: Vec<NodeId> = Vec::new();
        let namespace_declaration = ast::get_namespace_declaration_node(&cx.nodes[node], cx.nodes);
        if namespace_declaration.is_some() && !ast::is_default_import(&cx.nodes[node], cx.nodes) {
            // import * as n from "mod";
            let namespace_name = cx.nodes[namespace_declaration.unwrap()].name();
            let require_call = self.create_require_call(ec, cx, node);
            let initializer = self.get_helper_expression_for_import(ec, cx, node, require_call);
            variables.push(fac(ec, cx.nodes, |f, nodes| {
                let name = namespace_name.map(|n| f.clone_node(nodes, n));
                f.new_variable_declaration(
                    nodes,
                    name,
                    None, /* exclamationToken */
                    None, /* type */
                    Some(initializer),
                )
            }));
        } else {
            // import d from "mod";
            // import { x, y } from "mod";
            // import d, { x, y } from "mod";
            // import d, * as n from "mod";
            let require_call = self.create_require_call(ec, cx, node);
            let initializer = self.get_helper_expression_for_import(ec, cx, node, require_call);
            variables.push(fac(ec, cx.nodes, |f, nodes| {
                let generated = f.new_generated_name_for_node(nodes, node);
                f.new_variable_declaration(
                    nodes,
                    Some(generated),
                    None, /* exclamationToken */
                    None, /* type */
                    Some(initializer),
                )
            }));

            if namespace_declaration.is_some() && ast::is_default_import(&cx.nodes[node], cx.nodes)
            {
                let namespace_name = cx.nodes[namespace_declaration.unwrap()].name();
                variables.push(fac(ec, cx.nodes, |f, nodes| {
                    let name = namespace_name.map(|n| f.clone_node(nodes, n));
                    let generated = f.new_generated_name_for_node(nodes, node);
                    f.new_variable_declaration(
                        nodes,
                        name,
                        None, /* exclamationToken */
                        None, /* type */
                        Some(generated),
                    )
                }));
            }
        }

        let var_statement = fac(ec, cx.nodes, |f, nodes| {
            let decl_list = f.new_node_list(variables);
            let decl_list =
                f.new_variable_declaration_list(nodes, Some(decl_list), ast::NodeFlags::CONST);
            f.new_variable_statement(nodes, None /* modifiers */, Some(decl_list))
        });
        ec.borrow().set_original(var_statement, node);
        ec.borrow()
            .assign_comment_and_source_map_ranges(cx.nodes, var_statement, node);
        statements.push(var_statement);
        statements = self.append_exports_of_import_declaration(ec, cx, statements, node);
        fac(ec, cx.nodes, |f, nodes| {
            single_or_many(f, nodes, Some(statements))
        })
    }

    /// `tx.visitTopLevelImportEqualsDeclaration` — `node` must be an
    /// `ImportEqualsDeclaration`.
    fn visit_top_level_import_equals_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if !ast::is_external_module_import_equals_declaration(&cx.nodes[node], cx.nodes) {
            // import m = n;
            panic!(
                "import= for internal module references should be handled in an earlier transformer."
            )
        }

        let mut statements: Vec<NodeId> = Vec::new();
        if ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::EXPORT) {
            // export import m = require("mod");
            let require = self.create_require_call(ec, cx, node);
            let node_loc = cx.nodes[node].loc;
            let statement = {
                let expression = self.create_export_expression(
                    ec,
                    cx,
                    cx.nodes[node]
                        .name()
                        .expect("import equals declaration has no name"),
                    require,
                    Some(&node_loc),
                    false, /* liveBinding */
                );
                fac(ec, cx.nodes, |f, nodes| {
                    f.new_expression_statement(nodes, Some(expression))
                })
            };
            ec.borrow().set_original(statement, node);
            ec.borrow()
                .assign_comment_and_source_map_ranges(cx.nodes, statement, node);
            statements.push(statement);
        } else {
            // import m = require("mod");
            let name = cx.nodes[node].name();
            let require = self.create_require_call(ec, cx, node);
            let statement = fac(ec, cx.nodes, |f, nodes| {
                let name = name.map(|n| f.clone_node(nodes, n));
                let var_decl = f.new_variable_declaration(
                    nodes,
                    name,
                    None, /* exclamationToken */
                    None, /* typeNode */
                    Some(require),
                );
                let decl_list = f.new_node_list(vec![var_decl]);
                let decl_list =
                    f.new_variable_declaration_list(nodes, Some(decl_list), ast::NodeFlags::CONST);
                f.new_variable_statement(nodes, None /* modifiers */, Some(decl_list))
            });
            ec.borrow().set_original(statement, node);
            ec.borrow()
                .assign_comment_and_source_map_ranges(cx.nodes, statement, node);
            statements.push(statement);
        }

        statements = self.append_exports_of_declaration(
            ec, cx, statements, node, None,  /* seen */
            false, /* liveBinding */
        );
        fac(ec, cx.nodes, |f, nodes| {
            single_or_many(f, nodes, Some(statements))
        })
    }

    /// `tx.visitTopLevelExportDeclaration` — `node` must be an
    /// `ExportDeclaration`.
    fn visit_top_level_export_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let (export_clause, _module_specifier) = {
            let d = cx.nodes[node].as_export_declaration();
            (d.export_clause, d.module_specifier)
        };
        if _module_specifier.is_none() {
            // Elide export declarations with no module specifier as they are handled
            // elsewhere.
            return None;
        }

        if export_clause.is_some() && ast::is_named_exports(&cx.nodes[export_clause.unwrap()]) {
            // export { x, y } from "mod";
            let mut statements: Vec<NodeId> = Vec::new();
            let require = self.create_require_call(ec, cx, node);
            let generated_name = fac(ec, cx.nodes, |f, nodes| {
                let generated = f.new_generated_name_for_node(nodes, node);
                let var_decl = f.new_variable_declaration(
                    nodes,
                    Some(generated),
                    None, /* exclamationToken */
                    None, /* type */
                    Some(require),
                );
                let decl_list = f.new_node_list(vec![var_decl]);
                let decl_list =
                    f.new_variable_declaration_list(nodes, Some(decl_list), ast::NodeFlags::NONE);
                let var_statement =
                    f.new_variable_statement(nodes, None /* modifiers */, Some(decl_list));
                (generated, var_statement)
            });
            let (generated_name, var_statement) = generated_name;
            ec.borrow().set_original(var_statement, node);
            ec.borrow()
                .assign_comment_and_source_map_ranges(cx.nodes, var_statement, node);
            statements.push(var_statement);

            let elements: Vec<NodeId> = cx.nodes[export_clause.unwrap()]
                .elements()
                .map(|e| e.to_vec())
                .unwrap_or_default();
            for specifier in elements {
                let specifier_name = cx.nodes[specifier]
                    .property_name_or_name()
                    .expect("export specifier has no name");
                let export_needs_import_default =
                    ast::module_export_name_is_default(&cx.nodes[specifier_name], cx.nodes);

                let target = if export_needs_import_default {
                    fac(ec, cx.nodes, |f, nodes| {
                        f.new_import_default_helper(nodes, generated_name)
                    })
                } else {
                    generated_name
                };

                let specifier_name_node = cx.nodes[specifier].name();
                let export_name =
                    if specifier_name_node.is_some_and(|n| ast::is_string_literal(&cx.nodes[n])) {
                        fac(ec, cx.nodes, |f, nodes| {
                            f.new_string_literal_from_node(nodes, specifier_name_node.unwrap())
                        })
                    } else {
                        fac(ec, cx.nodes, |f, nodes| {
                            f.get_export_name(nodes, Some(specifier))
                        })
                    };

                let exported_value = if ast::is_string_literal(&cx.nodes[specifier_name]) {
                    fac(ec, cx.nodes, |f, nodes| {
                        f.new_element_access_expression(
                            nodes,
                            Some(target),
                            None, /* questionDotToken */
                            Some(specifier_name),
                            ast::NodeFlags::NONE,
                        )
                    })
                } else {
                    fac(ec, cx.nodes, |f, nodes| {
                        f.new_property_access_expression(
                            nodes,
                            Some(target),
                            None, /* questionDotToken */
                            Some(specifier_name),
                            ast::NodeFlags::NONE,
                        )
                    })
                };
                let statement = {
                    let expression = self.create_export_expression(
                        ec,
                        cx,
                        export_name,
                        exported_value,
                        None, /* location */
                        true, /* liveBinding */
                    );
                    fac(ec, cx.nodes, |f, nodes| {
                        f.new_expression_statement(nodes, Some(expression))
                    })
                };
                ec.borrow().set_original(statement, specifier);
                ec.borrow()
                    .assign_comment_and_source_map_ranges(cx.nodes, statement, specifier);
                statements.push(statement);
            }

            return fac(ec, cx.nodes, |f, nodes| {
                single_or_many(f, nodes, Some(statements))
            });
        }

        if let Some(export_clause) = export_clause {
            // export * as ns from "mod";
            // export * as default from "mod";
            let clause_name = cx.nodes[export_clause].name().unwrap();
            let export_name = if ast::is_string_literal(&cx.nodes[clause_name]) {
                fac(ec, cx.nodes, |f, nodes| {
                    f.new_string_literal_from_node(nodes, clause_name)
                })
            } else {
                fac(ec, cx.nodes, |f, nodes| f.clone_node(nodes, clause_name))
            };
            let require = self.create_require_call(ec, cx, node);
            let inner = self.get_helper_expression_for_export(ec, cx, node, require);
            let statement = {
                let expression = self.create_export_expression(
                    ec,
                    cx,
                    export_name,
                    inner,
                    None,  /* location */
                    false, /* liveBinding */
                );
                fac(ec, cx.nodes, |f, nodes| {
                    f.new_expression_statement(nodes, Some(expression))
                })
            };
            ec.borrow().set_original(statement, node);
            ec.borrow()
                .assign_comment_and_source_map_ranges(cx.nodes, statement, node);
            return Some(statement);
        }

        // export * from "mod";
        let statement = {
            let inner = {
                let require = self.create_require_call(ec, cx, node);
                let helper = fac(ec, cx.nodes, |f, nodes| {
                    let exports = f.new_identifier(nodes, "exports");
                    f.new_export_star_helper(nodes, require, exports)
                });
                self.main_visit_node(cx, Some(helper))
                    .expect("visitor returned nil for ExportStarHelper")
            };
            fac(ec, cx.nodes, |f, nodes| {
                f.new_expression_statement(nodes, Some(inner))
            })
        };
        ec.borrow().set_original(statement, node);
        ec.borrow()
            .assign_comment_and_source_map_ranges(cx.nodes, statement, node);
        Some(statement)
    }

    /// `tx.visitTopLevelExportAssignment` — `node` must be an
    /// `ExportAssignment`.
    fn visit_top_level_export_assignment(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let (is_export_equals, expression) = {
            let d = cx.nodes[node].as_export_assignment();
            (d.is_export_equals, d.expression)
        };
        if is_export_equals {
            return None;
        }

        let node_loc = cx.nodes[node].loc;
        let default_name = fac(ec, cx.nodes, |f, nodes| f.new_identifier(nodes, "default"));
        let expression = self
            .main_visit_node(cx, expression)
            .expect("visitor returned nil for export assignment expression");
        Some(self.create_export_statement(
            ec,
            cx,
            default_name,
            expression,
            Some(&node_loc),
            true,  /* allowComments */
            false, /* liveBinding */
        ))
    }

    /// `tx.visitTopLevelFunctionDeclaration` — `node` must be a
    /// `FunctionDeclaration`.
    fn visit_top_level_function_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::EXPORT) {
            let (asterisk_token, parameters, body) = {
                let d = cx.nodes[node].as_function_declaration();
                (
                    d.function_like_with_body_base.body_base.asterisk_token,
                    d.function_like_with_body_base
                        .function_like_base
                        .parameters
                        .clone(),
                    d.function_like_with_body_base.body_base.body,
                )
            };
            let node_modifiers = cx.nodes[node].modifiers().cloned();
            let modifiers = extract_modifiers(
                Some(ec),
                cx.nodes,
                node_modifiers,
                !ast::ModifierFlags::EXPORT_DEFAULT,
            );
            let name = fac(ec, cx.nodes, |f, nodes| {
                f.get_declaration_name(nodes, Some(node))
            });
            let parameters = self.main_visit_nodes(cx, parameters);
            let body = self.main_visit_node(cx, body);
            fac(ec, cx.nodes, |f, nodes| {
                f.update_function_declaration(
                    nodes,
                    node,
                    modifiers,
                    asterisk_token,
                    Some(name),
                    None, /* typeParameters */
                    parameters,
                    None, /* type */
                    None, /* fullSignature */
                    body,
                )
                .unwrap_or(node)
            })
        } else {
            self.main_visit_each_child(cx, node)
        }
    }

    /// `tx.Visitor().VisitNodes(list)`
    fn main_visit_nodes(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        nodes: Option<tsc_ast::NodeList>,
    ) -> Option<tsc_ast::NodeList> {
        self.visitors().main.visit_nodes(cx, nodes)
    }

    /// `tx.visitTopLevelClassDeclaration` — `node` must be a
    /// `ClassDeclaration`.
    fn visit_top_level_class_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let mut statements: Vec<NodeId> = Vec::new();
        if ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::EXPORT) {
            let (heritage_clauses, members) = {
                let d = cx.nodes[node].as_class_declaration();
                (
                    d.class_like_base.heritage_clauses.clone(),
                    d.class_like_base.members.clone(),
                )
            };
            let node_modifiers = cx.nodes[node].modifiers().cloned();
            let extracted = extract_modifiers(
                Some(ec),
                cx.nodes,
                node_modifiers,
                !ast::ModifierFlags::EXPORT_DEFAULT,
            );
            let modifiers = self.visitors().main.visit_modifiers(cx, extracted);
            let name = fac(ec, cx.nodes, |f, nodes| {
                f.get_declaration_name(nodes, Some(node))
            });
            let heritage_clauses = self.main_visit_nodes(cx, heritage_clauses);
            let members = self.main_visit_nodes(cx, members);
            statements.push(fac(ec, cx.nodes, |f, nodes| {
                f.update_class_declaration(
                    nodes,
                    node,
                    modifiers,
                    Some(name),
                    None, /* typeParameters */
                    heritage_clauses,
                    members,
                )
                .unwrap_or(node)
            }));
        } else {
            statements.push(self.main_visit_each_child(cx, node));
        }
        statements = self.append_exports_of_class_or_function_declaration(ec, cx, statements, node);
        fac(ec, cx.nodes, |f, nodes| {
            single_or_many(f, nodes, Some(statements))
        })
    }

    /// `tx.visitTopLevelVariableStatement` — `node` must be a
    /// `VariableStatement`.
    fn visit_top_level_variable_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::EXPORT) {
            // export var a = b;
            let mut statements: Vec<NodeId> = Vec::new();
            let mut variables: Vec<NodeId> = Vec::new();
            let mut expressions: Vec<NodeId> = Vec::new();
            let mut modifiers: Option<tsc_ast::ModifierList> = None;

            let declaration_list = cx.nodes[node].as_variable_statement().declaration_list;
            let declaration_flags = declaration_list
                .map(|d| cx.nodes[d].flags)
                .unwrap_or_default();

            // `commitPendingVariables` / `commitPendingExpressions` are
            // expanded inline: as free closures they would capture `cx`
            // mutably for their entire lifetime, blocking the `cx` uses
            // inside the loop below.
            macro_rules! commit_pending_variables {
                () => {
                    if !variables.is_empty() {
                        let statement = fac(ec, cx.nodes, |f, nodes| {
                            let variable_list = f.new_node_list(std::mem::take(&mut variables));
                            let declaration_list = declaration_list.map(|d| {
                                f.update_variable_declaration_list(
                                    nodes,
                                    d,
                                    Some(variable_list),
                                    declaration_flags,
                                )
                                .unwrap_or(d)
                            });
                            f.update_variable_statement(
                                nodes,
                                node,
                                modifiers.clone(),
                                declaration_list,
                            )
                            .unwrap_or(node)
                        });
                        if !statements.is_empty() {
                            ec.borrow()
                                .add_emit_flags(statement, EmitFlags::NO_COMMENTS);
                        }
                        statements.push(statement);
                    }
                };
            }

            macro_rules! commit_pending_expressions {
                () => {
                    if !expressions.is_empty() {
                        let statement = {
                            let expression = fac(ec, cx.nodes, |f, nodes| {
                                f.inline_expressions(nodes, &expressions)
                                    .expect("InlineExpressions with non-empty input")
                            });
                            fac(ec, cx.nodes, |f, nodes| {
                                f.new_expression_statement(nodes, Some(expression))
                            })
                        };
                        ec.borrow()
                            .assign_comment_and_source_map_ranges(cx.nodes, statement, node);
                        if !statements.is_empty() {
                            ec.borrow()
                                .add_emit_flags(statement, EmitFlags::NO_COMMENTS);
                        }
                        statements.push(statement);
                        expressions.clear();
                    }
                };
            }

            macro_rules! push_variable {
                ($variable:expr) => {{
                    commit_pending_expressions!();
                    variables.push($variable);
                }};
            }

            macro_rules! push_expression {
                ($expression:expr) => {{
                    commit_pending_variables!();
                    expressions.push($expression);
                }};
            }

            // If we're exporting these variables, then these just become assignments to 'exports.x'.
            let declaration_nodes: Vec<NodeId> = declaration_list
                .and_then(|d| {
                    cx.nodes[d]
                        .as_variable_declaration_list()
                        .declarations
                        .as_ref()
                        .map(|l| l.nodes.iter().copied().collect())
                })
                .unwrap_or_default();
            for variable in declaration_nodes {
                let v_name = cx.nodes[variable].as_variable_declaration().name;
                let v_initializer = cx.nodes[variable].as_variable_declaration().initializer;

                if v_name.is_some_and(|n| ast::is_identifier(&cx.nodes[n]))
                    && is_local_name(&ec.borrow(), v_name.unwrap())
                {
                    // A "local name" generally means a variable declaration that *shouldn't* be
                    // converted to `exports.x = ...`, even if the declaration is exported. This
                    // usually indicates a class or function declaration that was converted into
                    // a variable declaration, as most references to the declaration will remain
                    // untransformed (i.e., `new C` rather than `new exports.C`). In these cases,
                    // an `export { x }` declaration will follow.

                    if modifiers.is_none() {
                        let node_modifiers = cx.nodes[node].modifiers().cloned();
                        modifiers = extract_modifiers(
                            Some(ec),
                            cx.nodes,
                            node_modifiers,
                            !ast::ModifierFlags::EXPORT_DEFAULT,
                        );
                    }

                    let variable = if let Some(initializer) = v_initializer {
                        let visited = self.main_visit_node(cx, Some(initializer));
                        let initializer = self.create_export_expression(
                            ec,
                            cx,
                            v_name.unwrap(),
                            visited.expect("visitor returned nil for initializer"),
                            None,  /* location */
                            false, /* liveBinding */
                        );
                        fac(ec, cx.nodes, |f, nodes| {
                            f.update_variable_declaration(
                                nodes,
                                variable,
                                v_name,
                                None, /* exclamationToken */
                                None, /* type */
                                Some(initializer),
                            )
                            .unwrap_or(variable)
                        })
                    } else {
                        variable
                    };

                    push_variable!(variable);
                } else if v_initializer.is_some()
                    && !v_name.is_some_and(|n| ast::is_binding_pattern(&cx.nodes[n]))
                    && (ast::is_arrow_function(&cx.nodes[v_initializer.unwrap()])
                        || ast::is_function_expression(&cx.nodes[v_initializer.unwrap()])
                        || ast::is_class_expression(&cx.nodes[v_initializer.unwrap()]))
                {
                    // preserve variable declarations for functions and classes to assign names
                    let (exclamation_token, type_node) = {
                        let d = cx.nodes[variable].as_variable_declaration();
                        (d.exclamation_token, d.type_)
                    };
                    let initializer = self.main_visit_node(cx, v_initializer);
                    push_variable!(fac(ec, cx.nodes, |f, nodes| {
                        f.new_variable_declaration(
                            nodes,
                            v_name,
                            exclamation_token,
                            type_node,
                            initializer,
                        )
                    }));

                    let property_access = fac(ec, cx.nodes, |f, nodes| {
                        let exports = f.new_identifier(nodes, "exports");
                        f.new_property_access_expression(
                            nodes,
                            Some(exports),
                            None, /* questionDotToken */
                            v_name,
                            ast::NodeFlags::NONE,
                        )
                    });
                    ec.borrow().assign_comment_and_source_map_ranges(
                        cx.nodes,
                        property_access,
                        v_name.unwrap(),
                    );

                    push_expression!(fac(ec, cx.nodes, |f, nodes| {
                        let name = f.clone_node(nodes, v_name.unwrap());
                        f.new_assignment_expression(nodes, property_access, name)
                    }));
                } else if v_name.is_some_and(|n| ast::is_identifier(&cx.nodes[n])) {
                    if let Some(expression) = self.transform_initialized_variable(ec, cx, variable)
                    {
                        let expression = self
                            .main_visit_node(cx, Some(expression))
                            .expect("visitor returned nil for initialized variable");
                        push_expression!(expression);
                    }
                } else if v_name.is_some_and(|n| ast::is_binding_pattern(&cx.nodes[n])) {
                    // For binding patterns with export modifier, use flattenDestructuringAssignment
                    // to decompose into individual export assignments
                    if let Some(expression) = self.transform_initialized_variable(ec, cx, variable)
                    {
                        push_expression!(expression);
                    }
                } else {
                    // For binding patterns, we can't do exports.{pattern} = value
                    // Just emit the assignment and let appendExportsOfVariableStatement handle the exports
                    if let Some(expression) = convert_variable_declaration_to_assignment_expression(
                        &mut ec.borrow_mut(),
                        cx.nodes,
                        variable,
                    ) {
                        let expression = self
                            .main_visit_node(cx, Some(expression))
                            .expect("visitor returned nil for assignment expression");
                        push_expression!(expression);
                    }
                }
            }

            commit_pending_variables!();
            commit_pending_expressions!();
            statements = self.append_exports_of_variable_statement(ec, cx, statements, node);
            return fac(ec, cx.nodes, |f, nodes| {
                single_or_many(f, nodes, Some(statements))
            });
        }
        Some(self.visit_top_level_nested_variable_statement(ec, cx, node))
    }

    /// `tx.transformInitializedVariable` — `node` must be a
    /// `VariableDeclaration`.
    fn transform_initialized_variable(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let (name, initializer) = {
            let d = cx.nodes[node].as_variable_declaration();
            (d.name, d.initializer)
        };
        initializer?;
        let name = name?;
        if ast::is_binding_pattern(&cx.nodes[name]) {
            // Convert the binding pattern into an equivalent assignment expression and visit it
            // as a destructuring assignment. This preserves native destructuring (and therefore
            // iterator semantics for array patterns) whenever each leaf identifier can be
            // substituted to an export reference. Only when the destructuring would assign to
            // re-aliased or multi-exported names (where native destructuring cannot update all
            // targets) does `visitDestructuringAssignment` fall back to flattening.
            let assignment = convert_variable_declaration_to_assignment_expression(
                &mut ec.borrow_mut(),
                cx.nodes,
                node,
            )?;
            let _guard = self.push_node(assignment);
            return Some(self.visit_destructuring_assignment(
                ec, cx, assignment, true, /* valueIsDiscarded */
            ));
        }
        let property_access = fac(ec, cx.nodes, |f, nodes| {
            let exports = f.new_identifier(nodes, "exports");
            f.new_property_access_expression(
                nodes,
                Some(exports),
                None, /* questionDotToken */
                Some(name),
                ast::NodeFlags::NONE,
            )
        });
        ec.borrow()
            .assign_comment_and_source_map_ranges(cx.nodes, property_access, name);
        Some(fac(ec, cx.nodes, |f, nodes| {
            f.new_assignment_expression(nodes, property_access, initializer.unwrap())
        }))
    }

    /// Visits a top-level nested variable statement as it may contain `var`
    /// declarations that are hoisted and may still be exported with
    /// `export {}`.
    fn visit_top_level_nested_variable_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let mut statements: Vec<NodeId> = Vec::new();
        statements.push(self.main_visit_each_child(cx, node));
        statements = self.append_exports_of_variable_statement(ec, cx, statements, node);
        fac(ec, cx.nodes, |f, nodes| {
            single_or_many(f, nodes, Some(statements))
        })
        .unwrap_or(node)
    }

    /// Visits a top-level nested `for` statement as it may contain `var`
    /// declarations that are hoisted and may still be exported with
    /// `export {}`.
    fn visit_top_level_nested_for_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (initializer, condition, incrementor, statement) = {
            let d = cx.nodes[node].as_for_statement();
            (
                d.initializer,
                d.condition,
                d.incrementor,
                d.iteration_statement_base.statement,
            )
        };
        if initializer.is_some_and(|i| ast::is_variable_declaration_list(&cx.nodes[i]))
            && !cx.nodes[initializer.unwrap()]
                .flags
                .intersects(ast::NodeFlags::BLOCK_SCOPED)
        {
            let export_statements = self.append_exports_of_variable_declaration_list(
                ec,
                cx,
                Vec::new(),
                initializer.unwrap(),
                false, /* isForInOrOfInitializer */
            );
            if !export_statements.is_empty() {
                // given:
                //   export { x }
                //   for (var x = 0; ;) { }
                // emits:
                //   var x = 0;
                //   exports.x = x;
                //   for (; ;) { }

                let mut statements: Vec<NodeId> = Vec::new();
                let var_decl_list = self
                    .visitors()
                    .discarded_value
                    .visit_node(cx, initializer)
                    .expect("visitor returned nil for variable declaration list");
                let var_statement = fac(ec, cx.nodes, |f, nodes| {
                    f.new_variable_statement(nodes, None /* modifiers */, Some(var_decl_list))
                });
                statements.push(var_statement);
                statements.extend(export_statements);

                let condition = self.main_visit_node(cx, condition);
                let incrementor = self.visitors().discarded_value.visit_node(cx, incrementor);
                let body =
                    ec_visit_iteration_body(&self.visitors().top_level_nested, cx, statement)
                        .expect("Expected visitor to return a statement");
                statements.push(fac(ec, cx.nodes, |f, nodes| {
                    f.update_for_statement(
                        nodes,
                        node,
                        None, /* initializer */
                        condition,
                        incrementor,
                        Some(body),
                    )
                    .unwrap_or(node)
                }));
                return fac(ec, cx.nodes, |f, nodes| {
                    single_or_many(f, nodes, Some(statements))
                })
                .unwrap_or(node);
            }
        }
        let initializer = self.visitors().discarded_value.visit_node(cx, initializer);
        let condition = self.main_visit_node(cx, condition);
        let incrementor = self.visitors().discarded_value.visit_node(cx, incrementor);
        let statement = ec_visit_iteration_body(&self.visitors().top_level_nested, cx, statement)
            .expect("Expected visitor to return a statement");
        fac(ec, cx.nodes, |f, nodes| {
            f.update_for_statement(
                nodes,
                node,
                initializer,
                condition,
                incrementor,
                Some(statement),
            )
            .unwrap_or(node)
        })
    }

    /// Visits a top-level nested `for..in` or `for..of` statement as it may
    /// contain `var` declarations that are hoisted and may still be exported
    /// with `export {}`.
    fn visit_top_level_nested_for_in_or_of_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (await_modifier, initializer, expression, statement) = {
            let d = cx.nodes[node].as_for_in_or_of_statement();
            (d.await_modifier, d.initializer, d.expression, d.statement)
        };
        if initializer.is_some_and(|i| ast::is_variable_declaration_list(&cx.nodes[i]))
            && !cx.nodes[initializer.unwrap()]
                .flags
                .intersects(ast::NodeFlags::BLOCK_SCOPED)
        {
            let export_statements = self.append_exports_of_variable_declaration_list(
                ec,
                cx,
                Vec::new(),
                initializer.unwrap(),
                true, /* isForInOrOfInitializer */
            );
            if !export_statements.is_empty() {
                // given:
                //   export { x }
                //   for (var x in y) {
                //     ...
                //   }
                // emits:
                //   for (var x in y) {
                //     exports.x = x;
                //     ...
                //   }

                let initializer = self.visitors().discarded_value.visit_node(cx, initializer);
                let expression = self.main_visit_node(cx, expression);
                let body =
                    ec_visit_iteration_body(&self.visitors().top_level_nested, cx, statement)
                        .expect("Expected visitor to return a statement");
                let body = if ast::is_block(&cx.nodes[body]) {
                    let block_statements: Vec<NodeId> = cx.nodes[body]
                        .as_block()
                        .statements
                        .as_ref()
                        .map(|l| l.nodes.iter().copied().collect())
                        .unwrap_or_default();
                    let block_statements_loc = cx.nodes[body]
                        .as_block()
                        .statements
                        .as_ref()
                        .map(|l| l.loc)
                        .unwrap_or_default();
                    let multi_line = cx.nodes[body].as_block().multi_line;
                    let mut body_statements = export_statements;
                    body_statements.extend(block_statements);
                    fac(ec, cx.nodes, |f, nodes| {
                        let mut body_statement_list = f.new_node_list(body_statements);
                        body_statement_list.loc = block_statements_loc;
                        f.update_block(nodes, body, Some(body_statement_list), multi_line)
                            .unwrap_or(body)
                    })
                } else {
                    let mut body_statements = export_statements;
                    body_statements.push(body);
                    fac(ec, cx.nodes, |f, nodes| {
                        let body_list = f.new_node_list(body_statements);
                        f.new_block(nodes, Some(body_list), true /* multiLine */)
                    })
                };
                return fac(ec, cx.nodes, |f, nodes| {
                    f.update_for_in_or_of_statement(
                        nodes,
                        node,
                        await_modifier,
                        initializer,
                        expression,
                        Some(body),
                    )
                    .unwrap_or(node)
                });
            }
        }
        let initializer = self.visitors().discarded_value.visit_node(cx, initializer);
        let expression = self.main_visit_node(cx, expression);
        let statement = ec_visit_iteration_body(&self.visitors().top_level_nested, cx, statement)
            .expect("Expected visitor to return a statement");
        fac(ec, cx.nodes, |f, nodes| {
            f.update_for_in_or_of_statement(
                nodes,
                node,
                await_modifier,
                initializer,
                expression,
                Some(statement),
            )
            .unwrap_or(node)
        })
    }

    /// Visits a top-level nested `do` statement as it may contain `var`
    /// declarations that are hoisted and may still be exported with
    /// `export {}`.
    fn visit_top_level_nested_do_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (statement, expression) = {
            let d = cx.nodes[node].as_do_statement();
            (d.iteration_statement_base.statement, d.expression)
        };
        let body = ec_visit_iteration_body(&self.visitors().top_level_nested, cx, statement)
            .expect("Expected visitor to return a statement");
        let expression = self.main_visit_node(cx, expression);
        fac(ec, cx.nodes, |f, nodes| {
            f.update_do_statement(nodes, node, Some(body), expression)
                .unwrap_or(node)
        })
    }

    /// Visits a top-level nested `while` statement as it may contain `var`
    /// declarations that are hoisted and may still be exported with
    /// `export {}`.
    fn visit_top_level_nested_while_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, statement) = {
            let d = cx.nodes[node].as_while_statement();
            (d.expression, d.iteration_statement_base.statement)
        };
        let expression = self.main_visit_node(cx, expression);
        let body = ec_visit_iteration_body(&self.visitors().top_level_nested, cx, statement)
            .expect("Expected visitor to return a statement");
        fac(ec, cx.nodes, |f, nodes| {
            f.update_while_statement(nodes, node, expression, Some(body))
                .unwrap_or(node)
        })
    }

    /// Visits a top-level nested labeled statement as it may contain `var`
    /// declarations that are hoisted and may still be exported with
    /// `export {}`.
    fn visit_top_level_nested_labeled_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (label, statement) = {
            let d = cx.nodes[node].as_labeled_statement();
            (d.label, d.statement)
        };
        let statement = self
            .visitors()
            .top_level_nested
            .visit_embedded_statement(cx, statement)
            .unwrap_or_else(|| fac(ec, cx.nodes, |f, nodes| f.new_empty_statement(nodes)));
        fac(ec, cx.nodes, |f, nodes| {
            f.update_labeled_statement(nodes, node, label, Some(statement))
                .unwrap_or(node)
        })
    }

    /// Visits a top-level nested `with` statement as it may contain `var`
    /// declarations that are hoisted and may still be exported with
    /// `export {}`.
    fn visit_top_level_nested_with_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, statement) = {
            let d = cx.nodes[node].as_with_statement();
            (d.expression, d.statement)
        };
        let statement = self
            .visitors()
            .top_level_nested
            .visit_embedded_statement(cx, statement)
            .unwrap_or_else(|| fac(ec, cx.nodes, |f, nodes| f.new_empty_statement(nodes)));
        let expression = self.main_visit_node(cx, expression);
        fac(ec, cx.nodes, |f, nodes| {
            f.update_with_statement(nodes, node, expression, Some(statement))
                .unwrap_or(node)
        })
    }

    /// Visits a top-level nested `if` statement as it may contain `var`
    /// declarations that are hoisted and may still be exported with
    /// `export {}`.
    fn visit_top_level_nested_if_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, then_statement, else_statement) = {
            let d = cx.nodes[node].as_if_statement();
            (d.expression, d.then_statement, d.else_statement)
        };
        let expression = self.main_visit_node(cx, expression);
        let then_statement = self
            .visitors()
            .top_level_nested
            .visit_embedded_statement(cx, then_statement)
            .unwrap_or_else(|| {
                fac(ec, cx.nodes, |f, nodes| {
                    let empty = f.new_node_list(vec![]);
                    f.new_block(nodes, Some(empty), false /* multiLine */)
                })
            });
        let else_statement = self
            .visitors()
            .top_level_nested
            .visit_embedded_statement(cx, else_statement);
        fac(ec, cx.nodes, |f, nodes| {
            f.update_if_statement(
                nodes,
                node,
                expression,
                Some(then_statement),
                else_statement,
            )
            .unwrap_or(node)
        })
    }

    /// Visits a top-level nested `switch` statement as it may contain `var`
    /// declarations that are hoisted and may still be exported with
    /// `export {}`.
    fn visit_top_level_nested_switch_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, case_block) = {
            let d = cx.nodes[node].as_switch_statement();
            (d.expression, d.case_block)
        };
        let expression = self.main_visit_node(cx, expression);
        let case_block = self.visitors().top_level_nested.visit_node(cx, case_block);
        fac(ec, cx.nodes, |f, nodes| {
            f.update_switch_statement(nodes, node, expression, case_block)
                .unwrap_or(node)
        })
    }

    /// Visits a top-level nested case block as it may contain `var`
    /// declarations that are hoisted and may still be exported with
    /// `export {}`.
    fn visit_top_level_nested_case_block(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        visit_each_child(&self.visitors().top_level_nested, cx, node)
    }

    /// Visits a top-level nested `case` or `default` clause as it may
    /// contain `var` declarations that are hoisted and may still be exported
    /// with `export {}`.
    fn visit_top_level_nested_case_or_default_clause(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, statements) = {
            let d = cx.nodes[node].as_case_or_default_clause();
            (d.expression, d.statements.clone())
        };
        let expression = self.main_visit_node(cx, expression);
        let statements = self.visitors().top_level_nested.visit_nodes(cx, statements);
        fac(ec, cx.nodes, |f, nodes| {
            f.update_case_or_default_clause(nodes, node, expression, statements)
                .unwrap_or(node)
        })
    }

    /// Visits a top-level nested `try` statement as it may contain `var`
    /// declarations that are hoisted and may still be exported with
    /// `export {}`.
    fn visit_top_level_nested_try_statement(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        visit_each_child(&self.visitors().top_level_nested, cx, node)
    }

    /// Visits a top-level nested `catch` clause as it may contain `var`
    /// declarations that are hoisted and may still be exported with
    /// `export {}`.
    fn visit_top_level_nested_catch_clause(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (variable_declaration, block) = {
            let d = cx.nodes[node].as_catch_clause();
            (d.variable_declaration, d.block)
        };
        let block = self.visitors().top_level_nested.visit_node(cx, block);
        fac(ec, cx.nodes, |f, nodes| {
            f.update_catch_clause(nodes, node, variable_declaration, block)
                .unwrap_or(node)
        })
    }

    /// Visits a top-level nested block as it may contain `var` declarations
    /// that are hoisted and may still be exported with `export {}`.
    fn visit_top_level_nested_block(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        visit_each_child(&self.visitors().top_level_nested, cx, node)
    }

    /// `tx.visitForStatement` — `node` must be a `ForStatement`.
    fn visit_for_statement(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        let (initializer, condition, incrementor, statement) = {
            let d = cx.nodes[node].as_for_statement();
            (
                d.initializer,
                d.condition,
                d.incrementor,
                d.iteration_statement_base.statement,
            )
        };
        let initializer = self.visitors().discarded_value.visit_node(cx, initializer);
        let condition = self.main_visit_node(cx, condition);
        let incrementor = self.visitors().discarded_value.visit_node(cx, incrementor);
        let statement = ec_visit_iteration_body(&self.visitors().main, cx, statement);
        fac(ec, cx.nodes, |f, nodes| {
            f.update_for_statement(nodes, node, initializer, condition, incrementor, statement)
                .unwrap_or(node)
        })
    }

    /// `tx.visitForInOrOfStatement` — `node` must be a `ForInOrOfStatement`.
    fn visit_for_in_or_of_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (await_modifier, initializer, expression, statement) = {
            let d = cx.nodes[node].as_for_in_or_of_statement();
            (d.await_modifier, d.initializer, d.expression, d.statement)
        };
        let initializer = self.visitors().discarded_value.visit_node(cx, initializer);
        let expression = self.main_visit_node(cx, expression);
        let statement = ec_visit_iteration_body(&self.visitors().main, cx, statement);
        fac(ec, cx.nodes, |f, nodes| {
            f.update_for_in_or_of_statement(
                nodes,
                node,
                await_modifier,
                initializer,
                expression,
                statement,
            )
            .unwrap_or(node)
        })
    }

    /// Visits an expression statement whose value will be discarded at runtime.
    fn visit_expression_statement(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        visit_each_child(&self.visitors().discarded_value, cx, node)
    }

    /// Visits a `void` expression whose value will be discarded at runtime.
    fn visit_void_expression(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        visit_each_child(&self.visitors().discarded_value, cx, node)
    }

    /// Visits a parenthesized expression whose value may be discarded at runtime.
    fn visit_parenthesized_expression(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        result_is_discarded: bool,
    ) -> NodeId {
        let expression = cx.nodes[node].as_parenthesized_expression().expression;
        let expression = if result_is_discarded {
            self.visitors().discarded_value.visit_node(cx, expression)
        } else {
            self.main_visit_node(cx, expression)
        };
        fac(ec, cx.nodes, |f, nodes| {
            f.update_parenthesized_expression(nodes, node, expression)
                .unwrap_or(node)
        })
    }

    /// Visits a partially emitted expression whose value may be discarded at
    /// runtime.
    fn visit_partially_emitted_expression(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        result_is_discarded: bool,
    ) -> NodeId {
        let expression = cx.nodes[node].as_partially_emitted_expression().expression;
        let expression = if result_is_discarded {
            self.visitors().discarded_value.visit_node(cx, expression)
        } else {
            self.main_visit_node(cx, expression)
        };
        fac(ec, cx.nodes, |f, nodes| {
            f.update_partially_emitted_expression(nodes, node, expression)
                .unwrap_or(node)
        })
    }

    /// Visits a binary expression whose value may be discarded, or which
    /// might contain an assignment to an exported identifier.
    fn visit_binary_expression(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        result_is_discarded: bool,
    ) -> NodeId {
        if ast::is_destructuring_assignment(&cx.nodes[node], cx.nodes) {
            return self.visit_destructuring_assignment(ec, cx, node, result_is_discarded);
        }

        if ast::is_assignment_expression(
            &cx.nodes[node],
            cx.nodes,
            false, /* excludeCompoundAssignment */
        ) {
            return self.visit_assignment_expression(ec, cx, node);
        }

        if ast::is_comma_expression(&cx.nodes[node], cx.nodes) {
            return self.visit_comma_expression(ec, cx, node, result_is_discarded);
        }

        self.main_visit_each_child(cx, node)
    }

    /// `tx.visitAssignmentExpression` — `node` must be a `BinaryExpression`.
    fn visit_assignment_expression(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        // When we see an assignment expression whose left-hand side is an exported symbol,
        // we should ensure all exports of that symbol are updated with the correct value.
        //
        // - We do not transform generated identifiers unless they are file-level reserved names.
        // - We do not transform identifiers tagged with the LocalName flag.
        // - We only transform identifiers that are exported at the top level.
        let (left, node_loc) = {
            let d = cx.nodes[node].as_binary_expression();
            (d.left, cx.nodes[node].loc)
        };
        if let Some(left) = left
            && ast::is_identifier(&cx.nodes[left])
            && (!is_generated_identifier(&ec.borrow(), left)
                || is_file_level_reserved_generated_identifier(&ec.borrow(), left))
            && !is_local_name(&ec.borrow(), left)
        {
            let exported_names = self.get_exports(ec, cx, left);
            if !exported_names.is_empty() {
                // For each additional export of the declaration, apply an export assignment.
                let mut expression = self.main_visit_each_child(cx, node);
                for export_name in exported_names {
                    expression = self.create_export_expression(
                        ec,
                        cx,
                        export_name,
                        expression,
                        Some(&node_loc),
                        false, /* liveBinding */
                    );
                }
                return expression;
            }
        }

        self.main_visit_each_child(cx, node)
    }

    /// Visits a destructuring assignment which might target an exported
    /// identifier.
    fn visit_destructuring_assignment(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        value_is_discarded: bool,
    ) -> NodeId {
        let left = cx.nodes[node].as_binary_expression().left;
        if left.is_some_and(|l| self.destructuring_needs_flattening(ec, cx, l)) {
            let tx2 = self
                .self_ref
                .borrow()
                .upgrade()
                .expect("transformer state dropped");
            let ec2 = ec.clone();
            // `vis`/`adapter` are declared before `callback` so they outlive
            // its destructor (drop order is reverse declaration order).
            let vis = self.visitors();
            let adapter = tx_adapter(&vis.main, ec);
            let callback: Box<CreateAssignmentCallback<'_>> =
                Box::new(move |_v, cx2, name, value, location| {
                    tx2.create_all_export_expressions(&ec2, cx2, name, value, location)
                });
            return flatten_destructuring_assignment(
                &adapter,
                cx,
                node,
                !value_is_discarded, /* needsValue */
                FlattenLevel::All,
                Some(callback),
            )
            .unwrap_or(node);
        }
        self.main_visit_each_child(cx, node)
    }

    /// `tx.destructuringNeedsFlattening` checks whether a destructuring
    /// assignment target contains any exported identifiers that need to be
    /// flattened into individual export assignments.
    fn destructuring_needs_flattening(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> bool {
        if ast::is_object_literal_expression(&cx.nodes[node]) {
            let properties: Vec<NodeId> = cx.nodes[node]
                .properties()
                .map(|p| p.to_vec())
                .unwrap_or_default();
            for elem in properties {
                match cx.nodes[elem].kind {
                    Kind::PropertyAssignment => {
                        if cx.nodes[elem]
                            .initializer()
                            .is_some_and(|i| self.destructuring_needs_flattening(ec, cx, i))
                        {
                            return true;
                        }
                    }
                    Kind::ShorthandPropertyAssignment => {
                        if cx.nodes[elem]
                            .name()
                            .is_some_and(|n| self.destructuring_needs_flattening(ec, cx, n))
                        {
                            return true;
                        }
                    }
                    Kind::SpreadAssignment => {
                        if cx.nodes[elem]
                            .expression()
                            .is_some_and(|e| self.destructuring_needs_flattening(ec, cx, e))
                        {
                            return true;
                        }
                    }
                    Kind::MethodDeclaration | Kind::GetAccessor | Kind::SetAccessor => {
                        return false;
                    }
                    _ => {}
                }
            }
        } else if ast::is_array_literal_expression(&cx.nodes[node]) {
            let elements: Vec<NodeId> = cx.nodes[node]
                .as_array_literal_expression()
                .elements
                .as_ref()
                .map(|l| l.nodes.iter().copied().collect())
                .unwrap_or_default();
            for elem in elements {
                if ast::is_spread_element(&cx.nodes[elem]) {
                    if cx.nodes[elem]
                        .expression()
                        .is_some_and(|e| self.destructuring_needs_flattening(ec, cx, e))
                    {
                        return true;
                    }
                } else if self.destructuring_needs_flattening(ec, cx, elem) {
                    return true;
                }
            }
        } else if ast::is_identifier(&cx.nodes[node]) {
            let exported_names = self.get_exports(ec, cx, node);
            if is_export_name(&ec.borrow(), node) {
                // The identifier is already wrapped to be an export reference; tolerate up to one
                // matching export.
                return exported_names.len() > 1;
            }
            if exported_names.is_empty() {
                return false;
            }
            // A single direct export whose export name matches the identifier text can be handled
            // natively: substitution will rewrite the identifier to `exports.X`, so no flattening
            // is needed. Re-aliased exports (where the export name differs from the local name) or
            // multi-exported names cannot be expressed natively in a destructuring assignment.
            if exported_names.len() == 1
                && self.is_direct_export(ec, cx, node)
                && cx.nodes[exported_names[0]].text(cx.nodes) == cx.nodes[node].text(cx.nodes)
            {
                return false;
            }
            return true;
        }
        false
    }

    /// `tx.createAllExportExpressions` is the callback used during
    /// destructuring flattening to create export expressions for each
    /// exported identifier binding. `name` must be an `Identifier`.
    fn create_all_export_expressions(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId,
        value: Option<NodeId>,
        location: &TextRange,
    ) -> NodeId {
        let exported_names = self.get_exports(ec, cx, name);
        let value = value.expect("CreateAssignmentCallback invoked with nil value");
        if !exported_names.is_empty() {
            // If the name is directly exported (i.e., `export let x`), assign to exports.name directly.
            // Otherwise, assign to the local binding first (i.e., `let x; export { x }`).
            let mut expression = if self.is_direct_export(ec, cx, name) {
                // Create exports.name = value to handle the direct export assignment,
                // since the Go port doesn't have an onSubstituteNode mechanism to rewrite identifiers.
                let (export_name, property_access) = fac(ec, cx.nodes, |f, nodes| {
                    let export_name = f.clone_node(nodes, name);
                    let exports = f.new_identifier(nodes, "exports");
                    let property_access = f.new_property_access_expression(
                        nodes,
                        Some(exports),
                        None, /* questionDotToken */
                        Some(export_name),
                        ast::NodeFlags::NONE,
                    );
                    (export_name, property_access)
                });
                ec.borrow().add_emit_flags(
                    export_name,
                    EmitFlags::NO_COMMENTS | EmitFlags::NO_SOURCE_MAP,
                );
                ec.borrow()
                    .add_emit_flags(property_access, EmitFlags::NO_COMMENTS);
                let expression = fac(ec, cx.nodes, |f, nodes| {
                    f.new_assignment_expression(nodes, property_access, value)
                });
                ec.borrow()
                    .assign_comment_and_source_map_ranges(cx.nodes, expression, name);
                expression
            } else {
                fac(ec, cx.nodes, |f, nodes| {
                    f.new_assignment_expression(nodes, name, value)
                })
            };
            for export_name in exported_names {
                expression = self.create_export_expression(
                    ec,
                    cx,
                    export_name,
                    expression,
                    Some(location),
                    false, /* liveBinding */
                );
            }
            return expression;
        }
        // If the identifier is directly exported but has no additional export aliases,
        // still write to exports.name.
        if self.is_direct_export(ec, cx, name) {
            let (export_name, property_access) = fac(ec, cx.nodes, |f, nodes| {
                let export_name = f.clone_node(nodes, name);
                let exports = f.new_identifier(nodes, "exports");
                let property_access = f.new_property_access_expression(
                    nodes,
                    Some(exports),
                    None, /* questionDotToken */
                    Some(export_name),
                    ast::NodeFlags::NONE,
                );
                (export_name, property_access)
            });
            ec.borrow().add_emit_flags(
                export_name,
                EmitFlags::NO_COMMENTS | EmitFlags::NO_SOURCE_MAP,
            );
            ec.borrow()
                .add_emit_flags(property_access, EmitFlags::NO_COMMENTS);
            let result = fac(ec, cx.nodes, |f, nodes| {
                f.new_assignment_expression(nodes, property_access, value)
            });
            ec.borrow()
                .assign_comment_and_source_map_ranges(cx.nodes, result, name);
            return result;
        }
        fac(ec, cx.nodes, |f, nodes| {
            f.new_assignment_expression(nodes, name, value)
        })
    }

    /// `tx.isDirectExport` checks whether the identifier is directly exported
    /// from the source file (e.g., `export let x` or `export function f()`),
    /// as opposed to being re-exported via `export { x }` for a
    /// locally-declared variable.
    fn is_direct_export(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, name: NodeId) -> bool {
        let original = ec
            .borrow()
            .most_original(Some(name))
            .expect("MostOriginal returned nil for a non-nil node");
        let export_container = {
            let mut symbols = self.symbols();
            self.resolver().get_referenced_export_container(
                original,
                false, /* prefixLocals */
                cx.nodes,
                &mut symbols,
            )
        };
        export_container.is_some_and(|c| ast::is_source_file(&cx.nodes[c]))
    }

    /// `tx.visitAssignmentProperty` — `node` must be a `PropertyAssignment`.
    fn visit_assignment_property(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (name, initializer) = {
            let d = cx.nodes[node].as_property_assignment();
            (d.named_member_base.name, d.initializer)
        };
        let name = self.main_visit_node(cx, name);
        let initializer = self
            .visitors()
            .assignment_pattern
            .visit_node(cx, initializer);
        fac(ec, cx.nodes, |f, nodes| {
            f.update_property_assignment(
                nodes,
                node,
                None, /* modifiers */
                name,
                None, /* postfixToken */
                None, /* typeNode */
                initializer,
            )
            .unwrap_or(node)
        })
    }

    /// `tx.visitShorthandAssignmentProperty` — `node` must be a
    /// `ShorthandPropertyAssignment`.
    fn visit_shorthand_assignment_property(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (name, equals_token, object_assignment_initializer) = {
            let d = cx.nodes[node].as_shorthand_property_assignment();
            (
                d.named_member_base.name,
                d.equals_token,
                d.object_assignment_initializer,
            )
        };
        let mut target = self.visit_destructuring_assignment_target_no_stack(
            ec,
            cx,
            name.expect("shorthand property assignment has no name"),
        );
        if ast::is_identifier(&cx.nodes[target]) {
            let object_assignment_initializer =
                self.main_visit_node(cx, object_assignment_initializer);
            return fac(ec, cx.nodes, |f, nodes| {
                f.update_shorthand_property_assignment(
                    nodes,
                    node,
                    None, /* modifiers */
                    Some(target),
                    None, /* postfixToken */
                    None, /* typeNode */
                    equals_token,
                    object_assignment_initializer,
                )
                .unwrap_or(node)
            });
        }
        if let Some(initializer) = object_assignment_initializer {
            let equals_token = equals_token.unwrap_or_else(|| {
                fac(ec, cx.nodes, |f, nodes| {
                    f.new_token(nodes, ast::Kind::EqualsToken)
                })
            });
            let initializer = self.main_visit_node(cx, Some(initializer));
            target = fac(ec, cx.nodes, |f, nodes| {
                f.new_binary_expression(
                    nodes,
                    None, /* modifiers */
                    Some(target),
                    None, /* typeNode */
                    Some(equals_token),
                    initializer,
                )
            });
        }
        let updated = fac(ec, cx.nodes, |f, nodes| {
            f.new_property_assignment(
                nodes,
                None, /* modifiers */
                name,
                None, /* postfixToken */
                None, /* typeNode */
                Some(target),
            )
        });
        ec.borrow().set_original(updated, node);
        ec.borrow()
            .assign_comment_and_source_map_ranges(cx.nodes, updated, node);
        updated
    }

    /// `tx.visitAssignmentRestProperty` — `node` must be a `SpreadAssignment`.
    fn visit_assignment_rest_property(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let expression = cx.nodes[node].as_spread_assignment().expression;
        let expression = expression.map(|e| self.visit_destructuring_assignment_target(ec, cx, e));
        fac(ec, cx.nodes, |f, nodes| {
            f.update_spread_assignment(nodes, node, expression)
                .unwrap_or(node)
        })
    }

    /// `tx.visitAssignmentRestElement` — `node` must be a `SpreadElement`.
    fn visit_assignment_rest_element(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let expression = cx.nodes[node].as_spread_element().expression;
        let expression = expression.map(|e| self.visit_destructuring_assignment_target(ec, cx, e));
        fac(ec, cx.nodes, |f, nodes| {
            f.update_spread_element(nodes, node, expression)
                .unwrap_or(node)
        })
    }

    /// `tx.visitAssignmentElement`
    fn visit_assignment_element(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if ast::is_binary_expression(&cx.nodes[node]) {
            let (left, operator_token, right) = {
                let d = cx.nodes[node].as_binary_expression();
                (d.left, d.operator_token, d.right)
            };
            if operator_token.is_some_and(|t| cx.nodes[t].kind == ast::Kind::EqualsToken) {
                let left = left.map(|l| self.visit_destructuring_assignment_target(ec, cx, l));
                let right = self.main_visit_node(cx, right);
                return fac(ec, cx.nodes, |f, nodes| {
                    f.update_binary_expression(
                        nodes,
                        node,
                        None, /* modifiers */
                        left,
                        None, /* typeNode */
                        operator_token,
                        right,
                    )
                    .unwrap_or(node)
                });
            }
        }

        self.visit_destructuring_assignment_target_no_stack(ec, cx, node)
    }

    /// `tx.visitDestructuringAssignmentTarget`
    fn visit_destructuring_assignment_target(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let _guard = self.push_node(node);
        match cx.nodes[node].kind {
            Kind::ObjectLiteralExpression | Kind::ArrayLiteralExpression => {
                self.visit_assignment_pattern_no_stack(ec, cx, node)
            }
            _ => self.visit_destructuring_assignment_target_no_stack(ec, cx, node),
        }
    }

    /// `tx.visitDestructuringAssignmentTargetNoStack`
    fn visit_destructuring_assignment_target_no_stack(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if ast::is_identifier(&cx.nodes[node])
            && (!is_generated_identifier(&ec.borrow(), node)
                || is_file_level_reserved_generated_identifier(&ec.borrow(), node))
            && !is_local_name(&ec.borrow(), node)
        {
            let mut expression = self.visit_expression_identifier(ec, cx, node);
            let exported_names = self.get_exports(ec, cx, node);
            if !exported_names.is_empty() {
                // transforms:
                //  var x;
                //  export { x }
                //  { x: x } = y
                // to:
                //  { x: { set value(v) { exports.x = x = v; } }.value } = y

                expression = {
                    let value = fac(ec, cx.nodes, |f, nodes| {
                        f.new_unique_name_ex(
                            nodes,
                            "value",
                            &AutoGenerateOptions {
                                flags: GeneratedIdentifierFlags::OPTIMISTIC,
                                ..Default::default()
                            },
                        )
                    });
                    let mut expression = fac(ec, cx.nodes, |f, nodes| {
                        f.new_assignment_expression(nodes, expression, value)
                    });

                    for export_name in &exported_names {
                        expression = self.create_export_expression(
                            ec,
                            cx,
                            *export_name,
                            expression,
                            None,  /* location */
                            false, /* liveBinding */
                        );
                    }

                    let statement = fac(ec, cx.nodes, |f, nodes| {
                        f.new_expression_statement(nodes, Some(expression))
                    });
                    fac(ec, cx.nodes, |f, nodes| {
                        let statement_list = f.new_node_list(vec![statement]);
                        let param = f.new_parameter_declaration(
                            nodes,
                            None, /* modifiers */
                            None, /* dotDotDotToken */
                            Some(value),
                            None, /* questionToken */
                            None, /* type */
                            None, /* initializer */
                        );
                        let parameters = f.new_node_list(vec![param]);
                        let value_ident = f.new_identifier(nodes, "value");
                        let block =
                            f.new_block(nodes, Some(statement_list), false /* multiLine */);
                        let value_setter = f.new_set_accessor_declaration(
                            nodes,
                            None, /* modifiers */
                            Some(value_ident),
                            None, /* typeParameters */
                            Some(parameters),
                            None, /* returnType */
                            None, /* fullSignature */
                            Some(block),
                        );
                        let property_list = f.new_node_list(vec![value_setter]);
                        let object_literal =
                            f.new_object_literal_expression(nodes, Some(property_list), false);
                        let value_ident = f.new_identifier(nodes, "value");
                        f.new_property_access_expression(
                            nodes,
                            Some(object_literal),
                            None, /* questionDotToken */
                            Some(value_ident),
                            ast::NodeFlags::NONE,
                        )
                    })
                };
                return expression;
            }
            return expression;
        }

        self.visit_no_stack(ec, cx, node, false /* resultIsDiscarded */)
    }

    /// Visits a comma expression whose left-hand value is always discarded,
    /// and whose right-hand value may be discarded at runtime.
    fn visit_comma_expression(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        result_is_discarded: bool,
    ) -> NodeId {
        let (left, operator_token, right) = {
            let d = cx.nodes[node].as_binary_expression();
            (d.left, d.operator_token, d.right)
        };
        let left = self.visitors().discarded_value.visit_node(cx, left);
        let right = if result_is_discarded {
            self.visitors().discarded_value.visit_node(cx, right)
        } else {
            self.main_visit_node(cx, right)
        };
        fac(ec, cx.nodes, |f, nodes| {
            f.update_binary_expression(
                nodes,
                node,
                None, /* modifiers */
                left,
                None, /* typeNode */
                operator_token,
                right,
            )
            .unwrap_or(node)
        })
    }

    /// Visits a prefix unary expression that might modify an exported identifier.
    fn visit_prefix_unary_expression(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        _result_is_discarded: bool,
    ) -> NodeId {
        // When we see a prefix increment expression whose operand is an exported
        // symbol, we should ensure all exports of that symbol are updated with the correct
        // value.
        //
        // - We do not transform generated identifiers for any reason.
        // - We do not transform identifiers tagged with the LocalName flag.
        // - We do not transform identifiers that were originally the name of an enum or
        //   namespace due to how they are transformed in TypeScript.
        // - We only transform identifiers that are exported at the top level.
        let (operator, operand) = {
            let d = cx.nodes[node].as_prefix_unary_expression();
            (d.operator, d.operand)
        };
        if (operator == Kind::PlusPlusToken || operator == Kind::MinusMinusToken)
            && operand.is_some_and(|o| ast::is_identifier(&cx.nodes[o]))
            && !is_local_name(&ec.borrow(), operand.unwrap())
        {
            let exported_names = self.get_exports(ec, cx, operand.unwrap());
            if !exported_names.is_empty() {
                // given:
                //   var x = 0;
                //   export { x }
                //   ++x;
                // emits:
                //   var x = 0;
                //   exports.x = x;
                //   exports.x = ++x;
                // note:
                //   after the operation, `exports.x` will hold the value of `x` after the increment.

                let operand_visited = self.main_visit_node(cx, operand);
                let mut expression = fac(ec, cx.nodes, |f, nodes| {
                    f.update_prefix_unary_expression(nodes, node, operator, operand_visited)
                        .unwrap_or(node)
                });
                for export_name in exported_names {
                    expression = self.create_export_expression(
                        ec,
                        cx,
                        export_name,
                        expression,
                        None,  /* location */
                        false, /* liveBinding */
                    );
                    ec.borrow()
                        .assign_comment_and_source_map_ranges(cx.nodes, expression, node);
                }
                return expression;
            }
        }
        self.main_visit_each_child(cx, node)
    }

    /// Visits a postfix unary expression that might modify an exported identifier.
    fn visit_postfix_unary_expression(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        result_is_discarded: bool,
    ) -> NodeId {
        // When we see a postfix increment expression whose operand is an exported
        // symbol, we should ensure all exports of that symbol are updated with the correct
        // value.
        //
        // - We do not transform generated identifiers for any reason.
        // - We do not transform identifiers tagged with the LocalName flag.
        // - We do not transform identifiers that were originally the name of an enum or
        //   namespace due to how they are transformed in TypeScript.
        // - We only transform identifiers that are exported at the top level.
        let (operator, operand) = {
            let d = cx.nodes[node].as_postfix_unary_expression();
            (d.operator, d.operand)
        };
        if (operator == Kind::PlusPlusToken || operator == Kind::MinusMinusToken)
            && operand.is_some_and(|o| ast::is_identifier(&cx.nodes[o]))
            && !is_local_name(&ec.borrow(), operand.unwrap())
        {
            let exported_names = self.get_exports(ec, cx, operand.unwrap());
            if !exported_names.is_empty() {
                // given (value is discarded):
                //   var x = 0;
                //   export { x }
                //   x++;
                // emits:
                //   var x = 0, y;
                //   exports.x = x;
                //   exports.x = (x++, x);
                // note:
                //   after the operation, `exports.x` will hold the value of `x` after the increment.
                //
                // given (value is not discarded):
                //   var x = 0, y;
                //   export { x }
                //   y = x++;
                // emits:
                //   var _a;
                //   var x = 0, y;
                //   exports.x = x;
                //   y = (exports.x = (_a = x++, x), _a);
                // note:
                //   after the operation, `exports.x` will hold the value of `x` after the increment, while
                //   `y` will hold the value of `x` before the increment.

                let mut temp: Option<NodeId> = None;
                let operand_visited = self.main_visit_node(cx, operand);
                let mut expression = fac(ec, cx.nodes, |f, nodes| {
                    f.update_postfix_unary_expression(nodes, node, operand_visited, operator)
                        .unwrap_or(node)
                });
                if !result_is_discarded {
                    let temp_name = fac(ec, cx.nodes, |f, nodes| f.new_temp_variable(nodes));
                    ec.borrow_mut()
                        .add_variable_declaration(cx.nodes, temp_name);

                    expression = fac(ec, cx.nodes, |f, nodes| {
                        f.new_assignment_expression(nodes, temp_name, expression)
                    });
                    ec.borrow()
                        .assign_comment_and_source_map_ranges(cx.nodes, expression, node);
                    temp = Some(temp_name);
                }

                let operand_clone = fac(ec, cx.nodes, |f, nodes| {
                    f.clone_node(nodes, operand.unwrap())
                });
                expression = fac(ec, cx.nodes, |f, nodes| {
                    f.new_comma_expression(nodes, expression, operand_clone)
                });
                ec.borrow()
                    .assign_comment_and_source_map_ranges(cx.nodes, expression, node);

                for export_name in exported_names {
                    expression = self.create_export_expression(
                        ec,
                        cx,
                        export_name,
                        expression,
                        None,  /* location */
                        false, /* liveBinding */
                    );
                    ec.borrow()
                        .assign_comment_and_source_map_ranges(cx.nodes, expression, node);
                }

                if let Some(temp) = temp {
                    expression = fac(ec, cx.nodes, |f, nodes| {
                        f.new_comma_expression(nodes, expression, temp)
                    });
                    ec.borrow()
                        .assign_comment_and_source_map_ranges(cx.nodes, expression, node);
                }

                return expression;
            }
        }

        self.main_visit_each_child(cx, node)
    }

    /// Visits a call expression that might reference an imported symbol and
    /// thus require an indirect call, or that might be an `import()` or
    /// `require()` call that may need to be rewritten.
    fn visit_call_expression(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        let (expression, question_dot_token, arguments, flags) = {
            let d = cx.nodes[node].as_call_expression();
            (
                d.expression,
                d.question_dot_token,
                d.arguments
                    .as_ref()
                    .map(|a| a.nodes.iter().copied().collect::<Vec<_>>()),
                cx.nodes[node].flags,
            )
        };
        let mut needs_rewrite = false;
        if self
            .compiler_options
            .rewrite_relative_import_extensions
            .is_true()
        {
            if (ast::is_import_call(&cx.nodes[node], cx.nodes)
                && !arguments.as_ref().is_none_or(|a| a.is_empty()))
                || (ast::is_in_js_file(Some(node), cx.nodes)
                    && ast::is_require_call(
                        &cx.nodes[node],
                        false, /* requireStringLiteralLikeArgument */
                        cx.nodes,
                    ))
            {
                needs_rewrite = true;
            }
        }
        if expression.is_some_and(|e| cx.nodes[e].kind == Kind::ImportKeyword)
            && self.should_transform_import_call(cx)
        {
            return self.visit_import_call_expression(ec, cx, node, needs_rewrite);
        }
        if needs_rewrite {
            return self.shim_or_rewrite_import_or_require_call(ec, cx, node);
        }
        if let Some(expression) = expression
            && ast::is_identifier(&cx.nodes[expression])
        {
            // given:
            //   import { f } from "mod";
            //   f();
            // emits:
            //   const mod_1 = require("mod");
            //   (0, mod_1.f)();
            // note:
            //   the indirect call is applied by the printer by way of the `EFIndirectCall` emit flag.
            let expression = self.visit_expression_identifier(ec, cx, expression);
            let arguments = self
                .visitors()
                .main
                .visit_nodes(cx, cx.nodes[node].as_call_expression().arguments.clone());
            let updated = fac(ec, cx.nodes, |f, nodes| {
                f.update_call_expression(
                    nodes,
                    node,
                    Some(expression),
                    question_dot_token,
                    None, /* typeArguments */
                    arguments,
                    flags,
                )
                .unwrap_or(node)
            });
            if !ast::is_identifier(&cx.nodes[expression])
                && !is_helper_name(
                    &ec.borrow(),
                    cx.nodes[node].as_call_expression().expression.unwrap(),
                )
            {
                ec.borrow()
                    .add_emit_flags(updated, EmitFlags::INDIRECT_CALL);
            }
            return updated;
        }
        self.main_visit_each_child(cx, node)
    }

    /// `tx.shouldTransformImportCall`
    fn should_transform_import_call(&self, cx: &VisitorCx<'_, '_>) -> bool {
        let current_source_file = self
            .current_source_file
            .get()
            .expect("currentSourceFile is nil");
        ast::should_transform_import_call(
            cx.nodes[current_source_file].as_source_file().file_name(),
            self.compiler_options,
            self.emit_module_format(cx, current_source_file),
        )
    }

    /// `tx.visitImportCallExpression` — `node` must be a `CallExpression`.
    fn visit_import_call_expression(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        rewrite_or_shim: bool,
    ) -> NodeId {
        if self.module_kind == ModuleKind::None && self.language_version >= ScriptTarget::ES2020 {
            return self.main_visit_each_child(cx, node);
        }

        let arguments: Vec<NodeId> = cx.nodes[node]
            .as_call_expression()
            .arguments
            .as_ref()
            .map(|a| a.nodes.iter().copied().collect())
            .unwrap_or_default();

        let external_module_name = fac(ec, cx.nodes, |f, nodes| {
            get_external_module_name_literal(
                f,
                nodes,
                node,
                self.current_source_file.get(),
                None, /* host */
                None, /* resolver */
                self.compiler_options,
            )
        });
        let first_argument = self.main_visit_node(cx, arguments.first().copied());

        // Only use the external module name if it differs from the first argument. This allows us to preserve the quote style of the argument on output.
        let argument = if external_module_name.is_some()
            && (first_argument.is_none()
                || !ast::is_string_literal(&cx.nodes[first_argument.unwrap()])
                || cx.nodes[first_argument.unwrap()].text(cx.nodes)
                    != cx.nodes[external_module_name.unwrap()].text(cx.nodes))
        {
            external_module_name
        } else if let Some(first_argument) = first_argument {
            if rewrite_or_shim {
                if ast::is_string_literal(&cx.nodes[first_argument]) {
                    rewrite_module_specifier(
                        &mut ec.borrow_mut(),
                        cx.nodes,
                        Some(first_argument),
                        self.compiler_options,
                    )
                } else {
                    Some(fac(ec, cx.nodes, |f, nodes| {
                        f.new_rewrite_relative_import_extensions_helper(
                            nodes,
                            first_argument,
                            self.compiler_options.jsx
                                == tsc_core::options_generated::JsxEmit::Preserve,
                        )
                    }))
                }
            } else {
                Some(first_argument)
            }
        } else {
            first_argument
        };
        self.create_import_call_expression_common_js(ec, cx, argument)
    }

    /// `tx.createImportCallExpressionCommonJS`
    fn create_import_call_expression_common_js(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        arg: Option<NodeId>,
    ) -> NodeId {
        // import(x)
        // emit as
        // Promise.resolve(`${x}`).then((s) => require(s)) /*CommonJS Require*/
        // We have to wrap require in then callback so that require is done in asynchronously
        // if we simply do require in resolve callback in Promise constructor. We will execute the loading immediately
        // If the arg is not inlineable, we have to evaluate and ToString() it in the current scope
        // Otherwise, we inline it in require() so that it's statically analyzable

        let need_sync_eval =
            arg.is_some() && !is_simple_inlineable_expression(&cx.nodes[arg.unwrap()]);

        fac(ec, cx.nodes, |f, nodes| {
            let mut promise_resolve_arguments: Vec<NodeId> = Vec::new();
            if need_sync_eval {
                let head = f.new_template_head(nodes, "", "", ast::TokenFlags::NONE);
                let tail = f.new_template_tail(nodes, "", "", ast::TokenFlags::NONE);
                let span = f.new_template_span(nodes, arg, Some(tail));
                let spans = f.new_node_list(vec![span]);
                let template = f.new_template_expression(nodes, Some(head), Some(spans));
                promise_resolve_arguments.push(template);
            }
            let promise_ident = f.new_identifier(nodes, "Promise");
            let resolve_ident = f.new_identifier(nodes, "resolve");
            let promise_resolve = f.new_property_access_expression(
                nodes,
                Some(promise_ident),
                None, /* questionDotToken */
                Some(resolve_ident),
                ast::NodeFlags::NONE,
            );
            let promise_resolve_args = f.new_node_list(promise_resolve_arguments);
            let promise_resolve_call = f.new_call_expression(
                nodes,
                Some(promise_resolve),
                None, /* questionDotToken */
                None, /* typeArguments */
                Some(promise_resolve_args),
                ast::NodeFlags::NONE,
            );

            let mut require_arguments: Vec<NodeId> = Vec::new();
            if need_sync_eval {
                require_arguments.push(f.new_identifier(nodes, "s"));
            } else if let Some(arg) = arg {
                require_arguments.push(arg);
            }

            let require_ident = f.new_identifier(nodes, "require");
            let require_args = f.new_node_list(require_arguments);
            let require_call = f.new_call_expression(
                nodes,
                Some(require_ident),
                None, /* questionDotToken */
                None, /* typeArguments */
                Some(require_args),
                ast::NodeFlags::NONE,
            );
            let require_call = f.new_import_star_helper(nodes, require_call);

            let mut parameters: Vec<NodeId> = Vec::new();
            if need_sync_eval {
                let s_ident = f.new_identifier(nodes, "s");
                let param = f.new_parameter_declaration(
                    nodes,
                    None, /* modifiers */
                    None, /* dotDotDotToken */
                    Some(s_ident),
                    None, /* questionToken */
                    None, /* type */
                    None, /* initializer */
                );
                parameters.push(param);
            }

            let parameters = f.new_node_list(parameters);
            let eq_gt = f.new_token(nodes, ast::Kind::EqualsGreaterThanToken);
            let function = f.new_arrow_function(
                nodes,
                None, /* modifiers */
                None, /* typeParameters */
                Some(parameters),
                None, /* type */
                None, /* fullSignature */
                Some(eq_gt),
                Some(require_call),
            );

            let then_ident = f.new_identifier(nodes, "then");
            let then = f.new_property_access_expression(
                nodes,
                Some(promise_resolve_call),
                None, /* questionDotToken */
                Some(then_ident),
                ast::NodeFlags::NONE,
            );
            let downleveled_args = f.new_node_list(vec![function]);
            f.new_call_expression(
                nodes,
                Some(then),
                None, /* questionDotToken */
                None, /* typeArguments */
                Some(downleveled_args),
                ast::NodeFlags::NONE,
            )
        })
    }

    /// `tx.shimOrRewriteImportOrRequireCall` — `node` must be a
    /// `CallExpression`.
    fn shim_or_rewrite_import_or_require_call(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, question_dot_token, arguments, flags) = {
            let d = cx.nodes[node].as_call_expression();
            (
                d.expression,
                d.question_dot_token,
                d.arguments.clone(),
                cx.nodes[node].flags,
            )
        };
        let expression = self.main_visit_node(cx, expression);
        let mut arguments_list = arguments;
        if let Some(list) = &arguments_list
            && !list.nodes.is_empty()
        {
            let first_arg = list.nodes[0];
            let mut first_argument = self
                .main_visit_node(cx, Some(first_arg))
                .expect("visitor returned nil for call argument");
            let first_argument_changed: bool;
            if ast::is_string_literal_like(&cx.nodes[first_argument]) {
                let rewritten = rewrite_module_specifier(
                    &mut ec.borrow_mut(),
                    cx.nodes,
                    Some(first_argument),
                    self.compiler_options,
                );
                first_argument_changed = rewritten != Some(first_argument);
                first_argument = rewritten.unwrap_or(first_argument);
            } else {
                first_argument = fac(ec, cx.nodes, |f, nodes| {
                    f.new_rewrite_relative_import_extensions_helper(
                        nodes,
                        first_argument,
                        self.compiler_options.jsx == tsc_core::options_generated::JsxEmit::Preserve,
                    )
                });
                first_argument_changed = true;
            }

            let rest_changed = self.visitors().main.visit_slice(cx, &list.nodes[1..]);
            if first_argument_changed || rest_changed.is_some() {
                let mut new_arguments = vec![first_argument];
                new_arguments.extend(rest_changed.unwrap_or_else(|| list.nodes[1..].to_vec()));
                arguments_list = Some({
                    let e = ec.borrow_mut();
                    let mut list = e.factory.new_node_list(new_arguments);
                    list.loc = cx.nodes[node]
                        .as_call_expression()
                        .arguments
                        .as_ref()
                        .map(|l| l.loc)
                        .unwrap_or_default();
                    list
                });
            }
        }

        fac(ec, cx.nodes, |f, nodes| {
            f.update_call_expression(
                nodes,
                node,
                expression,
                question_dot_token,
                None, /* typeArguments */
                arguments_list,
                flags,
            )
            .unwrap_or(node)
        })
    }

    /// Visits a tagged template expression that might reference an imported
    /// symbol and thus require an indirect call.
    fn visit_tagged_template_expression(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (tag, template, flags) = {
            let d = cx.nodes[node].as_tagged_template_expression();
            (d.tag, d.template, cx.nodes[node].flags)
        };
        if let Some(tag) = tag
            && ast::is_identifier(&cx.nodes[tag])
        {
            // given:
            //   import { f } from "mod";
            //   f``;
            // emits:
            //   const mod_1 = require("mod");
            //   (0, mod_1.f) ``;
            // note:
            //   the indirect call is applied by the printer by way of the `EFIndirectCall` emit flag.

            let expression = self.visit_expression_identifier(ec, cx, tag);
            let template = self.main_visit_node(cx, template);
            let updated = fac(ec, cx.nodes, |f, nodes| {
                f.update_tagged_template_expression(
                    nodes,
                    node,
                    Some(expression),
                    None, /* questionDotToken */
                    None, /* typeArguments */
                    template,
                    flags,
                )
                .unwrap_or(node)
            });
            if !ast::is_identifier(&cx.nodes[expression]) && !is_helper_name(&ec.borrow(), tag) {
                ec.borrow()
                    .add_emit_flags(updated, EmitFlags::INDIRECT_CALL);
            }
            return updated;
        }
        self.main_visit_each_child(cx, node)
    }

    /// Visits a shorthand property assignment that might reference an
    /// imported or exported symbol.
    fn visit_shorthand_property_assignment(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (name, equals_token, object_assignment_initializer) = {
            let d = cx.nodes[node].as_shorthand_property_assignment();
            (
                d.named_member_base.name,
                d.equals_token,
                d.object_assignment_initializer,
            )
        };
        let name = name.expect("shorthand property assignment has no name");
        let exported_or_imported_name = self.visit_expression_identifier(ec, cx, name);
        if exported_or_imported_name != name {
            // A shorthand property with an assignment initializer is probably part of a
            // destructuring assignment
            let mut expression = exported_or_imported_name;
            if object_assignment_initializer.is_some() {
                let initializer = self.main_visit_node(cx, object_assignment_initializer);
                expression = fac(ec, cx.nodes, |f, nodes| {
                    f.new_assignment_expression(nodes, expression, initializer.unwrap())
                });
            }
            let assignment = fac(ec, cx.nodes, |f, nodes| {
                f.new_property_assignment(
                    nodes,
                    None, /* modifiers */
                    Some(name),
                    None, /* postfixToken */
                    None, /* typeNode */
                    Some(expression),
                )
            });
            cx.nodes[assignment].loc = cx.nodes[node].loc;
            ec.borrow()
                .assign_comment_and_source_map_ranges(cx.nodes, assignment, node);
            return assignment;
        }
        let object_assignment_initializer = self.main_visit_node(cx, object_assignment_initializer);
        fac(ec, cx.nodes, |f, nodes| {
            f.update_shorthand_property_assignment(
                nodes,
                node,
                None, /* modifiers */
                Some(exported_or_imported_name),
                None, /* postfixToken */
                None, /* typeNode */
                equals_token,
                object_assignment_initializer,
            )
            .unwrap_or(node)
        })
    }

    /// Visits an identifier that, if it is in an expression position, might
    /// reference an imported or exported symbol.
    fn visit_identifier(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        let parent = self
            .parent_node
            .get()
            .expect("visitIdentifier requires a non-nil parentNode (Go would nil-pointer panic)");
        if is_identifier_reference(cx.nodes, node, parent) {
            return self.visit_expression_identifier(ec, cx, node);
        }
        node
    }

    /// Visits an identifier in an expression position that might reference
    /// an imported or exported symbol.
    fn visit_expression_identifier(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let info = ec.borrow().get_auto_generate_info(Some(node));
        if info.is_none_or(|i| i.flags.has_allow_name_substitution())
            && !is_helper_name(&ec.borrow(), node)
            && !is_local_name(&ec.borrow(), node)
            && !is_declaration_name_of_enum_or_namespace(&ec.borrow(), cx.nodes, node)
        {
            let original = ec
                .borrow()
                .most_original(Some(node))
                .expect("MostOriginal returned nil for a non-nil node");
            let export_container = {
                let mut symbols = self.symbols();
                self.resolver().get_referenced_export_container(
                    original,
                    is_export_name(&ec.borrow(), node),
                    cx.nodes,
                    &mut symbols,
                )
            };
            if export_container.is_some_and(|c| ast::is_source_file(&cx.nodes[c])) {
                let reference = fac(ec, cx.nodes, |f, nodes| {
                    let exports = f.new_identifier(nodes, "exports");
                    let name = f.clone_node(nodes, node);
                    f.new_property_access_expression(
                        nodes,
                        Some(exports),
                        None, /* questionDotToken */
                        Some(name),
                        ast::NodeFlags::NONE,
                    )
                });
                ec.borrow()
                    .assign_comment_and_source_map_ranges(cx.nodes, reference, node);
                cx.nodes[reference].loc = cx.nodes[node].loc;
                return reference;
            }

            let import_declaration = {
                let mut symbols = self.symbols();
                self.resolver()
                    .get_referenced_import_declaration(original, cx.nodes, &mut symbols)
            };
            if let Some(import_declaration) = import_declaration {
                if ast::is_import_clause(&cx.nodes[import_declaration]) {
                    let parent = cx.nodes[import_declaration]
                        .parent
                        .expect("import clause has no parent");
                    let reference = fac(ec, cx.nodes, |f, nodes| {
                        // Resolver returns parse-tree declarations; Parent is used to find the owning import declaration.
                        let target = f.new_generated_name_for_node(nodes, parent);
                        let default_ident = f.new_identifier(nodes, "default");
                        f.new_property_access_expression(
                            nodes,
                            Some(target),
                            None, /* questionDotToken */
                            Some(default_ident),
                            ast::NodeFlags::NONE,
                        )
                    });
                    ec.borrow()
                        .assign_comment_and_source_map_ranges(cx.nodes, reference, node);
                    cx.nodes[reference].loc = cx.nodes[node].loc;
                    return reference;
                }
                if ast::is_import_specifier(&cx.nodes[import_declaration]) {
                    let name = cx.nodes[import_declaration]
                        .property_name_or_name()
                        .expect("import specifier has no name");
                    let decl =
                        ast::find_ancestor(Some(import_declaration), cx.nodes, &mut |n, _| {
                            ast::is_import_declaration(n)
                        });
                    let target_source = decl.or(Some(import_declaration)).unwrap();
                    if ast::is_string_literal(&cx.nodes[name]) {
                        let reference = fac(ec, cx.nodes, |f, nodes| {
                            let target = f.new_generated_name_for_node(nodes, target_source);
                            let name_literal = f.new_string_literal_from_node(nodes, name);
                            f.new_element_access_expression(
                                nodes,
                                Some(target),
                                None, /* questionDotToken */
                                Some(name_literal),
                                ast::NodeFlags::NONE,
                            )
                        });
                        ec.borrow()
                            .assign_comment_and_source_map_ranges(cx.nodes, reference, node);
                        cx.nodes[reference].loc = cx.nodes[node].loc;
                        return reference;
                    }
                    let (reference_name, reference) = fac(ec, cx.nodes, |f, nodes| {
                        let target = f.new_generated_name_for_node(nodes, target_source);
                        let reference_name = f.clone_node(nodes, name);
                        let reference = f.new_property_access_expression(
                            nodes,
                            Some(target),
                            None, /* questionDotToken */
                            Some(reference_name),
                            ast::NodeFlags::NONE,
                        );
                        (reference_name, reference)
                    });
                    ec.borrow().add_emit_flags(
                        reference_name,
                        EmitFlags::NO_SOURCE_MAP | EmitFlags::NO_COMMENTS,
                    );
                    ec.borrow()
                        .assign_comment_and_source_map_ranges(cx.nodes, reference, node);
                    cx.nodes[reference].loc = cx.nodes[node].loc;
                    return reference;
                }
            }
        }
        node
    }

    /// Gets the exported names of an identifier, if it is exported.
    fn get_exports(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, name: NodeId) -> Vec<NodeId> {
        if !is_generated_identifier(&ec.borrow(), name) {
            let original = ec
                .borrow()
                .most_original(Some(name))
                .expect("MostOriginal returned nil for a non-nil node");
            let import_declaration = {
                let mut symbols = self.symbols();
                self.resolver()
                    .get_referenced_import_declaration(original, cx.nodes, &mut symbols)
            };
            if let Some(import_declaration) = import_declaration {
                return self.module_info(|i| i.exported_bindings.get(&import_declaration).to_vec());
            }

            // An exported namespace or enum may merge with an ambient declaration, which won't show up in .js emit, so
            // we analyze all value exports of a symbol.
            let declarations = {
                let mut symbols = self.symbols();
                self.resolver()
                    .get_referenced_value_declarations(original, cx.nodes, &mut symbols)
            };
            let mut bindings_set: Set<NodeId> = Set::default();
            let mut bindings: Vec<NodeId> = Vec::new();
            for declaration in declarations {
                let exported_bindings =
                    self.module_info(|i| i.exported_bindings.get(&declaration).to_vec());
                for binding in exported_bindings {
                    if !bindings_set.has(&binding) {
                        bindings_set.add(binding);
                        bindings.push(binding);
                    }
                }
            }
            return bindings;
        } else if is_file_level_reserved_generated_identifier(&ec.borrow(), name) {
            let text = cx.nodes[name].text(cx.nodes).into_owned();
            let export_specifiers = self.module_info(|i| i.export_specifiers.get(&text).to_vec());
            if !export_specifiers.is_empty() {
                return export_specifiers
                    .iter()
                    .map(|&s| cx.nodes[s].name().expect("export specifier has no name"))
                    .collect();
            }
        }
        Vec::new()
    }
}
