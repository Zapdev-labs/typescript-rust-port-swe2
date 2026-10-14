// Ported from tsc/internal/transformers/declarations/transform.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The declaration (`.d.ts`) transformer: rewrites a bound SourceFile into
// declaration form, elides invisible declarations, late-binds aliases whose
// visibility is discovered while serializing inferred types, rewrites CJS
// `module.exports`/`exports.x` assignments, synthesizes expando
// host/namespace declarations, and accumulates declaration-emit
// diagnostics through `SymbolTrackerImpl`.
//
// PORT notes:
//   - Go `*ast.Node` → `NodeId`; `*ast.SourceFile` → the SourceFile `NodeId`;
//     `*ast.Symbol` → `SymbolId`; `ast.NodeId` map keys stay `NodeId`.
//   - `tx.Visitor()` is the `v: &NodeVisitor` parameter threaded through the
//     visit callbacks (Go closes over the visitor pointer; the Rust
//     `VisitFn` signature passes it). The auxiliary visitors Go stores on
//     the transformer (`bindingNameVisitor`, `expressionVisitor`, `...`)
//     live in `RefCell<Option<NodeVisitor>>` slots on the state and are
//     installed by `new_declaration_transformer` after the `Rc` exists;
//     recursive `VisitEachChild` calls go through the `v` each callback is
//     handed, so no aliasing tricks are needed.
//   - `tx.Factory()` calls route through `self.ec.borrow_mut().factory` —
//     the real `printer::NodeFactory` hooked to the emit context — as
//     `transformer.rs` recommends, rather than the visitor's `cx.factory`
//     stand-in. This matters for `clone_node` (the real `onClone` hook
//     copies `autoGenerate` info) and for name generation
//     (`new_unique_name_ex`, `new_generated_name_for_node`,
//     `new_string_literal_from_node`), which only exist on the printer
//     factory.
//   - `tx.EmitContext()` calls use `self.ec.borrow()`/`borrow_mut()` — all
//     emit-metadata mutators (`set_original`, `add_emit_flags`,
//     `assign_comment_range`, `add_synthetic_leading_comment`,
//     `set_comment_range`) take `&self` in this port since the shared
//     tables are behind `Rc<RefCell>`.
//   - `tx.state` → `self.shared` (`Rc<RefCell<SymbolTrackerSharedState>>`);
//     `tx.tracker` → `self.tracker` (`RefCell<SymbolTrackerImpl>`). The
//     tracker reads the node arena through the `nodes: &[Node]` parameter
//     the `SymbolTracker` trait methods now carry (Go sees the live arena
//     through pointers instead).
//   - Go `defer` blocks become either RAII guards
//     (`DiagnosticContextGuard`, `EnclosingDeclarationGuard`) or explicit
//     save/restore pairs.
//   - Go `*ast.Node` returns collapse into `Option<NodeId>`; factory
//     `update_*` calls return `Option<NodeId>` where `None` means
//     "unchanged" (Go returned the input pointer), so call sites use
//     `.unwrap_or(input)`.
//   - Go nil `*ast.SourceFile` parameters (currentSourceFile) →
//     `Option<NodeId>`.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{
    self as ast, FileReference, Kind, ModifierFlags, Node, NodeFlags, NodeId, NodeList, Symbol,
    SymbolFlags, TokenFlags,
};
use tsc_core::core;
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::text::TextRange;
use tsc_nodebuilder::{self as nodebuilder, SymbolTracker};
use tsc_printer::{AutoGenerateOptions, EmitContext};
use tsc_printer::{EmitFlags, GeneratedIdentifierFlags};
use tsc_printer::{EmitResolver, SymbolAccessibilityResult};
use tsc_scanner::{self as scanner, scanner::SkipTriviaOptions};
use tsc_tspath::{self as tspath, RootedFilePath};

use crate::declarations::diagnostics::{
    GetSymbolAccessibilityDiagnostic, SymbolAccessibilityDiagnostic,
    create_get_symbol_accessibility_diagnostic_for_node,
    create_get_symbol_accessibility_diagnostic_for_node_name,
};
use crate::declarations::host::DeclarationEmitHost;
use crate::declarations::tracker::{
    SymbolTrackerImpl, SymbolTrackerSharedState, create_diagnostic_for_node,
};
use crate::declarations::util::{
    can_have_literal_initializer, can_produce_diagnostics, can_reuse_modifier_nodes,
    get_binding_name_visible, get_effective_base_type_node, has_scope_marker, is_always_type,
    is_declaration_and_not_visible, is_enclosing_declaration, is_private_method_type_parameter,
    mask_modifier_flags, needs_scope_marker, should_emit_function_properties,
    unwrap_parenthesized_expression,
};
use crate::transformer::Transformer;
use crate::utilities::{is_original_node_single_line, is_simple_inlineable_expression};

/// `type ReferencedFilePair struct` — a referenced file plus the file it was
/// referenced *from* (needed because `GetSourceFileFromReference` resolves
/// relative to the referencing file).
struct ReferencedFilePair {
    file: NodeId,
    ref_: FileReference,
}

/// `type thisPropertyAssignmentKey struct`.
#[derive(PartialEq, Eq, Hash)]
struct ThisPropertyAssignmentKey {
    name: String,
    /// PORT: `node *ast.Node` — used as the identity fallback when no
    /// property name text is available. `Option` mirrors Go nil (the
    /// struct is only stored, never dereferenced).
    node: Option<NodeId>,
    is_static: bool,
    is_private: bool,
}

/// `getThisPropertyAssignmentKey(name, node, isStatic)`.
fn get_this_property_assignment_key(
    name: Option<NodeId>,
    node: NodeId,
    is_static: bool,
    nodes: &[Node],
) -> ThisPropertyAssignmentKey {
    let is_private = name.is_some_and(|n| ast::is_private_identifier(&nodes[n]));
    if let Some(name) = name
        && !ast::is_dynamic_name(name, nodes)
    {
        if let (Some(name_text), true) = ast::try_get_text_of_property_name(name, nodes) {
            return ThisPropertyAssignmentKey {
                name: name_text,
                node: None,
                is_static,
                is_private,
            };
        }
    }
    ThisPropertyAssignmentKey {
        name: String::new(),
        node: Some(node),
        is_static,
        is_private,
    }
}

/// `declarationEmitNodeBuilderFlags` — `Flags` is a `pub u32` newtype
/// whose `BitOr` isn't `const`, so the constant is built on `.0` bits.
const DECLARATION_EMIT_NODE_BUILDER_FLAGS: nodebuilder::Flags = nodebuilder::Flags(
    nodebuilder::Flags::MULTILINE_OBJECT_LITERALS.0
        | nodebuilder::Flags::WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL.0
        | nodebuilder::Flags::USE_TYPE_OF_FUNCTION.0
        | nodebuilder::Flags::USE_STRUCTURAL_FALLBACK.0
        | nodebuilder::Flags::ALLOW_EMPTY_TUPLE.0
        | nodebuilder::Flags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS.0
        | nodebuilder::Flags::NO_TRUNCATION.0,
);

/// `declarationEmitInternalNodeBuilderFlags`.
const DECLARATION_EMIT_INTERNAL_NODE_BUILDER_FLAGS: nodebuilder::InternalFlags =
    nodebuilder::InternalFlags::ALLOW_UNRESOLVED_NAMES;

/// `ast.OEKExpressionTypePassthrough` — `OEKParentheses | OEKAssignments |
/// OEKComma` (the constant doesn't exist in the Rust module yet).
const OEK_EXPRESSION_TYPE_PASSTHROUGH: ast::OuterExpressionKinds = ast::OuterExpressionKinds(
    ast::outer_expression_kinds::PARENTHESES.0
        | ast::outer_expression_kinds::ASSIGNMENTS.0
        | ast::outer_expression_kinds::COMMA.0,
);

/// `type DeclarationTransformer struct` — split into the `Transformer`
/// machinery (visitor + emit context) and the shared `state` the closures
/// capture (Go's pointer receiver methods become methods on the state).
pub struct DeclarationTransformer<'a> {
    /// `transformers.Transformer` — the embedded base: emit context,
    /// transform factory, and the root `NodeVisitor`.
    pub tx: Transformer<'a>,
    /// Everything else that lived on the Go struct.
    state: Rc<DeclarationTransformerState<'a>>,
}

/// The mutable transform state plus the visitor-threaded methods.
struct DeclarationTransformerState<'a> {
    /// `host DeclarationEmitHost`.
    host: Rc<dyn DeclarationEmitHost + 'a>,
    /// `compilerOptions`.
    #[allow(dead_code)]
    compiler_options: &'a CompilerOptions,
    /// `tracker *SymbolTrackerImpl`.
    tracker: Rc<RefCell<SymbolTrackerImpl<'a>>>,
    /// `state *SymbolTrackerSharedState` — `shared` because `state` would
    /// collide with the enclosing struct name.
    shared: Rc<RefCell<SymbolTrackerSharedState<'a>>>,
    /// `resolver printer.EmitResolver`.
    resolver: Rc<RefCell<dyn EmitResolver + 'a>>,
    /// `declarationFilePath`.
    declaration_file_path: RootedFilePath,
    /// The emit context shared with `Transformer`.
    ec: Rc<RefCell<EmitContext>>,
    /// The live bound symbol arena — `TransformOptions::symbols`; every
    /// checker-side helper that Go reaches through `node.Symbol()`
    /// needs it.
    symbols: Option<&'a RefCell<Vec<Symbol>>>,

    /// `needsDeclare`.
    needs_declare: Cell<bool>,
    /// `needsScopeFixMarker`.
    needs_scope_fix_marker: Cell<bool>,
    /// `resultHasScopeMarker`.
    result_has_scope_marker: Cell<bool>,
    /// `enclosingDeclaration`.
    enclosing_declaration: Cell<Option<NodeId>>,
    /// `resultHasExternalModuleIndicator`.
    result_has_external_module_indicator: Cell<bool>,
    /// `suppressNewDiagnosticContexts`.
    suppress_new_diagnostic_contexts: Cell<bool>,
    /// `witnessedCjsExports`.
    witnessed_cjs_exports: RefCell<HashSet<String>>,
    /// `lateStatementReplacementMap map[ast.NodeId]*ast.Node` — `None`
    /// values mean "elided" (Go stored nil), a missing key means "not yet
    /// transformed".
    late_statement_replacement_map: RefCell<HashMap<NodeId, Option<NodeId>>>,
    /// `expandoHosts map[ast.NodeId]*ast.Node`.
    expando_hosts: RefCell<HashMap<NodeId, NodeId>>,
    /// `expandoMembers map[ast.NodeId][]*ast.Node`.
    expando_members: RefCell<HashMap<NodeId, Vec<NodeId>>>,
    /// `deferredExpandoAssignments map[ast.NodeId][]*ast.BinaryExpression`.
    deferred_expando_assignments: RefCell<HashMap<NodeId, Vec<NodeId>>>,
    /// `seenProperties`.
    seen_properties: RefCell<HashSet<ThisPropertyAssignmentKey>>,
    /// `thisPropertyAssignmentsCollected`.
    this_property_assignments_collected: RefCell<Vec<NodeId>>,
    /// `rawReferencedFiles`.
    raw_referenced_files: RefCell<Vec<ReferencedFilePair>>,
    /// `rawTypeReferenceDirectives`.
    raw_type_reference_directives: RefCell<Vec<FileReference>>,
    /// `rawLibReferenceDirectives`.
    raw_lib_reference_directives: RefCell<Vec<FileReference>>,
    /// The root visitor — `tx.Visitor()`; installed after construction.
    root_visitor: RefCell<Option<NodeVisitor<'a>>>,
    /// `bindingNameVisitor`.
    binding_name_visitor: RefCell<Option<NodeVisitor<'a>>>,
    /// `expressionVisitor`.
    expression_visitor: RefCell<Option<NodeVisitor<'a>>>,
    /// `cjsExportAssignmentVisitor`.
    cjs_export_assignment_visitor: RefCell<Option<NodeVisitor<'a>>>,
    /// `exportStrippingVisitor`.
    export_stripping_visitor: RefCell<Option<NodeVisitor<'a>>>,
    /// `thisPropertyVisitor`.
    this_property_visitor: RefCell<Option<NodeVisitor<'a>>>,
    /// `cjsExportAssignment`.
    cjs_export_assignment: Cell<Option<NodeId>>,
    /// `cjsExportMembers`.
    cjs_export_members: RefCell<Vec<NodeId>>,
    /// `cjsExportAssignmentName`.
    cjs_export_assignment_name: Cell<Option<NodeId>>,
    /// `declareStrippingVisitor`.
    declare_stripping_visitor: RefCell<Option<NodeVisitor<'a>>>,
    /// `inClassExpressionDeclaration`.
    in_class_expression_declaration: Cell<bool>,
}

/// `NewDeclarationTransformer(host, resolver, compilerOptions,
/// declarationFilePath)`.
///
/// PORT: Go asserts `resolver != nil && resolver.EmitContext() != nil` and
/// shares that `*EmitContext` with the transformer so the checker's original
/// tracking is visible here. `EmitResolver::emit_context()` in this port
/// returns a `&EmitContext` owned inside the checker (`NodeBuilderImpl.e`),
/// which cannot be shared by `Rc`; the transformer therefore owns a fresh
/// `EmitContext` — see PORTING-NOTES.
pub fn new_declaration_transformer<'a>(
    host: Rc<dyn DeclarationEmitHost + 'a>,
    resolver: Rc<RefCell<dyn EmitResolver + 'a>>,
    compiler_options: &'a CompilerOptions,
    declaration_file_path: RootedFilePath,
    // `TransformOptions::symbols` — required by the tracker for
    // isolated-declaration errors and by the expando paths below.
    symbols: Option<&'a RefCell<Vec<Symbol>>>,
) -> DeclarationTransformer<'a> {
    let shared = Rc::new(RefCell::new(SymbolTrackerSharedState {
        late_marked_statements: Vec::new(),
        diagnostics: Vec::new(),
        get_symbol_accessibility_diagnostic: None,
        error_name_node: None,
        isolated_declarations: compiler_options.isolated_declarations.is_true(),
        strip_internal: compiler_options.strip_internal.is_true(),
        current_source_file: None,
        resolver: resolver.clone(),
        report_expando_function_errors: None,
        deferred_param_diags: Vec::new(),
    }));
    let tracker = SymbolTrackerImpl::new(host.clone(), resolver.clone(), shared.clone(), symbols);
    // `context := resolver.EmitContext()` — the context shared with the
    // printer, not a fresh one: comment ranges and other emit-node metadata
    // assigned during the transform must be visible when the file prints.
    let ec = resolver.borrow().emit_context().clone();
    let state = Rc::new(DeclarationTransformerState {
        host,
        compiler_options,
        tracker: Rc::new(RefCell::new(tracker)),
        shared: shared.clone(),
        resolver: resolver.clone(),
        declaration_file_path,
        ec: ec.clone(),
        symbols,
        needs_declare: Cell::new(true),
        needs_scope_fix_marker: Cell::new(false),
        result_has_scope_marker: Cell::new(false),
        enclosing_declaration: Cell::new(None),
        result_has_external_module_indicator: Cell::new(false),
        suppress_new_diagnostic_contexts: Cell::new(false),
        witnessed_cjs_exports: RefCell::new(HashSet::new()),
        late_statement_replacement_map: RefCell::new(HashMap::new()),
        expando_hosts: RefCell::new(HashMap::new()),
        expando_members: RefCell::new(HashMap::new()),
        deferred_expando_assignments: RefCell::new(HashMap::new()),
        seen_properties: RefCell::new(HashSet::new()),
        this_property_assignments_collected: RefCell::new(Vec::new()),
        raw_referenced_files: RefCell::new(Vec::new()),
        raw_type_reference_directives: RefCell::new(Vec::new()),
        raw_lib_reference_directives: RefCell::new(Vec::new()),
        root_visitor: RefCell::new(None),
        binding_name_visitor: RefCell::new(None),
        expression_visitor: RefCell::new(None),
        cjs_export_assignment_visitor: RefCell::new(None),
        export_stripping_visitor: RefCell::new(None),
        this_property_visitor: RefCell::new(None),
        cjs_export_assignment: Cell::new(None),
        cjs_export_members: RefCell::new(Vec::new()),
        cjs_export_assignment_name: Cell::new(None),
        declare_stripping_visitor: RefCell::new(None),
        in_class_expression_declaration: Cell::new(false),
    });

    // `tx.state.reportExpandoFunctionErrors = func(node) {...}` — installed
    // on the shared state (the tracker invokes it); it captures the resolver
    // and the symbols arena the way the Go closure captures `resolver`.
    shared.borrow_mut().report_expando_function_errors = {
        let resolver = resolver.clone();
        let shared = shared.clone();
        let host = state.host.clone();
        Some(Box::new(move |node: NodeId, nodes: &[Node]| {
            if !shared.borrow().isolated_declarations {
                return;
            }
            let Some(symbols) = symbols else {
                return;
            };
            let props = resolver.borrow().get_properties_of_container_function(
                node,
                nodes,
                &symbols.borrow(),
            );
            for p in props {
                let value_declaration = symbols.borrow()[p.index()].value_declaration;
                // `value_declaration` lives in its program arena, not the emit
                // working buffer — resolve through the host.
                let decl_node =
                    value_declaration.and_then(|d| host.resolve_node(d, nodes));
                if decl_node.as_ref().is_some_and(|n| ast::is_binary_expression(n)) {
                    let error_target = decl_node
                        .as_ref()
                        .unwrap()
                        .as_binary_expression()
                        .left
                        .expect("BinaryExpression.left");
                    shared.borrow_mut().add_diagnostic(create_diagnostic_for_node(
                        nodes,
                        Some(error_target),
                        &tsc_diagnostics::Assigning_properties_to_functions_without_declaring_them_is_not_supported_with_isolatedDeclarations_Add_an_explicit_declaration_for_the_properties_assigned_to_this_function,
                        &[] as &[String],
                    ));
                }
            }
        }))
        .map(|f| Rc::new(f) as Rc<dyn Fn(NodeId, &[Node]) + 'a>)
    };

    // `tx.NewTransformer(tx.visit, context)`.
    let visit: Box<tsc_ast::visitor::VisitFn<'a>> = {
        let state = state.clone();
        Box::new(move |v, cx, node| state.visit(v, cx, node))
    };
    let tx = Transformer::new(visit, Some(ec));

    // The remaining visitors. Each visit fn is handed its own `v`, which is
    // what Go reaches through `tx.bindingNameVisitor` &co. when recurring.
    *state.root_visitor.borrow_mut() = {
        let state = state.clone();
        Some(
            tx.emit_context()
                .borrow()
                .new_node_visitor(Box::new(move |v, cx, node| state.visit(v, cx, node))),
        )
    };
    *state.binding_name_visitor.borrow_mut() = {
        let state = state.clone();
        Some(
            tx.emit_context()
                .borrow()
                .new_node_visitor(Box::new(move |v, cx, node| {
                    state.visit_binding_name(v, cx, node)
                })),
        )
    };
    *state.expression_visitor.borrow_mut() = {
        let state = state.clone();
        Some(
            tx.emit_context()
                .borrow()
                .new_node_visitor(Box::new(move |v, cx, node| {
                    state.visit_nested_expression(v, cx, node)
                })),
        )
    };
    *state.export_stripping_visitor.borrow_mut() = {
        let state = state.clone();
        Some(
            tx.emit_context()
                .borrow()
                .new_node_visitor(Box::new(move |_v, cx, node| {
                    Some(state.strip_export_modifiers(cx, node))
                })),
        )
    };
    *state.this_property_visitor.borrow_mut() = {
        let state = state.clone();
        Some(
            tx.emit_context()
                .borrow()
                .new_node_visitor(Box::new(move |v, cx, node| {
                    state.visit_this_property_assignments(v, cx, node)
                })),
        )
    };
    *state.cjs_export_assignment_visitor.borrow_mut() = {
        let state = state.clone();
        Some(
            tx.emit_context()
                .borrow()
                .new_node_visitor(Box::new(move |v, cx, node| {
                    state.visit_cjs_export_assignments(v, cx, node)
                })),
        )
    };
    *state.declare_stripping_visitor.borrow_mut() = {
        let state = state.clone();
        Some(
            tx.emit_context()
                .borrow()
                .new_node_visitor(Box::new(move |_v, cx, node| {
                    Some(state.strip_declare_modifiers(cx, node))
                })),
        )
    };

    DeclarationTransformer { tx, state }
}

impl<'a> DeclarationTransformer<'a> {
    /// `(tx *DeclarationTransformer) GetDiagnostics`.
    pub fn get_diagnostics(&self) -> Vec<tsc_ast::diagnostic::DiagnosticRef> {
        // Recompute parameter diagnostics whose `addUndefined` verdict came
        // from the degraded `RequiresAddingImplicitUndefinedUnsafe` fallback
        // (checker already borrowed inside the node builder). The checker is
        // free here, so the real verdict is available; the rebuilt diagnostic
        // overwrites the Arc's contents in place, preserving order.
        let fixups = std::mem::take(
            &mut self.state.shared.borrow_mut().deferred_param_diags,
        );
        for fixup in fixups {
            let Some(nodes) = self.state.host.arena_for(fixup.node.file_index(), &[])
            else {
                continue;
            };
            let add_undefined = self
                .state
                .resolver
                .borrow()
                .requires_adding_implicit_undefined(
                    fixup.node,
                    None,
                    None,
                    &nodes,
                    &[],
                );
            let correct = crate::declarations::diagnostics::build_param_diag(
                fixup.node,
                &nodes,
                add_undefined,
            );
            *tsc_ast::diagnostic::lock_diagnostic(&fixup.diag) =
                tsc_ast::diagnostic::lock_diagnostic(&correct).clone();
        }
        self.state.shared.borrow().diagnostics.clone()
    }

    /// `tx.TransformSourceFile(file)` — delegates to `Transformer`.
    pub fn transform_source_file(&self, nodes: &mut Vec<Node>, file: NodeId) -> Option<NodeId> {
        self.tx.transform_source_file(nodes, file)
    }
}

impl<'a> DeclarationTransformerState<'a> {
    /// `tx.EmitContext()` — shared handle for the short-lived borrows the
    /// port uses everywhere.
    fn ec(&self) -> std::cell::Ref<'_, EmitContext> {
        self.ec.borrow()
    }

    /// `(tx *DeclarationTransformer) shouldStripInternal`.
    fn should_strip_internal(&self, node: Option<NodeId>, nodes: &[Node]) -> bool {
        self.shared.borrow().strip_internal
            && node.is_some()
            && self.is_internal_declaration(node, nodes)
    }

    /// `(tx *DeclarationTransformer) isInternalDeclaration`.
    fn is_internal_declaration(&self, node: Option<NodeId>, nodes: &[Node]) -> bool {
        let Some(node) = node else {
            return false;
        };
        let Some(source_file) = self.shared.borrow().current_source_file else {
            return false;
        };
        let Some(parse_tree_node) = self.ec().most_original(Some(node)) else {
            return false;
        };
        if !ast::is_parse_tree_node(&nodes[parse_tree_node]) {
            return false;
        }
        let text = &nodes[source_file].as_source_file().text;

        if nodes[parse_tree_node].kind == Kind::Parameter {
            let params = nodes[parse_tree_node]
                .parent
                .and_then(|p| nodes[p].parameters())
                .map(|p| p.to_vec())
                .unwrap_or_default();
            let param_idx = params.iter().position(|&p| p == parse_tree_node);
            let previous_sibling = param_idx.filter(|&i| i > 0).map(|i| params[i - 1]);

            let mut comment_ranges: Vec<ast::CommentRange> = Vec::new();
            let f = ast::NodeFactory::default();
            if let Some(previous_sibling) = previous_sibling {
                // to handle
                // ... parameters, /** @internal */
                // public param: string
                let trailing_pos = scanner::scanner::skip_trivia_ex(
                    text,
                    nodes[previous_sibling].end() + 1,
                    Some(&SkipTriviaOptions {
                        stop_at_comments: true,
                        ..Default::default()
                    }),
                );
                comment_ranges.extend(scanner::scanner::get_trailing_comment_ranges(
                    &f,
                    text,
                    trailing_pos,
                ));
                comment_ranges.extend(scanner::scanner::get_leading_comment_ranges(
                    &f,
                    text,
                    nodes[node].pos(),
                ));
            } else {
                let trailing_pos = scanner::scanner::skip_trivia_ex(
                    text,
                    nodes[node].pos(),
                    Some(&SkipTriviaOptions {
                        stop_at_comments: true,
                        ..Default::default()
                    }),
                );
                comment_ranges.extend(scanner::scanner::get_trailing_comment_ranges(
                    &f,
                    text,
                    trailing_pos,
                ));
            }

            if let Some(last) = comment_ranges.last() {
                return has_internal_annotation(*last, source_file, nodes);
            }
            return false;
        }

        for comment_range in
            self.get_leading_comment_ranges_of_node(parse_tree_node, source_file, nodes)
        {
            if has_internal_annotation(comment_range, source_file, nodes) {
                return true;
            }
        }
        false
    }

    /// `(tx *DeclarationTransformer) getLeadingCommentRangesOfNode`.
    fn get_leading_comment_ranges_of_node(
        &self,
        node: NodeId,
        source_file: NodeId,
        nodes: &[Node],
    ) -> Vec<ast::CommentRange> {
        if nodes[node].kind == Kind::JsxText {
            return Vec::new();
        }
        scanner::scanner::get_leading_comment_ranges(
            &ast::NodeFactory::default(),
            &nodes[source_file].as_source_file().text,
            nodes[node].pos(),
        )
    }

    /// `(tx *DeclarationTransformer) visit` — functions as both
    /// `visitDeclarationStatements` and `transformRoot`.
    fn visit<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        match cx.nodes[node].kind {
            Kind::SourceFile => self.visit_source_file(v, cx, node),
            // statements we keep but do something to
            Kind::FunctionDeclaration
            | Kind::ModuleDeclaration
            | Kind::ImportEqualsDeclaration
            | Kind::InterfaceDeclaration
            | Kind::ClassDeclaration
            | Kind::JSTypeAliasDeclaration
            | Kind::TypeAliasDeclaration
            | Kind::EnumDeclaration
            | Kind::VariableStatement
            | Kind::ImportDeclaration
            | Kind::JSImportDeclaration
            | Kind::ExportDeclaration
            | Kind::ExportAssignment => self.visit_declaration_statements(v, cx, node),
            // statements we elide
            Kind::BreakStatement
            | Kind::ContinueStatement
            | Kind::DebuggerStatement
            | Kind::DoStatement
            | Kind::EmptyStatement
            | Kind::ForInStatement
            | Kind::ForOfStatement
            | Kind::ForStatement
            | Kind::IfStatement
            | Kind::LabeledStatement
            | Kind::ReturnStatement
            | Kind::SwitchStatement
            | Kind::ThrowStatement
            | Kind::TryStatement
            | Kind::WhileStatement
            | Kind::WithStatement
            | Kind::NotEmittedStatement
            | Kind::Block
            | Kind::MissingDeclaration
            | Kind::ExpressionStatement => None,
            // parts of things, things we just visit children of
            _ => self.visit_declaration_subtree(v, cx, node),
        }
    }

    /// `(tx *DeclarationTransformer) visitSourceFile`.
    fn visit_source_file<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        self.cjs_export_assignment_name.set(None);
        if cx.nodes[node].as_source_file().is_declaration_file {
            return Some(node);
        }

        self.needs_declare.set(true);
        self.needs_scope_fix_marker.set(false);
        self.result_has_scope_marker.set(false);
        self.enclosing_declaration.set(Some(node));
        self.shared.borrow_mut().get_symbol_accessibility_diagnostic = Some(throw_diagnostic());
        self.result_has_external_module_indicator.set(false);
        self.suppress_new_diagnostic_contexts.set(false);
        self.shared.borrow_mut().late_marked_statements = Vec::new();
        self.late_statement_replacement_map.borrow_mut().clear();
        self.expando_hosts.borrow_mut().clear();
        self.expando_members.borrow_mut().clear();
        self.deferred_expando_assignments.borrow_mut().clear();
        self.raw_referenced_files.borrow_mut().clear();
        self.raw_type_reference_directives.borrow_mut().clear();
        self.raw_lib_reference_directives.borrow_mut().clear();
        self.witnessed_cjs_exports.borrow_mut().clear();
        self.shared.borrow_mut().current_source_file = Some(node);
        self.collect_file_references(node, cx.nodes);
        let original = self.ec().most_original(Some(node)).unwrap_or(node);
        self.resolver
            .borrow_mut()
            .precalculate_declaration_emit_visibility(original, cx.nodes);
        let updated = self.transform_source_file_impl(v, cx, node);
        self.shared.borrow_mut().current_source_file = None;
        updated
    }

    /// `(tx *DeclarationTransformer) collectFileReferences`.
    fn collect_file_references(&self, source_file: NodeId, nodes: &[Node]) {
        let file = nodes[source_file].as_source_file();
        let pairs: Vec<ReferencedFilePair> = file
            .referenced_files
            .iter()
            .map(|ref_| ReferencedFilePair {
                file: source_file,
                ref_: ref_.clone(),
            })
            .collect();
        self.raw_referenced_files.borrow_mut().extend(pairs);
        self.raw_type_reference_directives
            .borrow_mut()
            .extend(file.type_reference_directives.iter().cloned());
        self.raw_lib_reference_directives
            .borrow_mut()
            .extend(file.lib_reference_directives.iter().cloned());
    }

    /// `(tx *DeclarationTransformer) appendCjsExports`.
    fn append_cjs_exports(
        &self,
        combined_statements: NodeList,
        cx: &mut VisitorCx<'_, '_>,
    ) -> NodeList {
        let mut result: Vec<NodeId> = Vec::new();
        if let Some(assignment) = self.cjs_export_assignment.get() {
            result.push(assignment);
        }
        result.extend_from_slice(&self.cjs_export_members.borrow());
        result.extend_from_slice(&combined_statements.nodes);
        let statement_nodes = flatten_syntax_lists(&result, cx.nodes);
        if statement_nodes.len() != combined_statements.nodes.len() {
            return self.ec().factory.new_node_list(statement_nodes);
        }
        combined_statements
    }

    /// `(tx *DeclarationTransformer) transformSourceFile`.
    fn transform_source_file_impl<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        self.cjs_export_assignment.set(None);
        self.cjs_export_assignment_name.set(None);
        self.cjs_export_members.borrow_mut().clear();
        // Go `defer` — cleared again on exit below.
        self.cjs_export_assignment_visitor
            .borrow()
            .as_ref()
            .expect("cjsExportAssignmentVisitor")
            .visit_node(cx, Some(node)); // collect nested module.exports= assignments
        self.expression_visitor
            .borrow()
            .as_ref()
            .expect("expressionVisitor")
            .visit_node(cx, Some(node)); // collect expando members (requires any export assignment be located in advance)
        let source_statements = cx.nodes[node].as_source_file().statements.clone();
        let statements = v
            .visit_nodes(cx, source_statements.clone())
            .or(source_statements)
            .expect("SourceFile.statements");
        let statements_loc = statements.loc;
        let mut combined_statements =
            self.transform_and_replace_late_painted_statements(v, cx, statements);
        combined_statements = self.append_cjs_exports(combined_statements, cx);
        combined_statements.loc = statements_loc; // setTextRange

        if ast::is_external_or_commonjs_module(cx.nodes[node].as_source_file()) {
            if ast::is_in_js_file(Some(node), cx.nodes) {
                if let Some((symbol, symbols)) = cx.nodes[node].symbol().zip(self.symbols) {
                    if let Some(export_equals) = symbols.borrow()[symbol.index()]
                        .exports
                        .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
                    {
                        let declarations =
                            symbols.borrow()[export_equals.index()].declarations.clone();
                        if declarations.len() > 1 {
                            for decl in declarations {
                                self.shared.borrow_mut().add_diagnostic(
                                    create_diagnostic_for_node(
                                        cx.nodes,
                                        Some(decl),
                                        &tsc_diagnostics::Multiple_module_exports_assignments_cannot_be_serialized_for_declaration_emit,
                                        &[] as &[String],
                                    ),
                                );
                            }
                        }
                    }
                }
            }
            if !self.result_has_external_module_indicator.get()
                || (self.needs_scope_fix_marker.get() && !self.result_has_scope_marker.get())
            {
                let marker = create_empty_exports(&mut self.ec.borrow_mut().factory, cx.nodes);
                let mut new_list = combined_statements.nodes.to_vec();
                new_list.push(marker);
                let mut with_marker = self.ec().factory.new_node_list(new_list);
                with_marker.loc = combined_statements.loc;
                combined_statements = with_marker;
            }
        }

        let end_of_file_token = cx.nodes[node].as_source_file().end_of_file_token;
        let result = self
            .ec
            .borrow_mut()
            .factory
            .update_source_file(cx.nodes, node, Some(combined_statements), end_of_file_token)
            .unwrap_or(node);
        let lib_references = self.get_lib_references();
        cx.nodes[result]
            .as_source_file_mut()
            .lib_reference_directives = lib_references.into_boxed_slice();
        let type_references = self.get_type_references();
        cx.nodes[result]
            .as_source_file_mut()
            .type_reference_directives = type_references.into_boxed_slice();
        cx.nodes[result].as_source_file_mut().is_declaration_file = true;
        let referenced_files =
            self.get_referenced_files(&self.declaration_file_path.directory(), cx.nodes);
        cx.nodes[result].as_source_file_mut().referenced_files =
            referenced_files.into_boxed_slice();

        // `defer` cleanup of the CJS capture state.
        self.cjs_export_assignment.set(None);
        self.cjs_export_assignment_name.set(None);
        self.cjs_export_members.borrow_mut().clear();
        Some(result)
    }

    /// `(tx *DeclarationTransformer) transformAndReplaceLatePaintedStatements`.
    fn transform_and_replace_late_painted_statements<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        statements: NodeList,
    ) -> NodeList {
        // This is a `while` loop because `handleSymbolAccessibilityError` can see additional import aliases marked as visible during
        // error handling which must now be included in the output and themselves checked for errors.
        // For example:
        // ```
        // module A {
        //   export module Q {}
        //   import B = Q;
        //   import C = B;
        //   export import D = C;
        // }
        // ```
        // In such a scenario, only Q and D are initially visible, but we don't consider imports as private names - instead we say they if they are referenced they must
        // be recorded. So while checking D's visibility we mark C as visible, then we must check C which in turn marks B, completing the chain of
        // dependent imports and allowing a valid declaration file output. Today, this dependent alias marking only happens for internal import aliases.
        loop {
            if self.shared.borrow().late_marked_statements.is_empty() {
                break;
            }
            let next = self.shared.borrow_mut().late_marked_statements.remove(0);

            let save_needs_declare = self.needs_declare.get();
            self.needs_declare.set(
                cx.nodes[next]
                    .parent
                    .is_some_and(|p| ast::is_source_file(&cx.nodes[p])),
            );

            let result = self.transform_top_level_declaration(v, cx, next);

            self.needs_declare.set(save_needs_declare);
            let original = self.ec().most_original(Some(next)).unwrap_or(next);
            let id = ast::get_node_id(&cx.nodes[original]);
            self.late_statement_replacement_map
                .borrow_mut()
                .insert(id, result);
        }

        // And lastly, we need to get the final form of all those indetermine import declarations from before and add them to the output list
        // (and remove them from the set to examine for outter declarations)
        let mut results: Vec<NodeId> = Vec::with_capacity(statements.nodes.len());
        for &statement in statements.nodes.iter() {
            if !ast::is_late_visibility_painted_statement(&cx.nodes[statement]) {
                results.push(statement);
                continue;
            }
            let original = self
                .ec()
                .most_original(Some(statement))
                .unwrap_or(statement);
            let id = ast::get_node_id(&cx.nodes[original]);
            let replacement = self
                .late_statement_replacement_map
                .borrow()
                .get(&id)
                .copied();
            let Some(replacement) = replacement else {
                results.push(statement);
                continue; // not replaced
            };
            let Some(replacement) = replacement else {
                continue; // deleted
            };
            if cx.nodes[replacement].kind == Kind::SyntaxList {
                if !self.needs_scope_fix_marker.get()
                    || !self.result_has_external_module_indicator.get()
                {
                    let children = cx.nodes[replacement].as_syntax_list().children.clone();
                    for elem in children {
                        if needs_scope_marker(&cx.nodes[elem], cx.nodes) {
                            self.needs_scope_fix_marker.set(true);
                        }
                        if cx.nodes[statement]
                            .parent
                            .is_some_and(|p| ast::is_source_file(&cx.nodes[p]))
                            && ast::is_external_module_indicator(&cx.nodes[elem])
                        {
                            self.result_has_external_module_indicator.set(true);
                        }
                    }
                }
                results.extend_from_slice(&cx.nodes[replacement].as_syntax_list().children);
            } else {
                if needs_scope_marker(&cx.nodes[replacement], cx.nodes) {
                    self.needs_scope_fix_marker.set(true);
                }
                if cx.nodes[statement]
                    .parent
                    .is_some_and(|p| ast::is_source_file(&cx.nodes[p]))
                    && ast::is_external_module_indicator(&cx.nodes[replacement])
                {
                    self.result_has_external_module_indicator.set(true);
                }
                results.push(replacement);
            }
        }

        self.ec().factory.new_node_list(results)
    }

    /// `(tx *DeclarationTransformer) getReferencedFiles` — handles path
    /// rewrites for preserved triple-slash `/// <reference path=... />`
    /// comments.
    fn get_referenced_files(
        &self,
        output_file_path: &tspath::RootedDirectoryPath,
        nodes: &[Node],
    ) -> Vec<FileReference> {
        let mut results: Vec<FileReference> = Vec::new();
        for pair in self.raw_referenced_files.borrow().iter() {
            let source_file = pair.file;
            let ref_ = &pair.ref_;

            if !ref_.preserve {
                continue;
            }

            let Some(file) = self
                .host
                .get_source_file_from_reference(source_file, ref_, nodes)
            else {
                continue;
            };

            let decl_file_name: RootedFilePath;
            // `file` lives in its own program arena, not the emit working
            // buffer — resolve through the host.
            let Some(file_node) = self.host.resolve_node(file, nodes) else {
                continue;
            };
            if file_node.as_source_file().is_declaration_file {
                decl_file_name = file_node.as_source_file().file_name().clone();
            } else {
                // Try to use output path for referenced file, or output js path if that doesn't exist, or the input path if all else fails
                let Some(paths) = self.host.get_output_paths_for(file, true, nodes) else {
                    continue;
                };
                let mut decl = paths.declaration_file_path().clone();
                if decl.as_string().is_empty() {
                    decl = paths.js_file_path().clone();
                }
                if decl.as_string().is_empty() {
                    decl = file_node.as_source_file().file_name().clone();
                }
                decl_file_name = decl;
            }
            // Should only be missing if the source file is missing a fileName (at which point we can't name a reference to it anyway)
            // TODO: Shouldn't this be a crash or assert instead of a silent continue?
            if decl_file_name.as_string().is_empty() {
                continue;
            }

            let file_name = tspath::get_relative_path_to_directory_or_url(
                output_file_path.as_string(),
                decl_file_name.as_string(),
                false,
                self.host.case_sensitivity(),
            );

            results.push(FileReference {
                text_range: TextRange::new(-1, -1),
                file_name,
                resolution_mode: ref_.resolution_mode,
                preserve: ref_.preserve,
            });
        }
        results
    }

    /// `(tx *DeclarationTransformer) getLibReferences`.
    fn get_lib_references(&self) -> Vec<FileReference> {
        // clone retained references
        let mut result = Vec::new();
        for ref_ in self.raw_lib_reference_directives.borrow().iter() {
            if !ref_.preserve {
                continue;
            }
            result.push(FileReference {
                text_range: TextRange::new(-1, -1),
                file_name: ref_.file_name.clone(),
                resolution_mode: ref_.resolution_mode,
                preserve: ref_.preserve,
            });
        }
        result
    }

    /// `(tx *DeclarationTransformer) getTypeReferences`.
    fn get_type_references(&self) -> Vec<FileReference> {
        // clone retained references
        let mut result = Vec::new();
        for ref_ in self.raw_type_reference_directives.borrow().iter() {
            if !ref_.preserve {
                continue;
            }
            result.push(FileReference {
                text_range: TextRange::new(-1, -1),
                file_name: ref_.file_name.clone(),
                resolution_mode: ref_.resolution_mode,
                preserve: ref_.preserve,
            });
        }
        result
    }

    /// `(tx *DeclarationTransformer) setupDiagnosticContext`.
    ///
    /// PORT: Go returns `(bool, func())` — the cleanup is an RAII guard
    /// here (dropping it restores the selector, name node, and suppression
    /// state).
    fn setup_diagnostic_context<'s>(
        &'s self,
        input: NodeId,
        nodes: &[Node],
    ) -> (bool, DiagnosticContextGuard<'s, 'a>) {
        let can_produce_diagnostic = can_produce_diagnostics(&nodes[input]);
        let old_within_object_literal_type = self.suppress_new_diagnostic_contexts.get();
        let should_enter_suppress_new_diagnostics_context =
            (nodes[input].kind == Kind::TypeLiteral || nodes[input].kind == Kind::MappedType)
                && !nodes[input].parent.is_some_and(|p| {
                    nodes[p].kind == Kind::TypeAliasDeclaration
                        || nodes[p].kind == Kind::JSTypeAliasDeclaration
                });

        let mut shared = self.shared.borrow_mut();
        let diag_replaced = can_produce_diagnostic && !self.suppress_new_diagnostic_contexts.get();
        let old_diag = if diag_replaced {
            std::mem::replace(
                &mut shared.get_symbol_accessibility_diagnostic,
                Some(create_get_symbol_accessibility_diagnostic_for_node(
                    input, nodes,
                )),
            )
        } else {
            None
        };
        let old_name = shared.error_name_node;
        drop(shared);

        if should_enter_suppress_new_diagnostics_context {
            self.suppress_new_diagnostic_contexts.set(true);
        }

        (
            can_produce_diagnostic,
            DiagnosticContextGuard {
                state: self,
                old_diag,
                diag_replaced,
                old_name,
                old_suppress: old_within_object_literal_type,
            },
        )
    }
}

/// RAII guard for the `(bool, func())` cleanup Go returns from
/// `setupDiagnosticContext`. Dropping restores
/// `getSymbolAccessibilityDiagnostic`, `errorNameNode`, and
/// `suppressNewDiagnosticContexts`.
struct DiagnosticContextGuard<'s, 'a> {
    state: &'s DeclarationTransformerState<'a>,
    old_diag: Option<GetSymbolAccessibilityDiagnostic>,
    /// `getSymbolAccessibilityDiagnostic` is only swapped when the context
    /// was actually installed; otherwise Go's restore would clobber the
    /// selector installed by a nested context that never ran.
    diag_replaced: bool,
    old_name: Option<NodeId>,
    old_suppress: bool,
}

impl<'s, 'a> Drop for DiagnosticContextGuard<'s, 'a> {
    fn drop(&mut self) {
        let mut shared = self.state.shared.borrow_mut();
        if self.diag_replaced {
            shared.get_symbol_accessibility_diagnostic = self.old_diag.take();
        }
        shared.error_name_node = self.old_name;
        drop(shared);
        self.state
            .suppress_new_diagnostic_contexts
            .set(self.old_suppress);
    }
}

/// `hasInternalAnnotation(commentRange, sourceFile)`.
fn has_internal_annotation(
    comment_range: ast::CommentRange,
    source_file: NodeId,
    nodes: &[Node],
) -> bool {
    let text = &nodes[source_file].as_source_file().text;
    let comment =
        &text[comment_range.text_range.pos() as usize..comment_range.text_range.end() as usize];
    comment.contains("@internal")
}

/// `nodeOrSyntaxListChildren(node)` — expand a SyntaxList to its children.
fn node_or_syntax_list_children(node: NodeId, nodes: &[Node]) -> Vec<NodeId> {
    if ast::is_syntax_list(&nodes[node]) {
        return nodes[node].as_syntax_list().children.to_vec();
    }
    vec![node]
}

/// `flattenSyntaxLists(nodes)`.
fn flatten_syntax_lists(list: &[NodeId], nodes: &[Node]) -> Vec<NodeId> {
    let mut out = Vec::new();
    for &node in list {
        out.extend(node_or_syntax_list_children(node, nodes));
    }
    out
}

/// `createEmptyExports(factory)` — `export {}` scope marker.
fn create_empty_exports(f: &mut tsc_printer::NodeFactory, nodes: &mut Vec<Node>) -> NodeId {
    let empty_list = f.new_node_list(Vec::new());
    let empty_exports = f.new_named_exports(nodes, Some(empty_list));
    f.new_export_declaration(nodes, None, false, Some(empty_exports), None, None)
}

/// `throwDiagnostic` — Go installs a selector that panics when the tracker
/// produces an error without a diagnostic context.
fn throw_diagnostic() -> GetSymbolAccessibilityDiagnostic {
    Box::new(|_, _| panic!("Diagnostic emitted without context"))
}

impl<'a> DeclarationTransformerState<'a> {
    /// `(tx *DeclarationTransformer) visitDeclarationSubtree`.
    fn visit_declaration_subtree<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        if self.should_strip_internal(Some(input), cx.nodes) {
            return None;
        }
        if ast::is_declaration(&cx.nodes[input]) {
            if is_declaration_and_not_visible(&self.ec(), &*self.resolver.borrow(), input, cx.nodes)
            {
                return None;
            }
            if ast::has_dynamic_name(input, cx.nodes) {
                let name_expression = cx.nodes[input]
                    .name()
                    .and_then(|n| cx.nodes[n].expression());
                if self.shared.borrow().isolated_declarations {
                    // Classes and object literals usually elide properties with computed names that are not of a literal type
                    // In isolated declarations TSC needs to error on these as we don't know the type in a DTE.
                    if !self
                        .resolver
                        .borrow()
                        .is_definitely_reference_to_global_symbol_object(
                            name_expression.unwrap_or(input),
                            cx.nodes,
                        )
                    {
                        let parent = cx.nodes[input].parent;
                        if parent.is_some_and(|p| {
                            ast::is_class_declaration(&cx.nodes[p])
                                || ast::is_object_literal_expression(&cx.nodes[p])
                        }) {
                            self.shared.borrow_mut().add_diagnostic(
                                create_diagnostic_for_node(
                                    cx.nodes,
                                    Some(input),
                                    &tsc_diagnostics::Computed_property_names_on_class_or_object_literals_cannot_be_inferred_with_isolatedDeclarations,
                                    &[] as &[String],
                                ),
                            );
                            return None;
                        } else if parent.is_some_and(|p| {
                            ast::is_interface_declaration(&cx.nodes[p])
                                || ast::is_type_literal_node(&cx.nodes[p])
                        }) && !name_expression
                            .is_some_and(|e| ast::is_entity_name_expression(&cx.nodes[e], cx.nodes))
                        {
                            // Type declarations just need to double-check that the input computed name is an entity name expression
                            self.shared.borrow_mut().add_diagnostic(
                                create_diagnostic_for_node(
                                    cx.nodes,
                                    Some(input),
                                    &tsc_diagnostics::Computed_properties_must_be_number_or_string_literals_variables_or_dotted_expressions_with_isolatedDeclarations,
                                    &[] as &[String],
                                ),
                            );
                            return None;
                        }
                    }
                } else if !self.resolver.borrow().is_late_bound(
                    self.ec().parse_node(cx.nodes, input).unwrap_or(input),
                    cx.nodes,
                ) || !name_expression
                    .is_some_and(|e| ast::is_entity_name_expression(&cx.nodes[e], cx.nodes))
                {
                    return None;
                }
            }
        }

        // Elide implementation signatures from overload sets
        if ast::is_function_like(Some(input), cx.nodes)
            && self
                .resolver
                .borrow()
                .is_implementation_of_overload(input, cx.nodes)
        {
            return None;
        }

        if cx.nodes[input].kind == Kind::SemicolonClassElement {
            return None;
        }

        if ast::is_heritage_clause(&cx.nodes[input]) {
            let types = cx.nodes[input].as_heritage_clause().types.clone();
            if types.as_ref().is_none_or(|t| {
                t.nodes.is_empty()
                    || (t.nodes.len() == 1
                        && ast::node_is_missing(t.nodes.first().copied(), cx.nodes))
            }) {
                return None;
            }
        }

        let previous_enclosing_declaration = self.enclosing_declaration.get();
        if is_enclosing_declaration(&cx.nodes[input], cx.nodes) {
            self.enclosing_declaration.set(Some(input));
        }

        let (can_produce_diagnostic, cleanup) = self.setup_diagnostic_context(input, cx.nodes);

        let result: Option<NodeId>;
        match cx.nodes[input].kind {
            Kind::MappedType => {
                result = Some(self.transform_mapped_type_node(v, cx, input));
            }
            Kind::HeritageClause => {
                result = self.transform_heritage_clause(v, cx, input);
            }
            Kind::MethodSignature => {
                result = self.transform_method_signature_declaration(v, cx, input);
            }
            Kind::MethodDeclaration => {
                result = self.transform_method_declaration(v, cx, input);
            }
            Kind::ConstructSignature => {
                result = Some(self.transform_construct_signature_declaration(v, cx, input));
            }
            Kind::Constructor => {
                result = Some(self.transform_constructor_declaration(v, cx, input));
            }
            Kind::GetAccessor => {
                result = self.transform_get_accessor_declaration(v, cx, input);
            }
            Kind::SetAccessor => {
                result = self.transform_set_accessor_declaration(v, cx, input);
            }
            Kind::PropertyDeclaration => {
                result = self.transform_property_declaration(v, cx, input);
            }
            Kind::PropertySignature => {
                result = self.transform_property_signature_declaration(v, cx, input);
            }
            Kind::CallSignature => {
                result = Some(self.transform_call_signature_declaration(v, cx, input));
            }
            Kind::IndexSignature => {
                result = Some(self.transform_index_signature_declaration(v, cx, input));
            }
            Kind::VariableDeclaration => {
                result = self.transform_variable_declaration(v, cx, input);
            }
            Kind::TypeParameter => {
                result = self.transform_type_parameter_declaration(v, cx, input);
            }
            Kind::ExpressionWithTypeArguments => {
                result = Some(self.transform_expression_with_type_arguments(v, cx, input));
            }
            Kind::TypeReference => {
                result = self.transform_type_reference(v, cx, input);
            }
            Kind::ConditionalType => {
                result = Some(self.transform_conditional_type_node(v, cx, input));
            }
            Kind::FunctionType => {
                result = Some(self.transform_function_type_node(v, cx, input));
            }
            Kind::ConstructorType => {
                result = Some(self.transform_constructor_type_node(v, cx, input));
            }
            Kind::ImportType => {
                result = Some(self.transform_import_type_node(v, cx, input));
            }
            Kind::TypeQuery => {
                let expr_name = cx.nodes[input].as_type_query_node().expr_name;
                self.check_entity_name_visibility(
                    expr_name,
                    self.enclosing_declaration.get(),
                    cx.nodes,
                );
                result = v.visit_each_child(cx, input).or(Some(input));
            }
            Kind::QualifiedName => {
                let right = cx.nodes[input].as_qualified_name().right;
                if right.is_some_and(|r| cx.nodes[r].kind == Kind::PrivateIdentifier) {
                    let text = right
                        .map(|r| cx.nodes[r].text(cx.nodes).into_owned())
                        .unwrap_or_default();
                    self.shared.borrow_mut().add_diagnostic(create_diagnostic_for_node(
                        cx.nodes,
                        Some(input),
                        &tsc_diagnostics::Declaration_emit_elides_private_members_but_0_refers_to_a_private_member_Write_an_explicit_type_here,
                        &[text],
                    ));
                }
                result = v.visit_each_child(cx, input).or(Some(input));
            }
            Kind::TupleType => {
                result = v.visit_each_child(cx, input).or(Some(input));
                if let Some(r) = result {
                    if is_original_node_single_line(&self.ec(), cx.nodes, Some(input)) {
                        self.ec().add_emit_flags(r, EmitFlags::SINGLE_LINE);
                    }
                }
            }
            Kind::JSDocTypeExpression => {
                result = Some(self.transform_js_doc_type_expression(v, cx, input));
            }
            Kind::JSDocTypeLiteral => {
                result = Some(self.transform_js_doc_type_literal(v, cx, input));
            }
            Kind::JSDocPropertyTag => {
                result = Some(self.transform_js_doc_property_tag(v, cx, input));
            }
            Kind::JSDocAllType => {
                result = Some(self.transform_js_doc_all_type(v, cx, input));
            }
            Kind::JSDocNullableType => {
                result = Some(self.transform_js_doc_nullable_type(v, cx, input));
            }
            Kind::JSDocNonNullableType => {
                result = Some(self.transform_js_doc_non_nullable_type(v, cx, input));
            }
            Kind::JSDocOptionalType => {
                result = Some(self.transform_js_doc_optional_type(v, cx, input));
            }
            Kind::JSDocVariadicType => {
                result = Some(self.transform_js_doc_variadic_type(v, cx, input));
            }
            _ => {
                result = v.visit_each_child(cx, input).or(Some(input));
            }
        }

        if result.is_some() && can_produce_diagnostic && ast::has_dynamic_name(input, cx.nodes) {
            self.check_name(input, cx.nodes);
        }

        drop(cleanup);
        self.enclosing_declaration
            .set(previous_enclosing_declaration);
        result
    }

    /// `(tx *DeclarationTransformer) checkName`.
    fn check_name(&self, node: NodeId, nodes: &[Node]) {
        let old_diag = {
            let mut shared = self.shared.borrow_mut();
            let old = shared.get_symbol_accessibility_diagnostic.take();
            if !self.suppress_new_diagnostic_contexts.get() {
                shared.get_symbol_accessibility_diagnostic = Some(
                    create_get_symbol_accessibility_diagnostic_for_node_name(node, nodes),
                );
            }
            shared.error_name_node = nodes[node].name();
            old
        };
        debug_assert!(ast::has_dynamic_name(node, nodes)); // Should only be called with dynamic names
        let entity_name = nodes[node].name().and_then(|n| nodes[n].expression());
        self.check_entity_name_visibility(entity_name, self.enclosing_declaration.get(), nodes);
        {
            let mut shared = self.shared.borrow_mut();
            if !self.suppress_new_diagnostic_contexts.get() {
                shared.get_symbol_accessibility_diagnostic = old_diag;
            }
            shared.error_name_node = None;
        }
    }

    /// `(tx *DeclarationTransformer) transformMappedTypeNode`.
    fn transform_mapped_type_node<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let d = cx.nodes[input].as_mapped_type_node();
        let readonly_token = d.readonly_token;
        let type_parameter = d.type_parameter;
        let name_type = d.name_type;
        let question_token = d.question_token;
        let input_type = d.type_;
        // handle missing template type nodes, since the printer does not
        let type_node = if input_type.is_none() {
            Some(
                self.ec
                    .borrow_mut()
                    .factory
                    .new_keyword_type_node(cx.nodes, Kind::AnyKeyword),
            )
        } else {
            v.visit_node(cx, input_type)
        };
        let type_parameter = v.visit_node(cx, type_parameter);
        let name_type = v.visit_node(cx, name_type);
        self.ec
            .borrow_mut()
            .factory
            .update_mapped_type_node(
                cx.nodes,
                input,
                readonly_token,
                type_parameter,
                name_type,
                question_token,
                type_node,
                None,
            )
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformHeritageClause`.
    fn transform_heritage_clause<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        clause: NodeId,
    ) -> Option<NodeId> {
        let token = cx.nodes[clause].as_heritage_clause().token;
        let types = cx.nodes[clause]
            .as_heritage_clause()
            .types
            .clone()
            .unwrap_or_default();
        let retained_clauses: Vec<NodeId> = core::filter(types.nodes.as_ref(), |t: &NodeId| {
            let t = *t;
            let name = ast::get_heritage_clause_element_name(&cx.nodes[t], cx.nodes);
            name.is_some_and(|name| {
                ast::is_entity_name(&cx.nodes[name])
                    || ast::is_entity_name_expression(&cx.nodes[name], cx.nodes)
            }) || (token == Kind::ExtendsKeyword
                && ast::is_expression_with_type_arguments(&cx.nodes[t])
                && cx.nodes[t]
                    .expression()
                    .is_some_and(|e| cx.nodes[e].kind == Kind::NullKeyword))
        })
        .into_owned();
        if retained_clauses.is_empty() {
            return None; // elide empty clause
        }
        if retained_clauses.len() == types.nodes.len() {
            return v.visit_each_child(cx, clause).or(Some(clause));
        }
        let new_types = self.ec().factory.new_node_list(retained_clauses);
        let new_types = v.visit_nodes(cx, Some(new_types));
        self.ec
            .borrow_mut()
            .factory
            .update_heritage_clause(cx.nodes, clause, token, new_types)
            .or(Some(clause))
    }

    /// `(tx *DeclarationTransformer) transformImportTypeNode`.
    fn transform_import_type_node<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        if !ast::is_literal_import_type_node(&cx.nodes[input], cx.nodes) {
            return input;
        }
        let (is_type_of, argument, attributes, qualifier, type_arguments) = {
            let d = cx.nodes[input].as_import_type_node();
            (
                d.is_type_of,
                d.argument,
                d.attributes,
                d.qualifier,
                d.node_with_type_arguments_base.type_arguments.clone(),
            )
        };
        let literal_type = argument.expect("literal import type argument");
        let literal = cx.nodes[literal_type].as_literal_type_node().literal;
        let rewritten_literal = {
            let specifier = self.rewrite_module_specifier(input, literal, cx.nodes);
            self.ec
                .borrow_mut()
                .factory
                .update_literal_type_node(cx.nodes, literal_type, specifier)
                .unwrap_or(literal_type)
        };
        let type_arguments = v.visit_nodes(cx, type_arguments);
        self.ec
            .borrow_mut()
            .factory
            .update_import_type_node(
                cx.nodes,
                input,
                is_type_of,
                Some(rewritten_literal),
                attributes,
                qualifier,
                type_arguments,
            )
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformConstructorTypeNode`.
    fn transform_constructor_type_node<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let type_parameters = cx.nodes[input]
            .as_constructor_type_node()
            .function_or_constructor_type_node_base
            .function_like_base
            .type_parameters
            .clone();
        let parameters = cx.nodes[input]
            .as_constructor_type_node()
            .function_or_constructor_type_node_base
            .function_like_base
            .parameters
            .clone();
        let type_node = cx.nodes[input]
            .as_constructor_type_node()
            .function_or_constructor_type_node_base
            .function_like_base
            .type_;
        let modifiers = self.ensure_modifiers(input, cx);
        let type_parameters = v.visit_nodes(cx, type_parameters);
        let parameters = self.update_param_list(input, parameters, cx);
        let type_node = v.visit_node(cx, type_node);
        self.ec
            .borrow_mut()
            .factory
            .update_constructor_type_node(
                cx.nodes,
                input,
                modifiers,
                type_parameters,
                Some(parameters),
                type_node,
            )
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformFunctionTypeNode`.
    fn transform_function_type_node<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let (type_parameters, parameters, type_node) = {
            let d = cx.nodes[input].as_function_type_node();
            (
                d.function_or_constructor_type_node_base
                    .function_like_base
                    .type_parameters
                    .clone(),
                d.function_or_constructor_type_node_base
                    .function_like_base
                    .parameters
                    .clone(),
                d.function_or_constructor_type_node_base
                    .function_like_base
                    .type_,
            )
        };
        let type_parameters = v.visit_nodes(cx, type_parameters);
        let parameters = self.update_param_list(input, parameters, cx);
        let type_node = v.visit_node(cx, type_node);
        self.ec
            .borrow_mut()
            .factory
            .update_function_type_node(
                cx.nodes,
                input,
                type_parameters,
                Some(parameters),
                type_node,
            )
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformConditionalTypeNode`.
    fn transform_conditional_type_node<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let (check_type, extends_type, true_type, false_type) = {
            let d = cx.nodes[input].as_conditional_type_node();
            (d.check_type, d.extends_type, d.true_type, d.false_type)
        };
        let check_type = v.visit_node(cx, check_type);
        let extends_type = v.visit_node(cx, extends_type);
        let old_enclosing_decl = self.enclosing_declaration.get();
        self.enclosing_declaration.set(true_type);
        let true_type = v.visit_node(cx, true_type);
        self.enclosing_declaration.set(old_enclosing_decl);
        let false_type = v.visit_node(cx, false_type);

        self.ec
            .borrow_mut()
            .factory
            .update_conditional_type_node(
                cx.nodes,
                input,
                check_type,
                extends_type,
                true_type,
                false_type,
            )
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformTypeReference`.
    fn transform_type_reference<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let type_name = cx.nodes[input].as_type_reference_node().type_name;
        self.check_entity_name_visibility(type_name, self.enclosing_declaration.get(), cx.nodes);
        v.visit_each_child(cx, input).or(Some(input))
    }

    /// `(tx *DeclarationTransformer) transformExpressionWithTypeArguments`.
    fn transform_expression_with_type_arguments<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let expression = cx.nodes[input]
            .as_expression_with_type_arguments()
            .expression;
        if expression.is_some_and(|e| {
            ast::is_entity_name(&cx.nodes[e])
                || ast::is_entity_name_expression(&cx.nodes[e], cx.nodes)
        }) {
            self.check_entity_name_visibility(
                expression,
                self.enclosing_declaration.get(),
                cx.nodes,
            );
        }
        v.visit_each_child(cx, input).unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformTypeParameterDeclaration`.
    fn transform_type_parameter_declaration<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let (modifiers, name, constraint, expression, default_type) = {
            let d = cx.nodes[input].as_type_parameter_declaration();
            (
                d.modifiers_base.modifiers.clone(),
                d.name,
                d.constraint,
                d.expression,
                d.default_type,
            )
        };
        if is_private_method_type_parameter(&*self.resolver.borrow(), input, cx.nodes)
            && (default_type.is_some() || constraint.is_some())
        {
            return self
                .ec
                .borrow_mut()
                .factory
                .update_type_parameter_declaration(
                    cx.nodes, input, modifiers, name, None, expression, None,
                )
                .or(Some(input));
        }
        v.visit_each_child(cx, input).or(Some(input))
    }

    /// `(tx *DeclarationTransformer) transformVariableDeclaration`.
    fn transform_variable_declaration<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let is_commonjs = self.shared.borrow().current_source_file.is_some_and(|f| {
            cx.nodes[f]
                .as_source_file()
                .common_js_module_indicator
                .is_some()
        });
        if is_commonjs && ast::is_variable_declaration_initialized_to_require(input, cx.nodes) {
            return self.transform_cjs_require_variable_declaration(v, cx, input);
        }
        let name = cx.nodes[input].as_variable_declaration().name;
        if name.is_some_and(|n| {
            ast::is_binding_pattern(&cx.nodes[n]) && has_any_binding_initializers(n, cx.nodes)
        }) {
            return self.recreate_binding_pattern(v, cx, name.unwrap());
        }
        // Variable declaration types also suppress new diagnostic contexts, provided the contexts wouldn't be made for binding pattern types
        self.suppress_new_diagnostic_contexts.set(true);
        let type_ = self.ensure_type(input, false, cx);
        let initializer = self.ensure_no_initializer(input, cx);
        let name = self
            .binding_name_visitor
            .borrow()
            .as_ref()
            .expect("bindingNameVisitor")
            .visit_node(cx, name);
        self.ec
            .borrow_mut()
            .factory
            .update_variable_declaration(cx.nodes, input, name, None, type_, initializer)
            .or(Some(input))
    }

    /// `(tx *DeclarationTransformer) transformCjsRequireVariableDeclaration`.
    fn transform_cjs_require_variable_declaration<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let initializer = cx.nodes[input].as_variable_declaration().initializer;
        let call_arg = initializer
            .map(|i| cx.nodes[i].as_call_expression().arguments.clone())
            .and_then(|args| args.and_then(|a| a.nodes.first().copied()));
        let specifier = self.rewrite_module_specifier(input, call_arg, cx.nodes);
        let name = cx.nodes[input].as_variable_declaration().name;
        if name.is_some_and(|n| ast::is_identifier(&cx.nodes[n])) {
            // `const x = require("something")` -> `import x = require("something")`
            let ext_ref = {
                let mut ec = self.ec.borrow_mut();
                ec.factory
                    .new_external_module_reference(cx.nodes, specifier)
            };
            return Some(self.ec.borrow_mut().factory.new_import_equals_declaration(
                cx.nodes,
                None,
                false,
                name,
                Some(ext_ref),
            ));
        } else if name.is_some_and(|n| ast::is_array_binding_pattern(&cx.nodes[n])) {
            // TODO: Is this actually reachable? should we error on this?
            return None;
        } else {
            // object binding pattern
            // `const {x, y: z} = require("something")` -> `import {x, y as z} from "something"`
            let elements: Vec<NodeId> = name
                .and_then(|n| cx.nodes[n].elements().map(|e| e.to_vec()))
                .unwrap_or_default();
            let mut import_specifiers: Vec<NodeId> = Vec::new();
            for elem in elements.iter() {
                let (elem_name, property_name) = {
                    let e = cx.nodes[*elem].as_binding_element();
                    (e.name, e.property_name)
                };
                if !elem_name.is_some_and(|n| ast::is_identifier(&cx.nodes[n])) {
                    continue; // nested destructuring, bail
                }
                import_specifiers.push(self.ec.borrow_mut().factory.new_import_specifier(
                    cx.nodes,
                    false,
                    property_name,
                    elem_name,
                ));
            }
            let import_decl = {
                let mut ec = self.ec.borrow_mut();
                let named = ec.factory.new_node_list(import_specifiers);
                let named_imports = ec.factory.new_named_imports(cx.nodes, Some(named));
                let import_clause = ec.factory.new_import_clause(
                    cx.nodes,
                    Kind::Unknown,
                    None,
                    Some(named_imports),
                );
                ec.factory.new_import_declaration(
                    cx.nodes,
                    None,
                    Some(import_clause),
                    specifier,
                    None,
                )
            };
            return Some(import_decl);
        }
    }

    /// `(tx *DeclarationTransformer) recreateBindingPattern`.
    fn recreate_binding_pattern<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let mut results: Vec<NodeId> = Vec::new();
        let elements: Vec<NodeId> = cx.nodes[input]
            .elements()
            .map(|e| e.to_vec())
            .unwrap_or_default();
        for elem in elements.iter() {
            let Some(result) = self.recreate_binding_element(cx, *elem) else {
                continue;
            };
            if cx.nodes[result].kind == Kind::SyntaxList {
                results.extend_from_slice(&cx.nodes[result].as_syntax_list().children);
            } else {
                results.push(result);
            }
        }
        if results.is_empty() {
            return None;
        }
        if results.len() == 1 {
            return Some(results[0]);
        }
        Some(
            self.ec
                .borrow_mut()
                .factory
                .new_syntax_list(cx.nodes, &results),
        )
    }

    /// `(tx *DeclarationTransformer) recreateBindingElement`.
    fn recreate_binding_element(&self, cx: &mut VisitorCx<'_, '_>, e: NodeId) -> Option<NodeId> {
        let name = cx.nodes[e].as_binding_element().name;
        let name = name?;
        if !get_binding_name_visible(&*self.resolver.borrow(), e, cx.nodes) {
            return None;
        }
        if ast::is_binding_pattern(&cx.nodes[name]) {
            return self.recreate_binding_pattern(
                self.binding_name_visitor
                    .borrow()
                    .as_ref()
                    .expect("bindingNameVisitor"),
                cx,
                name,
            );
        }
        let type_ = self.ensure_type(e, false, cx);
        Some(self.ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            Some(name),
            None,
            type_,
            None, // TODO: possible strada bug - not emitting const initialized binding pattern elements?
        ))
    }
}

/// `hasAnyBindingInitializers(bindingPattern)`.
fn has_any_binding_initializers(binding_pattern: NodeId, nodes: &[Node]) -> bool {
    for elem in nodes[binding_pattern].elements().unwrap_or(&[]).iter() {
        if !ast::is_binding_element(&nodes[*elem]) {
            continue;
        }
        let e = nodes[*elem].as_binding_element();
        if e.initializer.is_some() {
            return true;
        }
        if e.name.is_some_and(|n| {
            ast::is_binding_pattern(&nodes[n]) && has_any_binding_initializers(n, nodes)
        }) {
            return true;
        }
    }
    false
}

impl<'a> DeclarationTransformerState<'a> {
    /// `(tx *DeclarationTransformer) transformIndexSignatureDeclaration`.
    fn transform_index_signature_declaration<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let (parameters, input_type) = {
            let d = cx.nodes[input].as_index_signature_declaration();
            (
                d.function_like_base.parameters.clone(),
                d.function_like_base.type_,
            )
        };
        let mut t = _v.visit_node(cx, input_type);
        if t.is_none() {
            t = Some(
                self.ec
                    .borrow_mut()
                    .factory
                    .new_keyword_type_node(cx.nodes, Kind::AnyKeyword),
            );
        }
        let modifiers = self.ensure_modifiers(input, cx);
        let parameters = self.update_param_list(input, parameters, cx);
        self.ec
            .borrow_mut()
            .factory
            .update_index_signature_declaration(cx.nodes, input, modifiers, Some(parameters), t)
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformCallSignatureDeclaration`.
    fn transform_call_signature_declaration<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let (type_parameters, parameters) = {
            let d = cx.nodes[input].as_call_signature_declaration();
            (
                d.function_like_base.type_parameters.clone(),
                d.function_like_base.parameters.clone(),
            )
        };
        let type_parameters = self.ensure_type_params(input, type_parameters, cx);
        let parameters = self.update_param_list(input, parameters, cx);
        let return_type = self.ensure_type(input, false, cx);
        self.ec
            .borrow_mut()
            .factory
            .update_call_signature_declaration(
                cx.nodes,
                input,
                type_parameters,
                Some(parameters),
                return_type,
            )
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformPropertySignatureDeclaration`.
    fn transform_property_signature_declaration<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let (name, postfix_token) = {
            let d = cx.nodes[input].as_property_signature_declaration();
            (d.named_member_base.name, d.named_member_base.postfix_token)
        };
        if name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n])) {
            return None;
        }
        let modifiers = self.ensure_modifiers(input, cx);
        let type_node = self.ensure_type(input, false, cx);
        let initializer = self.ensure_no_initializer(input, cx);
        let result = self
            .ec
            .borrow_mut()
            .factory
            .update_property_signature_declaration(
                cx.nodes,
                input,
                modifiers,
                name,
                postfix_token,
                type_node,
                initializer, // TODO: possible strada bug (fixed here) - const property signatures never initialized
            )
            .unwrap_or(input);
        self.preserve_partial_js_doc(result, input, cx);
        Some(result)
    }

    /// `(tx *DeclarationTransformer) transformPropertyDeclaration`.
    fn transform_property_declaration<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let (name, mut postfix_token) = {
            let d = cx.nodes[input].as_property_declaration();
            (d.named_member_base.name, d.named_member_base.postfix_token)
        };
        if name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n])) {
            return None;
        }
        // Remove definite assignment assertion (!) from declaration files
        if postfix_token.is_some_and(|t| cx.nodes[t].kind == Kind::ExclamationToken) {
            postfix_token = None;
        }
        let modifiers = self.ensure_modifiers(input, cx);
        let type_node = self.ensure_type(input, false, cx);
        let initializer = self.ensure_no_initializer(input, cx);
        self.ec
            .borrow_mut()
            .factory
            .update_property_declaration(
                cx.nodes,
                input,
                modifiers,
                name,
                postfix_token,
                type_node,
                initializer,
            )
            .or(Some(input))
    }

    /// `(tx *DeclarationTransformer) transformSetAccessorDeclaration`.
    fn transform_set_accessor_declaration<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let name = cx.nodes[input]
            .as_set_accessor_declaration()
            .accessor_declaration_base
            .named_member_base
            .name;
        if name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n])) {
            return None;
        }
        let is_private = !self
            .resolver
            .borrow()
            .get_effective_declaration_flags(
                self.ec().parse_node(cx.nodes, input).unwrap_or(input),
                ModifierFlags::PRIVATE,
                cx.nodes,
            )
            .is_empty();
        let modifiers = self.ensure_modifiers(input, cx);
        let parameters = self.update_accessor_param_list(input, is_private, cx);
        self.ec
            .borrow_mut()
            .factory
            .update_set_accessor_declaration(
                cx.nodes,
                input,
                modifiers,
                name,
                None, // accessors shouldn't have type params
                Some(parameters),
                None,
                None,
                None,
            )
            .or(Some(input))
    }

    /// `(tx *DeclarationTransformer) transformGetAccesorDeclaration`.
    fn transform_get_accessor_declaration<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let name = cx.nodes[input]
            .as_get_accessor_declaration()
            .accessor_declaration_base
            .named_member_base
            .name;
        if name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n])) {
            return None;
        }
        let is_private = !self
            .resolver
            .borrow()
            .get_effective_declaration_flags(
                self.ec().parse_node(cx.nodes, input).unwrap_or(input),
                ModifierFlags::PRIVATE,
                cx.nodes,
            )
            .is_empty();
        let modifiers_for_get = self.ensure_modifiers(input, cx);
        let accessor_params = self.update_accessor_param_list(input, is_private, cx);
        let return_type = self.ensure_type(input, false, cx);
        self.ec
            .borrow_mut()
            .factory
            .update_get_accessor_declaration(
                cx.nodes,
                input,
                modifiers_for_get,
                name,
                None, // accessors shouldn't have type params
                Some(accessor_params),
                return_type,
                None,
                None,
            )
            .or(Some(input))
    }

    /// `(tx *DeclarationTransformer) updateAccessorParamList`.
    fn update_accessor_param_list(
        &self,
        input: NodeId,
        is_private: bool,
        cx: &mut VisitorCx<'_, '_>,
    ) -> NodeList {
        let mut new_params: Vec<NodeId> = Vec::new();
        if !is_private {
            if let Some(this_param) = ast::get_this_parameter(&cx.nodes[input], cx.nodes) {
                new_params.push(self.ensure_parameter(this_param, cx));
            }
        }
        if ast::is_set_accessor_declaration(&cx.nodes[input]) {
            let mut value_param: Option<NodeId> = None;
            let set_params = cx.nodes[input]
                .as_set_accessor_declaration()
                .accessor_declaration_base
                .function_like_with_body_base
                .function_like_base
                .parameters
                .clone();
            if !is_private {
                if new_params.len() == 1 && set_params.as_ref().is_some_and(|p| p.nodes.len() >= 2)
                {
                    value_param =
                        Some(self.ensure_parameter(set_params.as_ref().unwrap().nodes[1], cx));
                } else if new_params.is_empty()
                    && set_params.as_ref().is_some_and(|p| !p.nodes.is_empty())
                {
                    value_param =
                        Some(self.ensure_parameter(set_params.as_ref().unwrap().nodes[0], cx));
                }
            }
            if value_param.is_none() {
                // When synthesizing a missing value parameter, emit `value: any` for non-private accessors to match TypeScript's declaration emit behavior.
                let t = if !is_private {
                    Some(
                        self.ec
                            .borrow_mut()
                            .factory
                            .new_keyword_type_node(cx.nodes, Kind::AnyKeyword),
                    )
                } else {
                    None
                };
                value_param = Some({
                    let mut ec = self.ec.borrow_mut();
                    let ident = ec.factory.new_identifier(cx.nodes, "value");
                    ec.factory.new_parameter_declaration(
                        cx.nodes,
                        None,
                        None,
                        Some(ident),
                        None,
                        t,
                        None,
                    )
                });
            }
            new_params.push(value_param.unwrap());
        }
        self.ec().factory.new_node_list(new_params)
    }

    /// `(tx *DeclarationTransformer) transformConstructorDeclaration`.
    fn transform_constructor_declaration<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let parameters = cx.nodes[input]
            .as_constructor_declaration()
            .function_like_with_body_base
            .function_like_base
            .parameters
            .clone();
        // A constructor declaration may not have a type annotation
        let modifiers = self.ensure_modifiers(input, cx);
        let parameters = self.update_param_list(input, parameters, cx);
        self.ec
            .borrow_mut()
            .factory
            .update_constructor_declaration(
                cx.nodes,
                input,
                modifiers,
                None, // no type params
                Some(parameters),
                None, // no return type
                None,
                None,
            )
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformConstructSignatureDeclaration`.
    fn transform_construct_signature_declaration<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let (type_parameters, parameters) = {
            let d = cx.nodes[input].as_construct_signature_declaration();
            (
                d.function_like_base.type_parameters.clone(),
                d.function_like_base.parameters.clone(),
            )
        };
        let type_parameters = self.ensure_type_params(input, type_parameters, cx);
        let parameters = self.update_param_list(input, parameters, cx);
        let return_type = self.ensure_type(input, false, cx);
        self.ec
            .borrow_mut()
            .factory
            .update_construct_signature_declaration(
                cx.nodes,
                input,
                type_parameters,
                Some(parameters),
                return_type,
            )
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) omitPrivateMethodType`.
    fn omit_private_method_type(
        &self,
        input: NodeId,
        cx: &mut VisitorCx<'_, '_>,
    ) -> Option<NodeId> {
        if let (Some(symbol), Some(symbols)) = (cx.nodes[input].symbol(), self.symbols) {
            let declarations = symbols.borrow()[symbol.index()].declarations.clone();
            if !declarations.is_empty() && declarations[0] != input {
                return None;
            }
        }
        let modifiers = self.ensure_modifiers(input, cx);
        let name = cx.nodes[input].name();
        let result = if ast::is_method_signature_declaration(&cx.nodes[input]) {
            self.ec
                .borrow_mut()
                .factory
                .new_property_signature_declaration(
                    cx.nodes, modifiers, name, None, /*postfixToken*/
                    None, /*typeNode*/
                    None, /*initializer*/
                )
        } else {
            self.ec.borrow_mut().factory.new_property_declaration(
                cx.nodes, modifiers, name, None, /*postfixToken*/
                None, /*typeNode*/
                None, /*initializer*/
            )
        };
        self.preserve_js_doc(result, input, cx.nodes);
        Some(result)
    }

    /// `(tx *DeclarationTransformer) transformMethodSignatureDeclaration`.
    fn transform_method_signature_declaration<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let is_private = !self
            .resolver
            .borrow()
            .get_effective_declaration_flags(
                self.ec().parse_node(cx.nodes, input).unwrap_or(input),
                ModifierFlags::PRIVATE,
                cx.nodes,
            )
            .is_empty();
        if is_private {
            return self.omit_private_method_type(input, cx);
        }
        let (name, postfix_token, type_parameters, parameters) = {
            let d = cx.nodes[input].as_method_signature_declaration();
            (
                d.named_member_base.name,
                d.named_member_base.postfix_token,
                d.function_like_base.type_parameters.clone(),
                d.function_like_base.parameters.clone(),
            )
        };
        if name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n])) {
            return None;
        }
        let modifiers = self.ensure_modifiers(input, cx);
        let type_parameters = self.ensure_type_params(input, type_parameters, cx);
        let parameters = self.update_param_list(input, parameters, cx);
        let return_type = self.ensure_type(input, false, cx);
        self.ec
            .borrow_mut()
            .factory
            .update_method_signature_declaration(
                cx.nodes,
                input,
                modifiers,
                name,
                postfix_token,
                type_parameters,
                Some(parameters),
                return_type,
            )
            .or(Some(input))
    }

    /// `(tx *DeclarationTransformer) transformMethodDeclaration`.
    fn transform_method_declaration<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let is_private = !self
            .resolver
            .borrow()
            .get_effective_declaration_flags(
                self.ec().parse_node(cx.nodes, input).unwrap_or(input),
                ModifierFlags::PRIVATE,
                cx.nodes,
            )
            .is_empty();
        if is_private {
            return self.omit_private_method_type(input, cx);
        }
        let (name, postfix_token, type_parameters, parameters) = {
            let d = cx.nodes[input].as_method_declaration();
            (
                d.named_member_base.name,
                d.named_member_base.postfix_token,
                d.function_like_with_body_base
                    .function_like_base
                    .type_parameters
                    .clone(),
                d.function_like_with_body_base
                    .function_like_base
                    .parameters
                    .clone(),
            )
        };
        if name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n])) {
            return None;
        }
        let modifiers = self.ensure_modifiers(input, cx);
        let type_parameters = self.ensure_type_params(input, type_parameters, cx);
        let parameters = self.update_param_list(input, parameters, cx);
        let return_type = self.ensure_type(input, false, cx);
        self.ec
            .borrow_mut()
            .factory
            .update_method_declaration(
                cx.nodes,
                input,
                modifiers,
                None,
                name,
                postfix_token,
                type_parameters,
                Some(parameters),
                return_type,
                None,
                None,
            )
            .or(Some(input))
    }

    /// `(tx *DeclarationTransformer) visitDeclarationStatements`.
    fn visit_declaration_statements<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        if self.should_strip_internal(Some(input), cx.nodes) {
            return None;
        }
        match cx.nodes[input].kind {
            Kind::ExportDeclaration => {
                if cx.nodes[input]
                    .parent
                    .is_some_and(|p| ast::is_source_file(&cx.nodes[p]))
                {
                    self.result_has_external_module_indicator.set(true);
                }
                self.result_has_scope_marker.set(true);
                // Rewrite external module names if necessary
                let (modifiers, is_type_only, export_clause, module_specifier, attributes) = {
                    let d = cx.nodes[input].as_export_declaration();
                    (
                        d.modifiers_base.modifiers.clone(),
                        d.is_type_only,
                        d.export_clause,
                        d.module_specifier,
                        d.attributes,
                    )
                };
                self.ec
                    .borrow_mut()
                    .factory
                    .update_export_declaration(
                        cx.nodes,
                        input,
                        modifiers,
                        is_type_only,
                        export_clause,
                        self.rewrite_module_specifier(input, module_specifier, cx.nodes),
                        attributes,
                    )
                    .or(Some(input))
            }
            Kind::ExportAssignment => {
                let expression = cx.nodes[input].expression();
                let is_export_equals = cx.nodes[input].as_export_assignment().is_export_equals;
                Some(self.transform_export_assignment(
                    v,
                    cx,
                    input,
                    input,
                    expression,
                    is_export_equals,
                ))
            }
            _ => {
                let original = self.ec().most_original(Some(input)).unwrap_or(input);
                let id = ast::get_node_id(&cx.nodes[original]);
                if !self
                    .late_statement_replacement_map
                    .borrow()
                    .contains_key(&id)
                {
                    // Don't actually transform yet; just leave as original node - will be elided/swapped by late pass
                    let replacement = self.transform_top_level_declaration(v, cx, input);
                    self.late_statement_replacement_map
                        .borrow_mut()
                        .insert(id, replacement);
                }
                Some(input)
            }
        }
    }

    /// `(tx *DeclarationTransformer) tryGetNameOfAssignedExpression`.
    fn try_get_name_of_assigned_expression(
        &self,
        unwrapped: NodeId,
        cx: &mut VisitorCx<'_, '_>,
    ) -> Option<NodeId> {
        let mut name_node: Option<NodeId> = None;
        let mut name_text = String::new();
        if !ast::is_property_access_expression(&cx.nodes[unwrapped])
            && cx.nodes[unwrapped].name().is_some()
        {
            name_text = cx.nodes[unwrapped]
                .name()
                .map(|n| cx.nodes[n].text(cx.nodes).into_owned())
                .unwrap_or_default();
        } else if ast::is_identifier(&cx.nodes[unwrapped]) {
            name_text = cx.nodes[unwrapped].text(cx.nodes).into_owned();
        }
        if !name_text.is_empty() && name_text != "default" {
            if self.resolver.borrow().is_name_resolvable(
                self.enclosing_declaration.get(),
                &name_text,
                cx.nodes,
            ) {
                // create a unique name that shares the same text as its' base
                name_node = Some(self.ec.borrow_mut().factory.new_unique_name_ex(
                    cx.nodes,
                    &name_text,
                    &AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::OPTIMISTIC,
                        ..Default::default()
                    },
                ));
            } else {
                // use the node's name as-is, since it's not otherwise in-scope
                name_node = Some(
                    self.ec
                        .borrow_mut()
                        .factory
                        .new_identifier(cx.nodes, &name_text),
                );
            }
        }
        name_node
    }

    /// `(tx *DeclarationTransformer) getNameOfExportedAssignedExpression`.
    fn get_name_of_exported_assigned_expression(
        &self,
        unwrapped: NodeId,
        is_export_equals: bool,
        cx: &mut VisitorCx<'_, '_>,
    ) -> NodeId {
        let name_node =
            self.try_get_name_of_assigned_expression(unwrapped, cx)
                .unwrap_or_else(|| {
                    // fallback to a default name
                    let base =
                        if is_export_equals
                            && self.shared.borrow().current_source_file.is_some_and(|f| {
                                ast::is_source_file_js(cx.nodes[f].as_source_file())
                            })
                        {
                            // only JS files prefer to use `_exports` for export assignments - TS has always used `_default` for both `export=` and `export default`
                            "_exports"
                        } else {
                            "_default"
                        };
                    self.ec.borrow_mut().factory.new_unique_name_ex(
                        cx.nodes,
                        base,
                        &AutoGenerateOptions {
                            flags: GeneratedIdentifierFlags::OPTIMISTIC,
                            ..Default::default()
                        },
                    )
                });
        self.cjs_export_assignment_name.set(Some(name_node));
        name_node
    }

    /// `(tx *DeclarationTransformer) transformExportAssignment`.
    fn transform_export_assignment<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
        assignment: NodeId,
        expression: Option<NodeId>,
        is_export_equals: bool,
    ) -> NodeId {
        if cx.nodes[input]
            .parent
            .is_some_and(|p| ast::is_source_file(&cx.nodes[p]))
        {
            self.result_has_external_module_indicator.set(true);
        }
        self.result_has_scope_marker.set(true);
        if expression.is_some_and(|e| ast::is_identifier(&cx.nodes[e]))
            && cx.nodes[input].parent.is_some_and(|p| {
                ast::is_source_file(&cx.nodes[p]) || ast::is_module_block(&cx.nodes[p])
            })
        {
            let export_assignment = self.ec.borrow_mut().factory.new_export_assignment(
                cx.nodes,
                None,
                is_export_equals,
                None,
                expression,
            );
            self.ec()
                .assign_source_map_range(cx.nodes, export_assignment, input);
            self.preserve_js_doc(export_assignment, input, cx.nodes);
            return export_assignment;
        }

        {
            let mut shared = self.shared.borrow_mut();
            shared.get_symbol_accessibility_diagnostic = Some(Box::new(
                move |_res: &SymbolAccessibilityResult, _nodes: &[Node]| {
                    Some(SymbolAccessibilityDiagnostic {
                        diagnostic_message:
                            &tsc_diagnostics::Default_export_of_the_module_has_or_is_using_private_name_0,
                        error_node: Some(input),
                        type_name: None,
                    })
                },
            ));
        }
        self.tracker
            .borrow_mut()
            .push_error_fallback_node(assignment);

        // Check if the expression is a class expression - emit as a class declaration + export assignment
        let unwrapped = expression
            .map(|e| ast::skip_outer_expressions(e, OEK_EXPRESSION_TYPE_PASSTHROUGH, cx.nodes));
        let new_id = unwrapped
            .map(|u| self.get_name_of_exported_assigned_expression(u, is_export_equals, cx));
        if unwrapped.is_some_and(|u| ast::is_class_expression(&cx.nodes[u])) {
            let unwrapped = unwrapped.unwrap();
            let mods = {
                let mut mods: Vec<NodeId> = Vec::new();
                let mut ec = self.ec.borrow_mut();
                if self.needs_declare.get() {
                    mods.push(ec.factory.new_token(cx.nodes, Kind::DeclareKeyword));
                }
                ec.factory.new_modifier_list(cx.nodes, mods)
            };
            let class_decl = self.transform_class_expression_to_declaration(
                v,
                cx,
                unwrapped,
                new_id,
                Some(mods),
            );
            self.tracker.borrow_mut().pop_error_fallback_node();
            self.preserve_js_doc(class_decl, input, cx.nodes);
            // Reuse the same name node for the export so unique names resolve consistently
            let export_assignment = self.ec.borrow_mut().factory.new_export_assignment(
                cx.nodes,
                None,
                is_export_equals,
                None,
                new_id,
            );
            self.ec()
                .assign_source_map_range(cx.nodes, export_assignment, input);
            self.remove_all_comments(export_assignment);
            return self
                .ec
                .borrow_mut()
                .factory
                .new_syntax_list(cx.nodes, &[export_assignment, class_decl]);
        } else if unwrapped.is_some_and(|u| ast::is_function_like(Some(u), cx.nodes)) {
            let unwrapped = unwrapped.unwrap();
            let mods = {
                let mut mods: Vec<NodeId> = Vec::new();
                let mut ec = self.ec.borrow_mut();
                if self.needs_declare.get() {
                    mods.push(ec.factory.new_token(cx.nodes, Kind::DeclareKeyword));
                }
                ec.factory.new_modifier_list(cx.nodes, mods)
            };
            // Promote function or arrow function expressions to a function declaration
            let full_signature_type = cx.nodes[assignment].type_();
            let func_decl = self.transform_function_like_to_declaration(
                v,
                cx,
                unwrapped,
                new_id,
                Some(mods),
                full_signature_type,
            );
            self.tracker.borrow_mut().pop_error_fallback_node();
            self.preserve_js_doc(func_decl, input, cx.nodes);
            // Reuse the same name node for the export so unique names resolve consistently
            let export_assignment = self.ec.borrow_mut().factory.new_export_assignment(
                cx.nodes,
                None,
                is_export_equals,
                None,
                new_id,
            );
            self.ec()
                .assign_source_map_range(cx.nodes, export_assignment, input);
            self.remove_all_comments(export_assignment);
            return self
                .ec
                .borrow_mut()
                .factory
                .new_syntax_list(cx.nodes, &[export_assignment, func_decl]);
        }

        // expression is non-identifier, create _default typed variable to reference
        self.cjs_export_assignment_name.set(new_id);
        let (type_, initializer) = {
            let mut initializer: Option<NodeId> = None;
            if expression.is_some_and(|e| {
                ast::is_primitive_literal_value(
                    &cx.nodes[unwrap_parenthesized_expression(e, cx.nodes)],
                    true,
                    cx.nodes,
                )
            }) {
                let parse_node = self
                    .ec()
                    .parse_node(cx.nodes, assignment)
                    .unwrap_or(assignment);
                initializer = self.resolver.borrow().create_literal_const_value(
                    parse_node,
                    self.tracker.clone(),
                    cx.nodes,
                );
            }
            let type_ = if initializer.is_none() {
                self.ensure_type(assignment, false, cx)
            } else {
                None
            };
            (type_, initializer)
        };
        let var_decl = self.ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            new_id,
            None,
            type_,
            initializer,
        );
        self.tracker.borrow_mut().pop_error_fallback_node();
        let mod_list = {
            let mut ec = self.ec.borrow_mut();
            let mods = if self.needs_declare.get() {
                vec![ec.factory.new_token(cx.nodes, Kind::DeclareKeyword)]
            } else {
                Vec::new()
            };
            ec.factory.new_modifier_list(cx.nodes, mods)
        };
        let statement = {
            let mut ec = self.ec.borrow_mut();
            let decl_list = ec.factory.new_node_list(vec![var_decl]);
            let declaration_list = ec.factory.new_variable_declaration_list(
                cx.nodes,
                Some(decl_list),
                NodeFlags::CONST,
            );
            ec.factory
                .new_variable_statement(cx.nodes, Some(mod_list), Some(declaration_list))
        };
        let export_assignment = self.ec.borrow_mut().factory.new_export_assignment(
            cx.nodes,
            None,
            is_export_equals,
            None,
            new_id,
        );
        self.ec()
            .assign_source_map_range(cx.nodes, export_assignment, input);
        // Remove comments from the export declaration and copy them onto the synthetic _default declaration
        self.preserve_js_doc(statement, input, cx.nodes);
        self.ec
            .borrow_mut()
            .factory
            .new_syntax_list(cx.nodes, &[statement, export_assignment])
    }

    /// `(tx *DeclarationTransformer) transformFunctionLikeToDeclaration`.
    fn transform_function_like_to_declaration<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        unwrapped: NodeId,
        func_name: Option<NodeId>,
        mods: Option<tsc_ast::ModifierList>,
        full_signature_type: Option<NodeId>,
    ) -> NodeId {
        let (type_parameters, parameters, mut sig) = {
            let d = cx.nodes[unwrapped]
                .function_like_data()
                .expect("FunctionLikeData");
            (
                d.type_parameters.clone(),
                d.parameters.clone(),
                d.full_signature,
            )
        };
        if sig.is_none() {
            sig = full_signature_type;
        }
        if sig.is_none() {
            let type_parameters = self.ensure_type_params(unwrapped, type_parameters, cx);
            let parameters = self.update_param_list(unwrapped, parameters, cx);
            let return_type = self.ensure_type(unwrapped, false, cx);
            let sig = v.visit_node(cx, sig);
            self.ec.borrow_mut().factory.new_function_declaration(
                cx.nodes,
                mods,
                None,
                func_name,
                type_parameters,
                Some(parameters),
                return_type,
                sig,
                None,
            )
        } else {
            // If a full signature type node is present, emit as a variable statement to reuse it
            let sig_visited = v.visit_node(cx, sig);
            let mut ec = self.ec.borrow_mut();
            let var_decl =
                ec.factory
                    .new_variable_declaration(cx.nodes, func_name, None, sig_visited, None);
            let decl_list = ec.factory.new_node_list(vec![var_decl]);
            let decl_list = ec.factory.new_variable_declaration_list(
                cx.nodes,
                Some(decl_list),
                NodeFlags::CONST,
            );
            ec.factory
                .new_variable_statement(cx.nodes, mods, Some(decl_list))
        }
    }

    /// `(tx *DeclarationTransformer) transformBinaryExpressionToExportDeclaration`.
    fn transform_binary_expression_to_export_declaration(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
        name: Option<NodeId>,
    ) -> NodeId {
        let mut property_name = cx.nodes[input].as_binary_expression().right;

        // track alias target so referenced declarations are included in the output
        if let Some(property_name) = property_name {
            let visibility_result = self.resolver.borrow().is_entity_name_visible(
                property_name,
                self.enclosing_declaration.get(),
                cx.nodes,
            );
            self.tracker
                .borrow_mut()
                .handle_symbol_accessibility_error(visibility_result, cx.nodes);
        }

        if name.is_some_and(|n| ast::is_identifier(&cx.nodes[n]))
            && property_name.is_some_and(|p| {
                cx.nodes[p].text(cx.nodes)
                    == name.map(|n| cx.nodes[n].text(cx.nodes)).unwrap_or_default()
            })
        {
            property_name = None;
        }

        let mut ec = self.ec.borrow_mut();
        let specifier = ec
            .factory
            .new_export_specifier(cx.nodes, false, property_name, name);
        let spec_list = ec.factory.new_node_list(vec![specifier]);
        let named = ec.factory.new_named_exports(cx.nodes, Some(spec_list));
        ec.factory
            .new_export_declaration(cx.nodes, None, false, Some(named), None, None)
    }
}

/// `isCommonJSAliasExport(node)`.
fn is_commonjs_alias_export(
    node: NodeId,
    nodes: &[Node],
    symbols: Option<&RefCell<Vec<Symbol>>>,
) -> bool {
    if ast::is_binary_expression(&nodes[node])
        && nodes[node]
            .as_binary_expression()
            .right
            .is_some_and(|r| ast::is_identifier(&nodes[r]))
    {
        if let (Some(symbol), Some(symbols)) = (nodes[node].symbol(), symbols) {
            return symbols.borrow()[symbol.index()].declarations.len() == 1;
        }
    }
    false
}

impl<'a> DeclarationTransformerState<'a> {
    /// `(tx *DeclarationTransformer) transformCommonJSExport`.
    fn transform_commonjs_export<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
        name: Option<NodeId>,
    ) -> Option<NodeId> {
        let res = self.transform_commonjs_export_worker(v, cx, input, name);
        let res = res?;
        Some(self.wrap_in_cjs_export_namespace(cx, res))
    }

    /// `(tx *DeclarationTransformer) transformCommonJSExportWorker`.
    fn transform_commonjs_export_worker<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
        name: Option<NodeId>,
    ) -> Option<NodeId> {
        let mut name_text = String::new();
        if name.is_some_and(|n| {
            ast::is_identifier(&cx.nodes[n]) || ast::is_string_literal(&cx.nodes[n])
        }) {
            name_text = name
                .map(|n| cx.nodes[n].text(cx.nodes).into_owned())
                .unwrap_or_default();
        }
        if self.witnessed_cjs_exports.borrow().contains(&name_text) && !name_text.is_empty() {
            return None; // Already emitted this export name
        }
        self.witnessed_cjs_exports
            .borrow_mut()
            .insert(name_text.clone());
        self.result_has_external_module_indicator.set(true);
        self.result_has_scope_marker.set(true);
        // only transform cjs exports to shorthand at the top-level of a source file, otherwise we uniformly emit nested exports with a type annotation
        if is_commonjs_alias_export(input, cx.nodes, self.symbols)
            && cx.nodes[input]
                .parent
                .is_some_and(|p| ast::is_expression_statement(&cx.nodes[p]))
            && cx.nodes[input]
                .parent
                .and_then(|p| cx.nodes[p].parent)
                .is_some_and(|p| ast::is_source_file(&cx.nodes[p]))
        {
            // export { name }
            // export { source as name }
            return Some(self.transform_binary_expression_to_export_declaration(cx, input, name));
        }

        // Check if the RHS is a class expression - emit as a class declaration instead of a typed variable
        if ast::is_binary_expression(&cx.nodes[input]) {
            let right = cx.nodes[input].as_binary_expression().right;
            if let Some(rhs) = right.map(|r| unwrap_parenthesized_expression(r, cx.nodes))
                && ast::is_class_expression(&cx.nodes[rhs])
            {
                let class_expr_name = cx.nodes[rhs].as_class_expression().class_like_base.name;
                let has_expr_name =
                    class_expr_name.is_some_and(|n| !cx.nodes[n].text(cx.nodes).is_empty());

                if has_expr_name {
                    let class_expr_name = class_expr_name.unwrap();
                    // Set up TrackSymbol watch to detect if the class expression's own
                    // symbol is referenced during member type serialization.
                    {
                        let mut tracker = self.tracker.borrow_mut();
                        tracker.watched_class_symbol = cx.nodes[rhs].symbol();
                        tracker.class_symbol_tracked = false;
                    }

                    // Serialize class members using the class expression name, which
                    // triggers TrackSymbol for any self-referential member types.
                    let class_name_text = cx.nodes[class_expr_name].text(cx.nodes).into_owned();
                    let class_name = self
                        .ec
                        .borrow_mut()
                        .factory
                        .new_identifier(cx.nodes, &class_name_text);
                    let class_mods = {
                        let mut ec = self.ec.borrow_mut();
                        let m = ec.factory.new_token(cx.nodes, Kind::ExportKeyword);
                        ec.factory.new_modifier_list(cx.nodes, vec![m])
                    };
                    let class_decl = self.transform_class_expression_to_declaration(
                        v,
                        cx,
                        rhs,
                        Some(class_name),
                        Some(class_mods),
                    );
                    self.preserve_js_doc(class_decl, input, cx.nodes);

                    // Determine if namespace isolation is needed:
                    // - The class expression name differs from the export name, OR
                    // - The class's own symbol was used in a member's serialized type
                    let names_differ = !name.is_some_and(|n| {
                        ast::is_identifier(&cx.nodes[n])
                            && cx.nodes[class_expr_name].text(cx.nodes)
                                == cx.nodes[n].text(cx.nodes)
                    });
                    let needs_isolation =
                        names_differ || self.tracker.borrow().class_symbol_tracked;

                    if needs_isolation {
                        let mut ec = self.ec.borrow_mut();
                        let ns_name = ec.factory.new_unique_name_ex(
                            cx.nodes,
                            "_ns",
                            &AutoGenerateOptions {
                                flags: GeneratedIdentifierFlags::OPTIMISTIC,
                                ..Default::default()
                            },
                        );
                        let mut ns_mods: Vec<NodeId> = Vec::new();
                        if self.needs_declare.get() {
                            ns_mods.push(ec.factory.new_token(cx.nodes, Kind::DeclareKeyword));
                        }
                        let ns_mods = ec.factory.new_modifier_list(cx.nodes, ns_mods);
                        let block_list = ec.factory.new_node_list(vec![class_decl]);
                        let block = ec.factory.new_module_block(cx.nodes, Some(block_list));
                        let ns_decl = ec.factory.new_module_declaration(
                            cx.nodes,
                            Some(ns_mods),
                            Kind::NamespaceKeyword,
                            Some(ns_name),
                            None,
                            Some(block),
                        );

                        let mut alias_base = "_exported".to_string();
                        if let Some(n) = name
                            && ast::is_identifier(&cx.nodes[n])
                        {
                            let name_text = cx.nodes[n].text(cx.nodes).into_owned();
                            if scanner::utilities::is_identifier_text(
                                &format!("_{}", name_text),
                                LanguageVariant::Standard,
                            ) {
                                alias_base = format!("_{}", name_text);
                            }
                        }
                        let import_alias = ec.factory.new_unique_name_ex(
                            cx.nodes,
                            &alias_base,
                            &AutoGenerateOptions {
                                flags: GeneratedIdentifierFlags::OPTIMISTIC,
                                ..Default::default()
                            },
                        );
                        let qualified_name = ec.factory.new_qualified_name(
                            cx.nodes,
                            Some(ns_name),
                            Some(class_name),
                        );
                        let import_decl = ec.factory.new_import_equals_declaration(
                            cx.nodes,
                            None,
                            false,
                            Some(import_alias),
                            Some(qualified_name),
                        );
                        drop(ec);

                        let export_specifier = {
                            let mut ec = self.ec.borrow_mut();
                            let specifier = ec.factory.new_export_specifier(
                                cx.nodes,
                                false,
                                Some(import_alias),
                                name,
                            );
                            let list = ec.factory.new_node_list(vec![specifier]);
                            let named = ec.factory.new_named_exports(cx.nodes, Some(list));
                            let decl = ec.factory.new_export_declaration(
                                cx.nodes,
                                None,
                                false,
                                Some(named),
                                None,
                                None,
                            );
                            decl
                        };
                        self.remove_all_comments(export_specifier);

                        {
                            let mut tracker = self.tracker.borrow_mut();
                            tracker.watched_class_symbol = None;
                            tracker.class_symbol_tracked = false;
                        }
                        return Some(
                            self.ec.borrow_mut().factory.new_syntax_list(
                                cx.nodes,
                                &[ns_decl, import_decl, export_specifier],
                            ),
                        );
                    }

                    // No isolation needed: names match and no self-references.
                    // Update modifiers to include declare if needed.
                    {
                        let mut tracker = self.tracker.borrow_mut();
                        tracker.watched_class_symbol = None;
                        tracker.class_symbol_tracked = false;
                    }
                    let mut mods: Vec<NodeId> = Vec::new();
                    {
                        let mut ec = self.ec.borrow_mut();
                        mods.push(ec.factory.new_token(cx.nodes, Kind::ExportKeyword));
                        if self.needs_declare.get() {
                            mods.push(ec.factory.new_token(cx.nodes, Kind::DeclareKeyword));
                        }
                        let mod_list = ec.factory.new_modifier_list(cx.nodes, mods);
                        drop(ec);
                        let (name_, type_params, heritage, members) = {
                            let d = cx.nodes[class_decl].as_class_declaration();
                            (
                                d.class_like_base.name,
                                d.class_like_base.type_parameters.clone(),
                                d.class_like_base.heritage_clauses.clone(),
                                d.class_like_base.members.clone(),
                            )
                        };
                        return self.ec.borrow_mut().factory.update_class_declaration(
                            cx.nodes,
                            class_decl,
                            Some(mod_list),
                            name_,
                            type_params,
                            heritage,
                            members,
                        );
                    }
                }
                {
                    // unnamed class expression
                    let mut tracker = self.tracker.borrow_mut();
                    tracker.watched_class_symbol = None;
                    tracker.class_symbol_tracked = false;
                }
                let mods = {
                    let mut ec = self.ec.borrow_mut();
                    let mut mods: Vec<NodeId> = Vec::new();
                    mods.push(ec.factory.new_token(cx.nodes, Kind::ExportKeyword));
                    if self.needs_declare.get() {
                        mods.push(ec.factory.new_token(cx.nodes, Kind::DeclareKeyword));
                    }
                    ec.factory.new_modifier_list(cx.nodes, mods)
                };
                let mut class_name = name;
                if !class_name.is_some_and(|n| ast::is_identifier(&cx.nodes[n])) {
                    class_name = Some(self.ec.borrow_mut().factory.new_unique_name_ex(
                        cx.nodes,
                        "_class",
                        &AutoGenerateOptions {
                            flags: GeneratedIdentifierFlags::OPTIMISTIC,
                            ..Default::default()
                        },
                    ));
                }
                let class_decl = self.transform_class_expression_to_declaration(
                    v,
                    cx,
                    rhs,
                    class_name,
                    Some(mods),
                );
                self.preserve_js_doc(class_decl, input, cx.nodes);
                if !name.is_some_and(|n| ast::is_identifier(&cx.nodes[n])) {
                    // Non-identifier name: emit class declaration + named export
                    let export_decl = {
                        let mut ec = self.ec.borrow_mut();
                        let specifier = ec
                            .factory
                            .new_export_specifier(cx.nodes, false, class_name, name);
                        let list = ec.factory.new_node_list(vec![specifier]);
                        let named = ec.factory.new_named_exports(cx.nodes, Some(list));
                        ec.factory.new_export_declaration(
                            cx.nodes,
                            None,
                            false,
                            Some(named),
                            None,
                            None,
                        )
                    };
                    self.remove_all_comments(export_decl);
                    return Some(
                        self.ec
                            .borrow_mut()
                            .factory
                            .new_syntax_list(cx.nodes, &[class_decl, export_decl]),
                    );
                }
                return Some(class_decl);
            }
        }

        if name.is_some_and(|n| ast::is_identifier(&cx.nodes[n])) {
            if name.map(|n| cx.nodes[n].text(cx.nodes).into_owned()) == Some("default".to_string())
            {
                // const _default: Type; export default _default;
                let new_id = self.ec.borrow_mut().factory.new_unique_name_ex(
                    cx.nodes,
                    "_default",
                    &AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::OPTIMISTIC,
                        ..Default::default()
                    },
                );
                {
                    let mut shared = self.shared.borrow_mut();
                    shared.get_symbol_accessibility_diagnostic = Some(Box::new(
                        move |_res: &SymbolAccessibilityResult, _nodes: &[Node]| {
                            Some(SymbolAccessibilityDiagnostic {
                                diagnostic_message:
                                    &tsc_diagnostics::Default_export_of_the_module_has_or_is_using_private_name_0,
                                error_node: Some(input),
                                type_name: None,
                            })
                        },
                    ));
                }
                self.tracker.borrow_mut().push_error_fallback_node(input);
                let type_ = self.ensure_type(input, false, cx);
                let var_decl = self.ec.borrow_mut().factory.new_variable_declaration(
                    cx.nodes,
                    Some(new_id),
                    None,
                    type_,
                    None,
                );
                self.tracker.borrow_mut().pop_error_fallback_node();
                let mod_list = {
                    let mut ec = self.ec.borrow_mut();
                    let mods = if self.needs_declare.get() {
                        vec![ec.factory.new_token(cx.nodes, Kind::DeclareKeyword)]
                    } else {
                        Vec::new()
                    };
                    ec.factory.new_modifier_list(cx.nodes, mods)
                };
                let statement = {
                    let mut ec = self.ec.borrow_mut();
                    let decl_list = ec.factory.new_node_list(vec![var_decl]);
                    let decl_list = ec.factory.new_variable_declaration_list(
                        cx.nodes,
                        Some(decl_list),
                        NodeFlags::CONST,
                    );
                    ec.factory
                        .new_variable_statement(cx.nodes, Some(mod_list), Some(decl_list))
                };

                let assignment = self.ec.borrow_mut().factory.new_export_assignment(
                    cx.nodes,
                    cx.nodes[input].modifiers().cloned(),
                    false,
                    None,
                    Some(new_id),
                );
                // Remove comments from the export declaration and copy them onto the synthetic _default declaration
                self.preserve_js_doc(statement, input, cx.nodes);
                self.remove_all_comments(assignment);
                return Some(
                    self.ec
                        .borrow_mut()
                        .factory
                        .new_syntax_list(cx.nodes, &[statement, assignment]),
                );
            } else {
                let referenced = {
                    let symbols = self.symbols;
                    match symbols {
                        Some(symbols) => {
                            self.resolver.borrow_mut().get_referenced_value_declaration(
                                name.unwrap(),
                                cx.nodes,
                                symbols,
                            )
                        }
                        None => self
                            .resolver
                            .borrow()
                            .get_referenced_value_declaration_unsafe(name.unwrap(), cx.nodes),
                    }
                };
                if referenced == Some(input) || referenced.is_none() {
                    // only inline to a export var if the `name` lookup points at this assignment or nothing - if it points at something else, we must use a temp name
                    // export var name: Type
                    self.tracker.borrow_mut().push_error_fallback_node(input);
                    let type_ = self.ensure_type(input, false, cx);
                    let var_decl = self
                        .ec
                        .borrow_mut()
                        .factory
                        .new_variable_declaration(cx.nodes, name, None, type_, None);
                    self.tracker.borrow_mut().pop_error_fallback_node();
                    let mod_list = {
                        let mut ec = self.ec.borrow_mut();
                        let mods = if self.needs_declare.get() {
                            vec![
                                ec.factory.new_token(cx.nodes, Kind::ExportKeyword),
                                ec.factory.new_token(cx.nodes, Kind::DeclareKeyword),
                            ]
                        } else {
                            vec![ec.factory.new_token(cx.nodes, Kind::ExportKeyword)]
                        };
                        ec.factory.new_modifier_list(cx.nodes, mods)
                    };
                    let statement = {
                        let mut ec = self.ec.borrow_mut();
                        let decl_list = ec.factory.new_node_list(vec![var_decl]);
                        let decl_list = ec.factory.new_variable_declaration_list(
                            cx.nodes,
                            Some(decl_list),
                            NodeFlags::NONE,
                        );
                        ec.factory
                            .new_variable_statement(cx.nodes, Some(mod_list), Some(decl_list))
                    };
                    return Some(statement);
                }
            }
        }
        // const _exported: Type; export {_exported as "name"};
        let new_id = self.ec.borrow_mut().factory.new_unique_name_ex(
            cx.nodes,
            "_exported",
            &AutoGenerateOptions {
                flags: GeneratedIdentifierFlags::OPTIMISTIC,
                ..Default::default()
            },
        );
        {
            let mut shared = self.shared.borrow_mut();
            shared.get_symbol_accessibility_diagnostic = Some(Box::new(
                move |_res: &SymbolAccessibilityResult, _nodes: &[Node]| {
                    Some(SymbolAccessibilityDiagnostic {
                        diagnostic_message:
                            &tsc_diagnostics::Default_export_of_the_module_has_or_is_using_private_name_0,
                        error_node: Some(input),
                        type_name: None,
                    })
                },
            ));
        }
        self.tracker.borrow_mut().push_error_fallback_node(input);
        let type_ = self.ensure_type(input, false, cx);
        let var_decl = self.ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            Some(new_id),
            None,
            type_,
            None,
        );
        self.tracker.borrow_mut().pop_error_fallback_node();
        let mod_list = {
            let mut ec = self.ec.borrow_mut();
            let mods = if self.needs_declare.get() {
                vec![ec.factory.new_token(cx.nodes, Kind::DeclareKeyword)]
            } else {
                Vec::new()
            };
            ec.factory.new_modifier_list(cx.nodes, mods)
        };
        let statement = {
            let mut ec = self.ec.borrow_mut();
            let decl_list = ec.factory.new_node_list(vec![var_decl]);
            let decl_list = ec.factory.new_variable_declaration_list(
                cx.nodes,
                Some(decl_list),
                NodeFlags::CONST,
            );
            ec.factory
                .new_variable_statement(cx.nodes, Some(mod_list), Some(decl_list))
        };

        let assignment = {
            let mut ec = self.ec.borrow_mut();
            let specifier = ec
                .factory
                .new_export_specifier(cx.nodes, false, Some(new_id), name);
            let list = ec.factory.new_node_list(vec![specifier]);
            let named = ec.factory.new_named_exports(cx.nodes, Some(list));
            ec.factory
                .new_export_declaration(cx.nodes, None, false, Some(named), None, None)
        };
        // Remove comments from the export declaration and copy them onto the synthetic _default declaration
        self.preserve_js_doc(statement, input, cx.nodes);
        self.remove_all_comments(assignment);
        Some(
            self.ec
                .borrow_mut()
                .factory
                .new_syntax_list(cx.nodes, &[statement, assignment]),
        )
    }

    /// `(tx *DeclarationTransformer) wrapInCJSExportNamespace`.
    fn wrap_in_cjs_export_namespace(&self, cx: &mut VisitorCx<'_, '_>, content: NodeId) -> NodeId {
        let Some(ns_name) = self.cjs_export_assignment_name.get() else {
            return content;
        };
        // Reuse the same name node so unique names resolve consistently with the class/export
        let members: Vec<NodeId> = if cx.nodes[content].kind == Kind::SyntaxList {
            cx.nodes[content].as_syntax_list().children.to_vec()
        } else {
            vec![content]
        };
        let members = self
            .declare_stripping_visitor
            .borrow()
            .as_ref()
            .expect("declareStrippingVisitor")
            .visit_slice(cx, &members)
            .unwrap_or(members);
        let mut ec = self.ec.borrow_mut();
        let mut ns_mods: Vec<NodeId> = Vec::new();
        if self.needs_declare.get() {
            ns_mods.push(ec.factory.new_token(cx.nodes, Kind::DeclareKeyword));
        }
        let ns_mods = ec.factory.new_modifier_list(cx.nodes, ns_mods);
        let members_list = ec.factory.new_node_list(members);
        let block = ec.factory.new_module_block(cx.nodes, Some(members_list));
        ec.factory.new_module_declaration(
            cx.nodes,
            Some(ns_mods),
            Kind::NamespaceKeyword,
            Some(ns_name),
            None,
            Some(block),
        )
    }

    /// `(tx *DeclarationTransformer) transformClassExpressionToDeclaration` —
    /// converts a class expression into a class declaration for use in CJS
    /// export declarations (e.g., `exports.K = class K {}` or
    /// `module.exports = class Thing {}`). Delegates to the shared
    /// `buildClassMembers` helper to stay in sync with
    /// `transformClassDeclaration`.
    fn transform_class_expression_to_declaration<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        class_expr: NodeId,
        class_name: Option<NodeId>,
        modifiers: Option<tsc_ast::ModifierList>,
    ) -> NodeId {
        let previous_enclosing_declaration = self.enclosing_declaration.get();
        self.enclosing_declaration.set(Some(class_expr));
        let previous_in_class_expression_declaration = self.in_class_expression_declaration.get();
        self.in_class_expression_declaration.set(true);
        // Go `defer`: restored explicitly before returning (no early exits below).

        let mut extra_members: Vec<NodeId> = Vec::new();
        if ast::is_in_js_file(Some(class_expr), cx.nodes) {
            extra_members = self.collect_this_property_assignments(v, cx, class_expr);
        }
        let members = self.build_class_members(v, cx, class_expr, extra_members);
        let type_parameters = self.ensure_type_params(
            class_expr,
            cx.nodes[class_expr]
                .as_class_expression()
                .class_like_base
                .type_parameters
                .clone(),
            cx,
        );
        let heritage_clauses = v.visit_nodes(
            cx,
            cx.nodes[class_expr]
                .as_class_expression()
                .class_like_base
                .heritage_clauses
                .clone(),
        );

        let result = self.ec.borrow_mut().factory.new_class_declaration(
            cx.nodes,
            modifiers,
            class_name,
            type_parameters,
            heritage_clauses,
            Some(members),
        );
        self.enclosing_declaration
            .set(previous_enclosing_declaration);
        self.in_class_expression_declaration
            .set(previous_in_class_expression_declaration);
        result
    }

    /// `(tx *DeclarationTransformer) rewriteModuleSpecifier`.
    fn rewrite_module_specifier(
        &self,
        parent: NodeId,
        input: Option<NodeId>,
        nodes: &[Node],
    ) -> Option<NodeId> {
        input?;
        self.result_has_external_module_indicator.set(
            self.result_has_external_module_indicator.get()
                || (nodes[parent].kind != Kind::ModuleDeclaration
                    && nodes[parent].kind != Kind::ImportType),
        );
        input
    }

    /// `(tx *DeclarationTransformer) preserveJsDoc` — copies the comment
    /// range from original to updated node so JSDoc comments are preserved.
    fn preserve_js_doc(&self, updated: NodeId, original: NodeId, nodes: &[Node]) {
        self.ec().assign_comment_range(nodes, updated, original);
    }

    /// `(tx *DeclarationTransformer) preservePartialJsDoc`.
    fn preserve_partial_js_doc(
        &self,
        updated: NodeId,
        original: NodeId,
        cx: &mut VisitorCx<'_, '_>,
    ) {
        if !cx.nodes[original].flags.intersects(NodeFlags::REPARSED) {
            return;
        }
        let source_file = ast::get_source_file_of_node(Some(original), cx.nodes);
        let jsdoc = core::first_or_nil(&ast::eager_js_doc(cx.nodes, original, source_file));
        let Some(jsdoc) = jsdoc else {
            return;
        };
        let description = scanner::utilities::get_text_of_jsdoc_comment(
            cx.nodes[jsdoc].as_js_doc().comment.as_ref(),
            cx.nodes,
        );
        if description.is_empty() {
            return;
        }
        let text = format!("*\n * {}\n ", description.replace('\n', "\n * "));
        self.ec().add_synthetic_leading_comment(
            updated,
            Kind::MultiLineCommentTrivia,
            &text,
            true, /*hasTrailingNewLine*/
        );
    }

    /// `(tx *DeclarationTransformer) removeAllComments`.
    fn remove_all_comments(&self, node: NodeId) {
        self.ec().add_emit_flags(node, EmitFlags::NO_COMMENTS);
        // !!! TODO: Also remove synthetic trailing/leading comments added by transforms
        // emitNode.leadingComments = undefined;
        // emitNode.trailingComments = undefined;
    }

    /// `(tx *DeclarationTransformer) ensureType`.
    fn ensure_type(
        &self,
        node: NodeId,
        ignore_private: bool,
        cx: &mut VisitorCx<'_, '_>,
    ) -> Option<NodeId> {
        if !ignore_private
            && !self
                .resolver
                .borrow()
                .get_effective_declaration_flags(
                    self.ec().parse_node(cx.nodes, node).unwrap_or(node),
                    ModifierFlags::PRIVATE,
                    cx.nodes,
                )
                .is_empty()
        {
            // Private nodes emit no types (except private parameter properties, whose parameter types are actually visible)
            return None;
        }

        if self.should_print_with_initializer(node, cx.nodes) {
            // Literal const declarations will have an initializer ensured rather than a type
            return None;
        }

        // Should be removed createTypeOfDeclaration will actually now reuse the existing annotation so there is no real need to duplicate type walking
        // Left in for now to minimize diff during syntactic type node builder refactor
        let type_annotation = cx.nodes[node].type_();
        if !ast::is_export_assignment(&cx.nodes[node])
            && !ast::is_binding_element(&cx.nodes[node])
            && type_annotation.is_some()
            && (!ast::is_parameter_declaration(&cx.nodes[node]) || {
                // Do NOT hold a `symbol_arena` borrow across this call — the
                // resolver can mint new symbols while resolving the declared
                // type (RefCell already borrowed). The `symbols` param is
                // unused by the resolver.
                !self.resolver.borrow().requires_adding_implicit_undefined(
                    node,
                    None,
                    self.enclosing_declaration.get(),
                    cx.nodes,
                    &[],
                )
            })
        {
            if self
                .shared
                .borrow()
                .current_source_file
                .is_some_and(|f| ast::is_source_file_js(cx.nodes[f].as_source_file()))
            {
                // JS types have a heap of constructs we can't directly emit into .d.ts files; the node builder contains logic to remap those where possible, so we invoke it here
                // In strada we always built js declarations symbolically, so all js type nodes went through this postprocessing
                let mut js_flags = DECLARATION_EMIT_NODE_BUILDER_FLAGS;
                if self.in_class_expression_declaration.get() {
                    js_flags &= !nodebuilder::Flags::WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL;
                }
                let res = {
                    self.resolver.borrow().try_js_type_node_to_type_node(
                        type_annotation.unwrap(),
                        self.enclosing_declaration.get(),
                        js_flags,
                        DECLARATION_EMIT_INTERNAL_NODE_BUILDER_FLAGS,
                        self.tracker.clone(),
                        cx.nodes,
                    )
                };
                if res.is_some() {
                    return res;
                }
                // otherwise, fall back to full serialization
            } else {
                return self
                    .root_visitor
                    .borrow()
                    .as_ref()
                    .expect("rootVisitor")
                    .visit_node(cx, type_annotation);
            }
        }

        let old_error_name_node = self.shared.borrow().error_name_node;
        self.shared.borrow_mut().error_name_node = cx.nodes[node].name();
        // PORT: the selector is only swapped out when this node can produce
        // diagnostics; otherwise the enclosing context's selector stays put.
        let mut old_diag: Option<GetSymbolAccessibilityDiagnostic> = None;
        let diag_swapped = !self.suppress_new_diagnostic_contexts.get()
            && can_produce_diagnostics(&cx.nodes[node]);
        if diag_swapped {
            let mut shared = self.shared.borrow_mut();
            old_diag = std::mem::replace(
                &mut shared.get_symbol_accessibility_diagnostic,
                Some(create_get_symbol_accessibility_diagnostic_for_node(
                    node, cx.nodes,
                )),
            );
        }
        let type_node: Option<NodeId>;

        let mut flags = DECLARATION_EMIT_NODE_BUILDER_FLAGS;
        if self.in_class_expression_declaration.get() {
            flags &= !nodebuilder::Flags::WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL;
        }
        if ast::has_inferred_type(&cx.nodes[node]) {
            type_node = self.resolver.borrow().create_type_of_declaration(
                node,
                self.enclosing_declaration.get(),
                flags,
                DECLARATION_EMIT_INTERNAL_NODE_BUILDER_FLAGS,
                self.tracker.clone(),
                cx.nodes,
            );
        } else if ast::is_function_like(Some(node), cx.nodes) {
            type_node = self
                .resolver
                .borrow()
                .create_return_type_of_signature_declaration(
                    node,
                    self.enclosing_declaration.get(),
                    flags,
                    DECLARATION_EMIT_INTERNAL_NODE_BUILDER_FLAGS,
                    self.tracker.clone(),
                    cx.nodes,
                );
        } else {
            panic!(
                "ensureType: unreachable node kind {:?}",
                cx.nodes[node].kind
            );
        }

        self.shared.borrow_mut().error_name_node = old_error_name_node;
        if diag_swapped {
            self.shared.borrow_mut().get_symbol_accessibility_diagnostic = old_diag;
        }
        type_node.or_else(|| {
            Some(
                self.ec
                    .borrow_mut()
                    .factory
                    .new_keyword_type_node(cx.nodes, Kind::AnyKeyword),
            )
        })
    }

    /// `(tx *DeclarationTransformer) shouldPrintWithInitializer`.
    fn should_print_with_initializer(&self, node: NodeId, nodes: &[Node]) -> bool {
        can_have_literal_initializer(&*self.resolver.borrow(), node, nodes)
            && nodes[node].initializer().is_some()
            && self.resolver.borrow().is_literal_const_declaration(
                self.ec().most_original(Some(node)).unwrap_or(node),
                nodes,
            )
    }

    /// `(tx *DeclarationTransformer) checkEntityNameVisibility`.
    fn check_entity_name_visibility(
        &self,
        entity_name: Option<NodeId>,
        enclosing_declaration: Option<NodeId>,
        nodes: &[Node],
    ) {
        let Some(entity_name) = entity_name else {
            return;
        };
        let visibility_result = self.resolver.borrow().is_entity_name_visible(
            entity_name,
            enclosing_declaration,
            nodes,
        );
        self.tracker
            .borrow_mut()
            .handle_symbol_accessibility_error(visibility_result, nodes);
    }
}

impl<'a> DeclarationTransformerState<'a> {
    /// `(tx *DeclarationTransformer) transformTopLevelDeclaration` —
    /// transforms the direct child of a source file into zero or more
    /// replacement statements.
    fn transform_top_level_declaration<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        if !self.shared.borrow().late_marked_statements.is_empty() {
            // Remove duplicates of the current statement from the deferred work queue (this was done via orderedRemoveItem in strada - why? to ensure the same backing array? microop?)
            let filtered = core::filter(
                self.shared.borrow().late_marked_statements.as_slice(),
                |n| *n != input,
            )
            .into_owned();
            self.shared.borrow_mut().late_marked_statements = filtered;
        }
        if self.should_strip_internal(Some(input), cx.nodes) {
            return None;
        }
        if cx.nodes[input].kind == Kind::ImportEqualsDeclaration {
            return self.transform_import_equals_declaration(cx, input);
        }
        if cx.nodes[input].kind == Kind::ImportDeclaration
            || cx.nodes[input].kind == Kind::JSImportDeclaration
        {
            let res = self.transform_import_declaration(cx, input);
            if let Some(res) = res
                && cx.nodes[res].kind != Kind::ImportDeclaration
            {
                let res = self.ec.borrow_mut().factory.clone_node(cx.nodes, res);
                cx.nodes[res].kind = Kind::ImportDeclaration;
                return Some(res);
            }
            return res;
        }
        if ast::is_declaration(&cx.nodes[input])
            && is_declaration_and_not_visible(&self.ec(), &*self.resolver.borrow(), input, cx.nodes)
        {
            return None;
        }

        // !!! TODO: JSDoc support
        // if (isJSDocImportTag(input)) return;

        // Elide implementation signatures from overload sets
        if ast::is_function_like(Some(input), cx.nodes)
            && self
                .resolver
                .borrow()
                .is_implementation_of_overload(input, cx.nodes)
        {
            return None;
        }
        let original = self.ec().most_original(Some(input)).unwrap_or(input);
        let id = ast::get_node_id(&cx.nodes[original]);
        let is_expando_host = self.expando_hosts.borrow().contains_key(&id);
        let has_deferred_expando_assignments =
            self.deferred_expando_assignments.borrow().contains_key(&id);
        if is_expando_host || has_deferred_expando_assignments {
            return self.create_full_expando_block(v, cx, id);
        }

        let previous_enclosing_declaration = self.enclosing_declaration.get();
        if is_enclosing_declaration(&cx.nodes[input], cx.nodes) {
            self.enclosing_declaration.set(Some(input));
        }

        let can_produce_diagnostic = can_produce_diagnostics(&cx.nodes[input]);
        let (old_diag, old_name) = {
            let mut shared = self.shared.borrow_mut();
            let old_name = shared.error_name_node;
            let old_diag = if can_produce_diagnostic {
                std::mem::replace(
                    &mut shared.get_symbol_accessibility_diagnostic,
                    Some(create_get_symbol_accessibility_diagnostic_for_node(
                        input, cx.nodes,
                    )),
                )
            } else {
                None
            };
            (old_diag, old_name)
        };
        let save_needs_declare = self.needs_declare.get();

        let result: Option<NodeId> = match cx.nodes[input].kind {
            Kind::TypeAliasDeclaration | Kind::JSTypeAliasDeclaration => {
                Some(self.transform_type_alias_declaration(v, cx, input))
            }
            Kind::InterfaceDeclaration => Some(self.transform_interface_declaration(v, cx, input)),
            Kind::FunctionDeclaration => Some(self.transform_function_declaration(v, cx, input)),
            Kind::ModuleDeclaration => self.transform_module_declaration(v, cx, input),
            Kind::ClassDeclaration => self.transform_class_declaration(v, cx, input),
            Kind::VariableStatement => self.transform_variable_statement(v, cx, input),
            Kind::EnumDeclaration => Some(self.transform_enum_declaration(cx, input)),
            kind => {
                // Anything left unhandled is an error, so this should be unreachable
                panic!("Unhandled top-level node in declaration emit: {:?}", kind)
            }
        };

        self.enclosing_declaration
            .set(previous_enclosing_declaration);
        {
            let mut shared = self.shared.borrow_mut();
            if can_produce_diagnostic {
                shared.get_symbol_accessibility_diagnostic = old_diag;
            }
            shared.error_name_node = old_name;
        }
        self.needs_declare.set(save_needs_declare);
        result
    }

    /// `(tx *DeclarationTransformer) transformTypeAliasDeclaration`.
    fn transform_type_alias_declaration<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        self.needs_declare.set(false);
        let (name, type_parameters, type_node) = {
            let d = cx.nodes[input].as_type_alias_declaration();
            (d.name, d.type_parameters.clone(), d.type_)
        };
        let modifiers = self.ensure_modifiers(input, cx);
        let type_parameters = v.visit_nodes(cx, type_parameters);
        let type_node = v.visit_node(cx, type_node);
        self.ec
            .borrow_mut()
            .factory
            .update_type_alias_declaration(
                cx.nodes,
                input,
                modifiers,
                name,
                type_parameters,
                type_node,
            )
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformInterfaceDeclaration`.
    fn transform_interface_declaration<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let (name, type_parameters, heritage_clauses, members) = {
            let d = cx.nodes[input].as_interface_declaration();
            (
                d.name,
                d.type_parameters.clone(),
                d.heritage_clauses.clone(),
                d.members.clone(),
            )
        };
        let modifiers = self.ensure_modifiers(input, cx);
        let type_parameters = v.visit_nodes(cx, type_parameters);
        let heritage_clauses = v.visit_nodes(cx, heritage_clauses);
        let members = v.visit_nodes(cx, members);
        self.ec
            .borrow_mut()
            .factory
            .update_interface_declaration(
                cx.nodes,
                input,
                modifiers,
                name,
                type_parameters,
                heritage_clauses,
                members,
            )
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformFunctionDeclaration`.
    fn transform_function_declaration<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        if self
            .resolver
            .borrow()
            .is_expando_function_declaration(input, cx.nodes)
        {
            self.report_expando_function_errors(input, cx.nodes);
        }
        let (name, type_parameters, parameters) = {
            let d = cx.nodes[input].as_function_declaration();
            (
                d.name,
                d.function_like_with_body_base
                    .function_like_base
                    .type_parameters
                    .clone(),
                d.function_like_with_body_base
                    .function_like_base
                    .parameters
                    .clone(),
            )
        };
        let modifiers = self.ensure_modifiers(input, cx);
        let type_parameters = self.ensure_type_params(input, type_parameters, cx);
        let parameters = self.update_param_list(input, parameters, cx);
        let return_type = self.ensure_type(input, false, cx);
        self.ec
            .borrow_mut()
            .factory
            .update_function_declaration(
                cx.nodes,
                input,
                modifiers,
                None,
                name,
                type_parameters,
                Some(parameters),
                return_type,
                None, /*fullSignature*/
                None,
            )
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformModuleDeclaration`.
    fn transform_module_declaration<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        // !!! TODO: module declarations are now parsed into nested module objects with export modifiers
        // It'd be good to collapse those back in the declaration output, but the AST can't represent the
        // `namespace a.b.c` shape for the printer (without using invalid identifier names).
        let mods = self.ensure_modifiers(input, cx);
        let save_needs_declare = self.needs_declare.get();
        self.needs_declare.set(false);
        let (name, mut keyword, body, attributes) = {
            let d = cx.nodes[input].as_module_declaration();
            (d.name, d.keyword, d.body_base.body, d.attributes)
        };
        if keyword != Kind::GlobalKeyword
            && !name.is_some_and(|n| ast::is_string_literal(&cx.nodes[n]))
        {
            keyword = Kind::NamespaceKeyword;
        }
        let attributes = v.visit_node(cx, attributes);

        if let Some(inner) = body
            && cx.nodes[inner].kind == Kind::ModuleBlock
        {
            let old_needs_scope_fix = self.needs_scope_fix_marker.get();
            let old_has_scope_fix = self.result_has_scope_marker.get();
            self.result_has_scope_marker.set(false);
            self.needs_scope_fix_marker.set(false);
            let statement_list = cx.nodes[inner].statement_list().cloned();
            let statements = v.visit_nodes(cx, statement_list);
            let mut late_statements =
                self.transform_and_replace_late_painted_statements(v, cx, statements.unwrap());
            if cx.nodes[input].flags.intersects(NodeFlags::AMBIENT) {
                self.needs_scope_fix_marker.set(false); // If it was `declare`'d everything is implicitly exported already, ignore late printed "privates"
            }
            // With the final list of statements, there are 3 possibilities:
            // 1. There's an export assignment or export declaration in the namespace - do nothing
            // 2. Everything is exported and there are no export assignments or export declarations - strip all export modifiers
            // 3. Some things are exported, some are not, and there's no marker - add an empty marker
            if !ast::is_global_scope_augmentation(&cx.nodes[input])
                && !self.result_has_scope_marker.get()
                && !has_scope_marker(Some(&late_statements), cx.nodes)
            {
                if self.needs_scope_fix_marker.get() {
                    let marker = create_empty_exports(&mut self.ec.borrow_mut().factory, cx.nodes);
                    let mut list = late_statements.nodes.to_vec();
                    list.push(marker);
                    late_statements = self.ec().factory.new_node_list(list);
                } else {
                    late_statements = self
                        .export_stripping_visitor
                        .borrow()
                        .as_ref()
                        .expect("exportStrippingVisitor")
                        .visit_nodes(cx, Some(late_statements.clone()))
                        .unwrap_or(late_statements);
                }
            }

            let body = self
                .ec
                .borrow_mut()
                .factory
                .update_module_block(cx.nodes, inner, Some(late_statements))
                .unwrap_or(inner);
            self.needs_declare.set(save_needs_declare);
            self.needs_scope_fix_marker.set(old_needs_scope_fix);
            self.result_has_scope_marker.set(old_has_scope_fix);

            return self
                .ec
                .borrow_mut()
                .factory
                .update_module_declaration(
                    cx.nodes,
                    input,
                    mods,
                    keyword,
                    name,
                    attributes,
                    Some(body),
                )
                .or(Some(input));
        }
        if let Some(inner) = body {
            // trigger visit. ignore result (is deferred, so is just inner unless elided)
            v.visit_node(cx, Some(inner));
            // eagerly transform nested namespaces (the nesting doesn't need any elision or painting done)
            let original = self.ec().most_original(Some(inner)).unwrap_or(inner);
            let id = ast::get_node_id(&cx.nodes[original]);
            let body = self
                .late_statement_replacement_map
                .borrow_mut()
                .remove(&id)
                .flatten();
            return self
                .ec
                .borrow_mut()
                .factory
                .update_module_declaration(cx.nodes, input, mods, keyword, name, attributes, body)
                .or(Some(input));
        }
        self.ec
            .borrow_mut()
            .factory
            .update_module_declaration(cx.nodes, input, mods, keyword, name, attributes, None)
            .or(Some(input))
    }

    /// `(tx *DeclarationTransformer) stripExportModifiers`.
    fn strip_export_modifiers(&self, cx: &mut VisitorCx<'_, '_>, statement: NodeId) -> NodeId {
        let parse_node = self
            .ec()
            .parse_node(cx.nodes, statement)
            .unwrap_or(statement);
        if ast::is_import_equals_declaration(&cx.nodes[statement])
            || !self
                .resolver
                .borrow()
                .get_effective_declaration_flags(parse_node, ModifierFlags::DEFAULT, cx.nodes)
                .is_empty()
            || !ast::can_have_modifiers(&cx.nodes[statement])
        {
            // `export import` statements should remain as-is, as imports are _not_ implicitly exported in an ambient namespace
            // Likewise, `export default` classes and the like and just be `default`, so we preserve their `export` modifiers, too
            return statement;
        }

        let old_flags = ast::get_combined_modifier_flags(statement, cx.nodes);
        if !old_flags.intersects(ModifierFlags::EXPORT) {
            return statement;
        }
        let new_flags =
            ModifierFlags(old_flags.0 & (ModifierFlags::ALL.0 ^ ModifierFlags::EXPORT.0));
        let modifiers = {
            let mut ec = self.ec.borrow_mut();
            ast::create_modifiers_from_modifier_flags(new_flags, &mut |kind| {
                ec.factory.new_token(cx.nodes, kind)
            })
        };
        let list = self.ec().factory.new_modifier_list(cx.nodes, modifiers);
        ast::replace_modifiers(
            &mut self.ec.borrow_mut().factory,
            cx.nodes,
            statement,
            Some(list),
        )
        .unwrap_or(statement)
    }

    /// `(tx *DeclarationTransformer) buildClassMembers` — builds the member
    /// list for a class-like node (ClassDeclaration or ClassExpression);
    /// handles parameter properties, private identifiers, late-bound index
    /// signatures, and visited members. `extra_members` carries, e.g.,
    /// this-property assignments from JS files.
    fn build_class_members<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        class_node: NodeId,
        extra_members: Vec<NodeId>,
    ) -> NodeList {
        let ctor = ast::get_first_constructor_with_body(&cx.nodes[class_node], cx.nodes);
        let mut parameter_properties: Vec<NodeId> = Vec::new();
        if let Some(ctor) = ctor {
            let old_diag = self
                .shared
                .borrow_mut()
                .get_symbol_accessibility_diagnostic
                .take();
            let params = cx.nodes[ctor]
                .as_constructor_declaration()
                .function_like_with_body_base
                .function_like_base
                .parameters
                .clone();
            if let Some(params) = params {
                for &param in params.nodes.iter() {
                    if !ast::has_syntactic_modifier(
                        &cx.nodes[param],
                        ModifierFlags::PARAMETER_PROPERTY_MODIFIER,
                    ) || self.should_strip_internal(Some(param), cx.nodes)
                    {
                        continue;
                    }
                    self.shared.borrow_mut().get_symbol_accessibility_diagnostic = Some(
                        create_get_symbol_accessibility_diagnostic_for_node(param, cx.nodes),
                    );
                    if cx.nodes[param]
                        .name()
                        .is_some_and(|n| cx.nodes[n].kind == Kind::Identifier)
                    {
                        let modifiers = self.ensure_modifiers(param, cx);
                        let name = cx.nodes[param].name();
                        let question_token = cx.nodes[param].question_token(cx.nodes);
                        let type_node = self.ensure_type(param, false, cx);
                        let initializer = self.ensure_no_initializer(param, cx);
                        let updated = self.ec.borrow_mut().factory.new_property_declaration(
                            cx.nodes,
                            modifiers,
                            name,
                            question_token,
                            type_node,
                            initializer,
                        );
                        self.preserve_js_doc(updated, param, cx.nodes);
                        parameter_properties.push(updated);
                    } else {
                        // Pattern - this is currently an error, but we emit declarations for it somewhat correctly
                        let name = cx.nodes[param].name();
                        parameter_properties.extend(self.walk_binding_pattern(
                            name.unwrap(),
                            param,
                            cx,
                        ));
                    }
                }
            }
            self.shared.borrow_mut().get_symbol_accessibility_diagnostic = old_diag;
        }

        // When the class has at least one private identifier, create a unique constant identifier to retain the nominal typing behavior
        // Prevents other classes with the same public members from being used in place of the current class
        let mut private_identifier: Option<NodeId> = None;
        let members_list = cx.nodes[class_node]
            .class_like_data()
            .map(|d| d.members.clone())
            .flatten();
        if core::some(
            members_list
                .as_ref()
                .map(|m| m.nodes.as_ref())
                .unwrap_or(&[]),
            |member| {
                cx.nodes[*member]
                    .name()
                    .is_some_and(|n| ast::is_private_identifier(&cx.nodes[n]))
            },
        ) {
            private_identifier = Some({
                let mut ec = self.ec.borrow_mut();
                let name = ec.factory.new_private_identifier(cx.nodes, "#private");
                ec.factory
                    .new_property_declaration(cx.nodes, None, Some(name), None, None, None)
            });
        }

        let late_indexes = {
            self.resolver.borrow().create_late_bound_index_signatures(
                class_node,
                self.enclosing_declaration.get(),
                DECLARATION_EMIT_NODE_BUILDER_FLAGS,
                DECLARATION_EMIT_INTERNAL_NODE_BUILDER_FLAGS,
                self.tracker.clone(),
                cx.nodes,
            )
        };

        let mut member_nodes: Vec<NodeId> =
            Vec::with_capacity(members_list.as_ref().map(|m| m.nodes.len()).unwrap_or(0));
        if let Some(p) = private_identifier {
            member_nodes.push(p);
        }
        member_nodes.extend(late_indexes);
        member_nodes.extend(parameter_properties);
        member_nodes.extend(extra_members);
        if let Some(visit_result) = v.visit_nodes(cx, members_list)
            && !visit_result.nodes.is_empty()
        {
            member_nodes.extend_from_slice(&visit_result.nodes);
        }
        self.ec().factory.new_node_list(member_nodes)
    }

    /// `(tx *DeclarationTransformer) transformClassDeclaration`.
    fn transform_class_declaration<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let previous_enclosing_declaration = self.enclosing_declaration.get();
        self.enclosing_declaration.set(Some(input));
        // Go `defer`: restored explicitly before every return below.
        {
            let mut shared = self.shared.borrow_mut();
            shared.error_name_node = cx.nodes[input].name();
        }
        self.tracker.borrow_mut().push_error_fallback_node(input);

        let modifiers = self.ensure_modifiers(input, cx);
        let type_parameters = self.ensure_type_params(
            input,
            cx.nodes[input]
                .as_class_declaration()
                .class_like_base
                .type_parameters
                .clone(),
            cx,
        );

        // Collect this.x property assignments from constructors and static blocks in JS files
        let mut extra_members: Vec<NodeId> = Vec::new();
        if ast::is_in_js_file(Some(input), cx.nodes) {
            extra_members = self.collect_this_property_assignments(v, cx, input);
        }

        let members = self.build_class_members(v, cx, input, extra_members);

        let extends_clause = get_effective_base_type_node(input, cx.nodes);

        if let Some(extends_clause) = extends_clause {
            let expression = cx.nodes[extends_clause]
                .as_expression_with_type_arguments()
                .expression;
            let expression_is_name = expression.is_some_and(|e| {
                ast::is_entity_name_expression(&cx.nodes[e], cx.nodes)
                    || cx.nodes[e].kind == Kind::NullKeyword
            });
            if !expression_is_name {
                let extends_expr = expression.unwrap_or(extends_clause);
                // Add an isolated declarations error on this extends clause
                self.tracker
                    .borrow_mut()
                    .report_inference_fallback(extends_expr, cx.nodes);
                let mut old_id = "default".to_string();
                let input_name = cx.nodes[input].name();
                if ast::node_is_present(input_name, cx.nodes)
                    && input_name.is_some_and(|n| {
                        ast::is_identifier(&cx.nodes[n]) && !cx.nodes[n].text(cx.nodes).is_empty()
                    })
                {
                    old_id = input_name
                        .map(|n| cx.nodes[n].text(cx.nodes).into_owned())
                        .unwrap_or_default();
                }
                let new_id = self.ec.borrow_mut().factory.new_unique_name_ex(
                    cx.nodes,
                    &format!("{}_base", old_id),
                    &AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::OPTIMISTIC,
                        ..Default::default()
                    },
                );
                {
                    let mut shared = self.shared.borrow_mut();
                    shared.get_symbol_accessibility_diagnostic = Some(Box::new(
                        move |_res: &SymbolAccessibilityResult, _nodes: &[Node]| {
                            Some(SymbolAccessibilityDiagnostic {
                                diagnostic_message:
                                    &tsc_diagnostics::X_extends_clause_of_exported_class_0_has_or_is_using_private_name_1,
                                error_node: Some(extends_clause),
                                type_name: input_name,
                            })
                        },
                    ));
                }

                let type_of_expression = {
                    self.resolver.borrow().create_type_of_expression(
                        extends_expr,
                        Some(input),
                        DECLARATION_EMIT_NODE_BUILDER_FLAGS,
                        DECLARATION_EMIT_INTERNAL_NODE_BUILDER_FLAGS,
                        self.tracker.clone(),
                        cx.nodes,
                    )
                };
                let var_decl = self.ec.borrow_mut().factory.new_variable_declaration(
                    cx.nodes,
                    Some(new_id),
                    None,
                    type_of_expression,
                    None,
                );
                let mods = if self.needs_declare.get() {
                    let mut ec = self.ec.borrow_mut();
                    let m = ec.factory.new_token(cx.nodes, Kind::DeclareKeyword);
                    Some(ec.factory.new_modifier_list(cx.nodes, vec![m]))
                } else {
                    None
                };
                let statement = {
                    let mut ec = self.ec.borrow_mut();
                    let decl_list = ec.factory.new_node_list(vec![var_decl]);
                    let decl_list = ec.factory.new_variable_declaration_list(
                        cx.nodes,
                        Some(decl_list),
                        NodeFlags::CONST,
                    );
                    ec.factory
                        .new_variable_statement(cx.nodes, mods, Some(decl_list))
                };
                let new_heritage_clause = {
                    let parent = cx.nodes[extends_clause]
                        .parent
                        .expect("heritage clause parent");
                    let token = cx.nodes[parent].as_heritage_clause().token;
                    let type_arguments = cx.nodes[extends_clause]
                        .as_expression_with_type_arguments()
                        .type_arguments
                        .clone();
                    let type_arguments = v.visit_nodes(cx, type_arguments);
                    let mut ec = self.ec.borrow_mut();
                    let updated_element = ec
                        .factory
                        .update_expression_with_type_arguments(
                            cx.nodes,
                            extends_clause,
                            Some(new_id),
                            type_arguments,
                        )
                        .unwrap_or(extends_clause);
                    let list = ec.factory.new_node_list(vec![updated_element]);
                    ec.factory
                        .update_heritage_clause(cx.nodes, parent, token, Some(list))
                        .unwrap_or(parent)
                };
                // should just be `implements`
                let retained_heritage_clauses = v.visit_nodes(
                    cx,
                    cx.nodes[input]
                        .as_class_declaration()
                        .class_like_base
                        .heritage_clauses
                        .clone(),
                );
                let mut heritage_list = vec![new_heritage_clause];
                if let Some(retained) = retained_heritage_clauses
                    && !retained.nodes.is_empty()
                {
                    heritage_list.extend_from_slice(&retained.nodes);
                }
                let heritage_clauses = self.ec().factory.new_node_list(heritage_list);

                let updated_class = self
                    .ec
                    .borrow_mut()
                    .factory
                    .update_class_declaration(
                        cx.nodes,
                        input,
                        modifiers,
                        cx.nodes[input].name(),
                        type_parameters,
                        Some(heritage_clauses),
                        Some(members),
                    )
                    .unwrap_or(input);

                self.tracker.borrow_mut().pop_error_fallback_node();
                self.enclosing_declaration
                    .set(previous_enclosing_declaration);
                return Some(
                    self.ec
                        .borrow_mut()
                        .factory
                        .new_syntax_list(cx.nodes, &[statement, updated_class]),
                );
            }
        }

        let heritage_clauses = v.visit_nodes(
            cx,
            cx.nodes[input]
                .as_class_declaration()
                .class_like_base
                .heritage_clauses
                .clone(),
        );
        let result = self
            .ec
            .borrow_mut()
            .factory
            .update_class_declaration(
                cx.nodes,
                input,
                modifiers,
                cx.nodes[input].name(),
                type_parameters,
                heritage_clauses,
                Some(members),
            )
            .unwrap_or(input);
        self.tracker.borrow_mut().pop_error_fallback_node();
        self.enclosing_declaration
            .set(previous_enclosing_declaration);
        Some(result)
    }

    /// `(tx *DeclarationTransformer) visitThisPropertyAssignments`.
    fn visit_this_property_assignments<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let mut is_static = false;
        let this_container = ast::get_this_container(node, cx.nodes, false, false);
        let Some(this_target) = cx.nodes[this_container].parent else {
            return None; // thisContainer was source file, can't have expando-this
        };
        if ast::has_static_modifier(&cx.nodes[this_container])
            || ast::is_class_static_block_declaration(&cx.nodes[this_container])
        {
            is_static = true;
        }
        if Some(this_target) != self.enclosing_declaration.get() {
            return None; // stop searching within new `this` contexts
        }
        // `caseBlock:` — Go uses a labeled break for the early-exits below.
        'case_block: {
            if ast::get_assignment_declaration_kind(node, cx.nodes)
                == ast::JsDeclarationKind::ThisProperty
            {
                let mut name = ast::get_name_of_declaration(Some(node), cx.nodes);
                let base = self.symbols.and_then(|symbols| {
                    self.resolver
                        .borrow_mut()
                        .get_referenced_member_value_declaration(node, cx.nodes, symbols)
                });
                let key = get_this_property_assignment_key(name, node, is_static, cx.nodes);
                if base.is_none() || self.seen_properties.borrow().contains(&key) {
                    break 'case_block;
                }
                self.seen_properties.borrow_mut().insert(key);

                // problem: this prop might be overriding a prop from a base type. The checker has special bails for override compat comparisons for binary expression properties,
                // but what we transform to won't - so we either need to match the base type (for example, if it's a getter/setter) or emit nothing
                // See `checkKindsOfPropertyMemberOverrides` in the checker for what we're trying to satisfy here
                let heritage = cx.nodes[this_target]
                    .class_like_data()
                    .and_then(|d| d.heritage_clauses.clone());
                if heritage.as_ref().is_some_and(|h| !h.nodes.is_empty())
                    && !is_class_extending_null(this_target, cx.nodes)
                {
                    // there is a base type any assignments might be "from"
                    self.tracker
                        .borrow_mut()
                        .report_inference_fallback(this_target, cx.nodes); // Add an isolated declarations error on this class - we can't know how to transform this prop into an assignment without referring to type information
                    if self
                        .resolver
                        .borrow()
                        .is_this_property_assignment_declaration_redundant(node, cx.nodes)
                    {
                        break 'case_block; // skip assignments whose member is already provided by an `extends` base type (an inherited accessor/method, or an identical inherited property)
                        // TODO: If the property has an explicit `@type` annotation, we should probably emit it (maybe with an `override` modifier) instead of skipping it
                    }
                }

                let mods = if is_static {
                    let mut ec = self.ec.borrow_mut();
                    let m = ec.factory.new_token(cx.nodes, Kind::StaticKeyword);
                    Some(ec.factory.new_modifier_list(cx.nodes, vec![m]))
                } else {
                    None
                };
                if ast::has_dynamic_name(node, cx.nodes) {
                    let name_id = match name {
                        Some(n) => n,
                        None => break 'case_block,
                    };
                    if !is_simple_inlineable_expression(&cx.nodes[name_id]) {
                        break 'case_block; // Member either becomes an index signature or is a reassignment
                    }
                    self.check_name(node, cx.nodes);
                    name = Some(
                        self.ec
                            .borrow_mut()
                            .factory
                            .new_computed_property_name(cx.nodes, name),
                    ); // Convert `this[foo] = expr` to `[foo]: Type`
                }
                if let Some(n) = name {
                    if ast::get_text_of_property_name(n, cx.nodes) == "constructor" {
                        break 'case_block; // `constructor` is a builtin class member, not allowed to redeclare it
                    }
                }
                if name.is_some_and(|n| {
                    ast::is_identifier(&cx.nodes[n])
                        && !scanner::utilities::is_identifier_text(
                            &cx.nodes[n].text(cx.nodes),
                            LanguageVariant::Standard,
                        )
                }) {
                    name = Some(
                        self.ec
                            .borrow_mut()
                            .factory
                            .new_string_literal_from_node(cx.nodes, name.unwrap()),
                    );
                }
                let type_ = self.ensure_type(node, false, cx);
                let prop = self
                    .ec
                    .borrow_mut()
                    .factory
                    .new_property_declaration(cx.nodes, mods, name, None, type_, None);
                if cx.nodes[node]
                    .parent
                    .is_some_and(|p| ast::is_expression_statement(&cx.nodes[p]))
                {
                    self.preserve_js_doc(prop, cx.nodes[node].parent.unwrap(), cx.nodes);
                }
                self.this_property_assignments_collected
                    .borrow_mut()
                    .push(prop);
            }
        }
        v.visit_each_child(cx, node).or(Some(node))
    }

    /// `(tx *DeclarationTransformer) collectThisPropertyAssignments` — finds
    /// `this.x = expr` assignments in constructors, methods, and static
    /// blocks of JS classes and synthesizes PropertyDeclaration nodes for
    /// each unique property name.
    fn collect_this_property_assignments<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        class_node: NodeId,
    ) -> Vec<NodeId> {
        let members = cx.nodes[class_node]
            .class_like_data()
            .map(|d| d.members.clone())
            .flatten()
            .unwrap_or_default();
        // Pre-populate seen with existing direct member nodes to avoid duplicates
        let mut seen: HashSet<ThisPropertyAssignmentKey> = HashSet::new();
        for &member in members.nodes.iter() {
            if let Some(name) = cx.nodes[member].name() {
                let is_static = ast::is_static(&cx.nodes[member]);
                seen.insert(get_this_property_assignment_key(
                    Some(name),
                    member,
                    is_static,
                    cx.nodes,
                ));
            }
        }
        *self.seen_properties.borrow_mut() = seen;
        self.this_property_assignments_collected
            .borrow_mut()
            .clear();

        {
            let visitor = self.this_property_visitor.borrow();
            let visitor = visitor.as_ref().expect("thisPropertyVisitor");
            for &n in members.nodes.iter() {
                visitor.visit_each_child(cx, n);
            }
        }

        let collected = self.this_property_assignments_collected.borrow().clone();
        self.seen_properties.borrow_mut().clear();
        collected
    }

    /// `(tx *DeclarationTransformer) walkBindingPattern`.
    fn walk_binding_pattern(
        &self,
        pattern: NodeId,
        param: NodeId,
        cx: &mut VisitorCx<'_, '_>,
    ) -> Vec<NodeId> {
        let mut elems: Vec<NodeId> = Vec::new();
        let elements: Vec<NodeId> = cx.nodes[pattern]
            .elements()
            .map(|e| e.to_vec())
            .unwrap_or_default();
        for &elem in elements.iter() {
            if ast::is_omitted_expression(&cx.nodes[elem]) {
                continue;
            }
            let name = cx.nodes[elem].name();
            if name.is_some_and(|n| ast::is_binding_pattern(&cx.nodes[n])) {
                elems.extend(self.walk_binding_pattern(name.unwrap(), param, cx));
                continue;
            }
            let modifiers = self.ensure_modifiers(param, cx);
            let type_node = self.ensure_type(elem, false, cx);
            elems.push(self.ec.borrow_mut().factory.new_property_declaration(
                cx.nodes, modifiers, name, None, /*questionOrExclamationToken*/
                type_node, None, /*initializer*/
            ));
        }
        elems
    }

    /// `(tx *DeclarationTransformer) transformVariableStatement`.
    fn transform_variable_statement<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> Option<NodeId> {
        let declaration_list = cx.nodes[input].as_variable_statement().declaration_list;
        let input_nodes = declaration_list
            .map(|l| {
                cx.nodes[l]
                    .as_variable_declaration_list()
                    .declarations
                    .clone()
            })
            .flatten()
            .unwrap_or_default();
        let mut visible = false;
        for &decl in input_nodes.nodes.iter() {
            visible = get_binding_name_visible(&*self.resolver.borrow(), decl, cx.nodes);
            if visible {
                break;
            }
        }
        if !visible {
            return None;
        }

        let mut input_nodes_vec: Vec<NodeId> = input_nodes.nodes.to_vec();
        let mut extra_imports: Vec<NodeId> = Vec::new();
        let is_commonjs = self.shared.borrow().current_source_file.is_some_and(|f| {
            cx.nodes[f]
                .as_source_file()
                .common_js_module_indicator
                .is_some()
        });
        if is_commonjs {
            let mut normal_declarations: Vec<NodeId> = Vec::new();
            let mut imports: Vec<NodeId> = Vec::new();
            for n in input_nodes_vec {
                if ast::is_variable_declaration_initialized_to_require(n, cx.nodes) {
                    imports.push(n);
                } else {
                    normal_declarations.push(n);
                }
            }
            input_nodes_vec = normal_declarations;
            extra_imports = v.visit_slice(cx, &imports).unwrap_or(imports);
        }

        let nodes = v
            .visit_slice(cx, &input_nodes_vec)
            .unwrap_or_else(|| input_nodes_vec.clone());
        if nodes.is_empty() {
            if !extra_imports.is_empty() {
                return Some(
                    self.ec
                        .borrow_mut()
                        .factory
                        .new_syntax_list(cx.nodes, &extra_imports),
                );
            }
            return None;
        }
        let node_list = self.ec().factory.new_node_list(nodes);

        let modifiers = self.ensure_modifiers(input, cx);

        let decl_list = if ast::is_var_using(declaration_list.unwrap_or(input), cx.nodes)
            || ast::is_var_await_using(declaration_list.unwrap_or(input), cx.nodes)
        {
            let decl_list = self.ec.borrow_mut().factory.new_variable_declaration_list(
                cx.nodes,
                Some(node_list),
                NodeFlags::CONST,
            );
            let decl_list_source = declaration_list.unwrap_or(input);
            self.ec().set_original(decl_list, decl_list_source);
            self.ec()
                .set_comment_range(decl_list, cx.nodes[decl_list_source].loc);
            cx.nodes[decl_list].loc = cx.nodes[decl_list_source].loc;
            decl_list
        } else {
            self.ec
                .borrow_mut()
                .factory
                .update_variable_declaration_list(
                    cx.nodes,
                    declaration_list.unwrap_or(input),
                    Some(node_list),
                    declaration_list
                        .map(|l| cx.nodes[l].flags)
                        .unwrap_or_default(),
                )
                .unwrap_or(input)
        };
        let res = self
            .ec
            .borrow_mut()
            .factory
            .update_variable_statement(cx.nodes, input, modifiers, Some(decl_list))
            .unwrap_or(input);
        if !extra_imports.is_empty() {
            extra_imports.push(res);
            return Some(
                self.ec
                    .borrow_mut()
                    .factory
                    .new_syntax_list(cx.nodes, &extra_imports),
            );
        }
        Some(res)
    }

    /// `(tx *DeclarationTransformer) transformEnumDeclaration`.
    fn transform_enum_declaration(&self, cx: &mut VisitorCx<'_, '_>, input: NodeId) -> NodeId {
        let (name, members) = {
            let d = cx.nodes[input].as_enum_declaration();
            (d.name, d.members.clone())
        };
        let member_vec: Vec<NodeId> = members.map(|m| m.nodes.to_vec()).unwrap_or_default();
        let mut new_members: Vec<NodeId> = Vec::new();
        for &m in member_vec.iter() {
            if self.should_strip_internal(Some(m), cx.nodes) {
                continue;
            }

            // Rewrite enum values to their constants, if available
            let enum_value = self.resolver.borrow().get_enum_member_value(m, cx.nodes);

            if self.shared.borrow().isolated_declarations
                && cx.nodes[m].initializer().is_some()
                && enum_value.has_external_references
                // This will be its own compiler error instead, so don't report.
                && !cx.nodes[m]
                    .name()
                    .is_some_and(|n| ast::is_computed_property_name(&cx.nodes[n]))
            {
                self.shared.borrow_mut().add_diagnostic(create_diagnostic_for_node(
                    cx.nodes,
                    Some(m),
                    &tsc_diagnostics::Enum_member_initializers_must_be_computable_without_references_to_external_symbols_with_isolatedDeclarations,
                    &[] as &[String],
                ));
            }

            let new_initializer: Option<NodeId> = match enum_value.value {
                Some(tsc_evaluator::Value::Number(value)) => {
                    let mut ec = self.ec.borrow_mut();
                    if value.is_inf() {
                        if value > 0.0 {
                            Some(ec.factory.new_identifier(cx.nodes, "Infinity"))
                        } else {
                            let inner = ec.factory.new_identifier(cx.nodes, "Infinity");
                            Some(ec.factory.new_prefix_unary_expression(
                                cx.nodes,
                                Kind::MinusToken,
                                Some(inner),
                            ))
                        }
                    } else if value.is_nan() {
                        Some(ec.factory.new_identifier(cx.nodes, "NaN"))
                    } else if value >= 0.0 {
                        Some(ec.factory.new_numeric_literal(
                            cx.nodes,
                            &value.to_string(),
                            TokenFlags::NONE,
                        ))
                    } else {
                        let lit = ec.factory.new_numeric_literal(
                            cx.nodes,
                            &(-value).to_string(),
                            TokenFlags::NONE,
                        );
                        Some(ec.factory.new_prefix_unary_expression(
                            cx.nodes,
                            Kind::MinusToken,
                            Some(lit),
                        ))
                    }
                }
                Some(tsc_evaluator::Value::String(value)) => {
                    Some(self.ec.borrow_mut().factory.new_string_literal(
                        cx.nodes,
                        &value,
                        TokenFlags::NONE,
                    ))
                }
                _ => None,
            };
            let result = self
                .ec
                .borrow_mut()
                .factory
                .update_enum_member(cx.nodes, m, cx.nodes[m].name(), new_initializer)
                .unwrap_or(m);
            self.preserve_js_doc(result, m, cx.nodes);
            new_members.push(result);
        }
        let member_list = self.ec().factory.new_node_list(new_members);
        let modifiers = self.ensure_modifiers(input, cx);
        self.ec
            .borrow_mut()
            .factory
            .update_enum_declaration(cx.nodes, input, modifiers, name, Some(member_list))
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) ensureModifiers`.
    fn ensure_modifiers(
        &self,
        node: NodeId,
        cx: &mut VisitorCx<'_, '_>,
    ) -> Option<tsc_ast::ModifierList> {
        let parse_node = self.ec().parse_node(cx.nodes, node).unwrap_or(node);
        let current_flags =
            ast::get_combined_modifier_flags(parse_node, cx.nodes) & ModifierFlags::ALL;
        let new_flags = self.ensure_modifier_flags(node, cx.nodes);
        if current_flags == new_flags {
            // Elide decorators
            let mods = cx.nodes[node].modifiers();
            let Some(mods) = mods else {
                return None;
            };
            if can_reuse_modifier_nodes(&mods.nodes, cx.nodes) {
                let retained: Vec<NodeId> =
                    core::filter(mods.nodes.as_ref(), |n| ast::is_modifier(&cx.nodes[*n]))
                        .into_owned();
                return Some(self.ec().factory.new_modifier_list(cx.nodes, retained));
            }
        }
        let result = {
            let mut ec = self.ec.borrow_mut();
            ast::create_modifiers_from_modifier_flags(new_flags, &mut |kind| {
                ec.factory.new_token(cx.nodes, kind)
            })
        };
        if result.is_empty() {
            return None;
        }
        Some(self.ec().factory.new_modifier_list(cx.nodes, result))
    }

    /// `(tx *DeclarationTransformer) ensureModifierFlags`.
    fn ensure_modifier_flags(&self, node: NodeId, nodes: &[Node]) -> ModifierFlags {
        let mut mask = ModifierFlags(
            ModifierFlags::ALL.0
                ^ (ModifierFlags::PUBLIC | ModifierFlags::ASYNC | ModifierFlags::OVERRIDE).0,
        ); // No async and override modifiers in declaration files
        let mut additions = ModifierFlags::NONE;
        if self.needs_declare.get() && !is_always_type(&nodes[node]) {
            additions = ModifierFlags::AMBIENT;
        }
        let parent_is_file = nodes[node]
            .parent
            .is_some_and(|p| nodes[p].kind == Kind::SourceFile);
        if !parent_is_file {
            mask = ModifierFlags(mask.0 ^ ModifierFlags::AMBIENT.0);
            additions = ModifierFlags::NONE;
        }
        if ast::is_implicitly_exported_js_doc_declaration(&nodes[node], nodes) {
            additions = additions | ModifierFlags::EXPORT;
        }
        mask_modifier_flags(node, mask, additions, nodes)
    }

    /// `(tx *DeclarationTransformer) ensureTypeParams`.
    fn ensure_type_params(
        &self,
        node: NodeId,
        params: Option<NodeList>,
        cx: &mut VisitorCx<'_, '_>,
    ) -> Option<NodeList> {
        if !self
            .resolver
            .borrow()
            .get_effective_declaration_flags(
                self.ec().parse_node(cx.nodes, node).unwrap_or(node),
                ModifierFlags::PRIVATE,
                cx.nodes,
            )
            .is_empty()
        {
            return None;
        }
        let mut type_parameters = self
            .root_visitor
            .borrow()
            .as_ref()
            .expect("rootVisitor")
            .visit_nodes(cx, params);
        if type_parameters.is_some() {
            return type_parameters;
        }
        let old_error_name_node = self.shared.borrow().error_name_node;
        self.shared.borrow_mut().error_name_node = cx.nodes[node].name();
        // PORT: same swap-only-when-canProduce rule as `ensureType`.
        let mut old_diag: Option<GetSymbolAccessibilityDiagnostic> = None;
        let diag_swapped = !self.suppress_new_diagnostic_contexts.get()
            && can_produce_diagnostics(&cx.nodes[node]);
        if diag_swapped {
            let mut shared = self.shared.borrow_mut();
            old_diag = std::mem::replace(
                &mut shared.get_symbol_accessibility_diagnostic,
                Some(create_get_symbol_accessibility_diagnostic_for_node(
                    node, cx.nodes,
                )),
            );
        }

        let full_signature = cx.nodes[node]
            .function_like_data()
            .and_then(|d| d.full_signature);
        if full_signature.is_some() {
            let nodes_result = {
                self.resolver
                    .borrow()
                    .create_type_parameters_of_signature_declaration(
                        node,
                        self.enclosing_declaration.get(),
                        DECLARATION_EMIT_NODE_BUILDER_FLAGS,
                        DECLARATION_EMIT_INTERNAL_NODE_BUILDER_FLAGS,
                        self.tracker.clone(),
                        cx.nodes,
                    )
            };
            type_parameters = Some(NodeList {
                loc: cx.nodes[node].loc,
                nodes: nodes_result.into(),
                is_missing: false,
            });
        }

        self.shared.borrow_mut().error_name_node = old_error_name_node;
        if diag_swapped {
            self.shared.borrow_mut().get_symbol_accessibility_diagnostic = old_diag;
        }
        type_parameters
    }

    /// `(tx *DeclarationTransformer) updateParamList`.
    fn update_param_list(
        &self,
        node: NodeId,
        params: Option<NodeList>,
        cx: &mut VisitorCx<'_, '_>,
    ) -> NodeList {
        let param_vec: Vec<NodeId> = params.map(|p| p.nodes.to_vec()).unwrap_or_default();
        if !self
            .resolver
            .borrow()
            .get_effective_declaration_flags(
                self.ec().parse_node(cx.nodes, node).unwrap_or(node),
                ModifierFlags::PRIVATE,
                cx.nodes,
            )
            .is_empty()
            || param_vec.is_empty()
        {
            return self.ec().factory.new_node_list(Vec::new());
        }
        let results: Vec<NodeId> = param_vec
            .iter()
            .map(|&p| self.ensure_parameter(p, cx))
            .collect();
        self.ec().factory.new_node_list(results)
    }

    /// `(tx *DeclarationTransformer) ensureParameter`.
    fn ensure_parameter(&self, p: NodeId, cx: &mut VisitorCx<'_, '_>) -> NodeId {
        // PORT: when `suppressNewDiagnosticContexts` is set, Go neither saves
        // nor replaces the selector — so the take/restore below is skipped
        // entirely, leaving the outer selector in place.
        let old_diag = if !self.suppress_new_diagnostic_contexts.get() {
            let mut shared = self.shared.borrow_mut();
            std::mem::replace(
                &mut shared.get_symbol_accessibility_diagnostic,
                Some(create_get_symbol_accessibility_diagnostic_for_node(
                    p, cx.nodes,
                )),
            )
        } else {
            None
        };
        let mut question_token: Option<NodeId> = None;
        if self.resolver.borrow().is_optional_parameter(p, cx.nodes) {
            let existing = cx.nodes[p].question_token(cx.nodes);
            if let Some(existing) = existing {
                question_token = Some(existing);
            } else {
                question_token = Some(
                    self.ec
                        .borrow_mut()
                        .factory
                        .new_token(cx.nodes, Kind::QuestionToken),
                );
            }
        }
        let (dot_dot_dot_token, name) = {
            let d = cx.nodes[p].as_parameter_declaration();
            (d.dot_dot_dot_token, d.name)
        };
        let result = {
            let name = self
                .binding_name_visitor
                .borrow()
                .as_ref()
                .expect("bindingNameVisitor")
                .visit_node(cx, name);
            let type_node = self.ensure_type(p, true, cx);
            let initializer = self.ensure_no_initializer(p, cx);
            self.ec
                .borrow_mut()
                .factory
                .update_parameter_declaration(
                    cx.nodes,
                    p,
                    None,
                    dot_dot_dot_token,
                    name,
                    question_token,
                    type_node,
                    initializer,
                )
                .unwrap_or(p)
        };
        if !self.suppress_new_diagnostic_contexts.get() {
            self.shared.borrow_mut().get_symbol_accessibility_diagnostic = old_diag;
        }
        result
    }

    /// `(tx *DeclarationTransformer) ensureNoInitializer`.
    fn ensure_no_initializer(&self, node: NodeId, cx: &mut VisitorCx<'_, '_>) -> Option<NodeId> {
        if self.should_print_with_initializer(node, cx.nodes) {
            let initializer = cx.nodes[node].initializer();
            let unwrapped_initializer =
                initializer.map(|i| unwrap_parenthesized_expression(i, cx.nodes));
            if !unwrapped_initializer
                .is_some_and(|i| ast::is_primitive_literal_value(&cx.nodes[i], true, cx.nodes))
            {
                self.tracker
                    .borrow_mut()
                    .report_inference_fallback(node, cx.nodes);
            }
            let parse_node = self.ec().parse_node(cx.nodes, node).unwrap_or(node);
            return self.resolver.borrow().create_literal_const_value(
                parse_node,
                self.tracker.clone(),
                cx.nodes,
            );
        }
        None
    }

    /// `(tx *DeclarationTransformer) visitBindingName`.
    fn visit_binding_name<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        match cx.nodes[node].kind {
            Kind::Identifier | Kind::OmittedExpression => Some(node),
            Kind::ArrayBindingPattern | Kind::ObjectBindingPattern => {
                v.visit_each_child(cx, node).or(Some(node))
            }
            Kind::BindingElement => {
                let (dot_dot_dot_token, property_name, name) = {
                    let d = cx.nodes[node].as_binding_element();
                    (d.dot_dot_dot_token, d.property_name, d.name)
                };
                if property_name.is_some_and(|p| {
                    ast::is_computed_property_name(&cx.nodes[p])
                        && cx.nodes[p]
                            .expression()
                            .is_some_and(|e| ast::is_entity_name_expression(&cx.nodes[e], cx.nodes))
                }) {
                    let expr = property_name.and_then(|p| cx.nodes[p].expression());
                    self.check_entity_name_visibility(
                        expr,
                        self.enclosing_declaration.get(),
                        cx.nodes,
                    );
                }
                let name = self
                    .binding_name_visitor
                    .borrow()
                    .as_ref()
                    .expect("bindingNameVisitor")
                    .visit_node(cx, name);
                self.ec
                    .borrow_mut()
                    .factory
                    .update_binding_element(
                        cx.nodes,
                        node,
                        dot_dot_dot_token,
                        property_name,
                        name,
                        None, /*initializer*/
                    )
                    .or(Some(node))
            }
            _ => Some(node),
        }
    }
}

/// `isClassExtendingNull(node)`.
fn is_class_extending_null(node: NodeId, nodes: &[Node]) -> bool {
    let Some(extends_clause) = ast::get_heritage_clause(&nodes[node], Kind::ExtendsKeyword, nodes)
    else {
        return false;
    };
    let types = nodes[extends_clause].as_heritage_clause().types.clone();
    let Some(types) = types else {
        return false;
    };
    if types.nodes.len() != 1 {
        return false;
    }
    let expr = nodes[types.nodes[0]]
        .as_expression_with_type_arguments()
        .expression;
    expr.is_some_and(|e| nodes[e].kind == Kind::NullKeyword)
}

impl<'a> DeclarationTransformerState<'a> {
    /// `(tx *DeclarationTransformer) transformImportEqualsDeclaration`.
    fn transform_import_equals_declaration(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        decl: NodeId,
    ) -> Option<NodeId> {
        if !self
            .resolver
            .borrow()
            .is_declaration_visible(decl, cx.nodes)
        {
            return None;
        }
        let (modifiers, is_type_only, name, module_reference) = {
            let d = cx.nodes[decl].as_import_equals_declaration();
            (
                d.modifiers_base.modifiers.clone(),
                d.is_type_only,
                d.name,
                d.module_reference,
            )
        };
        if module_reference.is_some_and(|m| cx.nodes[m].kind == Kind::ExternalModuleReference) {
            // Rewrite external module names if necessary
            let specifier = ast::get_external_module_import_equals_declaration_expression(
                &cx.nodes[decl],
                cx.nodes,
            );
            let updated = {
                let mut ec = self.ec.borrow_mut();
                ec.factory
                    .update_external_module_reference(
                        cx.nodes,
                        module_reference.unwrap(),
                        self.rewrite_module_specifier(decl, specifier, cx.nodes),
                    )
                    .unwrap_or(module_reference.unwrap())
            };
            return self
                .ec
                .borrow_mut()
                .factory
                .update_import_equals_declaration(
                    cx.nodes,
                    decl,
                    modifiers,
                    is_type_only,
                    name,
                    Some(updated),
                )
                .or(Some(decl));
        }
        let old_diag = {
            let mut shared = self.shared.borrow_mut();
            std::mem::replace(
                &mut shared.get_symbol_accessibility_diagnostic,
                Some(create_get_symbol_accessibility_diagnostic_for_node(
                    decl, cx.nodes,
                )),
            )
        };
        self.check_entity_name_visibility(
            module_reference,
            self.enclosing_declaration.get(),
            cx.nodes,
        );
        self.shared.borrow_mut().get_symbol_accessibility_diagnostic = old_diag;
        Some(decl)
    }

    /// `(tx *DeclarationTransformer) transformImportDeclaration`.
    fn transform_import_declaration(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        decl: NodeId,
    ) -> Option<NodeId> {
        let (modifiers, import_clause, module_specifier, attributes) = {
            let d = cx.nodes[decl].as_import_declaration();
            (
                d.modifiers_base.modifiers.clone(),
                d.import_clause,
                d.module_specifier,
                d.attributes,
            )
        };
        let Some(import_clause) = import_clause else {
            // import "mod" - possibly needed for side effects? (global interface patches, module augmentations, etc)
            return self
                .ec
                .borrow_mut()
                .factory
                .update_import_declaration(
                    cx.nodes,
                    decl,
                    modifiers,
                    None,
                    self.rewrite_module_specifier(decl, module_specifier, cx.nodes),
                    attributes,
                )
                .or(Some(decl));
        };
        let mut phase_modifier = cx.nodes[import_clause].as_import_clause().phase_modifier;
        if phase_modifier == Kind::DeferKeyword {
            phase_modifier = Kind::Unknown;
        }
        // The `importClause` visibility corresponds to the default's visibility.
        let mut visible_default_binding: Option<NodeId> = None;
        if cx.nodes[import_clause].name().is_some() {
            let vis = self
                .resolver
                .borrow()
                .is_declaration_visible(import_clause, cx.nodes);
            if vis {
                visible_default_binding = cx.nodes[import_clause].name();
            }
        }
        let named_bindings = cx.nodes[import_clause].as_import_clause().named_bindings;
        let Some(named_bindings) = named_bindings else {
            // No named bindings (either namespace or list), meaning the import is just default or should be elided
            if visible_default_binding.is_none() {
                return None;
            }
            let updated_clause = self
                .ec
                .borrow_mut()
                .factory
                .update_import_clause(
                    cx.nodes,
                    import_clause,
                    phase_modifier,
                    visible_default_binding,
                    /*namedBindings*/ None,
                )
                .unwrap_or(import_clause);
            return self
                .ec
                .borrow_mut()
                .factory
                .update_import_declaration(
                    cx.nodes,
                    decl,
                    modifiers,
                    Some(updated_clause),
                    self.rewrite_module_specifier(decl, module_specifier, cx.nodes),
                    attributes,
                )
                .or(Some(decl));
        };
        if cx.nodes[named_bindings].kind == Kind::NamespaceImport {
            // Namespace import (optionally with visible default)
            let retained_named_bindings = if self
                .resolver
                .borrow()
                .is_declaration_visible(named_bindings, cx.nodes)
            {
                Some(named_bindings)
            } else {
                None
            };
            if visible_default_binding.is_none() && retained_named_bindings.is_none() {
                return None;
            }
            let updated_clause = self
                .ec
                .borrow_mut()
                .factory
                .update_import_clause(
                    cx.nodes,
                    import_clause,
                    phase_modifier,
                    visible_default_binding,
                    retained_named_bindings,
                )
                .unwrap_or(import_clause);
            return self
                .ec
                .borrow_mut()
                .factory
                .update_import_declaration(
                    cx.nodes,
                    decl,
                    modifiers,
                    Some(updated_clause),
                    self.rewrite_module_specifier(decl, module_specifier, cx.nodes),
                    attributes,
                )
                .or(Some(decl));
        }
        // Named imports (optionally with visible default)
        let elements: Vec<NodeId> = cx.nodes[named_bindings]
            .elements()
            .map(|e| e.to_vec())
            .unwrap_or_default();
        let binding_list: Vec<NodeId> = core::filter(&elements, |b| {
            self.resolver.borrow().is_declaration_visible(*b, cx.nodes)
        })
        .into_owned();
        if !binding_list.is_empty() || visible_default_binding.is_some() {
            let named_imports = if !binding_list.is_empty() {
                let mut ec = self.ec.borrow_mut();
                let list = ec.factory.new_node_list(binding_list);
                Some(
                    ec.factory
                        .update_named_imports(cx.nodes, named_bindings, Some(list))
                        .unwrap_or(named_bindings),
                )
            } else {
                None
            };
            let updated_clause = self
                .ec
                .borrow_mut()
                .factory
                .update_import_clause(
                    cx.nodes,
                    import_clause,
                    phase_modifier,
                    visible_default_binding,
                    named_imports,
                )
                .unwrap_or(import_clause);
            return self
                .ec
                .borrow_mut()
                .factory
                .update_import_declaration(
                    cx.nodes,
                    decl,
                    modifiers,
                    Some(updated_clause),
                    self.rewrite_module_specifier(decl, module_specifier, cx.nodes),
                    attributes,
                )
                .or(Some(decl));
        }
        // Augmentation of export depends on import
        if self
            .resolver
            .borrow()
            .is_import_required_by_augmentation(decl, cx.nodes)
        {
            if self.shared.borrow().isolated_declarations {
                self.shared.borrow_mut().add_diagnostic(create_diagnostic_for_node(
                    cx.nodes,
                    Some(decl),
                    &tsc_diagnostics::Declaration_emit_for_this_file_requires_preserving_this_import_for_augmentations_This_is_not_supported_with_isolatedDeclarations,
                    &[] as &[String],
                ));
            }
            return self
                .ec
                .borrow_mut()
                .factory
                .update_import_declaration(
                    cx.nodes,
                    decl,
                    modifiers,
                    /*importClause*/ None,
                    self.rewrite_module_specifier(decl, module_specifier, cx.nodes),
                    attributes,
                )
                .or(Some(decl));
        }
        // Nothing visible
        None
    }

    /// `(tx *DeclarationTransformer) transformJSDocTypeExpression`.
    fn transform_js_doc_type_expression<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        v.visit_node(cx, cx.nodes[input].as_js_doc_type_expression().type_)
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformJSDocTypeLiteral`.
    fn transform_js_doc_type_literal<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let tags = cx.nodes[input]
            .as_js_doc_type_literal()
            .js_doc_property_tags
            .clone();
        let members = v
            .visit_slice(cx, &tags)
            .unwrap_or_else(|| tags.to_vec());
        let replacement = {
            let mut ec = self.ec.borrow_mut();
            let list = ec.factory.new_node_list(members);
            ec.factory.new_type_literal_node(cx.nodes, Some(list))
        };
        self.ec().set_original(replacement, input);
        replacement
    }

    /// `(tx *DeclarationTransformer) transformJSDocPropertyTag`.
    fn transform_js_doc_property_tag<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let (name, type_expression) = {
            let d = cx.nodes[input].as_js_doc_parameter_or_property_tag();
            (d.name, d.type_expression)
        };
        let name = v.visit_node(cx, name);
        let type_expression = v.visit_node(cx, type_expression);
        let replacement = self
            .ec
            .borrow_mut()
            .factory
            .new_property_signature_declaration(cx.nodes, None, name, None, type_expression, None);
        self.ec().set_original(replacement, input);
        replacement
    }

    /// `(tx *DeclarationTransformer) transformJSDocAllType`.
    fn transform_js_doc_all_type<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let replacement = self
            .ec
            .borrow_mut()
            .factory
            .new_keyword_type_node(cx.nodes, Kind::AnyKeyword);
        self.ec().set_original(replacement, input);
        replacement
    }

    /// `(tx *DeclarationTransformer) transformJSDocNullableType`.
    fn transform_js_doc_nullable_type<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let type_node = cx.nodes[input].as_js_doc_nullable_type().type_;
        let replacement = {
            let inner = v.visit_node(cx, type_node);
            let mut ec = self.ec.borrow_mut();
            let null_lit = ec
                .factory
                .new_keyword_expression(cx.nodes, Kind::NullKeyword);
            let lit_type = ec.factory.new_literal_type_node(cx.nodes, Some(null_lit));
            let list = ec
                .factory
                .new_node_list(vec![inner.unwrap_or(input), lit_type]);
            ec.factory.new_union_type_node(cx.nodes, Some(list))
        };
        self.ec().set_original(replacement, input);
        replacement
    }

    /// `(tx *DeclarationTransformer) transformJSDocNonNullableType`.
    fn transform_js_doc_non_nullable_type<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        v.visit_node(cx, cx.nodes[input].as_js_doc_non_nullable_type().type_)
            .unwrap_or(input)
    }

    /// `(tx *DeclarationTransformer) transformJSDocVariadicType`.
    fn transform_js_doc_variadic_type<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let type_node = cx.nodes[input].as_js_doc_variadic_type().type_;
        let element = v.visit_node(cx, type_node);
        let replacement = self
            .ec
            .borrow_mut()
            .factory
            .new_array_type_node(cx.nodes, element);
        self.ec().set_original(replacement, input);
        replacement
    }

    /// `(tx *DeclarationTransformer) transformJSDocOptionalType`.
    fn transform_js_doc_optional_type<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        input: NodeId,
    ) -> NodeId {
        let type_node = cx.nodes[input].as_js_doc_optional_type().type_;
        let replacement = {
            let inner = v.visit_node(cx, type_node);
            let mut ec = self.ec.borrow_mut();
            let undefined = ec
                .factory
                .new_keyword_type_node(cx.nodes, Kind::UndefinedKeyword);
            let list = ec
                .factory
                .new_node_list(vec![inner.unwrap_or(input), undefined]);
            ec.factory.new_union_type_node(cx.nodes, Some(list))
        };
        self.ec().set_original(replacement, input);
        replacement
    }

    /// `(tx *DeclarationTransformer) getNameExpressionPreferringIdentifier`.
    fn get_name_expression_preferring_identifier(
        &self,
        name_expr: Option<NodeId>,
        cx: &mut VisitorCx<'_, '_>,
    ) -> Option<NodeId> {
        let mut name_expr = name_expr?;
        if ast::is_numeric_literal(&cx.nodes[name_expr]) {
            // Numeric property names are string properties in JS; convert to string literal
            let text = cx.nodes[name_expr].text(cx.nodes).into_owned();
            name_expr =
                self.ec
                    .borrow_mut()
                    .factory
                    .new_string_literal(cx.nodes, &text, TokenFlags::NONE);
        }
        if ast::is_string_literal_like(&cx.nodes[name_expr])
            && scanner::utilities::is_identifier_text(
                &cx.nodes[name_expr].text(cx.nodes),
                LanguageVariant::Standard,
            )
        {
            let text = cx.nodes[name_expr].text(cx.nodes).into_owned();
            let result = self.ec.borrow_mut().factory.new_identifier(cx.nodes, &text); // prefer non-string literal names where possible
            let kw_kind =
                scanner::utilities::identifier_to_keyword_kind(cx.nodes[result].as_identifier());
            // keep keywords as strings, except `default`, which has special reformulations in the transformer
            if kw_kind == Kind::Unknown || kw_kind == Kind::DefaultKeyword {
                // fake this into a parse tree node so the reference resolver resolves the node via `resolveName`
                cx.nodes[result].parent = cx.nodes[name_expr].parent;
                cx.nodes[result].flags =
                    NodeFlags(cx.nodes[result].flags.0 & !NodeFlags::SYNTHESIZED.0);
                // intentionally leave Loc unset so the string isn't used as the text source of the identifier
                return Some(result);
            }
        }
        Some(name_expr)
    }

    /// `(tx *DeclarationTransformer) stripDeclareModifiers`.
    fn strip_declare_modifiers(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        let mods = cx.nodes[node].modifiers();
        if let Some(mods) = mods {
            let flags = cx.nodes[node].modifier_flags();
            if flags.intersects(ModifierFlags::AMBIENT) {
                let filtered: Vec<NodeId> = core::filter(mods.nodes.as_ref(), |m| {
                    cx.nodes[*m].kind != Kind::DeclareKeyword
                })
                .into_owned();
                let list = self.ec().factory.new_modifier_list(cx.nodes, filtered);
                cx.nodes[node].set_modifiers(Some(list));
            }
        }
        node // no need to recur into children, only strip at top-level
    }

    /// `(tx *DeclarationTransformer) visitCJSExportAssignments`.
    fn visit_cjs_export_assignments<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        expression: NodeId,
    ) -> Option<NodeId> {
        let (_can, _cleanup) = self.setup_diagnostic_context(expression, cx.nodes);
        if ast::get_assignment_declaration_kind(expression, cx.nodes)
            == ast::JsDeclarationKind::ModuleExports
            && self.shared.borrow().current_source_file.is_some_and(|f| {
                cx.nodes[f]
                    .as_source_file()
                    .common_js_module_indicator
                    .is_some()
            })
        {
            let right = cx.nodes[expression].as_binary_expression().right;
            let parent = cx.nodes[expression].parent.unwrap_or(expression);
            let result = self.transform_export_assignment(
                self.root_visitor.borrow().as_ref().expect("rootVisitor"),
                cx,
                parent,
                expression,
                right,
                true, /*isExportEquals*/
            );
            self.cjs_export_assignment.set(Some(result));
            self.result_has_scope_marker.set(true);
            self.result_has_external_module_indicator.set(true);
        }
        v.visit_each_child(cx, expression).or(Some(expression)) // recur through the whole tree, looking for module.exports=
    }

    /// `(tx *DeclarationTransformer) visitNestedExpression`.
    fn visit_nested_expression<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        expression: NodeId,
    ) -> Option<NodeId> {
        let (_can, _cleanup) = self.setup_diagnostic_context(expression, cx.nodes);
        match ast::get_assignment_declaration_kind(expression, cx.nodes) {
            ast::JsDeclarationKind::Property => {
                self.transform_expando_assignment(cx, expression);
            }
            ast::JsDeclarationKind::ExportsProperty => {
                if self.shared.borrow().current_source_file.is_some_and(|f| {
                    cx.nodes[f]
                        .as_source_file()
                        .common_js_module_indicator
                        .is_some()
                }) {
                    let left = cx.nodes[expression].as_binary_expression().left;
                    let name = left.and_then(|l| {
                        ast::get_element_or_property_access_name(&cx.nodes[l], cx.nodes)
                    });
                    let name = self.get_name_expression_preferring_identifier(name, cx);
                    let result = self.transform_commonjs_export(
                        self.root_visitor.borrow().as_ref().expect("rootVisitor"),
                        cx,
                        expression,
                        name,
                    );
                    if let Some(result) = result {
                        self.cjs_export_members.borrow_mut().push(result);
                    }
                }
            }
            ast::JsDeclarationKind::ObjectDefinePropertyExports => {
                if self.shared.borrow().current_source_file.is_some_and(|f| {
                    cx.nodes[f]
                        .as_source_file()
                        .common_js_module_indicator
                        .is_some()
                }) {
                    let name = cx.nodes[expression]
                        .arguments()
                        .and_then(|a| a.get(1).copied());
                    let name = self.get_name_expression_preferring_identifier(name, cx);
                    let result = self.transform_commonjs_export(
                        self.root_visitor.borrow().as_ref().expect("rootVisitor"),
                        cx,
                        expression,
                        name,
                    );
                    if let Some(result) = result {
                        self.cjs_export_members.borrow_mut().push(result);
                    }
                }
            }
            _ => {}
        }
        v.visit_each_child(cx, expression).or(Some(expression)) // recur through the whole tree, looking for special assignments
    }

    /// `(tx *DeclarationTransformer) transformExpandoAssignment`.
    fn transform_expando_assignment(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) {
        let left = cx.nodes[node].as_binary_expression().left;

        let Some(symbol) = cx.nodes[node].symbol() else {
            return;
        };
        let symbol_has_assignment_flag = self.symbols.is_some_and(|symbols| {
            symbols.borrow()[symbol.index()]
                .flags
                .intersects(SymbolFlags::ASSIGNMENT)
        });
        if !symbol_has_assignment_flag {
            return;
        }

        let Some(ns) = left.map(|l| ast::get_leftmost_access_expression(l, cx.nodes)) else {
            return;
        };
        if cx.nodes[ns].kind != Kind::Identifier {
            return;
        }

        let Some(symbols) = self.symbols else {
            return;
        };
        let declaration = self.resolver.borrow_mut().get_referenced_value_declaration(
            ns, cx.nodes, symbols,
        );
        let Some(declaration) = declaration else {
            return;
        };

        if self.should_strip_internal(Some(declaration), cx.nodes) {
            return;
        }

        if ast::is_variable_declaration(&cx.nodes[declaration])
            && cx.nodes[declaration].type_().is_some()
        {
            return;
        }

        if ast::is_function_declaration(&cx.nodes[declaration])
            && cx.nodes[declaration]
                .function_like_data()
                .and_then(|d| d.full_signature)
                .is_some()
        {
            return;
        }

        if ast::is_variable_declaration(&cx.nodes[declaration])
            && !ast::is_function_like(cx.nodes[declaration].initializer(), cx.nodes)
        {
            return; // We're going to add a type, no need to dupe members with a namespace
        }

        let Some(host) = cx.nodes[declaration].symbol() else {
            return;
        };

        let name_text = cx.nodes[ns].text(cx.nodes).into_owned();
        let name = self
            .ec
            .borrow_mut()
            .factory
            .new_identifier(cx.nodes, &name_text);
        let property = left
            .map(|l| self.try_get_property_name(l, cx.nodes))
            .unwrap_or_default();
        if property.is_empty()
            || !scanner::utilities::is_identifier_text(&property, LanguageVariant::Standard)
        {
            return;
        }

        let host_id = self.get_expando_host_id(declaration, cx.nodes);

        if ast::is_declaration(&cx.nodes[declaration])
            && is_declaration_and_not_visible(
                &self.ec(),
                &*self.resolver.borrow(),
                declaration,
                cx.nodes,
            )
        {
            // The host isn't visible (yet) - printing the type of a visible declaration may still
            // late-mark it as visible (e.g. an exported variable whose type prints as `typeof host`),
            // so defer the assignment to be processed if and when that happens.
            self.deferred_expando_assignments
                .borrow_mut()
                .entry(host_id)
                .or_default()
                .push(node);
            return;
        }

        if ast::is_function_declaration(&cx.nodes[declaration])
            && !should_emit_function_properties(declaration, cx.nodes, &symbols.borrow())
        {
            return;
        }

        self.transform_expando_host(name, declaration, cx);

        let export_name = self
            .ec
            .borrow_mut()
            .factory
            .new_identifier(cx.nodes, &property);
        let mut local_name = self.try_get_name_of_assigned_expression(node, cx);
        if local_name.is_none()
            && !self.resolver.borrow().is_name_resolvable(
                self.enclosing_declaration.get(),
                &property,
                cx.nodes,
            )
            && !ast::is_non_contextual_keyword(scanner::scanner::string_to_token(
                &cx.nodes[export_name].text(cx.nodes),
            ))
        {
            // use exportName as localName if there won't be any conflicts or keyword issues
            local_name = Some(export_name);
        }
        if local_name.is_none()
            || ast::is_non_contextual_keyword(scanner::scanner::string_to_token(
                &cx.nodes[local_name.unwrap()].text(cx.nodes),
            ))
        {
            // fallback to a generated name if the localName doesn't exist or is a keyword
            local_name = Some(
                self.ec
                    .borrow_mut()
                    .factory
                    .new_generated_name_for_node(cx.nodes, node),
            );
        }
        let local_name = local_name.unwrap();

        let (_can, _cleanup) = self.setup_diagnostic_context(node, cx.nodes);

        let preexisting_expando_has_export = core::some(
            self.expando_members
                .borrow()
                .get(&host_id)
                .map(|m| m.as_slice())
                .unwrap_or(&[]),
            |d| ast::is_export_declaration(&cx.nodes[*d]),
        );

        let right = cx.nodes[node].as_binary_expression().right;
        if right.is_some_and(|r| ast::is_identifier(&cx.nodes[r])) {
            if !preexisting_expando_has_export {
                self.add_export_modifier_to_expando_members(host_id, cx);
            }
            // alias-like, emit an `export {name}` or `export {name as alias}`
            let result =
                self.transform_binary_expression_to_export_declaration(cx, node, Some(export_name));
            self.expando_members
                .borrow_mut()
                .entry(host_id)
                .or_default()
                .push(result);
            return;
        }

        let var_modifiers = if preexisting_expando_has_export {
            let mut ec = self.ec.borrow_mut();
            let mods =
                ast::create_modifiers_from_modifier_flags(ModifierFlags::EXPORT, &mut |kind| {
                    ec.factory.new_token(cx.nodes, kind)
                });
            Some(ec.factory.new_modifier_list(cx.nodes, mods))
        } else {
            None
        };

        let synthesized_namespace = {
            let mut ec = self.ec.borrow_mut();
            let empty_list = ec.factory.new_node_list(Vec::new());
            let block = ec.factory.new_module_block(cx.nodes, Some(empty_list));
            ec.factory.new_module_declaration(
                cx.nodes,
                None, /*modifiers*/
                Kind::NamespaceKeyword,
                Some(name),
                None,
                Some(block),
            )
        };
        cx.nodes[synthesized_namespace].parent = self.enclosing_declaration.get();
        if let Some(declaration_data) = cx.nodes[synthesized_namespace].data.declaration_data_mut()
        {
            declaration_data.symbol = Some(host);
        }
        let local_name_text = cx.nodes[local_name].text(cx.nodes).into_owned();
        if let Some(container_data) = cx.nodes[synthesized_namespace]
            .data
            .locals_container_data_mut()
        {
            container_data.locals.set(local_name_text, symbol);
        }

        let old_enclosing = self.enclosing_declaration.get();
        self.enclosing_declaration.set(Some(synthesized_namespace));

        let type_ = self.ensure_type(node, false, cx);
        let mut statements: Vec<NodeId> = Vec::new();
        {
            let mut ec = self.ec.borrow_mut();
            let var_decl = ec.factory.new_variable_declaration(
                cx.nodes,
                Some(local_name),
                None, /*exclamationToken*/
                type_,
                None, /*initializer*/
            );
            let decl_list = ec.factory.new_node_list(vec![var_decl]);
            let decl_list = ec.factory.new_variable_declaration_list(
                cx.nodes,
                Some(decl_list),
                NodeFlags::NONE,
            );
            statements.push(ec.factory.new_variable_statement(
                cx.nodes,
                var_modifiers,
                Some(decl_list),
            ));
        }

        if cx.nodes[local_name].text(cx.nodes) != cx.nodes[export_name].text(cx.nodes) {
            let export_decl = {
                let mut ec = self.ec.borrow_mut();
                let specifier = ec.factory.new_export_specifier(
                    cx.nodes,
                    false, /*isTypeOnly*/
                    Some(local_name),
                    Some(export_name),
                );
                let list = ec.factory.new_node_list(vec![specifier]);
                let named_exports = ec.factory.new_named_exports(cx.nodes, Some(list));
                ec.factory.new_export_declaration(
                    cx.nodes,
                    None,  /*modifiers*/
                    false, /*isTypeOnly*/
                    Some(named_exports),
                    None, /*moduleSpecifier*/
                    None, /*attributes*/
                )
            };
            statements.push(export_decl);
            if !preexisting_expando_has_export {
                // Done before adding statements to expando members to keep the initial variable statement, before we rename anything, private
                self.add_export_modifier_to_expando_members(host_id, cx);
            }
        }

        self.expando_members
            .borrow_mut()
            .entry(host_id)
            .or_default()
            .extend(statements);

        // `defer`: enclosing declaration restore
        self.enclosing_declaration.set(old_enclosing);
    }

    /// `(tx *DeclarationTransformer) addExportModifierToExpandoMembers` —
    /// adds an `export` modifier to all existing expando members so they
    /// remain exported after the `export {}` is added.
    fn add_export_modifier_to_expando_members(&self, host_id: NodeId, cx: &mut VisitorCx<'_, '_>) {
        // only invoked when `tx.expandoMembers` does not *yet* contain an `export` declaration, so no need to skip one here to prevent `export export {}`
        let decls = self
            .expando_members
            .borrow()
            .get(&host_id)
            .cloned()
            .unwrap_or_default();
        for decl in decls {
            let modifier_flags =
                ModifierFlags::EXPORT | ast::get_combined_modifier_flags(decl, cx.nodes);
            let mods = {
                let mut ec = self.ec.borrow_mut();
                let mods = ast::create_modifiers_from_modifier_flags(modifier_flags, &mut |kind| {
                    ec.factory.new_token(cx.nodes, kind)
                });
                ec.factory.new_modifier_list(cx.nodes, mods)
            };
            cx.nodes[decl].set_modifiers(Some(mods));
        }
    }

    /// `(tx *DeclarationTransformer) getExpandoHostId`.
    fn get_expando_host_id(&self, declaration: NodeId, nodes: &[Node]) -> NodeId {
        let root = if ast::is_variable_declaration(&nodes[declaration]) {
            nodes[declaration]
                .parent
                .and_then(|p| nodes[p].parent)
                .unwrap_or(declaration)
        } else {
            declaration
        };
        let original = self.ec().most_original(Some(root)).unwrap_or(root);
        ast::get_node_id(&nodes[original])
    }

    /// `(tx *DeclarationTransformer) transformExpandoHost`.
    fn transform_expando_host(
        &self,
        name: NodeId,
        declaration: NodeId,
        cx: &mut VisitorCx<'_, '_>,
    ) {
        let root = if ast::is_variable_declaration(&cx.nodes[declaration]) {
            cx.nodes[declaration]
                .parent
                .and_then(|p| cx.nodes[p].parent)
                .unwrap_or(declaration)
        } else {
            declaration
        };
        let id = self.get_expando_host_id(declaration, cx.nodes);

        if self.expando_hosts.borrow().contains_key(&id) {
            return;
        }

        let save_needs_declare = self.needs_declare.get();
        self.needs_declare.set(true);

        let mut modifier_flags = self.ensure_modifier_flags(root, cx.nodes);
        let default_export = modifier_flags.intersects(ModifierFlags::EXPORT)
            && modifier_flags.intersects(ModifierFlags::DEFAULT);

        self.needs_declare.set(save_needs_declare);

        if default_export {
            modifier_flags = modifier_flags | ModifierFlags::AMBIENT;
            modifier_flags = ModifierFlags(modifier_flags.0 ^ ModifierFlags::DEFAULT.0);
            modifier_flags = ModifierFlags(modifier_flags.0 ^ ModifierFlags::EXPORT.0);
        }

        let (_can, _cleanup) = self.setup_diagnostic_context(declaration, cx.nodes);

        let modifiers = {
            let mut ec = self.ec.borrow_mut();
            let mods = ast::create_modifiers_from_modifier_flags(modifier_flags, &mut |kind| {
                ec.factory.new_token(cx.nodes, kind)
            });
            ec.factory.new_modifier_list(cx.nodes, mods)
        };
        let mut replacement: Vec<NodeId> = Vec::new();

        if ast::is_function_declaration(&cx.nodes[declaration]) {
            let (type_parameters, parameters, asterisk_token) =
                extract_expando_host_params(declaration, cx.nodes);
            let fn_name = cx.nodes[declaration].name();
            let type_parameters = self.ensure_type_params(declaration, type_parameters, cx);
            let parameters = self.update_param_list(declaration, parameters, cx);
            let return_type = self.ensure_type(declaration, false, cx);
            replacement.push(
                self.ec
                    .borrow_mut()
                    .factory
                    .update_function_declaration(
                        cx.nodes,
                        declaration,
                        Some(modifiers),
                        asterisk_token,
                        fn_name,
                        type_parameters,
                        Some(parameters),
                        return_type,
                        None, /*fullSignature*/
                        None, /*body*/
                    )
                    .unwrap_or(declaration),
            );
        } else if ast::is_variable_declaration(&cx.nodes[declaration])
            && cx.nodes[declaration]
                .initializer()
                .is_some_and(|i| ast::is_function_expression_or_arrow_function(&cx.nodes[i]))
        {
            let fn_ = cx.nodes[declaration].initializer().unwrap();
            let (type_parameters, parameters, asterisk_token) =
                extract_expando_host_params(fn_, cx.nodes);
            let fn_name_text = cx.nodes[name].text(cx.nodes).into_owned();
            let fn_name = self
                .ec
                .borrow_mut()
                .factory
                .new_identifier(cx.nodes, &fn_name_text);
            let type_parameters = self.ensure_type_params(fn_, type_parameters, cx);
            let parameters = self.update_param_list(fn_, parameters, cx);
            let return_type = self.ensure_type(fn_, false, cx);
            replacement.push(self.ec.borrow_mut().factory.new_function_declaration(
                cx.nodes,
                Some(modifiers),
                asterisk_token,
                Some(fn_name),
                type_parameters,
                Some(parameters),
                return_type,
                None, /*fullSignature*/
                None, /*body*/
            ));
        } else {
            let result = self.transform_top_level_declaration(
                self.root_visitor.borrow().as_ref().expect("rootVisitor"),
                cx,
                declaration,
            );
            drop(_cleanup);
            self.expando_hosts
                .borrow_mut()
                .insert(id, result.unwrap_or(declaration));
            return;
        }

        self.report_expando_function_errors(declaration, cx.nodes);

        if default_export {
            if cx.nodes[declaration]
                .parent
                .is_some_and(|p| ast::is_source_file(&cx.nodes[p]))
            {
                self.result_has_external_module_indicator.set(true);
            }
            self.result_has_scope_marker.set(true);
            replacement.push(self.ec.borrow_mut().factory.new_export_assignment(
                cx.nodes,
                None,  /*modifiers*/
                false, /*isExportEquals*/
                None,  /*typeNode*/
                Some(name),
            ));
        }

        // store host result to be added to the output when it's actually visited
        {
            let block = self
                .ec
                .borrow_mut()
                .factory
                .new_syntax_list(cx.nodes, &replacement);
            self.expando_hosts.borrow_mut().insert(id, block);
        }
        drop(_cleanup);
        if self
            .late_statement_replacement_map
            .borrow()
            .contains_key(&id)
        {
            let result = self.create_full_expando_block(
                self.root_visitor.borrow().as_ref().expect("rootVisitor"),
                cx,
                id,
            );
            self.late_statement_replacement_map
                .borrow_mut()
                .insert(id, result);
        }
    }

    /// `(tx *DeclarationTransformer) createFullExpandoBlock`.
    fn create_full_expando_block<'v>(
        &self,
        _v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        id: NodeId,
    ) -> Option<NodeId> {
        // Process any expando assignments on this host that were skipped because it wasn't
        // visible when they were collected - if it's still not visible, they simply get
        // re-deferred, and are dropped if the host is never late-marked visible.
        let deferred = self.deferred_expando_assignments.borrow_mut().remove(&id);
        if let Some(deferred) = deferred {
            for assignment in deferred {
                self.transform_expando_assignment(cx, assignment);
            }
        }
        let n = self.expando_hosts.borrow().get(&id).copied();
        let add_ons = self
            .expando_members
            .borrow()
            .get(&id)
            .cloned()
            .unwrap_or_default();
        if !add_ons.is_empty() {
            let mut modifiers: Option<tsc_ast::ModifierList> = None;
            let mut name: Option<NodeId> = None;
            let mut host: Vec<NodeId> = Vec::new();
            if let Some(n) = n
                && cx.nodes[n].kind == Kind::SyntaxList
            {
                // find the first named syntax list element and use its' name & modifiers
                for &c in cx.nodes[n].as_syntax_list().children.iter() {
                    if cx.nodes[c].name().is_some() {
                        name = cx.nodes[c]
                            .name()
                            .map(|nm| self.ec.borrow_mut().factory.clone_node(cx.nodes, nm));
                        if let Some(mods) = cx.nodes[c].modifiers() {
                            let mod_ids: Vec<NodeId> = mods.nodes.iter().copied().collect();
                            let cloned: Vec<NodeId> = {
                                let mut ec = self.ec.borrow_mut();
                                mod_ids
                                    .iter()
                                    .map(|&m| ec.factory.clone_node(cx.nodes, m))
                                    .collect()
                            };
                            modifiers = Some(
                                self.ec
                                    .borrow_mut()
                                    .factory
                                    .new_modifier_list(cx.nodes, cloned),
                            );
                        }
                        break;
                    }
                }
                host = cx.nodes[n].as_syntax_list().children.to_vec();
            } else if let Some(n) = n {
                name = cx.nodes[n]
                    .name()
                    .map(|nm| self.ec.borrow_mut().factory.clone_node(cx.nodes, nm));
                if let Some(mods) = cx.nodes[n].modifiers() {
                    let mod_ids: Vec<NodeId> = mods.nodes.iter().copied().collect();
                    let cloned: Vec<NodeId> = {
                        let mut ec = self.ec.borrow_mut();
                        mod_ids
                            .iter()
                            .map(|&m| ec.factory.clone_node(cx.nodes, m))
                            .collect()
                    };
                    modifiers = Some(
                        self.ec
                            .borrow_mut()
                            .factory
                            .new_modifier_list(cx.nodes, cloned),
                    );
                }
                host = vec![n];
            }
            if let Some(name) = name {
                let module_decl = {
                    let mut ec = self.ec.borrow_mut();
                    let members = ec.factory.new_node_list(add_ons);
                    let block = ec.factory.new_module_block(cx.nodes, Some(members));
                    ec.factory.new_module_declaration(
                        cx.nodes,
                        modifiers,
                        Kind::NamespaceKeyword,
                        Some(name),
                        None,
                        Some(block),
                    )
                };
                host.push(module_decl);
                return Some(
                    self.ec
                        .borrow_mut()
                        .factory
                        .new_syntax_list(cx.nodes, &host),
                );
            }
        }
        n
    }

    /// `(tx *DeclarationTransformer) tryGetPropertyName`.
    fn try_get_property_name(&self, node: NodeId, nodes: &[Node]) -> String {
        if ast::is_element_access_expression(&nodes[node]) {
            return self
                .resolver
                .borrow_mut()
                .get_element_access_expression_name(Some(node));
        }
        if ast::is_property_access_expression(&nodes[node]) {
            return nodes[node]
                .name()
                .map(|n| nodes[n].text(nodes).into_owned())
                .unwrap_or_default();
        }
        String::new()
    }

    /// The `reportExpandoFunctionErrors` hook installed on the shared state —
    /// `tx.state.reportExpandoFunctionErrors(declaration)`.
    fn report_expando_function_errors(&self, node: NodeId, nodes: &[Node]) {
        let f = self
            .shared
            .borrow()
            .report_expando_function_errors
            .clone();
        if let Some(f) = f {
            f(node, nodes);
        }
    }
}

/// `isNotDeclareModifier`.
#[allow(dead_code)]
fn is_not_declare_modifier(node: &Node) -> bool {
    node.kind != Kind::DeclareKeyword
}

/// `extractExpandoHostParams`.
fn extract_expando_host_params(
    node: NodeId,
    nodes: &[Node],
) -> (Option<NodeList>, Option<NodeList>, Option<NodeId>) {
    match nodes[node].kind {
        Kind::FunctionExpression => {
            let fn_ = &nodes[node]
                .as_function_expression()
                .function_like_with_body_base;
            (
                fn_.function_like_base.type_parameters.clone(),
                fn_.function_like_base.parameters.clone(),
                fn_.body_base.asterisk_token,
            )
        }
        Kind::ArrowFunction => {
            let fn_ = &nodes[node]
                .as_arrow_function()
                .function_like_with_body_base
                .function_like_base;
            (fn_.type_parameters.clone(), fn_.parameters.clone(), None)
        }
        _ => {
            let fn_ = &nodes[node]
                .as_function_declaration()
                .function_like_with_body_base;
            (
                fn_.function_like_base.type_parameters.clone(),
                fn_.function_like_base.parameters.clone(),
                fn_.body_base.asterisk_token,
            )
        }
    }
}
