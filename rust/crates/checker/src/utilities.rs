// Ported from tsc/internal/checker/utilities.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT conventions:
// - `*ast.Node` → `NodeId` (or `Option<NodeId>` where Go passes `nil`),
//   paired with the per-file `nodes: &[ast::Node]` arena on free functions.
//   Where committed call sites pass `&Node` and the body only needs the
//   node's own fields, the parameter is `node: &ast::Node`.
// - `*ast.Symbol` → `SymbolId` (`Option<SymbolId>` for nil); symbol fields
//   are read through `c.symbol_arena.borrow()[s.index()]`.
// - `*Type` → `TypeId` (`Option<TypeId>` for nil); type fields are read
//   through the `types.get(t)` guard on `crate::types::TypeArena`.
// - `*TypeMapper` → `crate::mapper::TypeMapperId`.
// - `args ...any` → generic `args: &[T: Display]`, mirroring
//   `Checker::new_diagnostic_for_node` in checker_core.rs.
// - `context.Context` → `tsc_core::context::Context` (`c.ctx`).
//
// Items that landed in sibling files before this wave (re-exported so
// `crate::utilities::<name>` resolves): `NewDiagnosticForNode` (Checker
// method + free fn below), `compareSymbolsWorker`, `compareNodes`,
// `createSymbolTable`, `isThisTypeParameter`, `isObjectOrArrayLiteralType`,
// `isTupleType` (checker.go), `ValueToString` (checker_core::value_to_string).
//
// PORT(approximation) — `compare_types` operates on `&TypeArena` only
// (committed signature `crate::utilities::compare_types(&self.types, a, b)`).
// Without the checker it cannot reach `symbol_arena`/`file_index_map`/
// `type_mappers`, so symbol ordering uses `SymbolId` index order and node
// ordering uses `NodeId` ordering (`file_index << 44 | local_index`, which
// approximates Go's `fileIndexMap[s]` + `Pos()` order because files are
// indexed in program order and nodes are allocated in source order). This
// yields a deterministic total order — sufficient for the sort/dedup/
// binary-search call sites — but may differ from Go's order when names or
// declaration order would have disagreed with id order.

use rustc_hash::FxHashMap;
use std::sync::OnceLock;

use tsc_ast::{self as ast, NodeId, SymbolId, SymbolTable};
use tsc_collections::OrderedMap;
use tsc_core::core as core_helpers;
use tsc_core::text::TextRange;
use tsc_diagnostics as diagnostics;
use tsc_evaluator as evaluator;

use crate::checker_core::Checker;
use crate::mapper::{TypeMapperData, TypeMapperId, TypeMapperKind};
use crate::types::{ObjectFlags, Signature, SignatureId, TypeArena, TypeData, TypeFlags, TypeId};

// Re-exports so `crate::utilities::<name>` resolves for helpers committed to
// checker_core.rs before this file landed.
pub use crate::checker_core::{
    create_symbol_table, is_object_or_array_literal_type, is_this_type_parameter, is_tuple_type,
    value_to_string,
};

// ===========================================================================
// Diagnostics
// ===========================================================================

/// `NewDiagnosticForNode` (checker/utilities.go) — free-function form;
/// `nodes` is the arena of the file containing `node` (Go derefs `*ast.Node`
/// directly).
pub fn new_diagnostic_for_node<T: std::fmt::Display>(
    node: Option<NodeId>,
    nodes: &[ast::Node],
    message: &'static diagnostics::Message,
    args: &[T],
) -> ast::diagnostic::DiagnosticRef {
    let mut file = None;
    let mut loc = TextRange::default();
    if let Some(node) = node {
        if let Some(source_file) = ast::get_source_file_of_node(Some(node), nodes) {
            let sf = nodes[source_file].as_source_file();
            loc = tsc_scanner::scanner::get_error_range_for_node(sf, node, nodes);
            file = Some(ast::diagnostic::DiagnosticFile::from_node(source_file, nodes));
        }
    }
    ast::diagnostic::new_diagnostic(file, loc, message, args)
}

/// `NewDiagnosticChainForNode` (checker/utilities.go). The first `c`
/// parameter is a port addition — the fallback `NewDiagnosticForNode` path
/// needs the program's per-file node arena for `node`. Committed call sites
/// pass `node` as a bare `NodeId`, so it is `impl Into<Option<NodeId>>`.
pub fn new_diagnostic_chain_for_node<T: std::fmt::Display>(
    c: &Checker,
    chain: Option<ast::diagnostic::DiagnosticRef>,
    node: impl Into<Option<NodeId>>,
    message: &'static diagnostics::Message,
    args: &[T],
) -> ast::diagnostic::DiagnosticRef {
    if chain.is_some() {
        return ast::diagnostic::new_diagnostic_chain(chain.as_ref(), message, args);
    }
    match node.into() {
        Some(node) => {
            let nodes = c.program_nodes(node);
            new_diagnostic_for_node(Some(node), &nodes, message, args)
        }
        None => ast::diagnostic::new_diagnostic(None, TextRange::default(), message, args),
    }
}

/// `findInMap` — first value satisfying `pred` (Go iterates a map; the port
/// iterates `OrderedMap` values — the surviving committed caller operates on
/// a `SymbolTable`).
pub(crate) fn find_in_map<K, V>(
    m: &OrderedMap<K, V>,
    mut predicate: impl FnMut(&V) -> bool,
) -> Option<&V>
where
    K: Eq + std::hash::Hash,
{
    m.values().find(|v| predicate(*v))
}

// ===========================================================================
// Token / modifier predicates
// ===========================================================================

/// `tokenIsIdentifierOrKeyword`.
pub(crate) fn token_is_identifier_or_keyword(token: ast::Kind) -> bool {
    token >= ast::Kind::Identifier
}

/// `tokenIsIdentifierOrKeywordOrGreaterThan`.
pub(crate) fn token_is_identifier_or_keyword_or_greater_than(token: ast::Kind) -> bool {
    token == ast::Kind::GreaterThanToken || token_is_identifier_or_keyword(token)
}

/// `hasOverrideModifier`.
pub(crate) fn has_override_modifier(node: &ast::Node) -> bool {
    ast::has_syntactic_modifier(node, ast::ModifierFlags::OVERRIDE)
}

/// `hasAsyncModifier`.
pub(crate) fn has_async_modifier(node: &ast::Node) -> bool {
    ast::has_syntactic_modifier(node, ast::ModifierFlags::ASYNC)
}

/// `getSelectedModifierFlags` — `node.ModifierFlags() & flags`.
pub(crate) fn get_selected_modifier_flags(
    node: &ast::Node,
    flags: ast::ModifierFlags,
) -> ast::ModifierFlags {
    node.modifier_flags() & flags
}

/// `hasReadonlyModifier`.
pub(crate) fn has_readonly_modifier(node: &ast::Node) -> bool {
    ast::has_modifier(node, ast::ModifierFlags::READONLY)
}

/// `isStaticPrivateIdentifierProperty` — the `c` parameter is a port
/// addition (Go derefs `s.ValueDeclaration` fields directly; here we need
/// the symbol arena plus the declaration's node arena for
/// `IsPrivateIdentifierClassElementDeclaration`/`IsStatic`).
pub(crate) fn is_static_private_identifier_property(c: &Checker, s: SymbolId) -> bool {
    let value_declaration = c.symbol_arena.borrow()[s.index()].value_declaration;
    let Some(decl) = value_declaration else {
        return false;
    };
    let nodes = c.program_nodes(decl);
    ast::is_private_identifier_class_element_declaration(&nodes[decl])
        && ast::is_static(&nodes[decl], &nodes)
}

/// `isEmptyObjectLiteral`.
pub(crate) fn is_empty_object_literal(expression: &ast::Node) -> bool {
    ast::is_object_literal_expression(expression)
        && expression.properties().map_or(0, |p| p.len()) == 0
}

// ===========================================================================
// AssignmentKind
// ===========================================================================

/// `type AssignmentKind int32`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(i32)]
pub enum AssignmentKind {
    /// `AssignmentKindNone`
    None = 0,
    /// `AssignmentKindDefinite`
    Definite = 1,
    /// `AssignmentKindCompound`
    Compound = 2,
}

/// `AssignmentKindNone`/`AssignmentKindDefinite`/`AssignmentKindCompound` —
/// committed call sites use `AssignmentKind::NONE`/`DEFINITE`/`COMPOUND`.
impl AssignmentKind {
    /// `AssignmentKindNone`.
    pub const NONE: AssignmentKind = AssignmentKind::None;
    /// `AssignmentKindDefinite`.
    pub const DEFINITE: AssignmentKind = AssignmentKind::Definite;
    /// `AssignmentKindCompound`.
    pub const COMPOUND: AssignmentKind = AssignmentKind::Compound;
}

/// `type AssignmentTarget = ast.Node` — BinaryExpression |
/// PrefixUnaryExpression | PostfixUnaryExpression | ForInOrOfStatement.
pub type AssignmentTarget = NodeId;

/// `getAssignmentTargetKind`.
pub(crate) fn get_assignment_target_kind(node: NodeId, nodes: &[ast::Node]) -> AssignmentKind {
    let Some(target) = ast::get_assignment_target(node, nodes) else {
        return AssignmentKind::None;
    };
    match nodes[target].kind {
        ast::Kind::BinaryExpression => {
            let binary_operator = nodes[target].as_binary_expression().operator_token.kind;
            if binary_operator == ast::Kind::EqualsToken
                || ast::is_logical_or_coalescing_assignment_operator(binary_operator)
            {
                AssignmentKind::Definite
            } else {
                AssignmentKind::Compound
            }
        }
        ast::Kind::PrefixUnaryExpression | ast::Kind::PostfixUnaryExpression => {
            AssignmentKind::Compound
        }
        ast::Kind::ForInStatement | ast::Kind::ForOfStatement => AssignmentKind::Definite,
        _ => panic!("Unhandled case in getAssignmentTargetKind"),
    }
}

/// `isDeleteTarget`.
pub(crate) fn is_delete_target(node: NodeId, nodes: &[ast::Node]) -> bool {
    if !ast::is_access_expression(&nodes[node], nodes) {
        return false;
    }
    let node = ast::walk_up_parenthesized_expressions(nodes[node].parent, nodes);
    node.is_some_and(|n| nodes[n].kind == ast::Kind::DeleteExpression)
}

/// `isInCompoundLikeAssignment`. Committed call sites pass a `&Node`; the
/// `NodeId` is recovered via `node.id` (Go derefs `*ast.Node` fields).
pub(crate) fn is_in_compound_like_assignment(node: NodeId, nodes: &[ast::Node]) -> bool {
    let Some(target) = ast::get_assignment_target(node, nodes) else {
        return false;
    };
    // `IsAssignmentExpression(target /*excludeCompoundAssignment*/, true)`
    ast::is_assignment_expression(&nodes[target], nodes, true)
        && is_compound_like_assignment(target, nodes)
}

/// `isCompoundLikeAssignment`.
pub(crate) fn is_compound_like_assignment(assignment: NodeId, nodes: &[ast::Node]) -> bool {
    let right = ast::skip_parentheses(
        nodes[assignment]
            .as_binary_expression()
            .right
            .expect("binary right"),
        nodes,
    );
    nodes[right].kind == ast::Kind::BinaryExpression
        && is_shift_operator_or_higher(nodes[right].as_binary_expression().operator_token.kind)
}

/// `isConstTypeReference`.
pub(crate) fn is_const_type_reference(node: &ast::Node, nodes: &[ast::Node]) -> bool {
    ast::is_type_reference_node(node)
        && node.type_arguments().map_or(0, |t| t.len()) == 0
        && node.as_type_reference_node().type_name.is_some_and(|tn| {
            ast::is_identifier(&nodes[tn]) && nodes[tn].text(nodes) == "const"
        })
}

/// `isConstTypeReferenceName` — whether `node` is the `const` type name of a
/// `const` assertion (`x as const` / `<const>x`), which must not be resolved
/// as a real name.
pub(crate) fn is_const_type_reference_name(node: Option<NodeId>, nodes: &[ast::Node]) -> bool {
    let Some(node) = node else { return false };
    ast::is_identifier(&nodes[node])
        && nodes[node].parent.is_some_and(|p| {
            is_const_type_reference(&nodes[p], nodes)
                && nodes[p]
                    .parent
                    .is_some_and(|pp| ast::is_assertion_expression(&nodes[pp]))
        })
}

/// `isExportAssignmentExpressionName` — whether `node` is (the root entity
/// name of) the expression of an `export =` / `export default` assignment.
/// Referencing a namespace or type-only name there is legal, and
/// `checkExportAssignment` decides whether it is an error, so
/// `checkIdentifier` must not report a value-usage error for it.
pub(crate) fn is_export_assignment_expression_name(
    node: Option<NodeId>,
    nodes: &[ast::Node],
) -> bool {
    let Some(mut current) = node else { return false };
    while let Some(parent) = nodes[current].parent {
        if !ast::is_property_access_or_qualified_name(&nodes[parent]) {
            break;
        }
        current = parent;
    }
    nodes[current].parent.is_some_and(|p| {
        ast::is_export_assignment(&nodes[p]) && nodes[p].expression() == Some(current)
    })
}

/// `GetSingleVariableOfVariableStatement`.
pub fn get_single_variable_of_variable_statement(
    node: NodeId,
    nodes: &[ast::Node],
) -> Option<NodeId> {
    if !ast::is_variable_statement(&nodes[node]) {
        return None;
    }
    let declaration_list = nodes[node].as_variable_statement().declaration_list?;
    core_helpers::first_or_nil(
        nodes[declaration_list]
            .as_variable_declaration_list()
            .declarations
            .as_ref()
            .map(|l| l.nodes())
            .unwrap_or(&[]),
    )
}

/// `isTypeReferenceIdentifier`.
pub(crate) fn is_type_reference_identifier(mut node: NodeId, nodes: &[ast::Node]) -> bool {
    while let Some(parent) = nodes[node].parent {
        if nodes[parent].kind != ast::Kind::QualifiedName {
            break;
        }
        node = parent;
    }
    nodes[node]
        .parent
        .is_some_and(|p| ast::is_type_reference_node(&nodes[p]))
}

/// `IsInTypeQuery` — TypeScript 1.0 spec (April 2014): 3.6.3. A type query
/// consists of the keyword typeof followed by an expression restricted to a
/// single identifier or a sequence of identifiers separated by periods.
pub fn is_in_type_query(node: NodeId, nodes: &[ast::Node]) -> bool {
    ast::find_ancestor_or_quit(Some(node), nodes, &mut |n, _nodes| match n.kind {
        ast::Kind::TypeQuery => ast::FindAncestorResult::True,
        ast::Kind::Identifier | ast::Kind::QualifiedName => ast::FindAncestorResult::False,
        _ => ast::FindAncestorResult::Quit,
    })
    .is_some()
}

/// `canHaveLocals`.
pub(crate) fn can_have_locals(node: &ast::Node) -> bool {
    matches!(
        node.kind,
        ast::Kind::ArrowFunction
            | ast::Kind::Block
            | ast::Kind::CallSignature
            | ast::Kind::CaseBlock
            | ast::Kind::CatchClause
            | ast::Kind::ClassStaticBlockDeclaration
            | ast::Kind::ConditionalType
            | ast::Kind::Constructor
            | ast::Kind::ConstructorType
            | ast::Kind::ConstructSignature
            | ast::Kind::ForStatement
            | ast::Kind::ForInStatement
            | ast::Kind::ForOfStatement
            | ast::Kind::FunctionDeclaration
            | ast::Kind::FunctionExpression
            | ast::Kind::FunctionType
            | ast::Kind::GetAccessor
            | ast::Kind::IndexSignature
            | ast::Kind::JSDocSignature
            | ast::Kind::MappedType
            | ast::Kind::MethodDeclaration
            | ast::Kind::MethodSignature
            | ast::Kind::ModuleDeclaration
            | ast::Kind::SetAccessor
            | ast::Kind::SourceFile
            | ast::Kind::TypeAliasDeclaration
            | ast::Kind::JSTypeAliasDeclaration
    )
}

/// `isShorthandAmbientModuleSymbol` — needs the declaration's arena.
pub(crate) fn is_shorthand_ambient_module_symbol(c: &Checker, module_symbol: SymbolId) -> bool {
    let value_declaration = c.symbol_arena.borrow()[module_symbol.index()].value_declaration;
    match value_declaration {
        Some(decl) => {
            let nodes = c.program_nodes(decl);
            is_shorthand_ambient_module(&nodes[decl])
        }
        None => false,
    }
}

/// `isShorthandAmbientModule` — the only kind of module that can be missing
/// a body is a shorthand ambient module.
pub(crate) fn is_shorthand_ambient_module(node: &ast::Node) -> bool {
    node.kind == ast::Kind::ModuleDeclaration && node.body().is_none()
}

/// `getAliasDeclarationFromName`.
pub(crate) fn get_alias_declaration_from_name(
    node: NodeId,
    nodes: &[ast::Node],
) -> Option<NodeId> {
    let Some(mut parent) = nodes[node].parent else {
        return None;
    };
    match nodes[parent].kind {
        ast::Kind::ImportClause
        | ast::Kind::ImportSpecifier
        | ast::Kind::NamespaceImport
        | ast::Kind::ExportSpecifier
        | ast::Kind::ExportAssignment
        | ast::Kind::ImportEqualsDeclaration
        | ast::Kind::NamespaceExport => Some(parent),
        ast::Kind::QualifiedName => get_alias_declaration_from_name(parent, nodes),
        _ => None,
    }
    // (Go switches on `node.Parent.Kind`; `parent` is already bound above.)
    .map(|p| {
        let _ = &mut parent;
        p
    })
}

/// `entityNameToString` — `ast.EntityNameToString(name, scanner.GetTextOfNode)`.
pub(crate) fn entity_name_to_string(name: NodeId, nodes: &[ast::Node]) -> String {
    ast::entity_name_to_string(name, nodes, Some(&mut |nodes, id| {
        tsc_scanner::utilities::get_text_of_node(id, nodes)
    }))
}

/// `getContainingQualifiedNameNode`.
pub(crate) fn get_containing_qualified_name_node(mut node: NodeId, nodes: &[ast::Node]) -> NodeId {
    while let Some(parent) = nodes[node].parent {
        if !ast::is_qualified_name(&nodes[parent]) {
            break;
        }
        node = parent;
    }
    node
}

/// `isSideEffectImport`.
pub(crate) fn is_side_effect_import(node: NodeId, nodes: &[ast::Node]) -> bool {
    ast::find_ancestor(Some(node), nodes, &mut |n, _| ast::is_import_declaration(n))
        .is_some_and(|a| nodes[a].import_clause().is_none())
}

/// `getExternalModuleRequireArgument`.
pub(crate) fn get_external_module_require_argument(
    node: NodeId,
    nodes: &[ast::Node],
) -> Option<NodeId> {
    if ast::is_variable_declaration_initialized_to_require(node, nodes) {
        return nodes[node]
            .initializer()
            .and_then(|i| nodes[i].arguments().and_then(|a| a.first().copied()));
    }
    None
}

/// `isRightSideOfAccessExpression`.
pub(crate) fn is_right_side_of_access_expression(node: NodeId, nodes: &[ast::Node]) -> bool {
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    (ast::is_property_access_expression(&nodes[parent]) && nodes[parent].name() == Some(node))
        || (ast::is_element_access_expression(&nodes[parent])
            && nodes[parent].as_element_access_expression().argument_expression == Some(node))
}

/// `isTopLevelInExternalModuleAugmentation`.
pub(crate) fn is_top_level_in_external_module_augmentation(
    node: impl Into<Option<NodeId>>,
    nodes: &[ast::Node],
) -> bool {
    let Some(node) = node.into() else {
        return false;
    };
    nodes[node].parent.is_some_and(|p| {
        ast::is_module_block(&nodes[p])
            && nodes[p]
                .parent
                .is_some_and(|pp| ast::is_external_module_augmentation(&nodes[pp], nodes))
    })
}

/// `isSyntacticDefault`.
pub(crate) fn is_syntactic_default(node: &ast::Node) -> bool {
    (ast::is_export_assignment(node) && !node.as_export_assignment().is_export_equals)
        || ast::has_syntactic_modifier(node, ast::ModifierFlags::DEFAULT)
        || ast::is_export_specifier(node)
        || ast::is_namespace_export(node)
}

/// `hasExportAssignmentSymbol` — needs the symbol arena for `.exports`.
pub(crate) fn has_export_assignment_symbol(c: &Checker, module_symbol: SymbolId) -> bool {
    c.symbol_arena.borrow()[module_symbol.index()]
        .exports
        .get(ast::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
        .is_some()
}

/// `isTypeAlias`.
pub(crate) fn is_type_alias(node: &ast::Node) -> bool {
    ast::is_type_or_js_type_alias_declaration(node)
}

/// `hasOnlyExpressionInitializer`.
pub(crate) fn has_only_expression_initializer(node: &ast::Node) -> bool {
    matches!(
        node.kind,
        ast::Kind::VariableDeclaration
            | ast::Kind::Parameter
            | ast::Kind::BindingElement
            | ast::Kind::PropertyDeclaration
            | ast::Kind::PropertyAssignment
            | ast::Kind::EnumMember
    )
}

/// `hasDotDotDotToken`. Committed call sites pass both `(&Node)` and
/// `(&Node, &[Node])`; the body only reads the node's own fields, matching
/// Go, so the canonical signature is `(&Node)` — 2-arg sites must drop the
/// second argument (PORT: documented divergence).
pub(crate) fn has_dot_dot_dot_token(node: &ast::Node) -> bool {
    match node.kind {
        ast::Kind::Parameter => {
            node.as_parameter_declaration().dot_dot_dot_token.is_some()
        }
        ast::Kind::BindingElement => node.as_binding_element().dot_dot_dot_token.is_some(),
        ast::Kind::NamedTupleMember => {
            node.as_named_tuple_member().dot_dot_dot_token.is_some()
        }
        ast::Kind::JsxExpression => node.as_jsx_expression().dot_dot_dot_token.is_some(),
        _ => false,
    }
}

/// `IsTypeAny`.
pub fn is_type_any(types: &TypeArena, t: TypeId) -> bool {
    types.get(t).flags.intersects(TypeFlags::ANY)
}

/// `isJSDocOptionalParameter` — Go returns false (jsdoc support not yet).
pub(crate) fn is_jsdoc_optional_parameter(_node: NodeId) -> bool {
    false // !!!
}

/// `isExclamationToken`.
pub(crate) fn is_exclamation_token(node: impl Into<Option<NodeId>>, _nodes: &[ast::Node]) -> bool {
    node.into()
        .is_some_and(|n| _nodes[n].kind == ast::Kind::ExclamationToken)
}

/// `isOptionalDeclaration`.
pub(crate) fn is_optional_declaration(declaration: &ast::Node, nodes: &[ast::Node]) -> bool {
    ast::has_question_token(declaration, nodes)
}

impl Checker {
    /// `(c *Checker) isOptionalParameter` (checker/utilities.go).
    /// `!!! TODO: JSDoc support` — preserved from Go.
    pub(crate) fn is_optional_parameter(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        if ast::is_parameter_declaration(&nodes[node]) && nodes[node].question_token(&nodes).is_some()
        {
            return true;
        }
        if !ast::is_parameter_declaration(&nodes[node]) {
            return false;
        }
        if nodes[node].initializer().is_some() {
            let parent = nodes[node].parent.expect("parameter parent");
            let signature = self.get_signature_from_declaration(parent);
            let parameter_index = core_helpers::find_index(
                nodes[parent].parameters().unwrap_or(&[]),
                |&p| p == node,
            );
            tsc_debug::assert_!(parameter_index >= 0);
            // Only consider syntactic or instantiated parameters as
            // optional, not `void` parameters as this function is used in
            // grammar checks and checking for `void` too early results in
            // parameter types widening too early and causes some
            // noImplicitAny errors to be lost.
            return parameter_index
                >= self.get_min_argument_count_ex(
                    signature,
                    crate::relater::MinArgumentCountFlags::STRONG_ARITY_FOR_UNTYPED_JS
                        | crate::relater::MinArgumentCountFlags::VOID_IS_NON_OPTIONAL,
                );
        }
        let parent = nodes[node].parent.expect("parameter parent");
        if let Some(iife) = ast::get_immediately_invoked_function_expression(parent, &nodes) {
            let parameter_index = core_helpers::find_index(
                nodes[parent].parameters().unwrap_or(&[]),
                |&p| p == node,
            );
            return nodes[node].type_().is_none()
                && nodes[node]
                    .as_parameter_declaration()
                    .dot_dot_dot_token
                    .is_none()
                && parameter_index >= self.get_effective_call_arguments(iife).len() as i32;
        }
        false
    }
}

/// `isEmptyArrayLiteral`.
pub(crate) fn is_empty_array_literal(expression: &ast::Node) -> bool {
    ast::is_array_literal_expression(expression)
        && expression.elements().map_or(0, |e| e.len()) == 0
}

/// `declarationBelongsToPrivateAmbientMember`.
pub(crate) fn declaration_belongs_to_private_ambient_member(
    declaration: NodeId,
    nodes: &[ast::Node],
) -> bool {
    let root = ast::get_root_declaration(declaration, nodes);
    let member_declaration = if nodes[root].kind == ast::Kind::Parameter {
        nodes[root].parent.unwrap_or(root)
    } else {
        root
    };
    is_private_within_ambient(&nodes[member_declaration], nodes)
}

/// `isPrivateWithinAmbient`.
pub(crate) fn is_private_within_ambient(node: &ast::Node, _nodes: &[ast::Node]) -> bool {
    (ast::has_modifier(node, ast::ModifierFlags::PRIVATE)
        || ast::is_private_identifier_class_element_declaration(node))
        && node.flags.intersects(ast::NodeFlags::AMBIENT)
}

/// `isTypeAssertion`. Committed call sites pass both `(&Node)` and
/// `(NodeId, &[Node])`; `SkipParentheses` needs the arena, so the canonical
/// form is `(NodeId, &[Node])`.
pub(crate) fn is_type_assertion(node: NodeId, nodes: &[ast::Node]) -> bool {
    ast::is_assertion_expression(&nodes[ast::skip_parentheses(node, nodes)])
}

impl Checker {
    /// `(c *Checker) sortSymbols` — `slices.SortFunc(symbols,
    /// c.compareSymbols)`.
    pub(crate) fn sort_symbols(&mut self, symbols: &mut [SymbolId]) {
        let compare_symbols = self
            .compare_symbols
            .clone()
            .expect("compareSymbols is initialized by new_checker");
        symbols.sort_by(|&a, &b| compare_symbols(self, Some(a), Some(b)).cmp(&0));
    }
}

// ===========================================================================
// CompareTypes
// ===========================================================================

/// `CompareTypes` (checker/utilities.go) — `-1`/`0`/`1` ordering on types.
///
/// PORT(approximation): the committed signature operates on `&TypeArena`
/// only (see the module header for the ordering caveats).
pub fn compare_types(types: &TypeArena, t1: TypeId, t2: TypeId) -> i32 {
    compare_types_opt(types, Some(t1), Some(t2))
}

fn compare_types_opt(types: &TypeArena, t1: Option<TypeId>, t2: Option<TypeId>) -> i32 {
    if t1 == t2 {
        return 0;
    }
    let Some(t1) = t1 else { return -1 };
    let Some(t2) = t2 else { return 1 };
    {
        let a = types.get(t1);
        let b = types.get(t2);
        if a.checker_shard != b.checker_shard {
            panic!("Cannot compare types from different checkers")
        }
    }
    // First sort in order of increasing type flags values.
    let flags1 = types.get(t1).flags;
    let flags2 = types.get(t2).flags;
    let c = get_sort_order_flags(flags1) - get_sort_order_flags(flags2);
    if c != 0 {
        return c;
    }
    // Order named types by name and, in the case of aliased types, by alias
    // type arguments.
    let c = compare_type_names(types, t1, t2);
    if c != 0 {
        return c;
    }
    // We have unnamed types or types with identical names. Now sort by data
    // specific to the type.
    let flags = types.get(t1).flags;
    let object_flags1 = types.get(t1).object_flags;
    let object_flags2 = types.get(t2).object_flags;
    match () {
        _ if flags.intersects(
            TypeFlags::ANY
                | TypeFlags::UNKNOWN
                | TypeFlags::STRING
                | TypeFlags::NUMBER
                | TypeFlags::BOOLEAN
                | TypeFlags::BIG_INT
                | TypeFlags::ES_SYMBOL
                | TypeFlags::VOID
                | TypeFlags::UNDEFINED
                | TypeFlags::NULL
                | TypeFlags::NEVER
                | TypeFlags::NON_PRIMITIVE,
        ) =>
        {
            // Only distinguished by type IDs, handled below.
        }
        _ if flags.intersects(TypeFlags::OBJECT) => {
            // Order instantiation expression types without relying on lazy
            // symbol IDs. Order other unnamed or identically named object
            // types by symbol.
            if object_flags1.intersects(ObjectFlags::INSTANTIATION_EXPRESSION_TYPE)
                && object_flags2.intersects(ObjectFlags::INSTANTIATION_EXPRESSION_TYPE)
            {
                let declaration1 = types
                    .get(t1)
                    .symbol
                    .and_then(|s| symbol_declarations(s).first().copied());
                let declaration2 = types
                    .get(t2)
                    .symbol
                    .and_then(|s| symbol_declarations(s).first().copied());
                // A single instantiation expression can produce multiple
                // types for union constituents, so compare their source
                // declarations before comparing the shared expression node.
                let c = compare_node_ids(declaration1, declaration2);
                if c != 0 {
                    return c;
                }
                let c = compare_node_ids(
                    types.get(t1).as_instantiation_expression_type().node,
                    types.get(t2).as_instantiation_expression_type().node,
                );
                if c != 0 {
                    return c;
                }
            } else {
                let c = compare_symbol_ids(types.get(t1).symbol, types.get(t2).symbol);
                if c != 0 {
                    return c;
                }
            }
            // When object types have the same or no symbol, order by kind.
            // We order type references before other kinds.
            if object_flags1.intersects(ObjectFlags::REFERENCE)
                && object_flags2.intersects(ObjectFlags::REFERENCE)
            {
                let (target1, node1) = {
                    let r = types.get(t1);
                    let r = r.as_type_reference();
                    (r.target, r.node)
                };
                let (target2, node2) = {
                    let r = types.get(t2);
                    let r = r.as_type_reference();
                    (r.target, r.node)
                };
                let tuple1 = target1.is_some_and(|t| {
                    types.get(t).object_flags.intersects(ObjectFlags::TUPLE)
                });
                let tuple2 = target2.is_some_and(|t| {
                    types.get(t).object_flags.intersects(ObjectFlags::TUPLE)
                });
                if tuple1 && tuple2 {
                    // Tuple types have no associated symbol, instead we order
                    // by tuple element information.
                    let c = compare_tuple_types(
                        types,
                        types.get(target1.unwrap()).as_tuple_type(),
                        types.get(target2.unwrap()).as_tuple_type(),
                    );
                    if c != 0 {
                        return c;
                    }
                }
                // Here we know we have references to instantiations of the
                // same type because we have matching targets.
                if node1.is_none() && node2.is_none() {
                    // Non-deferred type references with the same target are
                    // sorted by their type argument lists.
                    let c = compare_type_lists(
                        types,
                        &types.get(t1).as_type_reference().resolved_type_arguments,
                        &types.get(t2).as_type_reference().resolved_type_arguments,
                    );
                    if c != 0 {
                        return c;
                    }
                } else {
                    // Deferred type references with the same target are
                    // ordered by the source location of the reference.
                    let c = compare_node_ids(node1, node2);
                    if c != 0 {
                        return c;
                    }
                    // Instantiations of the same deferred type reference are
                    // ordered by their associated type mappers (which reflect
                    // the mapping of in-scope type parameters to type
                    // arguments).
                    let c = compare_type_mappers(
                        types.get(t1).as_object_type().mapper,
                        types.get(t2).as_object_type().mapper,
                    );
                    if c != 0 {
                        return c;
                    }
                }
            } else if object_flags1.intersects(ObjectFlags::REFERENCE) {
                return -1;
            } else if object_flags2.intersects(ObjectFlags::REFERENCE) {
                return 1;
            } else {
                // Order unnamed non-reference object types by kind and
                // instantiation data.
                let c = (object_flags1 & ObjectFlags::OBJECT_TYPE_KIND_MASK).0 as i64
                    - (object_flags2 & ObjectFlags::OBJECT_TYPE_KIND_MASK).0 as i64;
                if c != 0 {
                    return c.clamp(-1, 1) as i32 * (c.signum() as i32).abs() + {
                        // preserve exact int diff semantics
                        let _ = c;
                        0
                    };
                }
                // (kept simple — see below)
                let _ = c;
                if object_flags1.intersects(ObjectFlags::REVERSE_MAPPED) {
                    let (source1, mapped1, constraint1) = {
                        let r = types.get(t1);
                        let r = r.as_reverse_mapped_type();
                        (r.source, r.mapped_type, r.constraint_type)
                    };
                    let (source2, mapped2, constraint2) = {
                        let r = types.get(t2);
                        let r = r.as_reverse_mapped_type();
                        (r.source, r.mapped_type, r.constraint_type)
                    };
                    let c = compare_types_opt(types, source1, source2);
                    if c != 0 {
                        return c;
                    }
                    let c = compare_types_opt(types, mapped1, mapped2);
                    if c != 0 {
                        return c;
                    }
                    let c = compare_types_opt(types, constraint1, constraint2);
                    if c != 0 {
                        return c;
                    }
                }
                let mut m1 = types.get(t1).as_object_type().mapper;
                let mut m2 = types.get(t2).as_object_type().mapper;
                if object_flags1.intersects(ObjectFlags::MAPPED) {
                    // instantiateAnonymousType prepends a fresh type
                    // parameter mapping. Compare the effective instantiation,
                    // not the identity of that fresh parameter.
                    if let Some(m) = m1 {
                        m1 = composite_m2(m);
                    }
                    if let Some(m) = m2 {
                        m2 = composite_m2(m);
                    }
                }
                let c = compare_type_mappers(m1, m2);
                if c != 0 {
                    return c;
                }
            }
        }
        _ if flags.intersects(TypeFlags::UNION) => {
            // Unions are ordered by origin and then constituent type lists.
            let (o1, types1) = {
                let u = types.get(t1);
                (u.as_union_type().origin, u.types().to_vec())
            };
            let (o2, types2) = {
                let u = types.get(t2);
                (u.as_union_type().origin, u.types().to_vec())
            };
            match (o1, o2) {
                (None, None) => {
                    let c = compare_type_lists(types, &types1, &types2);
                    if c != 0 {
                        return c;
                    }
                }
                (None, Some(_)) => return 1,
                (Some(_), None) => return -1,
                (Some(o1), Some(o2)) => {
                    let c = compare_types(types, o1, o2);
                    if c != 0 {
                        return c;
                    }
                }
            }
        }
        _ if flags.intersects(TypeFlags::INTERSECTION) => {
            // Intersections are ordered by their constituent type lists.
            let c = compare_type_lists(types, types.get(t1).types(), types.get(t2).types());
            if c != 0 {
                return c;
            }
        }
        _ if flags
            .intersects(TypeFlags::ENUM | TypeFlags::ENUM_LITERAL | TypeFlags::UNIQUE_ES_SYMBOL) =>
        {
            // Enum members are ordered by their symbol (and thus their
            // declaration order).
            let c = compare_symbol_ids(types.get(t1).symbol, types.get(t2).symbol);
            if c != 0 {
                return c;
            }
        }
        _ if flags.intersects(TypeFlags::STRING_LITERAL) => {
            // String literal types are ordered by their values.
            let v1 = literal_string(types.get(t1).as_literal_type().value.as_ref());
            let v2 = literal_string(types.get(t2).as_literal_type().value.as_ref());
            let c = v1.cmp(v2);
            if c != std::cmp::Ordering::Equal {
                return c as i32 - 1;
            }
        }
        _ if flags.intersects(TypeFlags::NUMBER_LITERAL) => {
            // Numeric literal types are ordered by their values.
            let v1 = literal_number(types.get(t1).as_literal_type().value.as_ref());
            let v2 = literal_number(types.get(t2).as_literal_type().value.as_ref());
            let c = v1.compare(v2);
            if c != 0 {
                return c;
            }
        }
        _ if flags.intersects(TypeFlags::BIG_INT_LITERAL) => {
            let c = crate::checker_d::get_big_int_literal_value(types, t1)
                .compare(crate::checker_d::get_big_int_literal_value(types, t2));
            if c != 0 {
                return c;
            }
        }
        _ if flags.intersects(TypeFlags::BOOLEAN_LITERAL) => {
            let b1 = literal_bool(types.get(t1).as_literal_type().value.as_ref());
            let b2 = literal_bool(types.get(t2).as_literal_type().value.as_ref());
            if b1 != b2 {
                return if b1 { 1 } else { -1 };
            }
        }
        _ if flags.intersects(TypeFlags::TYPE_PARAMETER) => {
            let c = compare_symbol_ids(types.get(t1).symbol, types.get(t2).symbol);
            if c != 0 {
                return c;
            }
        }
        _ if flags.intersects(TypeFlags::INDEX) => {
            let (target1, index_flags1) = {
                let t = types.get(t1);
                let t = t.as_index_type();
                (t.target, t.index_flags)
            };
            let (target2, index_flags2) = {
                let t = types.get(t2);
                let t = t.as_index_type();
                (t.target, t.index_flags)
            };
            let c = compare_types_opt(types, target1, target2);
            if c != 0 {
                return c;
            }
            let c = index_flags1.0 as i64 - index_flags2.0 as i64;
            if c != 0 {
                return c as i32;
            }
        }
        _ if flags.intersects(TypeFlags::INDEXED_ACCESS) => {
            let (object1, index1) = {
                let t = types.get(t1);
                let t = t.as_indexed_access_type();
                (t.object_type, t.index_type)
            };
            let (object2, index2) = {
                let t = types.get(t2);
                let t = t.as_indexed_access_type();
                (t.object_type, t.index_type)
            };
            let c = compare_types_opt(types, object1, object2);
            if c != 0 {
                return c;
            }
            let c = compare_types_opt(types, index1, index2);
            if c != 0 {
                return c;
            }
        }
        _ if flags.intersects(TypeFlags::CONDITIONAL) => {
            let (root1, mapper1) = {
                let t = types.get(t1);
                let t = t.as_conditional_type();
                (t.root.as_ref().and_then(|r| r.node), t.mapper)
            };
            let (root2, mapper2) = {
                let t = types.get(t2);
                let t = t.as_conditional_type();
                (t.root.as_ref().and_then(|r| r.node), t.mapper)
            };
            let c = compare_node_ids(root1, root2);
            if c != 0 {
                return c;
            }
            let c = compare_type_mappers(mapper1, mapper2);
            if c != 0 {
                return c;
            }
        }
        _ if flags.intersects(TypeFlags::SUBSTITUTION) => {
            let (base1, constraint1) = {
                let t = types.get(t1);
                let t = t.as_substitution_type();
                (t.base_type, t.constraint)
            };
            let (base2, constraint2) = {
                let t = types.get(t2);
                let t = t.as_substitution_type();
                (t.base_type, t.constraint)
            };
            let c = compare_types_opt(types, base1, base2);
            if c != 0 {
                return c;
            }
            let c = compare_types_opt(types, constraint1, constraint2);
            if c != 0 {
                return c;
            }
        }
        _ if flags.intersects(TypeFlags::TEMPLATE_LITERAL) => {
            let (texts1, types1) = {
                let t = types.get(t1);
                let t = t.as_template_literal_type();
                (t.texts.clone(), t.types.clone())
            };
            let (texts2, types2) = {
                let t = types.get(t2);
                let t = t.as_template_literal_type();
                (t.texts.clone(), t.types.clone())
            };
            let c = texts1.cmp(&texts2);
            if c != std::cmp::Ordering::Equal {
                return c as i32 - 1;
            }
            let c = compare_type_lists(types, &types1, &types2);
            if c != 0 {
                return c;
            }
        }
        _ if flags.intersects(TypeFlags::STRING_MAPPING) => {
            let target1 = types.get(t1).as_string_mapping_type().target;
            let target2 = types.get(t2).as_string_mapping_type().target;
            let c = compare_types_opt(types, target1, target2);
            if c != 0 {
                return c;
            }
        }
        _ => {}
    }
    // Fall back to type IDs. This results in type creation order for
    // built-in types.
    t1.0 as i64 as i32 - t2.0 as i64 as i32
}
