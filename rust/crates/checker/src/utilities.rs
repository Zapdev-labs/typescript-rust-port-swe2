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
// PORT(approximation) — `compare_types` takes `&TypeArena` plus the symbol
// arena (`&RefCell<Vec<ast::Symbol>>`); node ordering uses `NodeId`
// ordering (`file_index << 44 | local_index`, which approximates Go's
// `fileIndexMap[s]` + `Pos()` order because files are indexed in program
// order and nodes are allocated in source order), and the instantiation-
// expression declaration comparison treats declarations as absent (see
// the OBJECT branch).

use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::OnceLock;

use tsc_ast::{self as ast, NodeId, SymbolId, SymbolTable};
use tsc_collections::OrderedMap;
use tsc_core::core as core_helpers;
use tsc_core::text::TextRange;
use tsc_diagnostics as diagnostics;
use tsc_evaluator as evaluator;

use crate::checker_core::Checker;
use crate::mapper::{TypeMapperArena, TypeMapperData, TypeMapperId, TypeMapperKind};
use crate::types::{ElementFlags, ObjectFlags, Signature, TupleType, TypeArena, TypeFlags, TypeId};

// Re-exports so `crate::utilities::<name>` resolves for helpers committed to
// checker_core.rs / checker_c.rs / types.rs before this file landed.
pub(crate) use crate::checker_c::get_end_element_count;
pub use crate::checker_core::{
    create_symbol_table, is_object_or_array_literal_type, is_this_type_parameter, is_tuple_type,
    value_to_string,
};
pub use crate::types::{
    is_error_type, is_object_literal_type, is_type_any, is_type_usable_as_property_name,
};
pub use tsc_ast::get_containing_function;

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
            file = Some(ast::diagnostic::DiagnosticFile::from_node(
                source_file,
                nodes,
            ));
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
            let __program = c.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
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
    let __program = c.program.clone().expect("program");
    let nodes = __program.nodes((decl).file_index());
    ast::is_private_identifier_class_element_declaration(&nodes[decl], &nodes)
        && ast::is_static(&nodes[decl])
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
            let binary_operator = nodes[target]
                .as_binary_expression()
                .operator_token
                .map(|t| nodes[t].kind);
            if binary_operator == Some(ast::Kind::EqualsToken)
                || binary_operator
                    .is_some_and(|op| op.is_logical_or_coalescing_assignment_operator())
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
    if !ast::is_access_expression(&nodes[node]) {
        return false;
    }
    // Go: `node = ast.WalkUpParenthesizedExpressions(node.Parent)` — the walk
    // returns the topmost node itself, not its parent.
    nodes[node]
        .parent
        .and_then(|p| ast::walk_up_parenthesized_expressions(p, nodes))
        .is_some_and(|n| nodes[n].kind == ast::Kind::DeleteExpression)
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
        && nodes[right]
            .as_binary_expression()
            .operator_token
            .is_some_and(|t| nodes[t].kind.is_shift_operator_or_higher())
}

/// `isConstTypeReference`. Committed call sites pass a `NodeId`; the body
/// needs the arena for the type-name text anyway.
pub(crate) fn is_const_type_reference(node: NodeId, nodes: &[ast::Node]) -> bool {
    ast::is_type_reference_node(&nodes[node])
        && nodes[node].type_arguments().map_or(0, |t| t.len()) == 0
        && nodes[node]
            .as_type_reference_node()
            .type_name
            .is_some_and(|tn| ast::is_identifier(&nodes[tn]) && &*nodes[tn].text(nodes) == "const")
}

/// `isConstTypeReferenceName` — whether `node` is the `const` type name of a
/// `const` assertion (`x as const` / `<const>x`), which must not be resolved
/// as a real name.
pub(crate) fn is_const_type_reference_name(node: Option<NodeId>, nodes: &[ast::Node]) -> bool {
    let Some(node) = node else { return false };
    ast::is_identifier(&nodes[node])
        && nodes[node].parent.is_some_and(|p| {
            is_const_type_reference(p, nodes)
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
    let Some(mut current) = node else {
        return false;
    };
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
            let __program = c.program.clone().expect("program");
            let nodes = __program.nodes((decl).file_index());
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
pub(crate) fn get_alias_declaration_from_name(node: NodeId, nodes: &[ast::Node]) -> Option<NodeId> {
    let parent = nodes[node].parent?;
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
}

/// `entityNameToString` — `ast.EntityNameToString(name, scanner.GetTextOfNode)`.
pub(crate) fn entity_name_to_string(name: NodeId, nodes: &[ast::Node]) -> String {
    ast::entity_name_to_string(
        name,
        nodes,
        Some(&mut |nodes, id| tsc_scanner::utilities::get_text_of_node(id, nodes)),
    )
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
            && nodes[parent]
                .as_element_access_expression()
                .argument_expression
                == Some(node))
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
        .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
        .is_some()
}

/// `isTypeAlias` — `ast.IsTypeOrJSTypeAliasDeclaration` is inlined as the
/// two generated predicates (there is no combined helper in tsc-ast).
pub(crate) fn is_type_alias(node: &ast::Node) -> bool {
    ast::is_type_alias_declaration(node) || ast::is_js_type_alias_declaration(node)
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

/// `hasDotDotDotToken`. The `nodes` arena is unused (the body only reads the
/// node's own fields, matching Go) but committed call sites pass it.
pub(crate) fn has_dot_dot_dot_token(node: &ast::Node, _nodes: &[ast::Node]) -> bool {
    match node.kind {
        ast::Kind::Parameter => node.as_parameter_declaration().dot_dot_dot_token.is_some(),
        ast::Kind::BindingElement => node.as_binding_element().dot_dot_dot_token.is_some(),
        ast::Kind::NamedTupleMember => node.as_named_tuple_member().dot_dot_dot_token.is_some(),
        ast::Kind::JsxExpression => node.as_jsx_expression().dot_dot_dot_token.is_some(),
        _ => false,
    }
}

// `IsTypeAny` is re-exported from `crate::types` (canonical definition,
// needed by `crate::types::is_type_any` call sites too).

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
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if ast::is_parameter_declaration(&nodes[node])
            && nodes[node].question_token(&nodes).is_some()
        {
            return true;
        }
        if !ast::is_parameter_declaration(&nodes[node]) {
            return false;
        }
        if nodes[node].initializer().is_some() {
            let parent = nodes[node].parent.expect("parameter parent");
            let signature = self.get_signature_from_declaration(parent);
            let parameter_index =
                core_helpers::find_index(nodes[parent].parameters().unwrap_or(&[]), |&p| p == node);
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
            let parameter_index =
                core_helpers::find_index(nodes[parent].parameters().unwrap_or(&[]), |&p| p == node);
            return nodes[node].type_().is_none()
                && nodes[node]
                    .as_parameter_declaration()
                    .dot_dot_dot_token
                    .is_none()
                && parameter_index >= self.get_effective_call_arguments(iife).len() as i32;
        }
        false
    }

    /// `(c *Checker) isUncheckedJSSuggestion` (checker/utilities.go).
    pub(crate) fn is_unchecked_js_suggestion(
        &mut self,
        node: Option<NodeId>,
        suggestion: Option<SymbolId>,
        exclude_classes: bool,
    ) -> bool {
        let Some(node) = node else {
            return false;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let file = ast::get_source_file_of_node(Some(node), &nodes);
        if let Some(file) = file {
            let sf = nodes[file].as_source_file();
            if self.compiler_options.check_js.is_unknown()
                && sf.check_js_directive.is_none()
                && (sf.script_kind == tsc_core::scriptkind::ScriptKind::Js
                    || sf.script_kind == tsc_core::scriptkind::ScriptKind::Jsx)
            {
                let mut declaration_file: Option<NodeId> = None;
                if let Some(suggestion) = suggestion {
                    let declarations = {
                        self.symbol_arena.borrow()[suggestion.index()]
                            .declarations
                            .clone()
                    };
                    if let Some(&first_declaration) = declarations.first() {
                        declaration_file = ast::get_source_file_of_node(
                            Some(first_declaration),
                            &self.program_nodes(first_declaration),
                        );
                    }
                }
                let suggestion_has_no_extends_or_decorators = suggestion.is_none_or(|s| {
                    let value_declaration = self.symbol_arena.borrow()[s.index()].value_declaration;
                    value_declaration.is_none_or(|vd| {
                        let __program = self.program.clone().expect("program");
                        let vd_nodes = __program.nodes((vd).file_index());
                        !ast::is_class_like(Some(vd), &vd_nodes)
                            || ast::get_extends_heritage_clause_elements(&vd_nodes[vd], &vd_nodes)
                                .map_or(0, |e| e.len())
                                != 0
                            || ast::class_or_constructor_parameter_is_decorated(
                                false, vd, &vd_nodes,
                            )
                    })
                });
                return !(declaration_file.is_some_and(|df| {
                    df != file && {
                        let __program = self.program.clone().expect("program");
                        let df_nodes = __program.nodes((df).file_index());
                        ast::is_global_source_file(&df_nodes[df], &df_nodes)
                    }
                })) && !(exclude_classes
                    && suggestion.is_some_and(|s| {
                        self.symbol_arena.borrow()[s.index()]
                            .flags
                            .intersects(ast::SymbolFlags::CLASS)
                    })
                    && suggestion_has_no_extends_or_decorators)
                    && !(exclude_classes
                        && ast::is_property_access_expression(&nodes[node])
                        && nodes[node]
                            .expression()
                            .is_some_and(|e| nodes[e].kind == ast::Kind::ThisKeyword)
                        && suggestion_has_no_extends_or_decorators);
            }
        }
        false
    }

    /// `(c *Checker) isJSLiteralType` (checker/utilities.go).
    /// Returns if a type is or consists of a JSLiteral object type:
    /// directly literals, unions where every element is a jsliteral,
    /// intersections where at least one element is a jsliteral, and
    /// instantiable types constrained to a jsliteral.
    pub(crate) fn is_js_literal_type(&mut self, t: TypeId) -> bool {
        if self.no_implicit_any {
            // Flag is meaningless under `noImplicitAny` mode
            return false;
        }
        let flags;
        let object_flags;
        {
            let __arena_g = self.types.clone();
            let g = __arena_g.get(t);
            flags = g.flags();
            object_flags = g.object_flags();
        }
        if object_flags.intersects(ObjectFlags::JS_LITERAL) {
            return true;
        }
        if flags.intersects(TypeFlags::UNION) {
            let types = {
                self.types_handle()
                    .get(t)
                    .as_union_type()
                    .union_or_intersection
                    .types
                    .clone()
            };
            return types.iter().all(|&m| self.is_js_literal_type(m));
        }
        if flags.intersects(TypeFlags::INTERSECTION) {
            let types = {
                self.types_handle()
                    .get(t)
                    .as_intersection_type()
                    .union_or_intersection
                    .types
                    .clone()
            };
            return types.iter().any(|&m| self.is_js_literal_type(m));
        }
        if flags.intersects(TypeFlags::INSTANTIABLE) {
            let constraint = self.get_resolved_base_constraint(t, &mut Vec::new());
            return constraint != t && self.is_js_literal_type(constraint);
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
        || ast::is_private_identifier_class_element_declaration(node, _nodes))
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
pub fn compare_types(
    types: &TypeArena,
    symbols: &RefCell<Vec<ast::Symbol>>,
    mappers: &TypeMapperArena,
    program: Option<&Rc<dyn crate::checker_types::Program>>,
    t1: TypeId,
    t2: TypeId,
) -> i32 {
    compare_types_opt(types, symbols, mappers, program, Some(t1), Some(t2))
}

fn compare_types_opt(
    types: &TypeArena,
    symbols: &RefCell<Vec<ast::Symbol>>,
    mappers: &TypeMapperArena,
    program: Option<&Rc<dyn crate::checker_types::Program>>,
    t1: Option<TypeId>,
    t2: Option<TypeId>,
) -> i32 {
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
    let c = get_sort_order_flags(flags1) as i32 - get_sort_order_flags(flags2) as i32;
    if c != 0 {
        return c;
    }
    // Order named types by name and, in the case of aliased types, by alias
    // type arguments.
    let c = compare_type_names(types, symbols, mappers, program, t1, t2);
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
                let (declaration1, declaration2) = {
                    let syms = symbols.borrow();
                    let decl = |s: Option<SymbolId>| {
                        s.and_then(|s| syms[s.index()].declarations.first().copied())
                    };
                    (decl(types.get(t1).symbol), decl(types.get(t2).symbol))
                };
                // A single instantiation expression can produce multiple
                // types for union constituents, so compare their source
                // declarations before comparing the shared expression node.
                let c = compare_node_ids(declaration1, declaration2, program);
                if c != 0 {
                    return c;
                }
                let c = compare_node_ids(
                    types.get(t1).as_instantiation_expression_type().node,
                    types.get(t2).as_instantiation_expression_type().node,
                    program,
                );
                if c != 0 {
                    return c;
                }
            } else {
                let c = compare_symbols(
                    symbols,
                    program,
                    types.get(t1).symbol,
                    types.get(t2).symbol,
                );
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
                    (r.object_type.target, r.node)
                };
                let (target2, node2) = {
                    let r = types.get(t2);
                    let r = r.as_type_reference();
                    (r.object_type.target, r.node)
                };
                let tuple1 = target1
                    .is_some_and(|t| types.get(t).object_flags.intersects(ObjectFlags::TUPLE));
                let tuple2 = target2
                    .is_some_and(|t| types.get(t).object_flags.intersects(ObjectFlags::TUPLE));
                if tuple1 && tuple2 {
                    // Tuple types have no associated symbol, instead we order
                    // by tuple element information.
                    let c = compare_tuple_types(
                        program,
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
                        symbols,
                        mappers,
                        program,
                        &types.get(t1).as_type_reference().resolved_type_arguments,
                        &types.get(t2).as_type_reference().resolved_type_arguments,
                    );
                    if c != 0 {
                        return c;
                    }
                } else {
                    // Deferred type references with the same target are
                    // ordered by the source location of the reference.
                    let c = compare_node_ids(node1, node2, program);
                    if c != 0 {
                        return c;
                    }
                    // Instantiations of the same deferred type reference are
                    // ordered by their associated type mappers (which reflect
                    // the mapping of in-scope type parameters to type
                    // arguments).
                    let c = compare_type_mappers(
                        types,
                        symbols,
                        mappers,
                        program,
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
                let c = (object_flags1 & ObjectFlags::OBJECT_TYPE_KIND_MASK)
                    .0
                    .cmp(&(object_flags2 & ObjectFlags::OBJECT_TYPE_KIND_MASK).0)
                    as i32;
                if c != 0 {
                    return c;
                }
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
                    let c = compare_types_opt(types, symbols, mappers, program, source1, source2);
                    if c != 0 {
                        return c;
                    }
                    let c = compare_types_opt(types, symbols, mappers, program, mapped1, mapped2);
                    if c != 0 {
                        return c;
                    }
                    let c = compare_types_opt(types, symbols, mappers, program, constraint1, constraint2);
                    if c != 0 {
                        return c;
                    }
                }
                let mut m1 = types.get(t1).as_object_type().mapper;
                let mut m2 = types.get(t2).as_object_type().mapper;
                if object_flags1.intersects(ObjectFlags::MAPPED) {
                    // `instantiateAnonymousType` prepends a fresh type parameter
                    // mapping. Compare the effective instantiation, not the
                    // identity of that fresh parameter.
                    if let Some(m) = m1 {
                        m1 = mappers.with_data(m, |d| match d {
                            TypeMapperData::Composite(s) => Some(s.m2),
                            _ => m1,
                        });
                    }
                    if let Some(m) = m2 {
                        m2 = mappers.with_data(m, |d| match d {
                            TypeMapperData::Composite(s) => Some(s.m2),
                            _ => m2,
                        });
                    }
                }
                let c = compare_type_mappers(types, symbols, mappers, program, m1, m2);
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
                    let c = compare_type_lists(types, symbols, mappers, program, &types1, &types2);
                    if c != 0 {
                        return c;
                    }
                }
                (None, Some(_)) => return 1,
                (Some(_), None) => return -1,
                (Some(o1), Some(o2)) => {
                    let c = compare_types(types, symbols, mappers, program, o1, o2);
                    if c != 0 {
                        return c;
                    }
                }
            }
        }
        _ if flags.intersects(TypeFlags::INTERSECTION) => {
            // Intersections are ordered by their constituent type lists.
            let c =
                compare_type_lists(types, symbols, mappers, program, types.get(t1).types(), types.get(t2).types());
            if c != 0 {
                return c;
            }
        }
        _ if flags.intersects(
            TypeFlags::ENUM | TypeFlags::ENUM_LITERAL | TypeFlags::UNIQUE_ES_SYMBOL,
        ) =>
        {
            // Enum members are ordered by their symbol (and thus their
            // declaration order).
            let c = compare_symbols(
                symbols,
                program,
                types.get(t1).symbol,
                types.get(t2).symbol,
            );
            if c != 0 {
                return c;
            }
        }
        _ if flags.intersects(TypeFlags::STRING_LITERAL) => {
            // String literal types are ordered by their values.
            let g1 = types.get(t1);
            let g2 = types.get(t2);
            let v1 = literal_string(g1.as_literal_type().value.as_ref());
            let v2 = literal_string(g2.as_literal_type().value.as_ref());
            let c = v1.cmp(v2);
            if c != std::cmp::Ordering::Equal {
                return c as i32;
            }
        }
        _ if flags.intersects(TypeFlags::NUMBER_LITERAL) => {
            // Numeric literal types are ordered by their values.
            let v1 = literal_number(types.get(t1).as_literal_type().value.as_ref());
            let v2 = literal_number(types.get(t2).as_literal_type().value.as_ref());
            // PORT: `jsnum.Number` is `PartialOrd` (NaN compares unordered);
            // Go's `cmp.Compare` puts NaN before everything, so treat
            // unordered as less-than for a total order.
            let c = v1
                .partial_cmp(&v2)
                .map(|o| o as i32)
                .unwrap_or_else(|| if v1 == v2 { 0 } else { -1 });
            if c != 0 {
                return c;
            }
        }
        _ if flags.intersects(TypeFlags::BIG_INT_LITERAL) => {
            let c = crate::checker_d::get_big_int_literal_value(types, t1)
                .compare(&crate::checker_d::get_big_int_literal_value(types, t2));
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
            let c = compare_symbols(
                symbols,
                program,
                types.get(t1).symbol,
                types.get(t2).symbol,
            );
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
            let c = compare_types_opt(types, symbols, mappers, program, target1, target2);
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
            let c = compare_types_opt(types, symbols, mappers, program, object1, object2);
            if c != 0 {
                return c;
            }
            let c = compare_types_opt(types, symbols, mappers, program, index1, index2);
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
            let c = compare_node_ids(root1, root2, program);
            if c != 0 {
                return c;
            }
            let c = compare_type_mappers(types, symbols, mappers, program, mapper1, mapper2);
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
            let c = compare_types_opt(types, symbols, mappers, program, base1, base2);
            if c != 0 {
                return c;
            }
            let c = compare_types_opt(types, symbols, mappers, program, constraint1, constraint2);
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
                return c as i32;
            }
            let c = compare_type_lists(types, symbols, mappers, program, &types1, &types2);
            if c != 0 {
                return c;
            }
        }
        _ if flags.intersects(TypeFlags::STRING_MAPPING) => {
            let target1 = types.get(t1).as_string_mapping_type().target;
            let target2 = types.get(t2).as_string_mapping_type().target;
            let c = compare_types_opt(types, symbols, mappers, program, target1, target2);
            if c != 0 {
                return c;
            }
        }
        _ => {}
    }
    // Fall back to type IDs. This results in type creation order for
    // built-in types.
    t1.0.cmp(&t2.0) as i32
}

/// `getSortOrderFlags` — TypeFlagsEnum for all enum-like unit types (they're
/// sorted by their symbols).
fn get_sort_order_flags(flags: TypeFlags) -> u32 {
    if flags.intersects(TypeFlags::ENUM_LITERAL | TypeFlags::ENUM)
        && !flags.intersects(TypeFlags::UNION)
    {
        return TypeFlags::ENUM.0;
    }
    flags.0
}

/// `compareTypeNames` — order named types by name and, in the case of
/// aliased types, by alias type arguments.
fn compare_type_names(
    types: &TypeArena,
    symbols: &RefCell<Vec<ast::Symbol>>,
    mappers: &TypeMapperArena,
    program: Option<&Rc<dyn crate::checker_types::Program>>,
    t1: TypeId,
    t2: TypeId,
) -> i32 {
    let s1 = get_type_name_symbol(&types.get(t1));
    let s2 = get_type_name_symbol(&types.get(t2));
    if s1 == s2 {
        return compare_type_lists(
            types,
            symbols,
            mappers,
            program,
            types
                .get(t1)
                .alias
                .as_ref()
                .map_or(&[][..], |a| &a.type_arguments),
            types
                .get(t2)
                .alias
                .as_ref()
                .map_or(&[][..], |a| &a.type_arguments),
        );
    }
    let Some(s1) = s1 else { return 1 };
    let Some(s2) = s2 else { return -1 };
    let c = {
        let syms = symbols.borrow();
        syms[s1.index()].name.cmp(&syms[s2.index()].name) as i32
    };
    if c != 0 {
        return c;
    }
    // Keep distinct same-named declarations together before comparing
    // alias arguments or structure.
    compare_symbols(symbols, program, Some(s1), Some(s2))
}

/// `compareSymbolsWorker` (checker/utilities.go) — declaration position
/// (program file order, then pos), then name, then symbol id.
fn compare_symbols(
    symbols: &RefCell<Vec<ast::Symbol>>,
    program: Option<&Rc<dyn crate::checker_types::Program>>,
    s1: Option<SymbolId>,
    s2: Option<SymbolId>,
) -> i32 {
    if s1 == s2 {
        return 0;
    }
    let Some(s1) = s1 else { return 1 };
    let Some(s2) = s2 else { return -1 };
    let (decl1, decl2, name_ord) = {
        let syms = symbols.borrow();
        (
            syms[s1.index()].declarations.first().copied(),
            syms[s2.index()].declarations.first().copied(),
            syms[s1.index()].name.cmp(&syms[s2.index()].name) as i32,
        )
    };
    match (decl1, decl2) {
        (Some(d1), Some(d2)) => {
            let c = compare_node_ids(Some(d1), Some(d2), program);
            if c != 0 {
                return c;
            }
        }
        (Some(_), None) => return -1,
        (None, Some(_)) => return 1,
        (None, None) => {}
    }
    if name_ord != 0 {
        return name_ord;
    }
    // Fall back to symbol IDs — only for declaration-less duplicate names.
    s1.index().cmp(&s2.index()) as i32
}

/// `getTypeNameSymbol`.
fn get_type_name_symbol(t: &crate::types::Type) -> Option<SymbolId> {
    if let Some(alias) = &t.alias {
        return alias.symbol;
    }
    if t.flags
        .intersects(TypeFlags::TYPE_PARAMETER | TypeFlags::STRING_MAPPING)
        || t.object_flags
            .intersects(ObjectFlags::CLASS_OR_INTERFACE | ObjectFlags::REFERENCE)
    {
        return t.symbol;
    }
    None
}

/// `getObjectTypeName`.
pub(crate) fn get_object_type_name(t: &crate::types::Type) -> Option<SymbolId> {
    if t.object_flags
        .intersects(ObjectFlags::CLASS_OR_INTERFACE | ObjectFlags::REFERENCE)
    {
        return t.symbol;
    }
    None
}

/// `compareTupleTypes` — `elementInfos` field order.
fn compare_tuple_types(
    program: Option<&Rc<dyn crate::checker_types::Program>>,
    t1: &crate::types::TupleType,
    t2: &crate::types::TupleType,
) -> i32 {
    if std::ptr::eq(t1, t2) {
        return 0;
    }
    if t1.readonly != t2.readonly {
        return if t1.readonly { 1 } else { -1 };
    }
    if t1.element_infos.len() != t2.element_infos.len() {
        return t1.element_infos.len().cmp(&t2.element_infos.len()) as i32;
    }
    for (i1, i2) in t1.element_infos.iter().zip(t2.element_infos.iter()) {
        let c = i1.flags.0.cmp(&i2.flags.0) as i32;
        if c != 0 {
            return c;
        }
    }
    for (i1, i2) in t1.element_infos.iter().zip(t2.element_infos.iter()) {
        // compareElementLabels: nil sorts first (unlike compareNodes).
        let c = compare_element_labels(program, i1.labeled_declaration, i2.labeled_declaration);
        if c != 0 {
            return c;
        }
    }
    0
}

/// `compareElementLabels` — `n1 == nil → -1` (labels sort before named),
/// then `strings.Compare(n1.Name().Text(), n2.Name().Text())`.
fn compare_element_labels(
    program: Option<&Rc<dyn crate::checker_types::Program>>,
    n1: Option<NodeId>,
    n2: Option<NodeId>,
) -> i32 {
    if n1 == n2 {
        return 0;
    }
    let Some(n1) = n1 else { return -1 };
    let Some(n2) = n2 else { return 1 };
    let label_text = |n: NodeId| -> Option<String> {
        let nodes = program?.nodes(n.file_index());
        let name = nodes[n].name()?;
        Some(nodes[name].text(&nodes).into_owned())
    };
    match (label_text(n1), label_text(n2)) {
        (Some(a), Some(b)) => a.cmp(&b) as i32,
        // Fallback when the program is unavailable: keep the old NodeId
        // ordering so sorting stays deterministic.
        _ => n1.0.cmp(&n2.0) as i32,
    }
}

/// `compareTypeLists`.
fn compare_type_lists(
    types: &TypeArena,
    symbols: &RefCell<Vec<ast::Symbol>>,
    mappers: &TypeMapperArena,
    program: Option<&Rc<dyn crate::checker_types::Program>>,
    s1: &[TypeId],
    s2: &[TypeId],
) -> i32 {
    if s1.len() != s2.len() {
        return s1.len().cmp(&s2.len()) as i32;
    }
    for (&t1, &t2) in s1.iter().zip(s2.iter()) {
        let c = compare_types(types, symbols, mappers, program, t1, t2);
        if c != 0 {
            return c;
        }
    }
    0
}

/// `compareTypeMappers`.
fn compare_type_mappers(
    types: &TypeArena,
    symbols: &RefCell<Vec<ast::Symbol>>,
    mappers: &TypeMapperArena,
    program: Option<&Rc<dyn crate::checker_types::Program>>,
    m1: Option<TypeMapperId>,
    m2: Option<TypeMapperId>,
) -> i32 {
    if m1 == m2 {
        return 0;
    }
    let Some(m1) = m1 else { return 1 };
    let Some(m2) = m2 else { return -1 };
    let kind1 = mappers.kind(m1);
    let kind2 = mappers.kind(m2);
    if kind1 != kind2 {
        return kind1 as i32 - kind2 as i32;
    }
    match kind1 {
        TypeMapperKind::Simple => {
            let (s1, t1) = mappers.with_data(m1, |d| match d {
                TypeMapperData::Simple(s) => (s.source, s.target),
                _ => unreachable!(),
            });
            let (s2, t2) = mappers.with_data(m2, |d| match d {
                TypeMapperData::Simple(s) => (s.source, s.target),
                _ => unreachable!(),
            });
            let c = compare_types(types, symbols, mappers, program, s1, s2);
            if c != 0 {
                return c;
            }
            compare_types(types, symbols, mappers, program, t1, t2)
        }
        TypeMapperKind::Array => {
            let (src1, tgt1) = mappers.with_data(m1, |d| match d {
                TypeMapperData::Array(s) => (s.sources.clone(), s.targets.clone()),
                _ => unreachable!(),
            });
            let (src2, tgt2) = mappers.with_data(m2, |d| match d {
                TypeMapperData::Array(s) => (s.sources.clone(), s.targets.clone()),
                _ => unreachable!(),
            });
            let c = compare_type_lists(types, symbols, mappers, program, &src1, &src2);
            if c != 0 {
                return c;
            }
            compare_type_lists(types, symbols, mappers, program, &tgt1, &tgt2)
        }
        TypeMapperKind::Merged => {
            let (a1, b1) = mappers.with_data(m1, |d| match d {
                TypeMapperData::Merged(s) => (s.m1, s.m2),
                _ => unreachable!(),
            });
            let (a2, b2) = mappers.with_data(m2, |d| match d {
                TypeMapperData::Merged(s) => (s.m1, s.m2),
                _ => unreachable!(),
            });
            let c = compare_type_mappers(types, symbols, mappers, program, Some(a1), Some(a2));
            if c != 0 {
                return c;
            }
            compare_type_mappers(types, symbols, mappers, program, Some(b1), Some(b2))
        }
        _ => 0,
    }
}

/// `compareNodes` (checker/utilities.go:392) — order by containing file's
/// index in program order (`fileIndexMap`), then source position. Falls back
/// to raw `NodeId` ordering when no program is available.
fn compare_node_ids(
    n1: Option<NodeId>,
    n2: Option<NodeId>,
    program: Option<&Rc<dyn crate::checker_types::Program>>,
) -> i32 {
    if n1 == n2 {
        return 0;
    }
    let Some(n1) = n1 else { return 1 };
    let Some(n2) = n2 else { return -1 };
    let Some(program) = program else {
        return n1.0.cmp(&n2.0) as i32;
    };
    let nodes = program.nodes(n1.file_index());
    let s1 = ast::get_source_file_of_node(Some(n1), &nodes);
    let nodes2 = program.nodes(n2.file_index());
    let s2 = ast::get_source_file_of_node(Some(n2), &nodes2);
    match (s1, s2) {
        (Some(s1), Some(s2)) => {
            if s1 != s2 {
                let f1 = program.file_rank(s1).unwrap_or(0) as i64;
                let f2 = program.file_rank(s2).unwrap_or(0) as i64;
                // Order by index of file in the containing program
                return (f1 - f2) as i32;
            }
            // In the same file, order by source position
            nodes[n1].pos() - nodes[n2].pos()
        }
        // PORT(fallback): nodes without a resolvable source file keep the
        // previous raw-`NodeId` ordering.
        _ => n1.0.cmp(&n2.0) as i32,
    }
}

/// Extract the `evaluator::Value::String` payload of a literal type.
fn literal_string(value: Option<&evaluator::Value>) -> &str {
    match value {
        Some(evaluator::Value::String(s)) => s.as_str(),
        _ => panic!("literal_string: not a string literal"),
    }
}

/// Extract the `evaluator::Value::Number` payload of a literal type.
fn literal_number(value: Option<&evaluator::Value>) -> tsc_jsnum::Number {
    match value {
        Some(evaluator::Value::Number(n)) => *n,
        _ => panic!("literal_number: not a number literal"),
    }
}

/// Extract the `evaluator::Value::Bool` payload of a literal type.
fn literal_bool(value: Option<&evaluator::Value>) -> bool {
    match value {
        Some(evaluator::Value::Bool(b)) => *b,
        _ => panic!("literal_bool: not a boolean literal"),
    }
}

// `isTypeUsableAsPropertyName` (utilities.go:922) is re-exported from
// `crate::types` (canonical definition, needed by `crate::types::` call
// sites too).

/// `isNumericLiteralName` (utilities.go:941) — tests whether
/// `'ToString(ToNumber(name))'` is exactly equal to `name` (accepts
/// `Infinity`, `-Infinity`, and `NaN`, matching Go's `jsnum.FromString`).
pub(crate) fn is_numeric_literal_name(name: &str) -> bool {
    tsc_jsnum::from_string(name).to_string() == name
}

/// `pseudoBigIntToString` (utilities.go:1228).
pub(crate) fn pseudo_big_int_to_string(value: tsc_jsnum::PseudoBigInt) -> String {
    value.string()
}

/// `isLateBoundName` (utilities.go:1028).
pub(crate) fn is_late_bound_name(name: &str) -> bool {
    // Go: `len(name) >= 2 && name[0] == '\xfe' && name[1] == '@'`.
    name.starts_with("\u{FFFD}@")
}

/// `IsKnownSymbol` (utilities.go:1018).
pub fn is_known_symbol(c: &Checker, s: SymbolId) -> bool {
    is_late_bound_name(&c.symbol_arena.borrow()[s.index()].name)
}

/// `isRestParameter` (checker.go:28326) — `param.AsParameterDeclaration().DotDotDotToken != nil`.
pub(crate) fn is_rest_parameter(param: &ast::Node, _nodes: &[ast::Node]) -> bool {
    param.as_parameter_declaration().dot_dot_dot_token.is_some()
}

/// `hasRestParameter` (checker.go:28321).
pub(crate) fn has_rest_parameter_node(signature: &ast::Node, nodes: &[ast::Node]) -> bool {
    signature
        .parameters()
        .and_then(|p| p.last())
        .is_some_and(|last| is_rest_parameter(&nodes[*last], nodes))
}

/// `forEachYieldExpression` (checker/utilities.go:1264).
pub(crate) fn for_each_yield_expression(
    body: NodeId,
    nodes: &[ast::Node],
    visitor: &mut dyn FnMut(NodeId) -> bool,
) -> bool {
    fn traverse(
        node: NodeId,
        nodes: &[ast::Node],
        visitor: &mut dyn FnMut(NodeId) -> bool,
    ) -> bool {
        match nodes[node].kind {
            ast::Kind::YieldExpression => {
                if visitor(node) {
                    return true;
                }
                match nodes[node].expression() {
                    None => false,
                    Some(operand) => traverse(operand, nodes, visitor),
                }
            }
            // These are not allowed inside a generator now, but eventually
            // they may be allowed as local types. Regardless, skip them to
            // avoid the work.
            ast::Kind::EnumDeclaration
            | ast::Kind::InterfaceDeclaration
            | ast::Kind::ModuleDeclaration
            | ast::Kind::TypeAliasDeclaration => false,
            _ => {
                if ast::is_function_like(Some(node), nodes) {
                    // Do not descend into functions. Note that we will not
                    // include methods/accessors of a class because they would
                    // require first descending into the class. This is by
                    // design.
                    if let Some(name) = nodes[node].name()
                        && ast::is_computed_property_name(&nodes[name])
                    {
                        if let Some(expr) = nodes[name].expression() {
                            return traverse(expr, nodes, visitor);
                        }
                    }
                    false
                } else if !ast::is_part_of_type_node(node, nodes) {
                    // This is the general case, which should include mostly
                    // expressions and statements. Also includes NodeArrays.
                    nodes[node].for_each_child(nodes, &mut |c| traverse(c, nodes, visitor))
                } else {
                    false
                }
            }
        }
    }
    traverse(body, nodes, visitor)
}

/// `nodeStartsNewLexicalEnvironment` (utilities.go:1763).
pub(crate) fn node_starts_new_lexical_environment(node: NodeId, nodes: &[ast::Node]) -> bool {
    matches!(
        nodes[node].kind,
        ast::Kind::Constructor
            | ast::Kind::FunctionExpression
            | ast::Kind::FunctionDeclaration
            | ast::Kind::ArrowFunction
            | ast::Kind::MethodDeclaration
            | ast::Kind::GetAccessor
            | ast::Kind::SetAccessor
            | ast::Kind::ModuleDeclaration
            | ast::Kind::SourceFile
    )
}

/// `isInNameOfExpressionWithTypeArgumentsOrHeritageTypeReference`
/// (utilities.go:1188).
pub(crate) fn is_in_name_of_expression_with_type_arguments_or_heritage_type_reference(
    node: NodeId,
    nodes: &[ast::Node],
) -> bool {
    let mut node = node;
    while matches!(
        nodes[nodes[node].parent.unwrap()].kind,
        ast::Kind::PropertyAccessExpression | ast::Kind::QualifiedName
    ) {
        node = nodes[node].parent.unwrap();
    }
    let parent = nodes[node].parent.unwrap();
    nodes[parent].kind == ast::Kind::ExpressionWithTypeArguments
        || ast::is_name_of_heritage_clause_type_reference(node, nodes)
}

/// `isInRightSideOfImportOrExportAssignment` (utilities.go:1150).
pub(crate) fn is_in_right_side_of_import_or_export_assignment(
    mut node: NodeId,
    nodes: &[ast::Node],
) -> bool {
    while ast::is_qualified_name(&nodes[nodes[node].parent.unwrap()]) {
        node = nodes[node].parent.unwrap();
    }
    let parent = nodes[node].parent.unwrap();
    (nodes[parent].kind == ast::Kind::ImportEqualsDeclaration
        && nodes[parent]
            .as_import_equals_declaration()
            .module_reference
            == Some(node))
        || (nodes[parent].kind == ast::Kind::ExportAssignment
            && nodes[parent].expression() == Some(node))
}

/// `isJsxIntrinsicTagName` (utilities.go:1159).
pub(crate) fn is_jsx_intrinsic_tag_name(tag_name: NodeId, nodes: &[ast::Node]) -> bool {
    ast::is_identifier(&nodes[tag_name])
        && tsc_scanner::utilities::is_intrinsic_jsx_name(&nodes[tag_name].text(nodes))
        || ast::is_jsx_namespaced_name(&nodes[tag_name])
}

/// `isImportTypeQualifierPart` (utilities.go:1174).
pub(crate) fn is_import_type_qualifier_part(
    mut node: NodeId,
    nodes: &[ast::Node],
) -> Option<NodeId> {
    let mut parent = nodes[node].parent;
    while parent.is_some_and(|p| ast::is_qualified_name(&nodes[p])) {
        node = parent.unwrap();
        parent = nodes[node].parent;
    }
    let parent = parent?;
    if nodes[parent].kind == ast::Kind::ImportType
        && nodes[parent].as_import_type_node().qualifier == Some(node)
    {
        return Some(parent);
    }
    None
}

/// `getContainingObjectLiteral` (utilities.go:1165).
pub(crate) fn get_containing_object_literal(f: NodeId, nodes: &[ast::Node]) -> Option<NodeId> {
    let parent = nodes[f].parent?;
    if matches!(
        nodes[f].kind,
        ast::Kind::MethodDeclaration | ast::Kind::GetAccessor | ast::Kind::SetAccessor
    ) && nodes[parent].kind == ast::Kind::ObjectLiteralExpression
    {
        return Some(parent);
    }
    if nodes[f].kind == ast::Kind::FunctionExpression
        && nodes[parent].kind == ast::Kind::PropertyAssignment
    {
        return nodes[parent].parent;
    }
    None
}

/// `tryGetPropertyAccessOrIdentifierToString` (utilities.go:1613).
pub(crate) fn try_get_property_access_or_identifier_to_string(
    expr: NodeId,
    nodes: &[ast::Node],
) -> String {
    if ast::is_property_access_expression(&nodes[expr]) {
        if let Some(e) = nodes[expr].expression() {
            let base_str = try_get_property_access_or_identifier_to_string(e, nodes);
            if !base_str.is_empty() {
                if let Some(name) = nodes[expr].name() {
                    return format!(
                        "{}.{}",
                        base_str,
                        ast::entity_name_to_string(name, nodes, None)
                    );
                }
            }
        }
    } else if ast::is_element_access_expression(&nodes[expr]) {
        if let Some(e) = nodes[expr].expression() {
            let base_str = try_get_property_access_or_identifier_to_string(e, nodes);
            if !base_str.is_empty() {
                let argument = nodes[expr]
                    .as_element_access_expression()
                    .argument_expression;
                if let Some(argument) = argument {
                    if ast::is_property_name(&nodes[argument]) {
                        return format!(
                            "{}.{}",
                            base_str,
                            ast::get_property_name_for_property_name_node(argument, nodes)
                        );
                    }
                }
            }
        }
    } else if ast::is_identifier(&nodes[expr]) {
        return nodes[expr].text(nodes).into_owned();
    } else if ast::is_jsx_namespaced_name(&nodes[expr]) {
        return ast::entity_name_to_string(expr, nodes, None);
    }
    String::new()
}

/// `getBaseTypeNodeOfClass` (checker.go:19671).
pub(crate) fn get_base_type_node_of_class(c: &Checker, t: TypeId) -> Option<NodeId> {
    let __arena_symbol = c.types.clone();
    let symbol = __arena_symbol.get(t).symbol?;
    let __program = c.program.clone().expect("program");
    let decl = ast::get_class_like_declaration_of_symbol_with(&*c.sym(symbol), |d| {
        ast::is_class_like(Some(d), &__program.nodes(d.file_index()))
    })?;
    let nodes = __program.nodes((decl).file_index());

    ast::get_class_extends_heritage_element(&nodes[decl], &nodes)
}

// ===========================================================================
// getDeclarationModifierFlagsFromSymbol(Ex) (utilities.go:757)
// ===========================================================================
//
// Canonical port signature is `(c: &Checker, s: SymbolId)`: the checker is
// needed for `s.parent`'s flags (Go `s.Parent.Flags`) and to fetch each
// declaration's own per-file node arena (Go derefs `*ast.Node` pointers
// directly). Committed call sites that passed `(&Symbol, &[Node])` or a bare
// `&Symbol` were reconciled to this form.

/// `getDeclarationModifierFlagsFromSymbol` (utilities.go:757).
pub fn get_declaration_modifier_flags_from_symbol(c: &Checker, s: SymbolId) -> ast::ModifierFlags {
    get_declaration_modifier_flags_from_symbol_ex(c, s, false)
}

/// `getDeclarationModifierFlagsFromSymbolEx` (utilities.go:761).
pub(crate) fn get_declaration_modifier_flags_from_symbol_ex(
    c: &Checker,
    s: SymbolId,
    is_write: bool,
) -> ast::ModifierFlags {
    let (check_flags, symbol_flags, value_declaration, declarations, parent) = {
        let arena = c.symbol_arena.borrow();
        let sym = &arena[s.index()];
        (
            sym.check_flags,
            sym.flags,
            sym.value_declaration,
            sym.declarations.clone(),
            sym.parent,
        )
    };
    if check_flags.intersects(ast::checkflags::CheckFlags::SYNTHETIC) {
        let mut access_modifier = ast::ModifierFlags::NONE;
        if (!is_write && check_flags.intersects(ast::checkflags::CheckFlags::CONTAINS_PUBLIC))
            || (is_write
                && check_flags.intersects(ast::checkflags::CheckFlags::CONTAINS_WRITE_PUBLIC))
        {
            access_modifier = ast::ModifierFlags::PUBLIC;
        } else if (!is_write
            && check_flags.intersects(ast::checkflags::CheckFlags::CONTAINS_PROTECTED))
            || (is_write
                && check_flags.intersects(ast::checkflags::CheckFlags::CONTAINS_WRITE_PROTECTED))
        {
            access_modifier = ast::ModifierFlags::PROTECTED;
        } else if (!is_write
            && check_flags.intersects(ast::checkflags::CheckFlags::CONTAINS_PRIVATE))
            || (is_write
                && check_flags.intersects(ast::checkflags::CheckFlags::CONTAINS_WRITE_PRIVATE))
        {
            access_modifier = ast::ModifierFlags::PRIVATE;
        }
        if check_flags.intersects(ast::checkflags::CheckFlags::CONTAINS_STATIC) {
            return access_modifier | ast::ModifierFlags::STATIC;
        }
        return access_modifier;
    }
    if let Some(value_declaration) = value_declaration {
        let mut declaration: Option<NodeId> = None;
        if is_write {
            declaration = declarations.iter().copied().find(|&d| {
                let __program = c.program.clone().expect("program");
                let nodes = __program.nodes((d).file_index());
                ast::is_set_accessor_declaration(&nodes[d])
            });
        }
        if declaration.is_none() && symbol_flags.intersects(ast::SymbolFlags::GET_ACCESSOR) {
            declaration = declarations.iter().copied().find(|&d| {
                let __program = c.program.clone().expect("program");
                let nodes = __program.nodes((d).file_index());
                ast::is_get_accessor_declaration(&nodes[d])
            });
        }
        let declaration = declaration.unwrap_or(value_declaration);
        let __program = c.program.clone().expect("program");
        let nodes = __program.nodes((declaration).file_index());
        let flags = ast::get_combined_modifier_flags(declaration, &nodes);
        let parent_is_class = parent.is_some_and(|p| {
            c.symbol_arena.borrow()[p.index()]
                .flags
                .intersects(ast::SymbolFlags::CLASS)
        });
        if parent_is_class {
            return flags;
        }
        return flags & !ast::ModifierFlags::ACCESSIBILITY_MODIFIER;
    }
    if symbol_flags.intersects(ast::SymbolFlags::PROTOTYPE) {
        return ast::ModifierFlags::PUBLIC | ast::ModifierFlags::STATIC;
    }
    ast::ModifierFlags::NONE
}

// ===========================================================================
// Declaration / node helpers (utilities.go)
// ===========================================================================

/// `isDeclarationReadonly` (utilities.go:871).
pub(crate) fn is_declaration_readonly(declaration: NodeId, nodes: &[ast::Node]) -> bool {
    ast::get_combined_modifier_flags(declaration, nodes).intersects(ast::ModifierFlags::READONLY)
        && !ast::is_parameter_property_declaration(
            &nodes[declaration],
            &nodes[nodes[declaration].parent.expect("declaration parent")],
        )
}

/// `getContainingFunctionOrClassStaticBlock` (utilities.go:908).
pub(crate) fn get_containing_function_or_class_static_block(
    node: NodeId,
    nodes: &[ast::Node],
) -> Option<NodeId> {
    ast::find_ancestor(nodes[node].parent, nodes, &mut |n, nodes| {
        ast::is_function_like_or_class_static_block_declaration(Some(n.id), nodes)
    })
}

/// `isNodeDescendantOf` (utilities.go:912) — wraps
/// `ast::is_node_descendant_of` to accept either `NodeId` or
/// `Option<NodeId>` for committed call sites.
pub(crate) fn is_node_descendant_of(
    node: impl Into<Option<NodeId>>,
    ancestor: impl Into<Option<NodeId>>,
    nodes: &[ast::Node],
) -> bool {
    ast::is_node_descendant_of(node.into(), ancestor.into(), nodes)
}

/// `getPropertyNameFromType` (utilities.go:929). Gets the symbolic name for
/// a member from its type.
pub fn get_property_name_from_type(types: &TypeArena, t: TypeId) -> String {
    let ty = types.get(t);
    if ty.flags.intersects(TypeFlags::STRING_LITERAL) {
        if let Some(evaluator::Value::String(s)) = ty.as_literal_type().value.as_ref() {
            return s.clone();
        }
        panic!("getPropertyNameFromType: string literal without string value")
    }
    if ty.flags.intersects(TypeFlags::NUMBER_LITERAL) {
        if let Some(evaluator::Value::Number(n)) = ty.as_literal_type().value.as_ref() {
            return n.to_string();
        }
        panic!("getPropertyNameFromType: number literal without number value")
    }
    if ty.flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL) {
        return ty.as_unique_es_symbol_type().name.clone();
    }
    panic!("Unhandled case in getPropertyNameFromType")
}

/// `isThisProperty` (utilities.go:966). Accepts `NodeId` or
/// `Option<NodeId>` (Go `nil`) for committed call sites.
pub(crate) fn is_this_property(node: impl Into<Option<NodeId>>, nodes: &[ast::Node]) -> bool {
    let Some(node) = node.into() else {
        return false;
    };
    let n = &nodes[node];
    (ast::is_property_access_expression(n) || ast::is_element_access_expression(n))
        && n.expression()
            .is_some_and(|e| nodes[e].kind == ast::Kind::ThisKeyword)
}

/// `isValidNumberString` (utilities.go:970).
pub fn is_valid_number_string(s: &str, round_trip_only: bool) -> bool {
    if s.is_empty() {
        return false;
    }
    let n = tsc_jsnum::from_string(s);
    !n.is_nan() && !n.is_inf() && (!round_trip_only || n.to_string() == s)
}

/// `isValidBigIntString` (utilities.go:978). Uses the real scanner so error
/// reporting, `-` handling, and numeric-separator rejection match Go.
pub fn is_valid_big_int_string(s: &str, round_trip_only: bool) -> bool {
    if s.is_empty() {
        return false;
    }
    let text = format!("{s}n");
    let mut scanner = tsc_scanner::scanner::Scanner::new();
    scanner.set_skip_trivia(false);
    let success = std::rc::Rc::new(std::cell::Cell::new(true));
    {
        let success = success.clone();
        scanner.set_on_error(Some(
            move |_d: &'static diagnostics::Message,
                  _start: usize,
                  _length: usize,
                  _args: &[String]| {
                success.set(false);
            },
        ));
    }
    scanner.set_text(&text);
    let mut result = scanner.scan();
    let negative = result == ast::Kind::MinusToken;
    if negative {
        result = scanner.scan();
    }
    let flags = scanner.token_flags();
    // validate that
    // * scanning proceeded without error
    // * a bigint can be scanned, and that when it is scanned, it is
    // * the full length of the input string (so the scanner is one character
    //   beyond the augmented input length)
    // * it does not contain a numeric separator (the `BigInt` constructor
    //   does not accept a numeric separator in its input)
    if !(success.get()
        && result == ast::Kind::BigIntLiteral
        && scanner.token_end() == s.len() + 1
        && !flags.intersects(ast::TokenFlags::CONTAINS_SEPARATOR))
    {
        return false;
    }
    if round_trip_only {
        let token_value = String::from_utf8_lossy(scanner.token_value()).into_owned();
        let pseudo =
            tsc_jsnum::new_pseudo_big_int(&tsc_jsnum::parse_pseudo_big_int(&token_value), negative);
        return s == pseudo.to_string();
    }
    true
}

/// `getContainingClassExcludingClassDecorators` (utilities.go:1037).
pub(crate) fn get_containing_class_excluding_class_decorators(
    node: NodeId,
    nodes: &[ast::Node],
) -> Option<NodeId> {
    let decorator = ast::find_ancestor_or_quit(nodes[node].parent, nodes, &mut |n, _nodes| {
        if ast::is_class_like(Some(n.id), nodes) {
            return ast::FindAncestorResult::Quit;
        }
        if ast::is_decorator(n) {
            return ast::FindAncestorResult::True;
        }
        ast::FindAncestorResult::False
    });
    if let Some(decorator) = decorator {
        if let Some(dp) = nodes[decorator].parent {
            if ast::is_class_like(Some(dp), nodes) {
                return ast::get_containing_class(dp, nodes);
            }
        }
        return ast::get_containing_class(decorator, nodes);
    }
    ast::get_containing_class(node, nodes)
}

/// `isClassInstanceProperty` (utilities.go:1060).
pub(crate) fn is_class_instance_property(node: NodeId, nodes: &[ast::Node]) -> bool {
    if ast::is_in_js_file(Some(node), nodes)
        && ast::is_expando_property_declaration(Some(node), nodes)
    {
        let left = nodes[node]
            .as_binary_expression()
            .left
            .expect("expando left");
        return (!ast::is_bindable_static_access_expression(&nodes[left], nodes, false)
            || !nodes[left]
                .expression()
                .is_some_and(|e| ast::is_prototype_access(&nodes[e], nodes)))
            && !ast::is_bindable_static_name_expression(left, nodes, true);
    }
    nodes[node]
        .parent
        .is_some_and(|p| ast::is_class_like(Some(p), nodes))
        && ast::is_property_declaration(&nodes[node])
        && !ast::has_accessor_modifier(&nodes[node])
}

/// `isThisInitializedObjectBindingExpression` (utilities.go:1069).
pub(crate) fn is_this_initialized_object_binding_expression(
    node: NodeId,
    nodes: &[ast::Node],
) -> bool {
    let n = &nodes[node];
    if !(ast::is_shorthand_property_assignment(n) || ast::is_property_assignment(n)) {
        return false;
    }
    let Some(parent) = n.parent else { return false };
    let Some(grandparent) = nodes[parent].parent else {
        return false;
    };
    if !ast::is_binary_expression(&nodes[grandparent]) {
        return false;
    }
    let bin = nodes[grandparent].as_binary_expression();
    bin.operator_token
        .is_some_and(|t| nodes[t].kind == ast::Kind::EqualsToken)
        && bin
            .right
            .is_some_and(|r| nodes[r].kind == ast::Kind::ThisKeyword)
}

/// `isThisInitializedDeclaration` (utilities.go:1075).
pub(crate) fn is_this_initialized_declaration(node: NodeId, nodes: &[ast::Node]) -> bool {
    ast::is_variable_declaration(&nodes[node])
        && nodes[node]
            .initializer()
            .is_some_and(|i| nodes[i].kind == ast::Kind::ThisKeyword)
}

/// `isLiteralExpressionOfObject` (utilities.go:1107).
pub(crate) fn is_literal_expression_of_object(node: NodeId, nodes: &[ast::Node]) -> bool {
    matches!(
        nodes[node].kind,
        ast::Kind::ObjectLiteralExpression
            | ast::Kind::ArrayLiteralExpression
            | ast::Kind::RegularExpressionLiteral
            | ast::Kind::FunctionExpression
            | ast::Kind::ClassExpression
    )
}

/// `isNonNullAccess` (utilities.go:1120).
pub(crate) fn is_non_null_access(node: NodeId, nodes: &[ast::Node]) -> bool {
    ast::is_access_expression(&nodes[node])
        && nodes[node]
            .expression()
            .is_some_and(|e| ast::is_non_null_expression(&nodes[e]))
}

/// `getBindingElementPropertyName` (utilities.go:1124).
pub(crate) fn get_binding_element_property_name(node: &ast::Node) -> Option<NodeId> {
    node.property_name_or_name()
}

/// `isCallChain` (utilities.go:1128). `node.Flags & OptionalChain` only —
/// no arena needed.
pub(crate) fn is_call_chain(node: &ast::Node) -> bool {
    ast::is_call_expression(node) && node.flags.intersects(ast::NodeFlags::OPTIONAL_CHAIN)
}

/// `isSuperCall` (utilities.go:1136) — wraps `ast::is_super_call` for the
/// committed `(NodeId, &[Node])` call shape.
pub(crate) fn is_super_call(node: NodeId, nodes: &[ast::Node]) -> bool {
    ast::is_super_call(&nodes[node], nodes)
}

/// `getMembersOfDeclaration` (utilities.go:1140).
pub(crate) fn get_members_of_declaration(node: &ast::Node) -> Vec<NodeId> {
    match node.kind {
        ast::Kind::InterfaceDeclaration
        | ast::Kind::ClassDeclaration
        | ast::Kind::ClassExpression
        | ast::Kind::TypeLiteral => node.members().map(|m| m.to_vec()).unwrap_or_default(),
        ast::Kind::ObjectLiteralExpression => {
            node.properties().map(|p| p.to_vec()).unwrap_or_default()
        }
        _ => Vec::new(),
    }
}

/// `expressionResultIsUnused` (utilities.go:1203) — whether the result of
/// `node` is unused. Requires a node with a valid `parent` pointer.
pub(crate) fn expression_result_is_unused(node: &ast::Node, nodes: &[ast::Node]) -> bool {
    let mut node = node.id;
    loop {
        let Some(parent) = nodes[node].parent else {
            return false;
        };
        // walk up parenthesized expressions, but keep a pointer to the
        // top-most parenthesized expression
        if ast::is_parenthesized_expression(&nodes[parent]) {
            node = parent;
            continue;
        }
        // result is unused in an expression statement, `void` expression, or
        // the initializer or incrementer of a `for` loop
        if ast::is_expression_statement(&nodes[parent])
            || ast::is_void_expression(&nodes[parent])
            || (ast::is_for_statement(&nodes[parent])
                && (nodes[parent].initializer() == Some(node)
                    || nodes[parent].as_for_statement().incrementor == Some(node)))
        {
            return true;
        }
        if ast::is_binary_expression(&nodes[parent]) {
            let bin = nodes[parent].as_binary_expression();
            if bin
                .operator_token
                .is_some_and(|t| nodes[t].kind == ast::Kind::CommaToken)
            {
                // left side of comma is always unused
                if bin.left == Some(node) {
                    return true;
                }
                // right side of comma is unused if parent is unused
                node = parent;
                continue;
            }
        }
        return false;
    }
}

/// `getEnclosingContainer` (utilities.go:1298).
pub(crate) fn get_enclosing_container(node: NodeId, nodes: &[ast::Node]) -> Option<NodeId> {
    ast::find_ancestor(nodes[node].parent, nodes, &mut |n, nodes| {
        tsc_binder::binder::get_container_flags(n.id, nodes)
            & tsc_binder::binder::CONTAINER_FLAGS_IS_CONTAINER
            != 0
    })
}

/// `getDeclarationsOfKind` (utilities.go:1304). The `c` parameter is a port
/// addition — `SymbolId` needs the symbol arena, and declaration `kind`s
/// need each declaration's own file arena.
pub(crate) fn get_declarations_of_kind(
    c: &Checker,
    symbol: SymbolId,
    kind: ast::Kind,
) -> Vec<NodeId> {
    let declarations = c.symbol_arena.borrow()[symbol.index()].declarations.clone();
    declarations
        .into_iter()
        .filter(|&d| {
            let __program = c.program.clone().expect("program");
            let nodes = __program.nodes((d).file_index());
            nodes[d].kind == kind
        })
        .collect()
}

/// `hasType` (utilities.go:1308).
pub(crate) fn has_type(node: &ast::Node) -> bool {
    node.type_().is_some()
}

/// `getNonRestParameterCount` (utilities.go:1312).
pub(crate) fn get_non_rest_parameter_count(sig: &Signature) -> usize {
    sig.parameters.len() - usize::from(sig.has_rest_parameter())
}

/// `minAndMax` (utilities.go:1316). On an empty slice Go returns
/// `(0, 0)` — `minValue`/`maxValue` start at the zero value.
pub(crate) fn min_and_max<T: Copy>(
    slice: &[T],
    mut get_value: impl FnMut(T) -> usize,
) -> (usize, usize) {
    let mut min_value = 0usize;
    let mut max_value = 0usize;
    for (i, &element) in slice.iter().enumerate() {
        let value = get_value(element);
        if i == 0 {
            min_value = value;
            max_value = value;
        } else {
            min_value = min_value.min(value);
            max_value = max_value.max(value);
        }
    }
    (min_value, max_value)
}

// ===========================================================================
// containerAllowsBlockScopedVariable (grammarchecks.go:1796) — committed
// call sites route through `crate::utilities`.
// ===========================================================================

/// `(c *Checker) containerAllowsBlockScopedVariable`. The `&Checker` is
/// unused in Go (method receiver only for dispatch), so the port takes the
/// parent node id and arena directly; the committed `(parent, c, nodes)`
/// call site was reconciled to drop `self`.
pub(crate) fn container_allows_block_scoped_variable(parent: NodeId, nodes: &[ast::Node]) -> bool {
    match nodes[parent].kind {
        ast::Kind::IfStatement
        | ast::Kind::DoStatement
        | ast::Kind::WhileStatement
        | ast::Kind::WithStatement
        | ast::Kind::ForStatement
        | ast::Kind::ForInStatement
        | ast::Kind::ForOfStatement => false,
        ast::Kind::LabeledStatement => match nodes[parent].parent {
            Some(grandparent) => container_allows_block_scoped_variable(grandparent, nodes),
            None => true,
        },
        _ => true,
    }
}

// ===========================================================================
// isExternalOrCommonJSModule (ast/utilities.go:1690) — checker callers route
// through `crate::utilities`.
// ===========================================================================

/// `IsExternalOrCommonJSModule`.
pub fn is_external_or_common_js_module(file: &ast::SourceFile) -> bool {
    file.external_module_indicator.is_some() || file.common_js_module_indicator.is_some()
}

// ===========================================================================
// Tuple helpers (checker.go:23969..24025) — committed call sites route
// through `crate::utilities`.
// ===========================================================================

/// `getStartElementCount`.
pub(crate) fn get_start_element_count(t: &TupleType, flags: ElementFlags) -> usize {
    for (i, info) in t.element_infos.iter().enumerate() {
        if !info.flags.intersects(flags) {
            return i;
        }
    }
    t.element_infos.len()
}

/// `isMutableTupleType` (checker.go:24017).
pub(crate) fn is_mutable_tuple_type(types: &TypeArena, t: TypeId) -> bool {
    crate::checker_core::is_tuple_type(types, t)
        && !types
            .get(types.target_tuple_type(t).expect("tuple target"))
            .as_tuple_type()
            .readonly
}

/// `isGenericTupleType` (checker.go:24021) — `&TypeArena` free-fn form;
/// `Checker::is_generic_tuple_type` in checker_d.rs is the Go method
/// spelling of the same logic.
pub(crate) fn is_generic_tuple_type(types: &TypeArena, t: TypeId) -> bool {
    crate::checker_core::is_tuple_type(types, t)
        && types
            .get(types.target_tuple_type(t).expect("tuple target"))
            .as_tuple_type()
            .combined_flags
            .intersects(ElementFlags::VARIADIC)
}

/// `isSingleElementGenericTupleType` (checker.go:24025).
pub(crate) fn is_single_element_generic_tuple_type(types: &TypeArena, t: TypeId) -> bool {
    is_generic_tuple_type(types, t)
        && types
            .get(types.target_tuple_type(t).expect("tuple target"))
            .as_tuple_type()
            .element_infos
            .len()
            == 1
}

// ===========================================================================
// Mapped-type helpers (checker.go:29541/29589) — committed call sites route
// through `crate::utilities`.
// ===========================================================================

// `getMappedTypeModifiers` (checker.go:29541), `isPartialMappedType`
// (checker.go:29589) and `isConstEnumObjectType` (checker.go:28198) are
// canonical in `checker_d.rs` (committed `pub(crate)` there for
// inference.rs); re-exported for `crate::utilities::` call sites. All three
// take `(c: &Checker, t: TypeId)` because they need `c.program_nodes` /
// `c.sym` (Go derefs `t.checker` state); committed `(&c.types, t)` call
// sites were reconciled to pass `c`.
pub(crate) use crate::checker_d::{
    get_mapped_type_modifiers, is_const_enum_object_type, is_partial_mapped_type,
};

/// `isConstEnumOrConstEnumOnlyModule` (emitresolver.go:383) — checker
/// variant taking the checker + `SymbolId` (the `&Symbol` form lives in
/// `crate::emitresolver`).
pub(crate) fn is_const_enum_or_const_enum_only_module(c: &Checker, s: SymbolId) -> bool {
    crate::checker_d::is_const_enum_symbol(c, s)
        || c.sym(s)
            .flags
            .intersects(ast::SymbolFlags::CONST_ENUM_ONLY_MODULE)
}

// ===========================================================================
// rangeOfTypeParameters / allDeclarationsInSameSourceFile (utilities.go)
// ===========================================================================

/// `rangeOfTypeParameters` (utilities.go:1609).
pub(crate) fn range_of_type_parameters(
    source_file: &ast::SourceFile,
    type_parameters: &ast::NodeList,
    _nodes: &[ast::Node],
) -> TextRange {
    TextRange::new(
        type_parameters.pos() - 1,
        std::cmp::min(
            source_file.text().len() as tsc_core::text::TextPos,
            tsc_scanner::scanner::skip_trivia(source_file.text(), type_parameters.end()) + 1,
        ),
    )
}

/// `allDeclarationsInSameSourceFile` (utilities.go:1633). PORT: same source
/// file ⟺ same `NodeId` file index, so no arena dereference is needed
/// (`nodes` kept for the committed call shape).
pub(crate) fn all_declarations_in_same_source_file(
    symbol: &ast::Symbol,
    _nodes: &[ast::Node],
) -> bool {
    if symbol.declarations.len() > 1 {
        let file_index = symbol.declarations[0].file_index();
        symbol
            .declarations
            .iter()
            .all(|d| d.file_index() == file_index)
    } else {
        true
    }
}

// ===========================================================================
// getFeatureMap / FeatureMapEntry (utilities.go:1330)
// ===========================================================================

/// `type FeatureMapEntry struct` (utilities.go:1331).
pub struct FeatureMapEntry {
    /// `lib`.
    pub lib: String,
    /// `props`.
    pub props: Vec<String>,
}

/// `getFeatureMap` (utilities.go:1336) — `sync.OnceValue` → `OnceLock`.
pub fn get_feature_map() -> &'static FxHashMap<String, Vec<FeatureMapEntry>> {
    static FEATURE_MAP: OnceLock<FxHashMap<String, Vec<FeatureMapEntry>>> = OnceLock::new();
    FEATURE_MAP.get_or_init(|| {
        let e = |lib: &str, props: &[&str]| FeatureMapEntry {
            lib: lib.to_string(),
            props: props.iter().map(|p| p.to_string()).collect(),
        };
        let mut m: FxHashMap<String, Vec<FeatureMapEntry>> = FxHashMap::default();
        m.insert(
            "Array".into(),
            vec![
                e(
                    "es2015",
                    &[
                        "find",
                        "findIndex",
                        "fill",
                        "copyWithin",
                        "entries",
                        "keys",
                        "values",
                    ],
                ),
                e("es2016", &["includes"]),
                e("es2019", &["flat", "flatMap"]),
                e("es2022", &["at"]),
                e(
                    "es2023",
                    &[
                        "findLastIndex",
                        "findLast",
                        "toReversed",
                        "toSorted",
                        "toSpliced",
                        "with",
                    ],
                ),
            ],
        );
        m.insert("Iterator".into(), vec![e("es2015", &[])]);
        m.insert("IteratorConstructor".into(), vec![e("es2026", &["concat"])]);
        m.insert("RawJSON".into(), vec![e("es2026", &[])]);
        m.insert("JSON".into(), vec![e("es2026", &["isRawJSON", "rawJSON"])]);
        m.insert("AsyncIterator".into(), vec![e("es2015", &[])]);
        m.insert(
            "ArrayBuffer".into(),
            vec![e(
                "es2024",
                &[
                    "maxByteLength",
                    "resizable",
                    "resize",
                    "detached",
                    "transfer",
                    "transferToFixedLength",
                ],
            )],
        );
        m.insert(
            "Atomics".into(),
            vec![
                e(
                    "es2017",
                    &[
                        "add",
                        "and",
                        "compareExchange",
                        "exchange",
                        "isLockFree",
                        "load",
                        "or",
                        "store",
                        "sub",
                        "wait",
                        "notify",
                        "xor",
                    ],
                ),
                e("es2024", &["waitAsync"]),
            ],
        );
        m.insert(
            "SharedArrayBuffer".into(),
            vec![
                e("es2017", &["byteLength", "slice"]),
                e("es2024", &["growable", "maxByteLength", "grow"]),
            ],
        );
        m.insert("AsyncIterable".into(), vec![e("es2018", &[])]);
        m.insert("AsyncIterableIterator".into(), vec![e("es2018", &[])]);
        m.insert("AsyncGenerator".into(), vec![e("es2018", &[])]);
        m.insert("AsyncGeneratorFunction".into(), vec![e("es2018", &[])]);
        m.insert(
            "RegExp".into(),
            vec![
                e("es2015", &["flags", "sticky", "unicode"]),
                e("es2018", &["dotAll"]),
                e("es2024", &["unicodeSets"]),
            ],
        );
        m.insert("RegExpConstructor".into(), vec![e("es2025", &["escape"])]);
        m.insert(
            "Reflect".into(),
            vec![e(
                "es2015",
                &[
                    "apply",
                    "construct",
                    "defineProperty",
                    "deleteProperty",
                    "get",
                    "getOwnPropertyDescriptor",
                    "getPrototypeOf",
                    "has",
                    "isExtensible",
                    "ownKeys",
                    "preventExtensions",
                    "set",
                    "setPrototypeOf",
                ],
            )],
        );
        m.insert(
            "ArrayConstructor".into(),
            vec![e("es2015", &["from", "of"]), e("es2026", &["fromAsync"])],
        );
        m.insert(
            "ObjectConstructor".into(),
            vec![
                e(
                    "es2015",
                    &[
                        "assign",
                        "getOwnPropertySymbols",
                        "keys",
                        "is",
                        "setPrototypeOf",
                    ],
                ),
                e(
                    "es2017",
                    &["values", "entries", "getOwnPropertyDescriptors"],
                ),
                e("es2019", &["fromEntries"]),
                e("es2022", &["hasOwn"]),
                e("es2024", &["groupBy"]),
            ],
        );
        m.insert(
            "NumberConstructor".into(),
            vec![e(
                "es2015",
                &[
                    "isFinite",
                    "isInteger",
                    "isNaN",
                    "isSafeInteger",
                    "parseFloat",
                    "parseInt",
                ],
            )],
        );
        m.insert(
            "Math".into(),
            vec![
                e(
                    "es2015",
                    &[
                        "clz32", "imul", "sign", "log10", "log2", "log1p", "expm1", "cosh", "sinh",
                        "tanh", "acosh", "asinh", "atanh", "hypot", "trunc", "fround", "cbrt",
                    ],
                ),
                e("es2025", &["f16round"]),
                e("es2026", &["sumPrecise"]),
            ],
        );
        m.insert(
            "Map".into(),
            vec![
                e("es2015", &["entries", "keys", "values"]),
                e("es2026", &["getOrInsert", "getOrInsertComputed"]),
            ],
        );
        m.insert("MapConstructor".into(), vec![e("es2024", &["groupBy"])]);
        m.insert(
            "Set".into(),
            vec![
                e("es2015", &["entries", "keys", "values"]),
                e(
                    "es2025",
                    &[
                        "union",
                        "intersection",
                        "difference",
                        "symmetricDifference",
                        "isSubsetOf",
                        "isSupersetOf",
                        "isDisjointFrom",
                    ],
                ),
            ],
        );
        m.insert(
            "PromiseConstructor".into(),
            vec![
                e("es2015", &["all", "race", "reject", "resolve"]),
                e("es2020", &["allSettled"]),
                e("es2021", &["any"]),
                e("es2024", &["withResolvers"]),
                e("es2025", &["try"]),
            ],
        );
        m.insert(
            "Symbol".into(),
            vec![
                e("es2015", &["for", "keyFor"]),
                e("es2019", &["description"]),
            ],
        );
        m.insert(
            "WeakMap".into(),
            vec![
                e("es2015", &[]),
                e("es2026", &["getOrInsert", "getOrInsertComputed"]),
            ],
        );
        m.insert("WeakSet".into(), vec![e("es2015", &[])]);
        m.insert(
            "String".into(),
            vec![
                e(
                    "es2015",
                    &[
                        "codePointAt",
                        "includes",
                        "endsWith",
                        "normalize",
                        "repeat",
                        "startsWith",
                        "anchor",
                        "big",
                        "blink",
                        "bold",
                        "fixed",
                        "fontcolor",
                        "fontsize",
                        "italics",
                        "link",
                        "small",
                        "strike",
                        "sub",
                        "sup",
                    ],
                ),
                e("es2017", &["padStart", "padEnd"]),
                e("es2019", &["trimStart", "trimEnd", "trimLeft", "trimRight"]),
                e("es2020", &["matchAll"]),
                e("es2021", &["replaceAll"]),
                e("es2022", &["at"]),
                e("es2024", &["isWellFormed", "toWellFormed"]),
            ],
        );
        m.insert(
            "StringConstructor".into(),
            vec![e("es2015", &["fromCodePoint", "raw"])],
        );
        m.insert(
            "DateTimeFormat".into(),
            vec![e("es2017", &["formatToParts"])],
        );
        m.insert(
            "Promise".into(),
            vec![e("es2015", &[]), e("es2018", &["finally"])],
        );
        m.insert("RegExpMatchArray".into(), vec![e("es2018", &["groups"])]);
        m.insert("RegExpExecArray".into(), vec![e("es2018", &["groups"])]);
        m.insert(
            "Intl".into(),
            vec![
                e("es2018", &["PluralRules"]),
                e("es2020", &["RelativeTimeFormat", "Locale", "DisplayNames"]),
                e("es2021", &["ListFormat", "DateTimeFormat"]),
                e("es2022", &["Segmenter"]),
                e("es2025", &["DurationFormat"]),
            ],
        );
        m.insert("NumberFormat".into(), vec![e("es2018", &["formatToParts"])]);
        m.insert(
            "SymbolConstructor".into(),
            vec![
                e("es2020", &["matchAll"]),
                e("esnext", &["metadata", "dispose", "asyncDispose"]),
            ],
        );
        m.insert(
            "DataView".into(),
            vec![
                e(
                    "es2020",
                    &["setBigInt64", "setBigUint64", "getBigInt64", "getBigUint64"],
                ),
                e("es2025", &["setFloat16", "getFloat16"]),
            ],
        );
        m.insert("BigInt".into(), vec![e("es2020", &[])]);
        m.insert(
            "RelativeTimeFormat".into(),
            vec![e("es2020", &["format", "formatToParts", "resolvedOptions"])],
        );
        m.insert(
            "Int8Array".into(),
            vec![
                e("es2022", &["at"]),
                e(
                    "es2023",
                    &[
                        "findLastIndex",
                        "findLast",
                        "toReversed",
                        "toSorted",
                        "toSpliced",
                        "with",
                    ],
                ),
            ],
        );
        m.insert(
            "Uint8Array".into(),
            vec![
                e("es2022", &["at"]),
                e(
                    "es2023",
                    &[
                        "findLastIndex",
                        "findLast",
                        "toReversed",
                        "toSorted",
                        "toSpliced",
                        "with",
                    ],
                ),
                e(
                    "es2026",
                    &["toBase64", "setFromBase64", "toHex", "setFromHex"],
                ),
            ],
        );
        m.insert(
            "Uint8ClampedArray".into(),
            vec![
                e("es2022", &["at"]),
                e(
                    "es2023",
                    &[
                        "findLastIndex",
                        "findLast",
                        "toReversed",
                        "toSorted",
                        "toSpliced",
                        "with",
                    ],
                ),
            ],
        );
        m.insert(
            "Int16Array".into(),
            vec![
                e("es2022", &["at"]),
                e(
                    "es2023",
                    &[
                        "findLastIndex",
                        "findLast",
                        "toReversed",
                        "toSorted",
                        "toSpliced",
                        "with",
                    ],
                ),
            ],
        );
        m.insert(
            "Uint16Array".into(),
            vec![
                e("es2022", &["at"]),
                e(
                    "es2023",
                    &[
                        "findLastIndex",
                        "findLast",
                        "toReversed",
                        "toSorted",
                        "toSpliced",
                        "with",
                    ],
                ),
            ],
        );
        m.insert(
            "Int32Array".into(),
            vec![
                e("es2022", &["at"]),
                e(
                    "es2023",
                    &[
                        "findLastIndex",
                        "findLast",
                        "toReversed",
                        "toSorted",
                        "toSpliced",
                        "with",
                    ],
                ),
            ],
        );
        m.insert(
            "Uint32Array".into(),
            vec![
                e("es2022", &["at"]),
                e(
                    "es2023",
                    &[
                        "findLastIndex",
                        "findLast",
                        "toReversed",
                        "toSorted",
                        "toSpliced",
                        "with",
                    ],
                ),
            ],
        );
        m.insert("Float16Array".into(), vec![e("es2025", &[])]);
        m.insert(
            "Float32Array".into(),
            vec![
                e("es2022", &["at"]),
                e(
                    "es2023",
                    &[
                        "findLastIndex",
                        "findLast",
                        "toReversed",
                        "toSorted",
                        "toSpliced",
                        "with",
                    ],
                ),
            ],
        );
        m.insert(
            "Float64Array".into(),
            vec![
                e("es2022", &["at"]),
                e(
                    "es2023",
                    &[
                        "findLastIndex",
                        "findLast",
                        "toReversed",
                        "toSorted",
                        "toSpliced",
                        "with",
                    ],
                ),
            ],
        );
        m.insert(
            "BigInt64Array".into(),
            vec![
                e("es2020", &[]),
                e("es2022", &["at"]),
                e(
                    "es2023",
                    &[
                        "findLastIndex",
                        "findLast",
                        "toReversed",
                        "toSorted",
                        "toSpliced",
                        "with",
                    ],
                ),
            ],
        );
        m.insert(
            "BigUint64Array".into(),
            vec![
                e("es2020", &[]),
                e("es2022", &["at"]),
                e(
                    "es2023",
                    &[
                        "findLastIndex",
                        "findLast",
                        "toReversed",
                        "toSorted",
                        "toSpliced",
                        "with",
                    ],
                ),
            ],
        );
        m.insert("Error".into(), vec![e("es2022", &["cause"])]);
        m.insert("ErrorConstructor".into(), vec![e("es2026", &["isError"])]);
        m.insert(
            "Uint8ArrayConstructor".into(),
            vec![e("es2026", &["fromBase64", "fromHex"])],
        );
        m.insert("DisposableStack".into(), vec![e("esnext", &[])]);
        m.insert("AsyncDisposableStack".into(), vec![e("esnext", &[])]);
        m.insert("Date".into(), vec![e("esnext", &["toTemporalInstant"])]);
        m
    })
}

// ===========================================================================
// createModuleNotFoundChain / createModeMismatchDetails (utilities.go:1838)
// ===========================================================================

/// `type DiagnosticDetails struct` (utilities.go:1830).
pub struct DiagnosticDetails {
    /// `Message`.
    pub message: &'static diagnostics::Message,
    /// `Args` — Go `[]any`; committed call sites render `Vec<String>`.
    pub args: Vec<String>,
}

/// `CreateModuleNotFoundChain` (utilities.go:1844). Computes the diagnostic
/// message and arguments for a module-not-found error chain entry; shared
/// between the checker and the incremental builder.
pub fn create_module_not_found_chain(
    program: &dyn crate::checker_types::Program,
    file: &ast::SourceFile,
    module_reference: &str,
    mode: tsc_core::compileroptions::ResolutionMode,
    package_name: &str,
) -> DiagnosticDetails {
    let resolved_module = program.get_resolved_module(file, module_reference, mode);
    let mut package_name = package_name.to_string();
    if let Some(resolved_module) = &resolved_module {
        if !resolved_module.alternate_result.as_string().is_empty() {
            if resolved_module
                .alternate_result
                .contains_lowercase_directory_sequence("/node_modules/@types/")
            {
                package_name = format!(
                    "@types/{}",
                    tsc_module::util::mangle_scoped_package_name(&package_name)
                );
            }
            return DiagnosticDetails {
                message: &diagnostics::There_are_types_at_0_but_this_result_could_not_be_resolved_when_respecting_package_json_exports_The_1_library_may_need_to_update_its_package_json_or_typings,
                args: vec![
                    resolved_module.alternate_result.as_string().to_string(),
                    package_name,
                ],
            };
        }
    }
    let packages_map = program.get_packages_map();
    if packages_map.contains_key(&tsc_module::util::get_types_package_name(&package_name)) {
        return DiagnosticDetails {
            message: &diagnostics::If_the_0_package_actually_exposes_this_module_consider_sending_a_pull_request_to_amend_https_Colon_Slash_Slashgithub_com_SlashDefinitelyTyped_SlashDefinitelyTyped_Slashtree_Slashmaster_Slashtypes_Slash_1,
            args: vec![
                package_name.clone(),
                tsc_module::util::mangle_scoped_package_name(&package_name),
            ],
        };
    }
    if packages_map.get(&package_name).copied().unwrap_or(false) {
        return DiagnosticDetails {
            message: &diagnostics::If_the_0_package_actually_exposes_this_module_try_adding_a_new_declaration_d_ts_file_containing_declare_module_1,
            args: vec![package_name, module_reference.to_string()],
        };
    }
    DiagnosticDetails {
        message: &diagnostics::Try_npm_i_save_dev_types_Slash_1_if_it_exists_or_add_a_new_declaration_d_ts_file_containing_declare_module_0,
        args: vec![
            module_reference.to_string(),
            tsc_module::util::mangle_scoped_package_name(&package_name),
        ],
    }
}

/// `CreateModeMismatchDetails` (utilities.go:1875). Computes the diagnostic
/// message and arguments for a mode-mismatch error chain entry.
pub fn create_mode_mismatch_details(
    program: &dyn crate::checker_types::Program,
    file: &ast::SourceFile,
) -> DiagnosticDetails {
    let ext = file.file_name().extension();
    let target_ext = if ext == tsc_tspath::EXTENSION_TS {
        tsc_tspath::EXTENSION_MTS
    } else if ext == tsc_tspath::EXTENSION_JS {
        tsc_tspath::EXTENSION_MJS
    } else {
        ""
    };
    let meta = program.get_source_file_meta_data(file.path_key());
    let package_json_type = &meta.package_json_type;
    let package_json_directory = &meta.package_json_directory;

    if !package_json_directory.as_string().is_empty() && package_json_type.is_empty() {
        if !target_ext.is_empty() {
            return DiagnosticDetails {
                message: &diagnostics::To_convert_this_file_to_an_ECMAScript_module_change_its_file_extension_to_0_or_add_the_field_type_Colon_module_to_1,
                args: vec![
                    target_ext.to_string(),
                    package_json_directory
                        .resolve_file("package.json")
                        .as_string()
                        .to_string(),
                ],
            };
        }
        return DiagnosticDetails {
            message: &diagnostics::To_convert_this_file_to_an_ECMAScript_module_add_the_field_type_Colon_module_to_0,
            args: vec![package_json_directory
                .resolve_file("package.json")
                .as_string()
                .to_string()],
        };
    }
    if !target_ext.is_empty() {
        return DiagnosticDetails {
            message: &diagnostics::To_convert_this_file_to_an_ECMAScript_module_change_its_file_extension_to_0_or_create_a_local_package_json_file_with_type_Colon_module,
            args: vec![target_ext.to_string()],
        };
    }
    DiagnosticDetails {
        message: &diagnostics::To_convert_this_file_to_an_ECMAScript_module_create_a_local_package_json_file_with_type_Colon_module,
        args: Vec::new(),
    }
}

/// `quotedAndCommaSeparated` (utilities.go:1923).
pub(crate) fn quoted_and_comma_separated(items: &[String]) -> String {
    items
        .iter()
        .map(|item| format!("'{item}'"))
        .collect::<Vec<_>>()
        .join(", ")
}

// ===========================================================================
// Checker helpers that need cross-arena access (port additions).
// ===========================================================================

impl Checker {
    /// Port addition: the node arena of the file containing the symbol's
    /// (value) declaration — the Rust spelling of reading `*ast.Node` fields
    /// through a declaration.
    ///
    /// PORT: returns an `Rc` snapshot of the shared arena (see
    /// `checker_types::Program::nodes`).
    pub fn program_nodes_for_symbol(&self, s: SymbolId) -> std::rc::Rc<Vec<ast::Node>> {
        let declaration = {
            let arena = self.symbol_arena.borrow();
            let symbol = &arena[s.index()];
            symbol
                .value_declaration
                .or_else(|| symbol.declarations.first().copied())
        };
        match declaration {
            Some(d) => self.program_nodes(d),
            None => self.program_nodes(self.files[0]),
        }
    }
}

/// `isReservedMemberName` (utilities.go:1677) — canonical definition is in
/// `crate::checker_c` (re-exported for `crate::utilities::` call sites).
pub(crate) use crate::checker_c::is_reserved_member_name;

/// `introducesArgumentsExoticObject` (utilities.go:1681).
pub(crate) fn introduces_arguments_exotic_object(node: &ast::Node) -> bool {
    matches!(
        node.kind,
        ast::Kind::MethodDeclaration
            | ast::Kind::MethodSignature
            | ast::Kind::Constructor
            | ast::Kind::GetAccessor
            | ast::Kind::SetAccessor
            | ast::Kind::FunctionDeclaration
            | ast::Kind::FunctionExpression
    )
}

/// `symbolsToArray` (utilities.go:1690).
pub(crate) fn symbols_to_array(symbols: &SymbolTable) -> Vec<SymbolId> {
    symbols
        .entries()
        .filter(|(name, _)| !is_reserved_member_name(name))
        .map(|(_, &s)| s)
        .collect()
}

/// `SkipAlias` (utilities.go:1697) — free-function form.
pub fn skip_alias(c: &mut Checker, symbol: SymbolId) -> Option<SymbolId> {
    if c.sym(symbol).flags.intersects(ast::SymbolFlags::ALIAS) {
        return c.get_aliased_symbol(symbol);
    }
    Some(symbol)
}

/// `IsExternalModuleSymbol` (utilities.go:1703) — true if the symbol is for
/// an external module, as opposed to a namespace.
pub fn is_external_module_symbol(module_symbol: SymbolId, c: &Checker) -> bool {
    let sym = c.sym(module_symbol);
    sym.flags.intersects(ast::SymbolFlags::MODULE)
        && ast::symbol::is_ambient_module_symbol_name(&sym.name)
}

impl Checker {
    /// `(c *Checker) isCanceled` (utilities.go:1708).
    pub(crate) fn is_canceled(&self) -> bool {
        self.ctx.is_cancelled()
    }

    /// `(c *Checker) checkNotCanceled` (utilities.go:1714).
    pub(crate) fn check_not_canceled(&self) {
        if self.was_canceled {
            panic!("Checker was previously cancelled")
        }
    }
}

/// `walkUpOuterExpressions` (checker/utilities.go:1906) — climbs past all
/// outer expressions and returns the first non-outer-expression ancestor
/// (`None` mirrors Go's nil).
pub fn walk_up_outer_expressions(node: NodeId, nodes: &[ast::Node]) -> Option<NodeId> {
    let mut parent = nodes[node].parent;
    while let Some(p) = parent {
        if !ast::is_outer_expression(&nodes[p], ast::outer_expression_kinds::ALL, nodes) {
            break;
        }
        parent = nodes[p].parent;
    }
    parent
}

impl Checker {
    /// `(c *Checker) isConstantVariable` (utilities.go:1083).
    pub(crate) fn is_constant_variable(&mut self, symbol: SymbolId) -> bool {
        self.sym(symbol)
            .flags
            .intersects(ast::SymbolFlags::VARIABLE)
            && self
                .get_declaration_node_flags_from_symbol(symbol)
                .intersects(ast::NodeFlags::CONSTANT)
    }

    /// `(c *Checker) isParameterOrMutableLocalVariable` (utilities.go:1087).
    /// Returns true if symbol is a parameter, a catch clause variable, or a
    /// mutable local variable.
    pub(crate) fn is_parameter_or_mutable_local_variable(&mut self, symbol: SymbolId) -> bool {
        let value_declaration = self.sym(symbol).value_declaration;
        if let Some(value_declaration) = value_declaration {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((value_declaration).file_index());
            let declaration = ast::get_root_declaration(value_declaration, &nodes);
            let is_param_or_catch = ast::is_parameter_declaration(&nodes[declaration])
                || (ast::is_variable_declaration(&nodes[declaration])
                    && nodes[declaration]
                        .parent
                        .is_some_and(|p| ast::is_catch_clause(&nodes[p])));
            if is_param_or_catch {
                return true;
            }
            drop(nodes);
            return ast::is_variable_declaration(&self.program_nodes(declaration)[declaration])
                && self.is_mutable_local_variable_declaration(declaration);
        }
        false
    }

    /// `(c *Checker) isMutableLocalVariableDeclaration` (utilities.go:1099).
    /// Returns true if symbol is a non-exported and non-global `let` variable.
    pub(crate) fn is_mutable_local_variable_declaration(&mut self, declaration: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((declaration).file_index());
        let Some(decl_list) = nodes[declaration].parent else {
            return false;
        };
        nodes[decl_list].flags.intersects(ast::NodeFlags::LET)
            && !(ast::get_combined_modifier_flags(declaration, &nodes)
                .intersects(ast::ModifierFlags::EXPORT)
                || (nodes[decl_list]
                    .parent
                    .is_some_and(|vs| ast::is_variable_statement(&nodes[vs]))
                    && nodes[decl_list]
                        .parent
                        .and_then(|vs| nodes[vs].parent)
                        .is_some_and(|sf| ast::is_global_source_file(&nodes[sf], &nodes))))
    }
}
