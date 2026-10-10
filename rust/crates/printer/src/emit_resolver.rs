// Ported from tsc/internal/printer/emitresolver.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The resolver surface the printer and transforms use to answer semantic
// questions during emit. Implemented by the checker-side emit resolver.
//
// PORT: Go's `*ast.Node` parameters become `NodeId` plus the node arena
// (`&[Node]`) and symbol arena (`&mut Vec<Symbol>`) parameters, matching the
// convention used by `binder::ReferenceResolver` in this workspace.
// `GetConstantValue(node) any` becomes `Option<tsc_evaluator::Value>`.

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::{self as ast, Node, NodeId, Symbol};
use tsc_binder::referenceresolver::ReferenceResolver;
use tsc_evaluator::Value;
use tsc_nodebuilder::{Flags, InternalFlags, SymbolTracker};

use crate::emit_context::EmitContext;

/// `type SymbolAccessibility int32`
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum SymbolAccessibility {
    /// `SymbolAccessibilityAccessible`
    #[default]
    Accessible,
    /// `SymbolAccessibilityNotAccessible`
    NotAccessible,
    /// `SymbolAccessibilityCannotBeNamed`
    CannotBeNamed,
    /// `SymbolAccessibilityNotResolved`
    NotResolved,
}

/// `type SymbolAccessibilityResult struct`
#[derive(Clone, Default)]
pub struct SymbolAccessibilityResult {
    pub accessibility: SymbolAccessibility,
    /// aliases that need to have this symbol visible
    pub aliases_to_make_visible: Vec<NodeId>,
    /// Optional - symbol name that results in error
    pub error_symbol_name: String,
    /// Optional - node that results in error
    pub error_node: Option<NodeId>,
    /// Optional - If the symbol is not visible from module, module's name
    pub error_module_name: String,
}

/// `type TypeReferenceSerializationKind int32` — indicates how to serialize
/// the name for a TypeReferenceNode when emitting decorator metadata.
///
/// @internal
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum TypeReferenceSerializationKind {
    /// The TypeReferenceNode could not be resolved.
    /// The type name should be emitted using a safe fallback.
    #[default]
    Unknown,
    /// The TypeReferenceNode resolves to a type with a constructor
    /// function that can be reached at runtime (e.g. a `class`
    /// declaration or a `var` declaration for the static side
    /// of a type, such as the global `Promise` type in lib.d.ts).
    TypeWithConstructSignatureAndValue,
    /// The TypeReferenceNode resolves to a Void-like, Nullable, or Never type.
    VoidNullableOrNeverType,
    /// The TypeReferenceNode resolves to a Number-like type.
    NumberLikeType,
    /// The TypeReferenceNode resolves to a BigInt-like type.
    BigIntLikeType,
    /// The TypeReferenceNode resolves to a String-like type.
    StringLikeType,
    /// The TypeReferenceNode resolves to a Boolean-like type.
    BooleanType,
    /// The TypeReferenceNode resolves to an Array-like type.
    ArrayLikeType,
    /// The TypeReferenceNode resolved to the ESSymbol type.
    ESSymbolType,
    /// The TypeReferenceNode resolved to the global Promise constructor symbol.
    Promise,
    /// The TypeReferenceNode resolves to a Function type or a type with call signatures.
    TypeWithCallSignature,
    /// The TypeReferenceNode resolves to any other type.
    ObjectType,
}

/// `type EmitResolver interface`
pub trait EmitResolver: ReferenceResolver {
    /// `EmitContext() *EmitContext`
    /// PORT(deviation): Go returns `*printer.EmitContext`; the workspace
    /// forbids `unsafe`, so a `&EmitContext` cannot be produced from the
    /// shared `Rc<RefCell<EmitContext>>` the checker-side resolver holds.
    /// The `&Rc<RefCell<EmitContext>>` handle preserves the shared-cell
    /// semantics — callers `.borrow()`/`.borrow_mut()` it per use, or clone
    /// the `Rc` to share the same `EmitContext` (the way Go shares
    /// `resolver.EmitContext()` with the transformer).
    fn emit_context(&self) -> &Rc<RefCell<EmitContext>>;
    /// `IsReferencedAliasDeclaration(node *ast.Node) bool`
    fn is_referenced_alias_declaration(&self, node: NodeId, nodes: &[Node]) -> bool;
    /// `IsValueAliasDeclaration(node *ast.Node) bool`
    fn is_value_alias_declaration(&self, node: NodeId, nodes: &[Node]) -> bool;
    /// `IsTopLevelValueImportEqualsWithEntityName(node *ast.Node) bool`
    fn is_top_level_value_import_equals_with_entity_name(
        &self,
        node: NodeId,
        nodes: &[Node],
    ) -> bool;
    /// `MarkLinkedReferencesRecursively(file *ast.SourceFile)`
    fn mark_linked_references_recursively(&mut self, file: NodeId, nodes: &[Node]);
    /// `GetExternalModuleFileFromDeclaration(node *ast.Node) *ast.SourceFile`
    fn get_external_module_file_from_declaration(
        &self,
        node: NodeId,
        nodes: &[Node],
    ) -> Option<NodeId>;
    /// `GetEffectiveDeclarationFlags(node *ast.Node, flags ast.ModifierFlags) ast.ModifierFlags`
    fn get_effective_declaration_flags(
        &self,
        node: NodeId,
        flags: ast::ModifierFlags,
        nodes: &[Node],
    ) -> ast::ModifierFlags;

    // decorator metadata
    /// `GetTypeReferenceSerializationKind(name *ast.EntityName, serialScope *ast.Node) TypeReferenceSerializationKind`
    fn get_type_reference_serialization_kind(
        &self,
        name: NodeId,
        serial_scope: Option<NodeId>,
        nodes: &[Node],
    ) -> TypeReferenceSerializationKind;

    // const enum inlining
    /// `GetConstantValue(node *ast.Node) any`
    fn get_constant_value(&self, node: NodeId, nodes: &[Node]) -> Option<Value>;

    // JSX Emit
    /// `GetJsxFactoryEntity(location *ast.Node) *ast.Node`
    fn get_jsx_factory_entity(&self, location: NodeId, nodes: &[Node]) -> Option<NodeId>;
    /// `GetJsxFragmentFactoryEntity(location *ast.Node) *ast.Node`
    fn get_jsx_fragment_factory_entity(&self, location: NodeId, nodes: &[Node]) -> Option<NodeId>;
    /// `SetReferencedImportDeclaration(node *ast.IdentifierNode, ref *ast.Declaration)` — for overriding the reference resolver behavior for generated identifiers
    fn set_referenced_import_declaration(
        &mut self,
        node: NodeId,
        ref_: Option<NodeId>,
        nodes: &[Node],
    );

    // declaration emit checker functionality projections
    /// `PrecalculateDeclarationEmitVisibility(file *ast.SourceFile)`
    fn precalculate_declaration_emit_visibility(&mut self, file: NodeId, nodes: &[Node]);
    /// `IsSymbolAccessible(symbol *ast.Symbol, enclosingDeclaration *ast.Node, meaning ast.SymbolFlags, shouldComputeAliasToMarkVisible bool) SymbolAccessibilityResult`
    fn is_symbol_accessible(
        &self,
        symbol: ast::SymbolId,
        enclosing_declaration: Option<NodeId>,
        meaning: ast::SymbolFlags,
        should_compute_alias_to_mark_visible: bool,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> SymbolAccessibilityResult;
    /// `IsEntityNameVisible(entityName *ast.Node, enclosingDeclaration *ast.Node) SymbolAccessibilityResult` — previously SymbolVisibilityResult in strada - ErrorModuleName never set
    fn is_entity_name_visible(
        &self,
        entity_name: NodeId,
        enclosing_declaration: Option<NodeId>,
        nodes: &[Node],
    ) -> SymbolAccessibilityResult;
    /// `IsExpandoFunctionDeclaration(node *ast.Node) bool`
    fn is_expando_function_declaration(&self, node: NodeId, nodes: &[Node]) -> bool;
    /// `IsExpandoFunctionDeclarationUnsafe(node *ast.Node) bool`
    fn is_expando_function_declaration_unsafe(&self, node: NodeId, nodes: &[Node]) -> bool;
    /// `IsLiteralConstDeclaration(node *ast.Node) bool`
    fn is_literal_const_declaration(&self, node: NodeId, nodes: &[Node]) -> bool;
    /// `RequiresAddingImplicitUndefined(node *ast.Node, symbol *ast.Symbol, enclosingDeclaration *ast.Node) bool`
    fn requires_adding_implicit_undefined(
        &self,
        node: NodeId,
        symbol: Option<ast::SymbolId>,
        enclosing_declaration: Option<NodeId>,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> bool;
    /// `IsDeclarationVisible(node *ast.Node) bool`
    fn is_declaration_visible(&self, node: NodeId, nodes: &[Node]) -> bool;
    /// `IsNameResolvable(location *ast.Node, name string) bool`
    fn is_name_resolvable(&self, location: Option<NodeId>, name: &str, nodes: &[Node]) -> bool;
    /// `IsImportRequiredByAugmentation(decl *ast.ImportDeclaration) bool`
    fn is_import_required_by_augmentation(&self, decl: NodeId, nodes: &[Node]) -> bool;
    /// `IsDefinitelyReferenceToGlobalSymbolObject(node *ast.Node) bool`
    fn is_definitely_reference_to_global_symbol_object(&self, node: NodeId, nodes: &[Node])
    -> bool;
    /// `IsImplementationOfOverload(node *ast.SignatureDeclaration) bool`
    fn is_implementation_of_overload(&self, node: NodeId, nodes: &[Node]) -> bool;
    /// `GetEnumMemberValue(node *ast.Node) evaluator.Result`
    fn get_enum_member_value(&self, node: NodeId, nodes: &[Node]) -> tsc_evaluator::Result;
    /// `IsLateBound(node *ast.Node) bool`
    fn is_late_bound(&self, node: NodeId, nodes: &[Node]) -> bool;
    /// `IsOptionalParameter(node *ast.Node) bool`
    fn is_optional_parameter(&self, node: NodeId, nodes: &[Node]) -> bool;
    /// `IsThisPropertyAssignmentDeclarationRedundant(node *ast.Node) bool`
    fn is_this_property_assignment_declaration_redundant(
        &self,
        node: NodeId,
        nodes: &[Node],
    ) -> bool;

    // isolatedDeclarations-specific declaration emit
    /// `GetPropertiesOfContainerFunction(node *ast.Node) []*ast.Symbol`
    fn get_properties_of_container_function(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> Vec<ast::SymbolId>;
    /// `RequiresAddingImplicitUndefinedUnsafe(node *ast.Node, symbol *ast.Symbol, enclosingDeclaration *ast.Node) bool`
    fn requires_adding_implicit_undefined_unsafe(
        &self,
        node: NodeId,
        symbol: Option<ast::SymbolId>,
        enclosing_declaration: Option<NodeId>,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> bool;
    /// `GetReferencedValueDeclarationUnsafe(node *ast.IdentifierNode) *ast.Declaration`
    fn get_referenced_value_declaration_unsafe(
        &self,
        node: NodeId,
        nodes: &[Node],
    ) -> Option<NodeId>;

    // Node construction for declaration emit
    /// `CreateTypeOfDeclaration(declaration *ast.Node, enclosingDeclaration *ast.Node, flags nodebuilder.Flags, internalFlags nodebuilder.InternalFlags, tracker nodebuilder.SymbolTracker) *ast.Node`
    fn create_type_of_declaration(
        &self,
        declaration: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: Flags,
        internal_flags: InternalFlags,
        tracker: &mut dyn SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Option<NodeId>;
    /// `CreateReturnTypeOfSignatureDeclaration(...)`
    fn create_return_type_of_signature_declaration(
        &self,
        signature_declaration: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: Flags,
        internal_flags: InternalFlags,
        tracker: &mut dyn SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Option<NodeId>;
    /// `CreateTypeParametersOfSignatureDeclaration(...)`
    fn create_type_parameters_of_signature_declaration(
        &self,
        signature_declaration: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: Flags,
        internal_flags: InternalFlags,
        tracker: &mut dyn SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Vec<NodeId>;
    /// `CreateLiteralConstValue(node *ast.Node, tracker nodebuilder.SymbolTracker) *ast.Node`
    fn create_literal_const_value(
        &self,
        node: NodeId,
        tracker: &mut dyn SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Option<NodeId>;
    /// `CreateTypeOfExpression(...)`
    fn create_type_of_expression(
        &self,
        expression: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: Flags,
        internal_flags: InternalFlags,
        tracker: &mut dyn SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Option<NodeId>;
    /// `CreateLateBoundIndexSignatures(...)`
    fn create_late_bound_index_signatures(
        &self,
        container: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: Flags,
        internal_flags: InternalFlags,
        tracker: &mut dyn SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Vec<NodeId>;
    /// `TryJSTypeNodeToTypeNode(...)`
    fn try_js_type_node_to_type_node(
        &self,
        type_node: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: Flags,
        internal_flags: InternalFlags,
        tracker: &mut dyn SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Option<NodeId>;
}
