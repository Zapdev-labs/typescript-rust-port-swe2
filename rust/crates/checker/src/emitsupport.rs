// Ported from tsc/internal/checker/emitsupport.go @
// ec47d33c23e464a17cdf2475632cba629bee8763
//
// Declaration-visibility and "implicit undefined" support for emit —
// `isDeclarationVisible`, `isEntityNameVisible`, `hasVisibleDeclarations`
// and friends, as `Checker` methods.
//
// PORT notes:
//
// - `*ast.Node` → `NodeId` (`Option<NodeId>` for Go's nilable pointers);
//   `*ast.Symbol` → `SymbolId` (`Option<SymbolId>` for nilable).
// - Node parents never cross files, so all parent chains are walked inside
//   the declaration's own per-file arena (`c.program_nodes`).
// - `addVisibleAlias` is a method (`Checker::add_visible_alias`) rather than
//   a closure because a `FnMut` capturing `&mut Checker` would conflict with
//   the recursive `is_declaration_visible` calls in the same body.
// - `c.isSymbolAccessible`/`IsSymbolAccessibleByFlags` live in
//   `symbolaccessibility.go` — a concurrent port owns that file; the call
//   sites here use the expected `Option<SymbolId>` signature.
// - Mirrored helpers from `utilities.go`/`checker.go` that are not yet in
//   the Rust port are kept private here and marked `PORT(mirrored)`.

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, Node, NodeId, SymbolId};
use tsc_core::tristate::Tristate;
use tsc_printer::{SymbolAccessibility, SymbolAccessibilityResult};

use crate::checker_core::Checker;
use crate::emitresolver::call_resolve_name;
use crate::types::{TypeFlags, TypeId};

/// `getAnyImportSyntax` (checker/utilities.go).
///
/// PORT(mirrored): the canonical helper lives in the checker's utilities.go
/// wave; this copy is removed when `utilities.rs` lands it.
fn get_any_import_syntax(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    match nodes[node].kind {
        ast::Kind::ImportEqualsDeclaration => Some(node),
        ast::Kind::ImportClause => nodes[node].parent,
        ast::Kind::NamespaceImport => nodes[node].parent.and_then(|p| nodes[p].parent),
        ast::Kind::ImportSpecifier => nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .and_then(|p| nodes[p].parent),
        _ => None,
    }
}

/// `containsNonMissingUndefinedType` (checker/utilities.go).
///
/// PORT(mirrored): as above.
fn contains_non_missing_undefined_type(c: &Checker, t: TypeId) -> bool {
    let candidate = if c.types_handle().get(t).flags.intersects(TypeFlags::UNION) {
        c.types_handle().get(t).as_union_type().union_or_intersection.types[0]
    } else {
        t
    };
    c.types_handle().get(candidate)
        .flags
        .intersects(TypeFlags::UNDEFINED)
        && candidate != c.missing_type
}

/// `getMeaningOfEntityNameReference` (emitsupport.go).
pub(crate) fn get_meaning_of_entity_name_reference(entity_name: NodeId, nodes: &[Node]) -> ast::SymbolFlags {
    let parent = nodes[entity_name].parent;
    let parent_kind = parent.map(|p| nodes[p].kind);
    // get symbol of the first identifier of the entityName
    if parent_kind == Some(ast::Kind::TypeQuery)
        || parent_kind == Some(ast::Kind::ExpressionWithTypeArguments)
            && !ast::is_part_of_type_node(parent.unwrap(), nodes)
        || parent_kind == Some(ast::Kind::ComputedPropertyName)
        || parent_kind == Some(ast::Kind::TypePredicate)
            && nodes[parent.unwrap()]
                .as_type_predicate_node()
                .parameter_name
                == Some(entity_name)
        || parent_kind == Some(ast::Kind::BinaryExpression)
    {
        // Typeof value
        return ast::SymbolFlags::VALUE | ast::SymbolFlags::EXPORT_VALUE;
    }
    if nodes[entity_name].kind == ast::Kind::QualifiedName
        || nodes[entity_name].kind == ast::Kind::PropertyAccessExpression
        || parent_kind == Some(ast::Kind::ImportEqualsDeclaration)
        || parent_kind == Some(ast::Kind::QualifiedName)
            && nodes[parent.unwrap()].as_qualified_name().left == Some(entity_name)
        || parent_kind == Some(ast::Kind::PropertyAccessExpression)
            && nodes[parent.unwrap()].expression() == Some(entity_name)
        || parent_kind == Some(ast::Kind::ElementAccessExpression)
            && nodes[parent.unwrap()].expression() == Some(entity_name)
    {
        // Left identifier from type reference or TypeAlias
        // Entity name of the import declaration
        return ast::SymbolFlags::NAMESPACE;
    }
    // Type Reference or TypeAlias entity = Identifier
    ast::SymbolFlags::TYPE
}

impl Checker {
    /// `(c *Checker) isDeclarationVisible`.
    pub(crate) fn is_declaration_visible(&mut self, node: NodeId) -> bool {
        {
            let nodes = self.program_nodes(node);
            if !ast::is_parse_tree_node(&nodes[node]) {
                return false;
            }
        }

        let is_visible = self
            .emit_resolver_links
            .declaration_links
            .get(node)
            .is_visible;
        if is_visible == Tristate::Unknown {
            let visible = self.determine_if_declaration_is_visible(node);
            self.emit_resolver_links
                .declaration_links
                .get(node)
                .is_visible = if visible {
                Tristate::True
            } else {
                Tristate::False
            };
        }
        self.emit_resolver_links
            .declaration_links
            .get(node)
            .is_visible
            == Tristate::True
    }

    /// `(c *Checker) determineIfDeclarationIsVisible`.
    pub(crate) fn determine_if_declaration_is_visible(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        match nodes[node].kind {
            ast::Kind::JSDocCallbackTag | ast::Kind::JSDocTypedefTag => {
                // Top-level jsdoc type aliases are considered exported
                // First parent is comment node, second is hosting
                // declaration or token; we only care about those tokens or
                // declarations whose parent is a source file
                let parent = nodes[node].parent;
                let grandparent = parent.and_then(|p| nodes[p].parent);
                let great_grandparent = grandparent.and_then(|p| nodes[p].parent);
                great_grandparent.is_some_and(|p| ast::is_source_file(&nodes[p]))
            }
            ast::Kind::BindingElement => {
                let Some(parent) = nodes[node].parent else {
                    return false;
                };
                let Some(grandparent) = nodes[parent].parent else {
                    return false;
                };
                self.is_declaration_visible(grandparent)
            }
            ast::Kind::VariableDeclaration
            | ast::Kind::ModuleDeclaration
            | ast::Kind::ClassDeclaration
            | ast::Kind::InterfaceDeclaration
            | ast::Kind::TypeAliasDeclaration
            | ast::Kind::JSTypeAliasDeclaration
            | ast::Kind::FunctionDeclaration
            | ast::Kind::EnumDeclaration
            | ast::Kind::ImportEqualsDeclaration => {
                if ast::is_variable_declaration(&nodes[node])
                    && nodes[node].name().is_some_and(|name| {
                        ast::is_binding_pattern(&nodes[name])
                            && nodes[name]
                                .elements()
                                .is_some_and(|elements| elements.is_empty())
                    })
                {
                    // If the binding pattern is empty, this variable
                    // declaration is not visible
                    return false;
                }
                // falls through
                // External module augmentation is always visible
                // A @typedef at top-level in an external module is always
                // visible
                if ast::is_external_module_augmentation(&nodes[node], &nodes)
                    || ast::is_implicitly_exported_js_doc_declaration(&nodes[node], &nodes)
                {
                    return true;
                }
                let parent =
                    ast::get_declaration_container(node, &nodes).expect("declaration container");
                // If the node is not exported or it is not ambient module
                // element (except import declaration)
                if !self
                    .get_combined_modifier_flags_cached(node)
                    .intersects(ast::ModifierFlags::EXPORT)
                    && !(nodes[node].kind != ast::Kind::ImportEqualsDeclaration
                        && nodes[parent].kind != ast::Kind::SourceFile
                        && nodes[parent].flags.intersects(ast::NodeFlags::AMBIENT))
                {
                    return ast::is_global_source_file(&nodes[parent], &nodes);
                }
                // Exported members/ambient module elements (exception import
                // declaration) are visible if parent is visible
                self.is_declaration_visible(parent)
            }
            ast::Kind::PropertyDeclaration
            | ast::Kind::PropertySignature
            | ast::Kind::GetAccessor
            | ast::Kind::SetAccessor
            | ast::Kind::MethodDeclaration
            | ast::Kind::MethodSignature => {
                if self.get_effective_declaration_flags(
                    node,
                    ast::ModifierFlags::PRIVATE | ast::ModifierFlags::PROTECTED,
                ) != ast::ModifierFlags::NONE
                {
                    // Private/protected properties/methods are not visible
                    return false;
                }
                // Public properties/methods are visible if its parents are
                // visible, so:
                let Some(parent) = nodes[node].parent else {
                    return false;
                };
                self.is_declaration_visible(parent)
            }
            ast::Kind::Constructor
            | ast::Kind::ConstructSignature
            | ast::Kind::CallSignature
            | ast::Kind::IndexSignature
            | ast::Kind::Parameter
            | ast::Kind::ModuleBlock
            | ast::Kind::FunctionType
            | ast::Kind::ConstructorType
            | ast::Kind::TypeLiteral
            | ast::Kind::TypeReference
            | ast::Kind::ArrayType
            | ast::Kind::TupleType
            | ast::Kind::UnionType
            | ast::Kind::IntersectionType
            | ast::Kind::ParenthesizedType
            | ast::Kind::NamedTupleMember => {
                let Some(parent) = nodes[node].parent else {
                    return false;
                };
                self.is_declaration_visible(parent)
            }
            // Default binding, import specifier and namespace import is
            // visible only on demand so by default it is not visible
            ast::Kind::ImportClause | ast::Kind::NamespaceImport | ast::Kind::ImportSpecifier => {
                false
            }
            // Type parameters are always visible
            ast::Kind::TypeParameter => true,
            // Source file and namespace export are always visible
            ast::Kind::SourceFile | ast::Kind::NamespaceExportDeclaration => true,
            // Export assignments do not create name bindings outside the
            // module
            ast::Kind::ExportAssignment => false,
            // An `export {X}` (without a module specifier) is itself a
            // visible re-export of the named binding; it contributes to the
            // symbol's external visibility.
            ast::Kind::ExportSpecifier => {
                let export_decl = nodes[node].parent.and_then(|p| nodes[p].parent);
                if let Some(export_decl) = export_decl
                    && ast::is_export_declaration(&nodes[export_decl])
                    && nodes[export_decl]
                        .as_export_declaration()
                        .module_specifier
                        .is_none()
                {
                    let Some(parent) = nodes[export_decl].parent else {
                        return false;
                    };
                    return self.is_declaration_visible(parent);
                }
                false
            }
            _ => false,
        }
    }

    /// `(c *Checker) isEntityNameVisible`.
    pub(crate) fn is_entity_name_visible(
        &mut self,
        entity_name: NodeId,
        enclosing_declaration: Option<NodeId>,
        should_compute_alias_to_make_visible: bool,
    ) -> SymbolAccessibilityResult {
        let nodes = self.program_nodes(entity_name);
        if !ast::is_parse_tree_node(&nodes[entity_name]) {
            return SymbolAccessibilityResult {
                accessibility: SymbolAccessibility::NotAccessible,
                ..Default::default()
            };
        }

        let meaning = get_meaning_of_entity_name_reference(entity_name, &nodes);
        let first_identifier = ast::get_first_identifier(entity_name, &nodes);
        let first_identifier_text = nodes[first_identifier].text(&nodes).into_owned();

        let symbol = call_resolve_name(
            self,
            enclosing_declaration,
            &first_identifier_text,
            meaning,
            None,  /*nameNotFoundMessage*/
            false, /*isUse*/
            false, /*excludeGlobals*/
        );

        if let Some(symbol) = symbol
            && self
                .sym(symbol)
                .flags
                .intersects(ast::SymbolFlags::TYPE_PARAMETER)
            && meaning.intersects(ast::SymbolFlags::TYPE)
        {
            return SymbolAccessibilityResult {
                accessibility: SymbolAccessibility::Accessible,
                ..Default::default()
            };
        }

        if symbol.is_none() && ast::is_this_identifier(&nodes[first_identifier]) {
            let this_container = self.get_this_container(first_identifier, false, false);
            let sym = self.get_symbol_of_declaration(this_container);
            if self
                .is_symbol_accessible(sym, enclosing_declaration, meaning, false)
                .accessibility
                == SymbolAccessibility::Accessible
            {
                return SymbolAccessibilityResult {
                    accessibility: SymbolAccessibility::Accessible,
                    ..Default::default()
                };
            }
        }

        if symbol.is_none() {
            return SymbolAccessibilityResult {
                accessibility: SymbolAccessibility::NotResolved,
                error_symbol_name: first_identifier_text,
                error_node: Some(first_identifier),
                ..Default::default()
            };
        }

        if let Some(visible) =
            self.has_visible_declarations(symbol.unwrap(), should_compute_alias_to_make_visible)
        {
            return visible;
        }

        SymbolAccessibilityResult {
            accessibility: SymbolAccessibility::NotAccessible,
            error_symbol_name: first_identifier_text,
            error_node: Some(first_identifier),
            ..Default::default()
        }
    }

    /// `addVisibleAlias` — the `shouldComputeAliasToMakeVisible` branch of
    /// the `hasVisibleDeclarations` closure (see the header note on why this
    /// is a method).
    fn add_visible_alias(
        &mut self,
        declaration: NodeId,
        aliasing_statement: NodeId,
        aliases_to_make_visible_set: &mut Option<FxHashMap<NodeId, NodeId>>,
    ) {
        self.emit_resolver_links
            .declaration_links
            .get(declaration)
            .is_visible = Tristate::True;
        let nodes = self.program_nodes(declaration);
        let declaration_id = ast::get_node_id(&nodes[declaration]);
        aliases_to_make_visible_set
            .get_or_insert_with(FxHashMap::default)
            .insert(declaration_id, aliasing_statement);
    }

    /// `(c *Checker) hasVisibleDeclarations` — `nil` → `None`.
    pub(crate) fn has_visible_declarations(
        &mut self,
        symbol: SymbolId,
        should_compute_alias_to_make_visible: bool,
    ) -> Option<SymbolAccessibilityResult> {
        // `aliasesToMakeVisibleSet map[ast.NodeId]*ast.Node` — lazily
        // allocated like the Go nil map.
        let mut aliases_to_make_visible_set: Option<FxHashMap<NodeId, NodeId>> = None;
        // When `!shouldComputeAliasToMakeVisible` Go installs
        // `noopAddVisibleAlias`; the call sites below gate on the flag
        // instead.

        let declarations = self.sym(symbol).declarations.clone();
        for declaration in declarations {
            let nodes = self.program_nodes(declaration);
            if ast::is_identifier(&nodes[declaration]) {
                continue;
            }
            if !self.is_declaration_visible(declaration) {
                // Mark the unexported alias as visible if its parent is
                // visible because these kind of aliases can be used to name
                // types in declaration file
                let any_import_syntax = get_any_import_syntax(declaration, &nodes);
                if let Some(any_import_syntax) = any_import_syntax
                    && !ast::has_syntactic_modifier(
                        &nodes[any_import_syntax],
                        ast::ModifierFlags::EXPORT,
                    ) // import clause without export
                    && let Some(parent) = nodes[any_import_syntax].parent
                    && self.is_declaration_visible(parent)
                {
                    if should_compute_alias_to_make_visible {
                        self.add_visible_alias(
                            declaration,
                            any_import_syntax,
                            &mut aliases_to_make_visible_set,
                        );
                    }
                    continue;
                }
                if ast::is_variable_declaration(&nodes[declaration])
                    && let Some(variable_declaration_list) = nodes[declaration].parent
                    && let Some(variable_statement) = nodes[variable_declaration_list].parent
                    && ast::is_variable_statement(&nodes[variable_statement])
                    && !ast::has_syntactic_modifier(
                        &nodes[variable_statement],
                        ast::ModifierFlags::EXPORT,
                    ) // unexported variable statement
                    && let Some(container) = nodes[variable_statement].parent
                    && self.is_declaration_visible(container)
                {
                    if should_compute_alias_to_make_visible {
                        self.add_visible_alias(
                            declaration,
                            variable_statement,
                            &mut aliases_to_make_visible_set,
                        );
                    }
                    continue;
                }
                if ast::is_late_visibility_painted_statement(&nodes[declaration]) // unexported top-level statement
                    && !ast::has_syntactic_modifier(
                        &nodes[declaration],
                        ast::ModifierFlags::EXPORT,
                    )
                    && let Some(parent) = nodes[declaration].parent
                    && self.is_declaration_visible(parent)
                {
                    if should_compute_alias_to_make_visible {
                        self.add_visible_alias(
                            declaration,
                            declaration,
                            &mut aliases_to_make_visible_set,
                        );
                    }
                    continue;
                }
                if ast::is_binding_element(&nodes[declaration]) {
                    if self.sym(symbol).flags.intersects(ast::SymbolFlags::ALIAS)
                        && ast::is_in_js_file(Some(declaration), &nodes)
                        && let Some(binding_pattern) = nodes[declaration].parent
                        && let Some(variable_declaration) = nodes[binding_pattern].parent
                        && ast::is_variable_declaration(&nodes[variable_declaration])
                        && let Some(variable_declaration_list) =
                            nodes[variable_declaration].parent
                        && let Some(variable_statement) =
                            nodes[variable_declaration_list].parent
                        && ast::is_variable_statement(&nodes[variable_statement])
                        && !ast::has_syntactic_modifier(
                            &nodes[variable_statement],
                            ast::ModifierFlags::EXPORT,
                        )
                        // check if the thing containing the variable
                        // statement is visible (ie, the file)
                        && let Some(container) = nodes[variable_statement].parent
                        && self.is_declaration_visible(container)
                    {
                        // exported import-like top-level JS require statement
                        if should_compute_alias_to_make_visible {
                            self.add_visible_alias(
                                declaration,
                                variable_statement,
                                &mut aliases_to_make_visible_set,
                            );
                        }
                        continue;
                    }
                    if self
                        .sym(symbol)
                        .flags
                        .intersects(ast::SymbolFlags::BLOCK_SCOPED_VARIABLE)
                    {
                        let root_declaration =
                            ast::walk_up_binding_elements_and_patterns(declaration, &nodes);
                        if let Some(root_declaration) = root_declaration
                            && ast::is_parameter_declaration(&nodes[root_declaration])
                        {
                            return None;
                        }
                        let Some(root_declaration) = root_declaration else {
                            return None;
                        };
                        let variable_statement =
                            nodes[root_declaration].parent.and_then(|p| nodes[p].parent);
                        let Some(variable_statement) = variable_statement else {
                            return None;
                        };
                        if !ast::is_variable_statement(&nodes[variable_statement]) {
                            return None;
                        }
                        if ast::has_syntactic_modifier(
                            &nodes[variable_statement],
                            ast::ModifierFlags::EXPORT,
                        ) {
                            continue; // no alias to add, already exported
                        }
                        let Some(container) = nodes[variable_statement].parent else {
                            return None;
                        };
                        if !self.is_declaration_visible(container) {
                            return None; // not visible
                        }
                        if should_compute_alias_to_make_visible {
                            self.add_visible_alias(
                                declaration,
                                variable_statement,
                                &mut aliases_to_make_visible_set,
                            );
                        }
                        continue;
                    }
                }

                // Declaration is not visible
                return None;
            }
        }

        Some(SymbolAccessibilityResult {
            accessibility: SymbolAccessibility::Accessible,
            aliases_to_make_visible: aliases_to_make_visible_set
                .map(|set| set.into_values().collect())
                .unwrap_or_default(),
            ..Default::default()
        })
    }

    /// `(c *Checker) requiresAddingImplicitUndefined`.
    pub(crate) fn requires_adding_implicit_undefined(
        &mut self,
        declaration: NodeId,
        symbol: Option<SymbolId>,
        enclosing_declaration: Option<NodeId>,
    ) -> bool {
        {
            let nodes = self.program_nodes(declaration);
            if !ast::is_parse_tree_node(&nodes[declaration]) {
                return false;
            }
            match nodes[declaration].kind {
                ast::Kind::PropertyDeclaration
                | ast::Kind::PropertySignature
                | ast::Kind::JSDocPropertyTag => {
                    let symbol = symbol
                        .or_else(|| self.get_symbol_of_declaration(declaration))
                        .expect("symbol");
                    let t = self.get_type_of_symbol(symbol);
                    // `c.mappedSymbolLinks.Has(symbol)` — dead statement in
                    // Go (the result is discarded); ported verbatim.
                    let _ = self.mapped_symbol_links.has(&symbol);
                    let flags = self.sym(symbol).flags;
                    return flags.intersects(ast::SymbolFlags::PROPERTY)
                        && flags.intersects(ast::SymbolFlags::OPTIONAL)
                        && crate::utilities::is_optional_declaration(&nodes[declaration], &nodes)
                        && self.reverse_mapped_symbol_links.has(&symbol)
                        && self
                            .reverse_mapped_symbol_links
                            .get(symbol)
                            .mapped_type
                            .is_some()
                        && contains_non_missing_undefined_type(self, t);
                }
                ast::Kind::Parameter | ast::Kind::JSDocParameterTag => {
                    // hand off after the arena borrow is released
                }
                _ => panic!("Node cannot possibly require adding undefined"),
            }
        }
        self.requires_adding_implicit_undefined_worker(declaration, enclosing_declaration)
    }

    /// `(c *Checker) requiresAddingImplicitUndefinedWorker`.
    pub(crate) fn requires_adding_implicit_undefined_worker(
        &mut self,
        parameter: NodeId,
        enclosing_declaration: Option<NodeId>,
    ) -> bool {
        (self.is_required_initialized_parameter(parameter, enclosing_declaration)
            || self.is_optional_uninitialized_parameter_property(parameter))
            && !self.declared_parameter_type_contains_undefined(parameter)
    }

    /// `(c *Checker) declaredParameterTypeContainsUndefined`.
    pub(crate) fn declared_parameter_type_contains_undefined(&mut self, parameter: NodeId) -> bool {
        // typeNode := getNonlocalEffectiveTypeAnnotationNode(parameter); // !!! JSDoc Support
        let nodes = self.program_nodes(parameter);
        let Some(type_node) = nodes[parameter].type_() else {
            return false;
        };
        drop(nodes);
        let t = self.get_type_from_type_node(type_node);
        // allow error type here to avoid confusing errors that the
        // annotation has to contain undefined when it does in cases like
        // this:
        //
        // export function fn(x?: Unresolved | undefined): void {}
        self.is_error_type(t) || self.contains_undefined_type(t)
    }

    /// `(c *Checker) isOptionalUninitializedParameterProperty`.
    pub(crate) fn is_optional_uninitialized_parameter_property(
        &mut self,
        parameter: NodeId,
    ) -> bool {
        let nodes = self.program_nodes(parameter);
        self.strict_null_checks
            && self.is_optional_parameter(parameter)
            && ( /*isJSDocParameterTag(parameter) ||*/ nodes[parameter].initializer().is_none())
            // !!! TODO: JSDoc support
            && ast::has_syntactic_modifier(
                &nodes[parameter],
                ast::ModifierFlags::PARAMETER_PROPERTY_MODIFIER,
            )
    }

    /// `(c *Checker) isRequiredInitializedParameter`.
    pub(crate) fn is_required_initialized_parameter(
        &mut self,
        parameter: NodeId,
        enclosing_declaration: Option<NodeId>,
    ) -> bool {
        let nodes = self.program_nodes(parameter);
        if !self.strict_null_checks
            || self.is_optional_parameter(parameter)
            || /*isJSDocParameterTag(parameter) ||*/ nodes[parameter].initializer().is_none()
        // !!! TODO: JSDoc Support
        {
            return false;
        }
        if ast::has_syntactic_modifier(
            &nodes[parameter],
            ast::ModifierFlags::PARAMETER_PROPERTY_MODIFIER,
        ) {
            return enclosing_declaration.is_some_and(|d| {
                let decl_nodes = self.program_nodes(d);
                ast::is_function_like_declaration(Some(d), &decl_nodes)
            });
        }
        true
    }
}
