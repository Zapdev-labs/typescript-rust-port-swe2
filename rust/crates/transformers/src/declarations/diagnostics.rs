// Ported from tsc/internal/transformers/declarations/diagnostics.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The diagnostic-selection machinery the declaration transform installs into
// `SymbolTrackerSharedState::get_symbol_accessibility_diagnostic`, plus the
// `isolatedDeclarations` diagnostic constructors.
//
// PORT: Go's `*ast.Diagnostic` results are `DiagnosticRef`
// (`Arc<Mutex<Diagnostic>>`). Closures that Go types as
// `GetSymbolAccessibilityDiagnostic` are boxed `Fn` values which also take
// the `&[Node]` arena (Go closures reach nodes through pointers). The
// `checker.NewDiagnosticForNode` helper is reimplemented as
// `crate::declarations::tracker::create_diagnostic_for_node` — the checker
// type that hosted it is not part of this crate (see PORTING-NOTES).

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::diagnostic::DiagnosticRef;
use tsc_ast::{self as ast, Kind, Node, NodeId, Symbol};
use tsc_diagnostics::Message;
use tsc_printer::{EmitResolver, SymbolAccessibility, SymbolAccessibilityResult};

use crate::declarations::tracker::{create_diagnostic_for_node, SymbolTrackerSharedState};

/// `type SymbolAccessibilityDiagnostic struct`.
pub struct SymbolAccessibilityDiagnostic {
    pub error_node: Option<NodeId>,
    pub diagnostic_message: &'static Message,
    pub type_name: Option<NodeId>,
}

/// `type GetSymbolAccessibilityDiagnostic = func(symbolAccessibilityResult printer.SymbolAccessibilityResult) *SymbolAccessibilityDiagnostic`.
///
/// PORT: the arena is threaded through as a parameter since Go's closure
/// reads `*ast.Node` fields through pointers.
pub type GetSymbolAccessibilityDiagnostic =
    Box<dyn Fn(&SymbolAccessibilityResult, &[Node]) -> Option<SymbolAccessibilityDiagnostic>>;

/// `func(node, result) *diagnostics.Message` — a plain function pointer;
/// every selector in this file is non-capturing.
type SelectorFn = fn(NodeId, &SymbolAccessibilityResult, &[Node]) -> Option<&'static Message>;

/// `wrapSimpleDiagnosticSelector(node, selector)`.
pub(crate) fn wrap_simple_diagnostic_selector(
    node: NodeId,
    selector: SelectorFn,
) -> GetSymbolAccessibilityDiagnostic {
    Box::new(move |result, nodes| {
        let diagnostic_message = selector(node, result, nodes)?;
        Some(SymbolAccessibilityDiagnostic {
            error_node: Some(node),
            diagnostic_message,
            type_name: ast::get_name_of_declaration(Some(node), nodes),
        })
    })
}

/// `wrapNamedDiagnosticSelector(node, selector)`.
pub(crate) fn wrap_named_diagnostic_selector(
    node: NodeId,
    selector: SelectorFn,
) -> GetSymbolAccessibilityDiagnostic {
    Box::new(move |result, nodes| {
        let diagnostic_message = selector(node, result, nodes)?;
        let name = ast::get_name_of_declaration(Some(node), nodes);
        Some(SymbolAccessibilityDiagnostic {
            error_node: name,
            diagnostic_message,
            type_name: name,
        })
    })
}

/// `wrapFallbackErrorDiagnosticSelector(node, selector)`.
pub(crate) fn wrap_fallback_error_diagnostic_selector(
    node: NodeId,
    selector: SelectorFn,
) -> GetSymbolAccessibilityDiagnostic {
    Box::new(move |result, nodes| {
        let diagnostic_message = selector(node, result, nodes)?;
        let error_node = ast::get_name_of_declaration(Some(node), nodes).or(Some(node));
        Some(SymbolAccessibilityDiagnostic {
            error_node,
            diagnostic_message,
            type_name: None,
        })
    })
}

/// `selectDiagnosticBasedOnModuleName`.
fn select_diagnostic_based_on_module_name(
    result: &SymbolAccessibilityResult,
    module_not_nameable: &'static Message,
    private_module: &'static Message,
    non_module: &'static Message,
) -> &'static Message {
    if !result.error_module_name.is_empty() {
        if result.accessibility == SymbolAccessibility::CannotBeNamed {
            return module_not_nameable;
        }
        return private_module;
    }
    non_module
}

/// `selectDiagnosticBasedOnModuleNameNoNameCheck`.
fn select_diagnostic_based_on_module_name_no_name_check(
    result: &SymbolAccessibilityResult,
    private_module: &'static Message,
    non_module: &'static Message,
) -> &'static Message {
    if !result.error_module_name.is_empty() {
        return private_module;
    }
    non_module
}

/// `createGetSymbolAccessibilityDiagnosticForNodeName(node)`.
pub(crate) fn create_get_symbol_accessibility_diagnostic_for_node_name(
    node: NodeId,
    nodes: &[Node],
) -> GetSymbolAccessibilityDiagnostic {
    if ast::is_set_accessor_declaration(&nodes[node])
        || ast::is_get_accessor_declaration(&nodes[node])
    {
        wrap_simple_diagnostic_selector(node, get_accessor_name_visibility_diagnostic_message)
    } else if ast::is_method_declaration(&nodes[node])
        || ast::is_method_signature_declaration(&nodes[node])
    {
        wrap_simple_diagnostic_selector(node, get_method_name_visibility_diagnostic_message)
    } else {
        create_get_symbol_accessibility_diagnostic_for_node(node, nodes)
    }
}

/// `getAccessorNameVisibilityDiagnosticMessage`.
fn get_accessor_name_visibility_diagnostic_message(
    node: NodeId,
    result: &SymbolAccessibilityResult,
    nodes: &[Node],
) -> Option<&'static Message> {
    if ast::is_static(&nodes[node]) {
        Some(select_diagnostic_based_on_module_name(
            result,
            &tsc_diagnostics::Public_static_property_0_of_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            &tsc_diagnostics::Public_static_property_0_of_exported_class_has_or_is_using_name_1_from_private_module_2,
            &tsc_diagnostics::Public_static_property_0_of_exported_class_has_or_is_using_private_name_1,
        ))
    } else if nodes[node]
        .parent
        .is_some_and(|p| nodes[p].kind == Kind::ClassDeclaration)
    {
        Some(select_diagnostic_based_on_module_name(
            result,
            &tsc_diagnostics::Public_property_0_of_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            &tsc_diagnostics::Public_property_0_of_exported_class_has_or_is_using_name_1_from_private_module_2,
            &tsc_diagnostics::Public_property_0_of_exported_class_has_or_is_using_private_name_1,
        ))
    } else {
        Some(select_diagnostic_based_on_module_name_no_name_check(
            result,
            &tsc_diagnostics::Property_0_of_exported_interface_has_or_is_using_name_1_from_private_module_2,
            &tsc_diagnostics::Property_0_of_exported_interface_has_or_is_using_private_name_1,
        ))
    }
}

/// `getMethodNameVisibilityDiagnosticMessage`.
fn get_method_name_visibility_diagnostic_message(
    node: NodeId,
    result: &SymbolAccessibilityResult,
    nodes: &[Node],
) -> Option<&'static Message> {
    if ast::is_static(&nodes[node]) {
        Some(select_diagnostic_based_on_module_name(
            result,
            &tsc_diagnostics::Public_static_method_0_of_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            &tsc_diagnostics::Public_static_method_0_of_exported_class_has_or_is_using_name_1_from_private_module_2,
            &tsc_diagnostics::Public_static_method_0_of_exported_class_has_or_is_using_private_name_1,
        ))
    } else if nodes[node]
        .parent
        .is_some_and(|p| nodes[p].kind == Kind::ClassDeclaration)
    {
        Some(select_diagnostic_based_on_module_name(
            result,
            &tsc_diagnostics::Public_method_0_of_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            &tsc_diagnostics::Public_method_0_of_exported_class_has_or_is_using_name_1_from_private_module_2,
            &tsc_diagnostics::Public_method_0_of_exported_class_has_or_is_using_private_name_1,
        ))
    } else {
        Some(select_diagnostic_based_on_module_name_no_name_check(
            result,
            &tsc_diagnostics::Method_0_of_exported_interface_has_or_is_using_name_1_from_private_module_2,
            &tsc_diagnostics::Method_0_of_exported_interface_has_or_is_using_private_name_1,
        ))
    }
}

/// `createGetSymbolAccessibilityDiagnosticForNode(node)`.
pub(crate) fn create_get_symbol_accessibility_diagnostic_for_node(
    node: NodeId,
    nodes: &[Node],
) -> GetSymbolAccessibilityDiagnostic {
    let n = &nodes[node];
    if ast::is_variable_declaration(n)
        || ast::is_property_declaration(n)
        || ast::is_property_signature_declaration(n)
        || ast::is_property_access_expression(n)
        || ast::is_element_access_expression(n)
        || ast::is_binary_expression(n)
        || ast::is_binding_element(n)
        || ast::is_constructor_declaration(n)
    {
        wrap_simple_diagnostic_selector(
            node,
            get_variable_declaration_type_visibility_diagnostic_message,
        )
    } else if ast::is_set_accessor_declaration(n) || ast::is_get_accessor_declaration(n) {
        wrap_named_diagnostic_selector(
            node,
            get_accessor_declaration_type_visibility_diagnostic_message,
        )
    } else if ast::is_construct_signature_declaration(n)
        || ast::is_call_signature_declaration(n)
        || ast::is_method_declaration(n)
        || ast::is_method_signature_declaration(n)
        || ast::is_function_declaration(n)
        || ast::is_index_signature_declaration(n)
    {
        wrap_fallback_error_diagnostic_selector(node, get_return_type_visibility_diagnostic_message)
    } else if ast::is_parameter_declaration(n) {
        if n.parent.is_some_and(|p| {
            ast::is_parameter_property_declaration(n, &nodes[p])
                && ast::has_syntactic_modifier(&nodes[p], ast::ModifierFlags::PRIVATE)
        }) {
            return wrap_simple_diagnostic_selector(
                node,
                get_variable_declaration_type_visibility_diagnostic_message,
            );
        }
        wrap_simple_diagnostic_selector(
            node,
            get_parameter_declaration_type_visibility_diagnostic_message,
        )
    } else if ast::is_type_parameter_declaration(n) {
        wrap_simple_diagnostic_selector(
            node,
            get_type_parameter_constraint_visibility_diagnostic_message,
        )
    } else if ast::is_expression_with_type_arguments(n) {
        // unique node selection behavior, inline closure
        Box::new(move |_result: &SymbolAccessibilityResult, nodes: &[Node]| {
            let diagnostic_message;
            // Heritage clause is written by user so it can always be named
            let grandparent = nodes[node].parent.and_then(|p| nodes[p].parent);
            if grandparent.is_some_and(|p| ast::is_class_declaration(&nodes[p])) {
                // Class or Interface implemented/extended is inaccessible
                if nodes[node].parent.is_some_and(|p| {
                    ast::is_heritage_clause(&nodes[p])
                        && nodes[p].as_heritage_clause().token == Kind::ImplementsKeyword
                }) {
                    diagnostic_message =
                        &tsc_diagnostics::Implements_clause_of_exported_class_0_has_or_is_using_private_name_1;
                } else if grandparent.is_some_and(|p| nodes[p].name().is_some()) {
                    diagnostic_message =
                        &tsc_diagnostics::X_extends_clause_of_exported_class_0_has_or_is_using_private_name_1;
                } else {
                    diagnostic_message =
                        &tsc_diagnostics::X_extends_clause_of_exported_class_has_or_is_using_private_name_0;
                }
            } else {
                // interface is inaccessible
                diagnostic_message =
                    &tsc_diagnostics::X_extends_clause_of_exported_interface_0_has_or_is_using_private_name_1;
            }

            Some(SymbolAccessibilityDiagnostic {
                diagnostic_message,
                error_node: Some(node),
                type_name: ast::get_name_of_declaration(grandparent, nodes),
            })
        })
    } else if ast::is_import_equals_declaration(n) {
        wrap_simple_diagnostic_selector(node, |_n, _result, _nodes| {
            Some(&tsc_diagnostics::Import_declaration_0_is_using_private_name_1)
        })
    } else if ast::is_type_alias_declaration(n) || ast::is_js_type_alias_declaration(n) {
        // unique node selection behavior, inline closure
        Box::new(move |result: &SymbolAccessibilityResult, nodes: &[Node]| {
            let diagnostic_message = select_diagnostic_based_on_module_name_no_name_check(
                result,
                &tsc_diagnostics::Exported_type_alias_0_has_or_is_using_private_name_1_from_module_2,
                &tsc_diagnostics::Exported_type_alias_0_has_or_is_using_private_name_1,
            );
            let error_node = nodes[node].type_();
            let type_name = nodes[node].name();
            Some(SymbolAccessibilityDiagnostic {
                error_node,
                diagnostic_message,
                type_name,
            })
        })
    } else if ast::is_call_expression(n) {
        // JS object.defineProperty call
        // unique node selection behavior, inline closure
        Box::new(move |result: &SymbolAccessibilityResult, nodes: &[Node]| {
            let diagnostic_message = select_diagnostic_based_on_module_name(
                result,
                &tsc_diagnostics::Exported_variable_0_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
                &tsc_diagnostics::Exported_variable_0_has_or_is_using_name_1_from_private_module_2,
                &tsc_diagnostics::Exported_variable_0_has_or_is_using_private_name_1,
            );
            let arg = nodes[node].arguments().map(|a| a[1]);
            Some(SymbolAccessibilityDiagnostic {
                error_node: arg,
                diagnostic_message,
                type_name: arg,
            })
        })
    } else {
        panic!(
            "Attempted to set a declaration diagnostic context for unhandled node kind: {}",
            n.kind_string()
        )
    }
}

/// `getVariableDeclarationTypeVisibilityDiagnosticMessage`.
fn get_variable_declaration_type_visibility_diagnostic_message(
    node: NodeId,
    result: &SymbolAccessibilityResult,
    nodes: &[Node],
) -> Option<&'static Message> {
    let kind = nodes[node].kind;
    if kind == Kind::VariableDeclaration || kind == Kind::BindingElement {
        return Some(select_diagnostic_based_on_module_name(
            result,
            &tsc_diagnostics::Exported_variable_0_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            &tsc_diagnostics::Exported_variable_0_has_or_is_using_name_1_from_private_module_2,
            &tsc_diagnostics::Exported_variable_0_has_or_is_using_private_name_1,
        ));

        // This check is to ensure we don't report error on constructor parameter property as that error would be reported during parameter emit
        // The only exception here is if the constructor was marked as private. we are not emitting the constructor parameters at all.
    } else if kind == Kind::PropertyDeclaration
        || kind == Kind::PropertyAccessExpression
        || kind == Kind::ElementAccessExpression
        || kind == Kind::BinaryExpression
        || kind == Kind::PropertySignature
        || (kind == Kind::Parameter
            && nodes[node].parent.is_some_and(|p| {
                ast::has_syntactic_modifier(&nodes[p], ast::ModifierFlags::PRIVATE)
            }))
    {
        // TODO(jfreeman): Deal with computed properties in error reporting.
        if ast::is_static(&nodes[node]) {
            return Some(select_diagnostic_based_on_module_name(
                result,
                &tsc_diagnostics::Public_static_property_0_of_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
                &tsc_diagnostics::Public_static_property_0_of_exported_class_has_or_is_using_name_1_from_private_module_2,
                &tsc_diagnostics::Public_static_property_0_of_exported_class_has_or_is_using_private_name_1,
            ));
        } else if nodes[node]
            .parent
            .is_some_and(|p| nodes[p].kind == Kind::ClassDeclaration)
            || kind == Kind::Parameter
        {
            return Some(select_diagnostic_based_on_module_name(
                result,
                &tsc_diagnostics::Public_property_0_of_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
                &tsc_diagnostics::Public_property_0_of_exported_class_has_or_is_using_name_1_from_private_module_2,
                &tsc_diagnostics::Public_property_0_of_exported_class_has_or_is_using_private_name_1,
            ));
        } else {
            // Interfaces cannot have types that cannot be named
            return Some(select_diagnostic_based_on_module_name_no_name_check(
                result,
                &tsc_diagnostics::Property_0_of_exported_interface_has_or_is_using_name_1_from_private_module_2,
                &tsc_diagnostics::Property_0_of_exported_interface_has_or_is_using_private_name_1,
            ));
        }
    }
    None // TODO: Audit behavior - should this panic? potentially silent error state in strada
}

/// `getAccessorDeclarationTypeVisibilityDiagnosticMessage`.
fn get_accessor_declaration_type_visibility_diagnostic_message(
    node: NodeId,
    result: &SymbolAccessibilityResult,
    nodes: &[Node],
) -> Option<&'static Message> {
    if nodes[node].kind == Kind::SetAccessor {
        // Getters can infer the return type from the returned expression, but setters cannot, so the
        // "_from_external_module_1_but_cannot_be_named" case cannot occur.
        if ast::is_static(&nodes[node]) {
            Some(select_diagnostic_based_on_module_name_no_name_check(
                result,
                &tsc_diagnostics::Parameter_type_of_public_static_setter_0_from_exported_class_has_or_is_using_name_1_from_private_module_2,
                &tsc_diagnostics::Parameter_type_of_public_static_setter_0_from_exported_class_has_or_is_using_private_name_1,
            ))
        } else {
            Some(select_diagnostic_based_on_module_name_no_name_check(
                result,
                &tsc_diagnostics::Parameter_type_of_public_setter_0_from_exported_class_has_or_is_using_name_1_from_private_module_2,
                &tsc_diagnostics::Parameter_type_of_public_setter_0_from_exported_class_has_or_is_using_private_name_1,
            ))
        }
    } else if ast::is_static(&nodes[node]) {
        Some(select_diagnostic_based_on_module_name(
            result,
            &tsc_diagnostics::Return_type_of_public_static_getter_0_from_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            &tsc_diagnostics::Return_type_of_public_static_getter_0_from_exported_class_has_or_is_using_name_1_from_private_module_2,
            &tsc_diagnostics::Return_type_of_public_static_getter_0_from_exported_class_has_or_is_using_private_name_1,
        ))
    } else {
        Some(select_diagnostic_based_on_module_name(
            result,
            &tsc_diagnostics::Return_type_of_public_getter_0_from_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            &tsc_diagnostics::Return_type_of_public_getter_0_from_exported_class_has_or_is_using_name_1_from_private_module_2,
            &tsc_diagnostics::Return_type_of_public_getter_0_from_exported_class_has_or_is_using_private_name_1,
        ))
    }
}

/// `getReturnTypeVisibilityDiagnosticMessage`.
fn get_return_type_visibility_diagnostic_message(
    node: NodeId,
    result: &SymbolAccessibilityResult,
    nodes: &[Node],
) -> Option<&'static Message> {
    match nodes[node].kind {
        Kind::ConstructSignature => {
            // Interfaces cannot have return types that cannot be named
            Some(select_diagnostic_based_on_module_name_no_name_check(
                result,
                &tsc_diagnostics::Return_type_of_constructor_signature_from_exported_interface_has_or_is_using_name_0_from_private_module_1,
                &tsc_diagnostics::Return_type_of_constructor_signature_from_exported_interface_has_or_is_using_private_name_0,
            ))
        }
        Kind::CallSignature => {
            // Interfaces cannot have return types that cannot be named
            Some(select_diagnostic_based_on_module_name_no_name_check(
                result,
                &tsc_diagnostics::Return_type_of_call_signature_from_exported_interface_has_or_is_using_name_0_from_private_module_1,
                &tsc_diagnostics::Return_type_of_call_signature_from_exported_interface_has_or_is_using_private_name_0,
            ))
        }
        Kind::IndexSignature => {
            // Interfaces cannot have return types that cannot be named
            Some(select_diagnostic_based_on_module_name_no_name_check(
                result,
                &tsc_diagnostics::Return_type_of_index_signature_from_exported_interface_has_or_is_using_name_0_from_private_module_1,
                &tsc_diagnostics::Return_type_of_index_signature_from_exported_interface_has_or_is_using_private_name_0,
            ))
        }
        Kind::MethodDeclaration | Kind::MethodSignature => {
            if ast::is_static(&nodes[node]) {
                Some(select_diagnostic_based_on_module_name(
                    result,
                    &tsc_diagnostics::Return_type_of_public_static_method_from_exported_class_has_or_is_using_name_0_from_external_module_1_but_cannot_be_named,
                    &tsc_diagnostics::Return_type_of_public_static_method_from_exported_class_has_or_is_using_name_0_from_private_module_1,
                    &tsc_diagnostics::Return_type_of_public_static_method_from_exported_class_has_or_is_using_private_name_0,
                ))
            } else if nodes[node].parent.is_some_and(|p| nodes[p].kind == Kind::ClassDeclaration)
            {
                Some(select_diagnostic_based_on_module_name(
                    result,
                    &tsc_diagnostics::Return_type_of_public_method_from_exported_class_has_or_is_using_name_0_from_external_module_1_but_cannot_be_named,
                    &tsc_diagnostics::Return_type_of_public_method_from_exported_class_has_or_is_using_name_0_from_private_module_1,
                    &tsc_diagnostics::Return_type_of_public_method_from_exported_class_has_or_is_using_private_name_0,
                ))
            } else {
                // Interfaces cannot have return types that cannot be named
                Some(select_diagnostic_based_on_module_name_no_name_check(
                    result,
                    &tsc_diagnostics::Return_type_of_method_from_exported_interface_has_or_is_using_name_0_from_private_module_1,
                    &tsc_diagnostics::Return_type_of_method_from_exported_interface_has_or_is_using_private_name_0,
                ))
            }
        }
        Kind::FunctionDeclaration => Some(select_diagnostic_based_on_module_name(
            result,
            &tsc_diagnostics::Return_type_of_exported_function_has_or_is_using_name_0_from_external_module_1_but_cannot_be_named,
            &tsc_diagnostics::Return_type_of_exported_function_has_or_is_using_name_0_from_private_module_1,
            &tsc_diagnostics::Return_type_of_exported_function_has_or_is_using_private_name_0,
        )),
        kind => panic!("This is unknown kind for signature: {}", kind.kind_string()),
    }
}

/// `getParameterDeclarationTypeVisibilityDiagnosticMessage`.
fn get_parameter_declaration_type_visibility_diagnostic_message(
    node: NodeId,
    result: &SymbolAccessibilityResult,
    nodes: &[Node],
) -> Option<&'static Message> {
    match nodes[node].parent.map(|p| nodes[p].kind) {
        Some(Kind::Constructor) => Some(select_diagnostic_based_on_module_name(
            result,
            &tsc_diagnostics::Parameter_0_of_constructor_from_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            &tsc_diagnostics::Parameter_0_of_constructor_from_exported_class_has_or_is_using_name_1_from_private_module_2,
            &tsc_diagnostics::Parameter_0_of_constructor_from_exported_class_has_or_is_using_private_name_1,
        )),
        Some(Kind::ConstructSignature) | Some(Kind::ConstructorType) => {
            // Interfaces cannot have parameter types that cannot be named
            Some(select_diagnostic_based_on_module_name_no_name_check(
                result,
                &tsc_diagnostics::Parameter_0_of_constructor_signature_from_exported_interface_has_or_is_using_name_1_from_private_module_2,
                &tsc_diagnostics::Parameter_0_of_constructor_signature_from_exported_interface_has_or_is_using_private_name_1,
            ))
        }
        Some(Kind::CallSignature) => {
            // Interfaces cannot have parameter types that cannot be named
            Some(select_diagnostic_based_on_module_name_no_name_check(
                result,
                &tsc_diagnostics::Parameter_0_of_call_signature_from_exported_interface_has_or_is_using_name_1_from_private_module_2,
                &tsc_diagnostics::Parameter_0_of_call_signature_from_exported_interface_has_or_is_using_private_name_1,
            ))
        }
        Some(Kind::IndexSignature) => {
            // Interfaces cannot have parameter types that cannot be named
            Some(select_diagnostic_based_on_module_name_no_name_check(
                result,
                &tsc_diagnostics::Parameter_0_of_index_signature_from_exported_interface_has_or_is_using_name_1_from_private_module_2,
                &tsc_diagnostics::Parameter_0_of_index_signature_from_exported_interface_has_or_is_using_private_name_1,
            ))
        }
        Some(Kind::MethodDeclaration) | Some(Kind::MethodSignature) => {
            let parent = nodes[node].parent.unwrap();
            if ast::is_static(&nodes[parent]) {
                Some(select_diagnostic_based_on_module_name(
                    result,
                    &tsc_diagnostics::Parameter_0_of_public_static_method_from_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
                    &tsc_diagnostics::Parameter_0_of_public_static_method_from_exported_class_has_or_is_using_name_1_from_private_module_2,
                    &tsc_diagnostics::Parameter_0_of_public_static_method_from_exported_class_has_or_is_using_private_name_1,
                ))
            } else if nodes[parent]
                .parent
                .is_some_and(|p| nodes[p].kind == Kind::ClassDeclaration)
            {
                Some(select_diagnostic_based_on_module_name(
                    result,
                    &tsc_diagnostics::Parameter_0_of_public_method_from_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
                    &tsc_diagnostics::Parameter_0_of_public_method_from_exported_class_has_or_is_using_name_1_from_private_module_2,
                    &tsc_diagnostics::Parameter_0_of_public_method_from_exported_class_has_or_is_using_private_name_1,
                ))
            } else {
                // Interfaces cannot have parameter types that cannot be named
                Some(select_diagnostic_based_on_module_name_no_name_check(
                    result,
                    &tsc_diagnostics::Parameter_0_of_method_from_exported_interface_has_or_is_using_name_1_from_private_module_2,
                    &tsc_diagnostics::Parameter_0_of_method_from_exported_interface_has_or_is_using_private_name_1,
                ))
            }
        }
        Some(Kind::FunctionDeclaration)
        | Some(Kind::FunctionType)
        | Some(Kind::ArrowFunction)
        | Some(Kind::FunctionExpression) => Some(select_diagnostic_based_on_module_name(
            result,
            &tsc_diagnostics::Parameter_0_of_exported_function_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            &tsc_diagnostics::Parameter_0_of_exported_function_has_or_is_using_name_1_from_private_module_2,
            &tsc_diagnostics::Parameter_0_of_exported_function_has_or_is_using_private_name_1,
        )),
        Some(Kind::SetAccessor) | Some(Kind::GetAccessor) => {
            Some(select_diagnostic_based_on_module_name(
                result,
                &tsc_diagnostics::Parameter_0_of_accessor_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
                &tsc_diagnostics::Parameter_0_of_accessor_has_or_is_using_name_1_from_private_module_2,
                &tsc_diagnostics::Parameter_0_of_accessor_has_or_is_using_private_name_1,
            ))
        }
        other => panic!(
            "Unknown parent for parameter: {}",
            other.map_or("<none>".to_string(), |k| k.kind_string().to_string())
        ),
    }
}

/// `getTypeParameterConstraintVisibilityDiagnosticMessage`.
fn get_type_parameter_constraint_visibility_diagnostic_message(
    node: NodeId,
    _result: &SymbolAccessibilityResult,
    nodes: &[Node],
) -> Option<&'static Message> {
    // Type parameter constraints are named by user so we should always be able to name it
    match nodes[node].parent.map(|p| nodes[p].kind) {
        Some(Kind::ClassDeclaration) => {
            Some(&tsc_diagnostics::Type_parameter_0_of_exported_class_has_or_is_using_private_name_1)
        }
        Some(Kind::InterfaceDeclaration) => {
            Some(&tsc_diagnostics::Type_parameter_0_of_exported_interface_has_or_is_using_private_name_1)
        }
        Some(Kind::MappedType) => {
            Some(&tsc_diagnostics::Type_parameter_0_of_exported_mapped_object_type_is_using_private_name_1)
        }
        Some(Kind::ConstructorType) | Some(Kind::ConstructSignature) => {
            Some(&tsc_diagnostics::Type_parameter_0_of_constructor_signature_from_exported_interface_has_or_is_using_private_name_1)
        }
        Some(Kind::CallSignature) => {
            Some(&tsc_diagnostics::Type_parameter_0_of_call_signature_from_exported_interface_has_or_is_using_private_name_1)
        }
        Some(Kind::MethodDeclaration) | Some(Kind::MethodSignature) => {
            let parent = nodes[node].parent.unwrap();
            if ast::is_static(&nodes[parent]) {
                Some(&tsc_diagnostics::Type_parameter_0_of_public_static_method_from_exported_class_has_or_is_using_private_name_1)
            } else if nodes[parent]
                .parent
                .is_some_and(|p| nodes[p].kind == Kind::ClassDeclaration)
            {
                Some(&tsc_diagnostics::Type_parameter_0_of_public_method_from_exported_class_has_or_is_using_private_name_1)
            } else {
                Some(&tsc_diagnostics::Type_parameter_0_of_method_from_exported_interface_has_or_is_using_private_name_1)
            }
        }
        Some(Kind::FunctionType) | Some(Kind::FunctionDeclaration) => {
            Some(&tsc_diagnostics::Type_parameter_0_of_exported_function_has_or_is_using_private_name_1)
        }
        Some(Kind::InferType) => {
            Some(&tsc_diagnostics::Extends_clause_for_inferred_type_0_has_or_is_using_private_name_1)
        }
        Some(Kind::TypeAliasDeclaration) | Some(Kind::JSTypeAliasDeclaration) => {
            Some(&tsc_diagnostics::Type_parameter_0_of_exported_type_alias_has_or_is_using_private_name_1)
        }
        other => panic!(
            "This is unknown parent for type parameter: {}",
            other.map_or("<none>".to_string(), |k| k.kind_string().to_string())
        ),
    }
}

/// `getRelatedSuggestionByDeclarationKind(kind)`.
fn get_related_suggestion_by_declaration_kind(kind: Kind) -> Option<&'static Message> {
    match kind {
        Kind::ArrowFunction => Some(&tsc_diagnostics::Add_a_return_type_to_the_function_expression),
        Kind::FunctionExpression => {
            Some(&tsc_diagnostics::Add_a_return_type_to_the_function_expression)
        }
        Kind::MethodDeclaration => Some(&tsc_diagnostics::Add_a_return_type_to_the_method),
        Kind::GetAccessor => {
            Some(&tsc_diagnostics::Add_a_return_type_to_the_get_accessor_declaration)
        }
        Kind::SetAccessor => {
            Some(&tsc_diagnostics::Add_a_type_to_parameter_of_the_set_accessor_declaration)
        }
        Kind::FunctionDeclaration => {
            Some(&tsc_diagnostics::Add_a_return_type_to_the_function_declaration)
        }
        Kind::ConstructSignature => {
            Some(&tsc_diagnostics::Add_a_return_type_to_the_function_declaration)
        }
        Kind::Parameter => Some(&tsc_diagnostics::Add_a_type_annotation_to_the_parameter_0),
        Kind::VariableDeclaration => {
            Some(&tsc_diagnostics::Add_a_type_annotation_to_the_variable_0)
        }
        Kind::PropertyDeclaration => {
            Some(&tsc_diagnostics::Add_a_type_annotation_to_the_property_0)
        }
        Kind::PropertySignature => {
            Some(&tsc_diagnostics::Add_a_type_annotation_to_the_property_0)
        }
        Kind::ExportAssignment => {
            Some(&tsc_diagnostics::Move_the_expression_in_default_export_to_a_variable_and_add_a_type_annotation_to_it)
        }
        _ => None,
    }
}

/// `getErrorByDeclarationKind(kind)`.
fn get_error_by_declaration_kind(kind: Kind) -> Option<&'static Message> {
    match kind {
        Kind::FunctionExpression => {
            Some(&tsc_diagnostics::Function_must_have_an_explicit_return_type_annotation_with_isolatedDeclarations)
        }
        Kind::FunctionDeclaration => {
            Some(&tsc_diagnostics::Function_must_have_an_explicit_return_type_annotation_with_isolatedDeclarations)
        }
        Kind::ArrowFunction => {
            Some(&tsc_diagnostics::Function_must_have_an_explicit_return_type_annotation_with_isolatedDeclarations)
        }
        Kind::MethodDeclaration => {
            Some(&tsc_diagnostics::Method_must_have_an_explicit_return_type_annotation_with_isolatedDeclarations)
        }
        Kind::ConstructSignature => {
            Some(&tsc_diagnostics::Method_must_have_an_explicit_return_type_annotation_with_isolatedDeclarations)
        }
        Kind::GetAccessor => {
            Some(&tsc_diagnostics::At_least_one_accessor_must_have_an_explicit_type_annotation_with_isolatedDeclarations)
        }
        Kind::SetAccessor => {
            Some(&tsc_diagnostics::At_least_one_accessor_must_have_an_explicit_type_annotation_with_isolatedDeclarations)
        }
        Kind::Parameter => {
            Some(&tsc_diagnostics::Parameter_must_have_an_explicit_type_annotation_with_isolatedDeclarations)
        }
        Kind::VariableDeclaration => {
            Some(&tsc_diagnostics::Variable_must_have_an_explicit_type_annotation_with_isolatedDeclarations)
        }
        Kind::PropertyDeclaration => {
            Some(&tsc_diagnostics::Property_must_have_an_explicit_type_annotation_with_isolatedDeclarations)
        }
        Kind::PropertySignature => {
            Some(&tsc_diagnostics::Property_must_have_an_explicit_type_annotation_with_isolatedDeclarations)
        }
        Kind::ComputedPropertyName => {
            Some(&tsc_diagnostics::Computed_property_names_on_class_or_object_literals_cannot_be_inferred_with_isolatedDeclarations)
        }
        Kind::SpreadAssignment => {
            Some(&tsc_diagnostics::Objects_that_contain_spread_assignments_can_t_be_inferred_with_isolatedDeclarations)
        }
        Kind::ShorthandPropertyAssignment => {
            Some(&tsc_diagnostics::Objects_that_contain_shorthand_properties_can_t_be_inferred_with_isolatedDeclarations)
        }
        Kind::ArrayLiteralExpression => {
            Some(&tsc_diagnostics::Only_const_arrays_can_be_inferred_with_isolatedDeclarations)
        }
        Kind::ExportAssignment => {
            Some(&tsc_diagnostics::Default_exports_can_t_be_inferred_with_isolatedDeclarations)
        }
        Kind::SpreadElement => {
            Some(&tsc_diagnostics::Arrays_with_spread_elements_can_t_inferred_with_isolatedDeclarations)
        }
        _ => None,
    }
}

/// `isDeclarationEnoughForErrors(node)`.
fn is_declaration_enough_for_errors(node: &Node, nodes: &[Node]) -> bool {
    ast::is_export_assignment(node)
        || ast::is_statement(node, nodes)
        || ast::is_variable_declaration(node)
        || ast::is_property_declaration(node)
        || ast::is_parameter_declaration(node)
}

/// `isFunctionLikeAndNotConstructor(node)`.
fn is_function_like_and_not_constructor(node: &Node, nodes: &[Node]) -> bool {
    ast::is_function_like_declaration(Some(node.id), nodes)
        && !ast::is_constructor_declaration(node)
}

/// `findNearestDeclaration(node)`.
fn find_nearest_declaration(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let result = ast::find_ancestor(Some(node), nodes, &mut |n, nodes| {
        is_declaration_enough_for_errors(n, nodes)
    })?;
    if ast::is_export_assignment(&nodes[result]) {
        return Some(result);
    }
    if ast::is_return_statement(&nodes[result]) {
        return ast::find_ancestor(Some(result), nodes, &mut |n, nodes| {
            is_function_like_and_not_constructor(n, nodes)
        });
    }
    if ast::is_statement(&nodes[result], nodes) {
        return None;
    }
    Some(result)
}

/// `createEntityInTypeNodeError(node)`.
fn create_entity_in_type_node_error(node: NodeId, nodes: &[Node]) -> DiagnosticRef {
    let text = tsc_scanner::utilities::get_text_of_node(node, nodes);
    let diag = create_diagnostic_for_node(
        nodes,
        Some(node),
        &tsc_diagnostics::Type_containing_private_name_0_can_t_be_used_with_isolatedDeclarations,
        &[text],
    );
    add_parent_declaration_related_info(node, &diag, nodes);
    diag
}

/// `addParentDeclarationRelatedInfo(node, diag)`.
fn add_parent_declaration_related_info(node: NodeId, diag: &DiagnosticRef, nodes: &[Node]) {
    let Some(parent_declaration) = find_nearest_declaration(node, nodes) else {
        return;
    };
    let mut target_str = String::new();
    if !ast::is_export_assignment(&nodes[parent_declaration])
        && let Some(name) = nodes[parent_declaration].name()
    {
        target_str = tsc_scanner::utilities::get_text_of_node(name, nodes);
    }
    let related = create_diagnostic_for_node(
        nodes,
        Some(parent_declaration),
        get_related_suggestion_by_declaration_kind(nodes[parent_declaration].kind)
            .expect("related suggestion for declaration kind"),
        &[target_str],
    );
    diag.lock().unwrap().add_related_info(Some(related));
}

/// `createAccessorTypeError(node)`.
fn create_accessor_type_error(node: NodeId, nodes: &[Node], symbols: &[Symbol]) -> DiagnosticRef {
    let declarations = nodes[node]
        .symbol()
        .map(|s| symbols[s.index()].declarations.clone())
        .unwrap_or_default();
    let all_declarations =
        ast::get_all_accessor_declarations_for_declaration(node, &declarations, nodes);
    let get_accessor = all_declarations.get_accessor;
    let set_accessor = all_declarations.set_accessor;
    let mut target_node = node;
    if ast::is_set_accessor_declaration(&nodes[node])
        && let Some(params) = nodes[node].parameters()
        && !params.is_empty()
    {
        target_node = params[0];
    }
    let diag = create_diagnostic_for_node(
        nodes,
        Some(target_node),
        get_error_by_declaration_kind(nodes[node].kind)
            .expect("accessor error by declaration kind"),
        &[] as &[String],
    );
    if let Some(set_accessor) = set_accessor {
        let related = create_diagnostic_for_node(
            nodes,
            Some(set_accessor),
            get_related_suggestion_by_declaration_kind(nodes[set_accessor].kind)
                .expect("related suggestion for accessor kind"),
            &[] as &[String],
        );
        diag.lock().unwrap().add_related_info(Some(related));
    }
    if let Some(get_accessor) = get_accessor {
        let related = create_diagnostic_for_node(
            nodes,
            Some(get_accessor),
            get_related_suggestion_by_declaration_kind(nodes[get_accessor].kind)
                .expect("related suggestion for accessor kind"),
            &[] as &[String],
        );
        diag.lock().unwrap().add_related_info(Some(related));
    }
    diag
}

/// `createObjectLiteralError(node)`.
fn create_object_literal_error(node: NodeId, nodes: &[Node]) -> DiagnosticRef {
    let diag = create_diagnostic_for_node(
        nodes,
        Some(node),
        get_error_by_declaration_kind(nodes[node].kind)
            .expect("object literal error by declaration kind"),
        &[] as &[String],
    );
    add_parent_declaration_related_info(node, &diag, nodes);
    diag
}

/// `createArrayLiteralError(node)`.
fn create_array_literal_error(node: NodeId, nodes: &[Node]) -> DiagnosticRef {
    let diag = create_diagnostic_for_node(
        nodes,
        Some(node),
        get_error_by_declaration_kind(nodes[node].kind)
            .expect("array literal error by declaration kind"),
        &[] as &[String],
    );
    add_parent_declaration_related_info(node, &diag, nodes);
    diag
}

/// `createReturnTypeError(node)`.
fn create_return_type_error(node: NodeId, nodes: &[Node]) -> DiagnosticRef {
    let diag = create_diagnostic_for_node(
        nodes,
        Some(node),
        get_error_by_declaration_kind(nodes[node].kind)
            .expect("return type error by declaration kind"),
        &[] as &[String],
    );
    add_parent_declaration_related_info(node, &diag, nodes);
    let related = create_diagnostic_for_node(
        nodes,
        Some(node),
        get_related_suggestion_by_declaration_kind(nodes[node].kind)
            .expect("related suggestion for return type kind"),
        &[] as &[String],
    );
    diag.lock().unwrap().add_related_info(Some(related));
    diag
}

/// `createBindingElementError(node)`.
fn create_binding_element_error(node: NodeId, nodes: &[Node]) -> DiagnosticRef {
    create_diagnostic_for_node(
        nodes,
        Some(node),
        &tsc_diagnostics::Binding_elements_with_initializers_can_t_be_exported_directly_with_isolatedDeclarations,
        &[] as &[String],
    )
}

/// `createVariableOrPropertyError(node)`.
fn create_variable_or_property_error(node: NodeId, nodes: &[Node]) -> DiagnosticRef {
    let diag = create_diagnostic_for_node(
        nodes,
        Some(node),
        get_error_by_declaration_kind(nodes[node].kind)
            .expect("variable/property error by declaration kind"),
        &[] as &[String],
    );
    let target = nodes[node]
        .name()
        .map(|name| tsc_scanner::utilities::get_text_of_node(name, nodes))
        .unwrap_or_default();
    let related = create_diagnostic_for_node(
        nodes,
        Some(node),
        get_related_suggestion_by_declaration_kind(nodes[node].kind)
            .expect("related suggestion for variable/property kind"),
        &[target],
    );
    diag.lock().unwrap().add_related_info(Some(related));
    diag
}

/// `createExpressionError(node)`.
fn create_expression_error(node: NodeId, nodes: &[Node]) -> DiagnosticRef {
    create_expression_error_ex(node, None, nodes)
}

/// `createClassExpressionError(node)`.
fn create_class_expression_error(node: NodeId, nodes: &[Node]) -> DiagnosticRef {
    create_expression_error_ex(
        node,
        Some(&tsc_diagnostics::Inference_from_class_expressions_is_not_supported_with_isolatedDeclarations),
        nodes,
    )
}

/// `isParentForIDDIagnostic(node)`.
fn is_parent_for_idd_diagnostic(node: &Node, nodes: &[Node]) -> ast::FindAncestorResult {
    if ast::is_export_assignment(node) {
        return ast::FindAncestorResult::True;
    }
    if ast::is_statement(node, nodes) {
        return ast::FindAncestorResult::Quit;
    }
    ast::to_find_ancestor_result(
        !ast::is_parenthesized_expression(node) && !ast::is_assertion_expression(node),
    )
}

/// `createExpressionErrorEx(node, diagnosticMessage)`.
fn create_expression_error_ex(
    node: NodeId,
    diagnostic_message: Option<&'static Message>,
    nodes: &[Node],
) -> DiagnosticRef {
    let parent_declaration = find_nearest_declaration(node, nodes);
    if parent_declaration.is_none() {
        let diagnostic_message = diagnostic_message.unwrap_or(
            &tsc_diagnostics::Expression_type_can_t_be_inferred_with_isolatedDeclarations,
        );
        return create_diagnostic_for_node(nodes, Some(node), diagnostic_message, &[] as &[String]);
    }
    let parent_declaration = parent_declaration.unwrap();

    let mut target_str = String::new();
    if !ast::is_export_assignment(&nodes[parent_declaration])
        && let Some(name) = nodes[parent_declaration].name()
    {
        target_str = tsc_scanner::utilities::get_text_of_node(name, nodes);
    }
    let parent = ast::find_ancestor_or_quit(nodes[node].parent, nodes, &mut |n, nodes| {
        is_parent_for_idd_diagnostic(n, nodes)
    });

    if parent == Some(parent_declaration) {
        let diagnostic_message = diagnostic_message.unwrap_or_else(|| {
            get_error_by_declaration_kind(nodes[parent_declaration].kind)
                .expect("error by parent declaration kind")
        });
        let diag =
            create_diagnostic_for_node(nodes, Some(node), diagnostic_message, &[] as &[String]);
        let related = create_diagnostic_for_node(
            nodes,
            Some(parent_declaration),
            get_related_suggestion_by_declaration_kind(nodes[parent_declaration].kind)
                .expect("related suggestion for parent declaration kind"),
            &[target_str],
        );
        diag.lock().unwrap().add_related_info(Some(related));
        return diag;
    }
    let diagnostic_message = diagnostic_message
        .unwrap_or(&tsc_diagnostics::Expression_type_can_t_be_inferred_with_isolatedDeclarations);
    let diag = create_diagnostic_for_node(nodes, Some(node), diagnostic_message, &[] as &[String]);
    let related = create_diagnostic_for_node(
        nodes,
        Some(parent_declaration),
        get_related_suggestion_by_declaration_kind(nodes[parent_declaration].kind)
            .expect("related suggestion for parent declaration kind"),
        &[target_str],
    );
    diag.lock().unwrap().add_related_info(Some(related));
    let related = create_diagnostic_for_node(
        nodes,
        Some(node),
        &tsc_diagnostics::Add_satisfies_and_a_type_assertion_to_this_expression_satisfies_T_as_T_to_make_the_type_explicit,
        &[] as &[String],
    );
    diag.lock().unwrap().add_related_info(Some(related));
    diag
}

/// `type GetIsolatedDeclarationError = func(node) *ast.Diagnostic` — the
/// closure `NewSymbolTracker` stores on `SymbolTrackerImpl` (Go field
/// `getIsolatedDeclarationError`). Threaded the `nodes`/`symbols` arenas Go
/// reads through pointers.
pub type GetIsolatedDeclarationError<'a> =
    Box<dyn Fn(NodeId, &[Node], &[Symbol]) -> DiagnosticRef + 'a>;

/// A parameter diagnostic whose `addUndefined` verdict may have been
/// computed by the degraded `RequiresAddingImplicitUndefinedUnsafe`
/// fallback while the checker was already borrowed. Recomputed with the
/// real checker when diagnostics are collected; the owning arena is
/// resolved from `node.file_index()` at that point.
pub(crate) struct DeferredParamDiag {
    pub node: NodeId,
    pub diag: DiagnosticRef,
}

/// The body of Go's `createParameterError` once `addUndefined` is known —
/// shared by the eager (possibly degraded) path and the deferred recompute.
pub(crate) fn build_param_diag(
    node: NodeId,
    nodes: &[Node],
    add_undefined: bool,
) -> DiagnosticRef {
    if !add_undefined && nodes[node].initializer().is_some() {
        return create_expression_error(nodes[node].initializer().unwrap(), nodes);
    }
    let mut message = get_error_by_declaration_kind(nodes[node].kind);
    if add_undefined {
        message = Some(&tsc_diagnostics::Declaration_emit_for_this_parameter_requires_implicitly_adding_undefined_to_its_type_This_is_not_supported_with_isolatedDeclarations);
    }
    let diag = create_diagnostic_for_node(
        nodes,
        Some(node),
        message.expect("parameter error by declaration kind"),
        &[] as &[String],
    );
    let target_str = nodes[node]
        .name()
        .map(|name| tsc_scanner::utilities::get_text_of_node(name, nodes))
        .unwrap_or_default();
    let related = create_diagnostic_for_node(
        nodes,
        Some(node),
        get_related_suggestion_by_declaration_kind(nodes[node].kind)
            .expect("related suggestion for parameter kind"),
        &[target_str],
    );
    diag.lock().unwrap().add_related_info(Some(related));
    diag
}

/// `createGetIsolatedDeclarationErrors(resolver)`.
pub(crate) fn create_get_isolated_declaration_errors<'a>(
    resolver: Rc<RefCell<dyn EmitResolver + 'a>>,
    state: Rc<RefCell<SymbolTrackerSharedState<'a>>>,
) -> GetIsolatedDeclarationError<'a> {
    let create_parameter_error = move |node: NodeId,
                                       nodes: &[Node],
                                       symbols: &[Symbol]|
          -> DiagnosticRef {
        if nodes[node]
            .parent
            .is_some_and(|p| ast::is_set_accessor_declaration(&nodes[p]))
        {
            let parent = nodes[node].parent.unwrap();
            return create_accessor_type_error(parent, nodes, symbols);
        }
        // skip checker lock - node builder will already have one
        let add_undefined = resolver
            .borrow()
            .requires_adding_implicit_undefined_unsafe(node, None, None, nodes, symbols);
        let diag = build_param_diag(node, nodes, add_undefined);
        // `unsafe` returns a degraded `false` for annotated parameters while
        // the checker is borrowed (annotated params need type resolution).
        // Queue a recompute with the real checker; when the verdict already
        // matched, the rebuild overwrites an identical diagnostic.
        state.borrow_mut().deferred_param_diags.push(DeferredParamDiag {
            node,
            diag: diag.clone(),
        });
        diag
    };

    Box::new(
        move |node: NodeId, nodes: &[Node], symbols: &[Symbol]| -> DiagnosticRef {
            let heritage_clause =
                ast::find_ancestor(Some(node), nodes, &mut |n, _| ast::is_heritage_clause(n));
            if heritage_clause.is_some() {
                return create_diagnostic_for_node(
                nodes,
                Some(node),
                &tsc_diagnostics::Extends_clause_can_t_contain_an_expression_with_isolatedDeclarations,
                &[] as &[String],
            );
            }
            if ast::is_part_of_type_node(node, nodes) || ast::is_type_query_node(&nodes[node]) {
                return create_entity_in_type_node_error(node, nodes);
            }
            if ast::is_entity_name(&nodes[node])
                || ast::is_entity_name_expression(&nodes[node], nodes)
            {
                return create_entity_in_type_node_error(node, nodes);
            }
            match nodes[node].kind {
                Kind::GetAccessor | Kind::SetAccessor => {
                    create_accessor_type_error(node, nodes, symbols)
                }
                Kind::ComputedPropertyName
                | Kind::ShorthandPropertyAssignment
                | Kind::SpreadAssignment => create_object_literal_error(node, nodes),
                Kind::ArrayLiteralExpression | Kind::SpreadElement => {
                    create_array_literal_error(node, nodes)
                }
                Kind::MethodDeclaration
                | Kind::ConstructSignature
                | Kind::FunctionExpression
                | Kind::ArrowFunction
                | Kind::FunctionDeclaration => create_return_type_error(node, nodes),
                Kind::BindingElement => create_binding_element_error(node, nodes),
                Kind::PropertyDeclaration | Kind::VariableDeclaration => {
                    create_variable_or_property_error(node, nodes)
                }
                Kind::Parameter => create_parameter_error(node, nodes, symbols),
                Kind::PropertyAssignment => create_expression_error(
                    nodes[node]
                        .initializer()
                        .expect("PropertyAssignment.initializer"),
                    nodes,
                ),
                Kind::ClassExpression => create_class_expression_error(node, nodes),
                _ => create_expression_error(node, nodes),
            }
        },
    )
}
