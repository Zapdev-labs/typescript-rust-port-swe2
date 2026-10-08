// Ported from tsc/internal/binder/nameresolver.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The callback-driven name resolution loop shared by the checker. In Go the
// resolver fields hold `func` values that may be nil; here each hook is an
// `Option<Box<dyn FnMut>>` and the private helpers fall back to the same
// default implementations as Go when the hook is `None`.
//
// Pointer model: `*ast.Node` -> `NodeId`/`Option<NodeId>`; `*ast.Symbol` ->
// `SymbolId`/`Option<SymbolId>`; `ast.SymbolTable` -> `&SymbolTable` or an
// owned `SymbolTable` for `globals`. Because the node and symbol arenas are
// needed by nearly every helper, `resolve` takes them as parameters
// (`nodes: &[Node]`, `symbols: &mut Vec<Symbol>` — mutable so the transient
// `arguments` symbol can be lazily allocated).

use tsc_ast::ast::Node;
use tsc_ast::ast_generated::*;
use tsc_ast::ids::{NodeId, SymbolId};
use tsc_ast::kind_generated::Kind;
use tsc_ast::modifierflags::ModifierFlags;
use tsc_ast::nodeflags::NodeFlags;
use tsc_ast::symbol::{INTERNAL_SYMBOL_NAME_DEFAULT, Symbol, SymbolTable};
use tsc_ast::symbolflags::SymbolFlags;
use tsc_ast::utilities::*;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::options_generated::ScriptTarget;
use tsc_core::tristate::{TS_FALSE, TS_TRUE, TS_UNKNOWN, Tristate};
use tsc_diagnostics as diagnostics;

/// `type NameResolver struct` — hooks are `Option` boxed closures; `globals`
/// is an owned table (Go shares the caller's map; symbol tables are immutable
/// after binding so an owned snapshot has the same semantics).
type GetSymbolOfDeclarationHook<'a> = Box<dyn FnMut(NodeId, &[Node]) -> Option<SymbolId> + 'a>;
type ErrorHook<'a> =
    Box<dyn FnMut(Option<NodeId>, &'static diagnostics::Message, Vec<String>) + 'a>;
type LookupHook<'a> = Box<dyn FnMut(&SymbolTable, &str, SymbolFlags) -> Option<SymbolId> + 'a>;
type SymbolReferencedHook<'a> = Box<dyn FnMut(SymbolId, SymbolFlags) + 'a>;
type SetScopeChangeCacheHook<'a> = Box<dyn FnMut(NodeId, Tristate) + 'a>;
type GetScopeChangeCacheHook<'a> = Box<dyn FnMut(NodeId) -> Tristate + 'a>;
type OnPropertyWithInvalidInitializerHook<'a> =
    Box<dyn FnMut(Option<NodeId>, &str, NodeId, Option<SymbolId>) -> bool + 'a>;
type OnFailedToResolveSymbolHook<'a> =
    Box<dyn FnMut(Option<NodeId>, &str, SymbolFlags, &'static diagnostics::Message) + 'a>;
type OnSuccessfullyResolvedSymbolHook<'a> = Box<
    dyn FnMut(Option<NodeId>, SymbolId, SymbolFlags, Option<NodeId>, Option<NodeId>, bool) + 'a,
>;

pub struct NameResolver<'a> {
    pub compiler_options: &'a CompilerOptions,
    pub globals: SymbolTable,
    pub arguments_symbol: Option<SymbolId>,
    pub require_symbol: Option<SymbolId>,
    /// `GetSymbolOfDeclaration func(node *ast.Node) *ast.Symbol`
    pub get_symbol_of_declaration_hook: Option<GetSymbolOfDeclarationHook<'a>>,
    /// `Error func(location *ast.Node, message *diagnostics.Message, args ...any) *ast.Diagnostic`
    pub error_hook: Option<ErrorHook<'a>>,
    /// `Lookup func(symbols ast.SymbolTable, name string, meaning ast.SymbolFlags) *ast.Symbol`
    pub lookup_hook: Option<LookupHook<'a>>,
    /// `SymbolReferenced func(symbol *ast.Symbol, meaning ast.SymbolFlags)`
    pub symbol_referenced: Option<SymbolReferencedHook<'a>>,
    /// `SetRequiresScopeChangeCache func(node *ast.Node, value core.Tristate)`
    pub set_requires_scope_change_cache: Option<SetScopeChangeCacheHook<'a>>,
    /// `GetRequiresScopeChangeCache func(node *ast.Node) core.Tristate`
    pub get_requires_scope_change_cache: Option<GetScopeChangeCacheHook<'a>>,
    /// `OnPropertyWithInvalidInitializer`
    pub on_property_with_invalid_initializer: Option<OnPropertyWithInvalidInitializerHook<'a>>,
    /// `OnFailedToResolveSymbol`
    pub on_failed_to_resolve_symbol: Option<OnFailedToResolveSymbolHook<'a>>,
    /// `OnSuccessfullyResolvedSymbol`
    pub on_successfully_resolved_symbol: Option<OnSuccessfullyResolvedSymbolHook<'a>>,
}

impl<'a> NameResolver<'a> {
    /// `func (r *NameResolver) Resolve(...) *ast.Symbol`
    #[allow(clippy::too_many_arguments)]
    pub fn resolve(
        &mut self,
        location: Option<NodeId>,
        name: &str,
        meaning: SymbolFlags,
        name_not_found_message: Option<&'static diagnostics::Message>,
        is_use: bool,
        exclude_globals: bool,
        nodes: &[Node],
        symbols: &mut Vec<Symbol>,
    ) -> Option<SymbolId> {
        let mut result: Option<SymbolId> = None;
        let mut location = location;
        let mut last_location: Option<NodeId> = None;
        let mut last_self_reference_location: Option<NodeId> = None;
        let mut property_with_invalid_initializer: Option<NodeId> = None;
        let mut associated_declaration_for_containing_initializer_or_binding_name: Option<NodeId> =
            None;
        let mut within_deferred_context = false;
        let original_location = location; // needed for did-you-mean error reporting, which gathers candidates starting from the original location
        let name_is_const = name == "const";
        'loop_: while let Some(mut loc) = location {
            if name_is_const && is_const_assertion(&nodes[loc], nodes) {
                // `const` in an `as const` has no symbol, but issues no error because there is no *actual* lookup of the type
                // (it refers to the constant type of the expression instead)
                return None;
            }
            if is_module_or_enum_declaration(&nodes[loc])
                && last_location.is_some()
                && nodes[loc].name() == last_location
            {
                // If lastLocation is the name of a namespace or enum, skip the parent since it will have is own locals that could
                // conflict.
                last_location = Some(loc);
                location = nodes[loc].parent;
                continue;
            }
            let is_module_attributes = is_module_declaration(&nodes[loc])
                && nodes[loc].as_module_declaration().attributes.is_some()
                && last_location == nodes[loc].as_module_declaration().attributes;
            // Locals of a source file are not in scope (because they get merged into the global symbol table)
            if let Some(locals) = nodes[loc].locals() {
                if !is_global_source_file(&nodes[loc], nodes) {
                    result = self.lookup(locals, name, meaning, symbols);
                    if let Some(res) = result {
                        let mut use_result = true;
                        if is_module_attributes {
                            use_result = false;
                        } else if is_function_like(Some(loc), nodes)
                            && last_location.is_some()
                            && last_location != nodes[loc].body()
                        {
                            // symbol lookup restrictions for function-like declarations
                            // - Type parameters of a function are in scope in the entire function declaration, including the parameter
                            //   list and return type. However, local types are only in scope in the function body.
                            // - parameters are only in the scope of function body
                            // This restriction does not apply to JSDoc comment types because they are parented
                            // at a higher level than type parameters would normally be
                            let last = last_location.unwrap();
                            if meaning.intersects(symbols[res.index()].flags & SymbolFlags::TYPE)
                                && nodes[last].kind != Kind::JSDoc
                            {
                                // type parameters are visible in parameter list, return type and type parameter list.
                                // Synthetic fake scopes are added for signatures so type parameters are accessible from them.
                                use_result = symbols[res.index()]
                                    .flags
                                    .intersects(SymbolFlags::TYPE_PARAMETER)
                                    && (nodes[last].flags.intersects(NodeFlags::SYNTHESIZED)
                                        || Some(last) == nodes[loc].type_()
                                        || nodes[last].kind == Kind::Parameter
                                        || nodes[last].kind == Kind::JSDocParameterTag
                                        || nodes[last].kind == Kind::JSDocReturnTag
                                        || nodes[last].kind == Kind::TypeParameter);
                            }
                            if meaning
                                .intersects(symbols[res.index()].flags & SymbolFlags::VARIABLE)
                            {
                                // expression inside parameter will lookup as normal variable scope when targeting es2015+
                                if self.use_outer_variable_scope_in_parameter(
                                    res, loc, last, nodes, symbols,
                                ) {
                                    use_result = false;
                                } else if symbols[res.index()]
                                    .flags
                                    .intersects(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
                                {
                                    // parameters are visible only inside function body, parameter list and return type
                                    // technically for parameter list case here we might mix parameters and variables declared in function,
                                    // however it is detected separately when checking initializers of parameters
                                    // to make sure that they reference no variables declared after them.
                                    use_result = nodes[last].kind == Kind::Parameter
                                        || nodes[last].flags.intersects(NodeFlags::SYNTHESIZED)
                                        || Some(last) == nodes[loc].type_()
                                            && symbols[res.index()].value_declaration.is_some_and(
                                                |vd| {
                                                    find_ancestor(
                                                        Some(vd),
                                                        nodes,
                                                        &mut is_parameter_declaration_fn,
                                                    )
                                                    .is_some()
                                                },
                                            );
                                }
                            }
                        } else if nodes[loc].kind == Kind::ConditionalType {
                            // A type parameter declared using 'infer T' in a conditional type is visible only in
                            // the true branch of the conditional type.
                            use_result =
                                last_location == nodes[loc].as_conditional_type_node().true_type;
                        }
                        if use_result {
                            break 'loop_;
                        }
                        result = None;
                    }
                }
            }
            within_deferred_context =
                within_deferred_context || get_is_deferred_context(loc, last_location, nodes);
            match nodes[loc].kind {
                Kind::SourceFile
                    if !is_external_or_commonjs_module(nodes[loc].as_source_file()) => {}
                Kind::SourceFile | Kind::ModuleDeclaration => {
                    if is_module_attributes {
                        // fallthrough to bottom
                    } else if let Some(module_symbol) = self.get_symbol_of_declaration(loc, nodes) {
                        let module_exports = symbols[module_symbol.index()].exports.clone();
                        if is_source_file(&nodes[loc])
                            || is_module_declaration(&nodes[loc])
                                && nodes[loc].flags.intersects(NodeFlags::AMBIENT)
                                && !is_global_scope_augmentation(&nodes[loc])
                        {
                            // It's an external module. First see if the module has an export default and if the local
                            // name of that export default matches.
                            result = module_exports.get(INTERNAL_SYMBOL_NAME_DEFAULT).copied();
                            if let Some(res) = result {
                                let local_symbol =
                                    get_local_symbol_for_export_default(res, nodes, symbols);
                                if local_symbol.is_some()
                                    && symbols[res.index()].flags.intersects(meaning)
                                    && symbols[local_symbol.unwrap().index()].name == name
                                {
                                    break 'loop_;
                                }
                                result = None;
                            }
                            // Because of module/namespace merging, a module's exports are in scope,
                            // yet we never want to treat an export specifier as putting a member in scope.
                            // Therefore, if the name we find is purely an export specifier, it is not actually considered in scope.
                            // Two things to note about this:
                            //     1. We have to check this without calling getSymbol. The problem with calling getSymbol
                            //        on an export specifier is that it might find the export specifier itself, and try to
                            //        resolve it as an alias. This will cause the checker to consider the export specifier
                            //        a circular alias reference when it might not be.
                            //     2. We check === SymbolFlags.Alias in order to check that the symbol is *purely*
                            //        an alias. If we used &, we'd be throwing out symbols that have non alias aspects,
                            //        which is not the desired behavior.
                            if let Some(module_export) = module_exports.get(name).copied() {
                                if symbols[module_export.index()].flags == SymbolFlags::ALIAS
                                    && (get_declaration_of_kind(
                                        &symbols[module_export.index()],
                                        Kind::ExportSpecifier,
                                        nodes,
                                    )
                                    .is_some()
                                        || get_declaration_of_kind(
                                            &symbols[module_export.index()],
                                            Kind::NamespaceExport,
                                            nodes,
                                        )
                                        .is_some())
                                {
                                    // break out of switch, continue loop
                                } else {
                                    // fall through to ModuleMember lookup below
                                    Self::lookup_module_member(
                                        self,
                                        &module_exports,
                                        loc,
                                        name,
                                        meaning,
                                        nodes,
                                        symbols,
                                        &mut result,
                                    );
                                    if result.is_some() {
                                        break 'loop_;
                                    }
                                }
                            } else {
                                Self::lookup_module_member(
                                    self,
                                    &module_exports,
                                    loc,
                                    name,
                                    meaning,
                                    nodes,
                                    symbols,
                                    &mut result,
                                );
                                if result.is_some() {
                                    break 'loop_;
                                }
                            }
                        } else {
                            Self::lookup_module_member(
                                self,
                                &module_exports,
                                loc,
                                name,
                                meaning,
                                nodes,
                                symbols,
                                &mut result,
                            );
                            if result.is_some() {
                                break 'loop_;
                            }
                        }
                    }
                }
                Kind::EnumDeclaration => {
                    if let Some(enum_symbol) = self.get_symbol_of_declaration(loc, nodes) {
                        result = self.lookup(
                            &symbols[enum_symbol.index()].exports.clone(),
                            name,
                            meaning & SymbolFlags::ENUM_MEMBER,
                            symbols,
                        );
                        if let Some(res) = result {
                            if name_not_found_message.is_some()
                                && self.compiler_options.get_isolated_modules()
                                && !nodes[loc].flags.intersects(NodeFlags::AMBIENT)
                                && symbols[res.index()].value_declaration.is_some_and(|vd| {
                                    get_source_file_of_node(Some(loc), nodes)
                                        != get_source_file_of_node(Some(vd), nodes)
                                })
                            {
                                let isolated_modules_like_flag_name =
                                    if self.compiler_options.verbatim_module_syntax == TS_TRUE {
                                        "verbatimModuleSyntax"
                                    } else {
                                        "isolatedModules"
                                    };
                                let qualified =
                                    format!("{}.{}", symbols[enum_symbol.index()].name, name);
                                self.error(
                                    original_location,
                                    &diagnostics::Cannot_access_0_from_another_file_without_qualification_when_1_is_enabled_Use_2_instead,
                                    vec![
                                        name.to_string(),
                                        isolated_modules_like_flag_name.to_string(),
                                        qualified,
                                    ],
                                );
                            }
                            break 'loop_;
                        }
                    }
                }
                Kind::PropertyDeclaration => {
                    if !is_static(&nodes[loc]) {
                        if let Some(ctor) = nodes[loc]
                            .parent
                            .and_then(|p| find_constructor_declaration(&nodes[p], nodes))
                        {
                            if let Some(ctor_locals) = nodes[ctor].locals() {
                                if self
                                    .lookup(
                                        ctor_locals,
                                        name,
                                        meaning & SymbolFlags::VALUE,
                                        symbols,
                                    )
                                    .is_some()
                                {
                                    // Remember the property node, it will be used later to report appropriate error
                                    property_with_invalid_initializer = Some(loc);
                                }
                            }
                        }
                    }
                }
                Kind::ClassDeclaration | Kind::ClassExpression | Kind::InterfaceDeclaration => {
                    // Go `break`s out of the switch when a member is found but its
                    // type parameter isn't declared in this container — skipping
                    // the class-expression-name check below. Track that.
                    let mut skip_class_expression_name_check = false;
                    if let Some(location_symbol) = self.get_symbol_of_declaration(loc, nodes) {
                        result = self.lookup(
                            &symbols[location_symbol.index()].members.clone(),
                            name,
                            meaning & SymbolFlags::TYPE,
                            symbols,
                        );
                        if let Some(res) = result {
                            if !is_type_parameter_symbol_declared_in_container(
                                res, loc, nodes, symbols,
                            ) {
                                // ignore type parameters not declared in this container
                                result = None;
                                skip_class_expression_name_check = true;
                            } else {
                                if last_location.is_some_and(|l| is_static(&nodes[l])) {
                                    // TypeScript 1.0 spec (April 2014): 3.4.1
                                    // The scope of a type parameter extends over the entire declaration with which the type
                                    // parameter list is associated, with the exception of static member declarations in classes.
                                    if name_not_found_message.is_some() {
                                        self.error(
                                            original_location,
                                            &diagnostics::Static_members_cannot_reference_class_type_parameters,
                                            vec![],
                                        );
                                    }
                                    return None;
                                }
                                break 'loop_;
                            }
                        }
                    }
                    if !skip_class_expression_name_check
                        && is_class_expression(&nodes[loc])
                        && meaning.intersects(SymbolFlags::CLASS)
                    {
                        if let Some(class_name) = nodes[loc].name() {
                            if name == nodes[class_name].text(nodes) {
                                result = nodes[loc].symbol();
                                break 'loop_;
                            }
                        }
                    }
                }
                Kind::ExpressionWithTypeArguments => {
                    if last_location == nodes[loc].expression()
                        && nodes[loc]
                            .parent
                            .is_some_and(|p| is_heritage_clause(&nodes[p]))
                        && nodes[nodes[loc].parent.unwrap()].as_heritage_clause().token
                            == Kind::ExtendsKeyword
                    {
                        if let Some(container) = nodes[loc].parent.and_then(|p| nodes[p].parent) {
                            if is_class_like(Some(container), nodes) {
                                if let Some(container_symbol) =
                                    self.get_symbol_of_declaration(container, nodes)
                                {
                                    result = self.lookup(
                                        &symbols[container_symbol.index()].members.clone(),
                                        name,
                                        meaning & SymbolFlags::TYPE,
                                        symbols,
                                    );
                                    if result.is_some() {
                                        if name_not_found_message.is_some() {
                                            self.error(
                                                original_location,
                                                &diagnostics::Base_class_expressions_cannot_reference_class_type_parameters,
                                                vec![],
                                            );
                                        }
                                        return None;
                                    }
                                }
                            }
                        }
                    }
                }
                // It is not legal to reference a class's own type parameters from a computed property name that
                // belongs to the class. For example:
                //
                //   function foo<T>() { return '' }
                //   class C<T> { // <-- Class's own type parameter T
                //       [foo<T>()]() { } // <-- Reference to T from class's own computed property
                //   }
                Kind::ComputedPropertyName => {
                    let grandparent = nodes[loc].parent.and_then(|p| nodes[p].parent);
                    if let Some(gp) = grandparent {
                        if is_class_like(Some(gp), nodes) || is_interface_declaration(&nodes[gp]) {
                            // A reference to this grandparent's type parameters would be an error
                            if let Some(gp_symbol) = self.get_symbol_of_declaration(gp, nodes) {
                                result = self.lookup(
                                    &symbols[gp_symbol.index()].members.clone(),
                                    name,
                                    meaning & SymbolFlags::TYPE,
                                    symbols,
                                );
                                if result.is_some() {
                                    if name_not_found_message.is_some() {
                                        self.error(
                                            original_location,
                                            &diagnostics::A_computed_property_name_cannot_reference_a_type_parameter_from_its_containing_type,
                                            vec![],
                                        );
                                    }
                                    return None;
                                }
                            }
                        }
                    }
                }
                Kind::MethodDeclaration
                | Kind::Constructor
                | Kind::GetAccessor
                | Kind::SetAccessor
                | Kind::FunctionDeclaration => {
                    if meaning.intersects(SymbolFlags::VARIABLE) && name == "arguments" {
                        result = Some(self.arguments_symbol(symbols));
                        break 'loop_;
                    }
                }
                Kind::FunctionExpression => {
                    if meaning.intersects(SymbolFlags::VARIABLE) && name == "arguments" {
                        result = Some(self.arguments_symbol(symbols));
                        break 'loop_;
                    }
                    if meaning.intersects(SymbolFlags::FUNCTION) {
                        if let Some(function_name) = nodes[loc].as_function_expression().name {
                            if name == nodes[function_name].text(nodes) {
                                result = nodes[loc].symbol();
                                break 'loop_;
                            }
                        }
                    }
                }
                Kind::Decorator => {
                    // Decorators are resolved at the class declaration. Resolving at the parameter
                    // or member would result in looking up locals in the method.
                    //
                    //   function y() {}
                    //   class C {
                    //       method(@y x, y) {} // <-- decorator y should be resolved at the class declaration, not the parameter.
                    //   }
                    //
                    if nodes[loc]
                        .parent
                        .is_some_and(|p| nodes[p].kind == Kind::Parameter)
                    {
                        loc = nodes[loc].parent.unwrap();
                    }
                    //   function y() {}
                    //   class C {
                    //       @y method(x, y) {} // <-- decorator y should be resolved at the class declaration, not the method.
                    //   }
                    //
                    // class Decorators are resolved outside of the class to avoid referencing type parameters of that class.
                    //
                    //   type T = number;
                    //   declare function y(x: T): any;
                    //   @param(1 as T) // <-- T should resolve to the type alias outside of class C
                    //   class C<T> {}
                    if nodes[loc].parent.is_some_and(|p| {
                        is_class_element(&nodes[p]) || nodes[p].kind == Kind::ClassDeclaration
                    }) {
                        loc = nodes[loc].parent.unwrap();
                    }
                }
                Kind::Parameter => {
                    let parameter_declaration = nodes[loc].as_parameter_declaration();
                    if last_location.is_some()
                        && (last_location == parameter_declaration.initializer
                            || last_location == parameter_declaration.name
                                && last_location.is_some_and(|l| is_binding_pattern(&nodes[l])))
                        && associated_declaration_for_containing_initializer_or_binding_name
                            .is_none()
                    {
                        associated_declaration_for_containing_initializer_or_binding_name =
                            Some(loc);
                    }
                }
                Kind::BindingElement => {
                    let binding_element = nodes[loc].as_binding_element();
                    if last_location.is_some()
                        && (last_location == binding_element.initializer
                            || last_location == binding_element.name
                                && last_location.is_some_and(|l| is_binding_pattern(&nodes[l])))
                        && is_part_of_parameter_declaration(loc, nodes)
                        && associated_declaration_for_containing_initializer_or_binding_name
                            .is_none()
                    {
                        associated_declaration_for_containing_initializer_or_binding_name =
                            Some(loc);
                    }
                }
                Kind::InferType => {
                    if meaning.intersects(SymbolFlags::TYPE_PARAMETER) {
                        let type_parameter =
                            nodes[loc].as_infer_type_node().type_parameter.unwrap();
                        if let Some(parameter_name) =
                            nodes[type_parameter].as_type_parameter_declaration().name
                        {
                            if name == nodes[parameter_name].text(nodes) {
                                result = nodes[type_parameter].symbol();
                                break 'loop_;
                            }
                        }
                    }
                }
                Kind::ExportSpecifier => {
                    let export_specifier = nodes[loc].as_export_specifier();
                    if last_location.is_some()
                        && last_location == export_specifier.property_name
                        && nodes[loc]
                            .parent
                            .and_then(|p| nodes[p].parent)
                            .is_some_and(|pp| nodes[pp].module_specifier().is_some())
                    {
                        loc = nodes[nodes[loc].parent.unwrap()]
                            .parent
                            .and_then(|pp| nodes[pp].parent)
                            .expect("export specifier grandparent");
                    }
                }
                _ => {}
            }
            if is_self_reference_location(&nodes[loc], last_location, nodes) {
                last_self_reference_location = Some(loc);
            }
            last_location = Some(loc);
            // !!! In Strada, JSDocTemplateTag/JSDocParameterTag/JSDocReturnTag locations skip to
            // getEffectiveContainerForJSDocTemplateTag/getHostSignatureFromJSDoc instead of location.parent.
            // This is a no-op currently because JSDoc nodes have no locals and getEffectiveJSDocHost is not
            // fully ported for JS assignment patterns.
            location = nodes[loc].parent;
        }
        // We just climbed up parents looking for the name, meaning that we started in a descendant node of `lastLocation`.
        // If `result === lastSelfReferenceLocation.symbol`, that means that we are somewhere inside `lastSelfReferenceLocation` looking up a name, and resolving to `lastLocation` itself.
        // That means that this is a self-reference of `lastLocation`, and shouldn't count this when considering whether `lastLocation` is used.
        let referenced = is_use
            && result.is_some()
            && (last_self_reference_location.is_none()
                || result != last_self_reference_location.and_then(|l| nodes[l].symbol()));
        if referenced {
            if let Some(hook) = self.symbol_referenced.as_mut() {
                hook(result.unwrap(), meaning);
            }
        }
        if result.is_none() && !exclude_globals {
            let globals = self.globals.clone();
            result = self.lookup(
                &globals,
                name,
                meaning | SymbolFlags::GLOBAL_LOOKUP,
                symbols,
            );
        }
        if result.is_none() {
            if let Some(original_location) = original_location {
                if is_in_js_file(Some(original_location), nodes)
                    && nodes[original_location].parent.is_some()
                {
                    let parent = nodes[original_location].parent.unwrap();
                    if is_require_call(
                        &nodes[parent],
                        false, /*requireStringLiteralLikeArgument*/
                        nodes,
                    ) {
                        return self.require_symbol;
                    }
                }
            }
        }
        if let Some(name_not_found_message) = name_not_found_message {
            if let (Some(property), Some(hook)) = (
                property_with_invalid_initializer,
                self.on_property_with_invalid_initializer.as_mut(),
            ) {
                if hook(original_location, name, property, result) {
                    return None;
                }
            }
            match result {
                None => {
                    if let Some(hook) = self.on_failed_to_resolve_symbol.as_mut() {
                        hook(original_location, name, meaning, name_not_found_message);
                    }
                }
                Some(result) => {
                    if let Some(hook) = self.on_successfully_resolved_symbol.as_mut() {
                        hook(
                            original_location,
                            result,
                            meaning,
                            last_location,
                            associated_declaration_for_containing_initializer_or_binding_name,
                            within_deferred_context,
                        );
                    }
                }
            }
        }
        result
    }

    /// `r.lookup(moduleExports, name, meaning&ast.SymbolFlagsModuleMember)`
    /// with the CommonJS-module-indicator check — shared by the three arms of
    /// the `KindSourceFile`/`KindModuleDeclaration` case above.
    #[allow(clippy::too_many_arguments)]
    fn lookup_module_member(
        &mut self,
        module_exports: &SymbolTable,
        location: NodeId,
        name: &str,
        meaning: SymbolFlags,
        nodes: &[Node],
        symbols: &[Symbol],
        result: &mut Option<SymbolId>,
    ) {
        if name == INTERNAL_SYMBOL_NAME_DEFAULT {
            return;
        }
        let res = self.lookup(
            module_exports,
            name,
            meaning & SymbolFlags::MODULE_MEMBER,
            symbols,
        );
        if let Some(res) = res {
            if is_source_file(&nodes[location])
                && nodes[location]
                    .as_source_file()
                    .common_js_module_indicator
                    .is_some()
                && !symbols[res.index()].flags.intersects(SymbolFlags::TYPE)
            {
                *result = None;
            } else {
                *result = Some(res);
            }
        }
    }

    /// `func (r *NameResolver) useOuterVariableScopeInParameter`.
    fn use_outer_variable_scope_in_parameter(
        &mut self,
        result: SymbolId,
        location: NodeId,
        last_location: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> bool {
        if is_parameter_declaration(&nodes[last_location]) {
            if let Some(body) = nodes[location].body() {
                if let Some(value_declaration) = symbols[result.index()].value_declaration {
                    if nodes[value_declaration].pos() >= nodes[body].pos()
                        && nodes[value_declaration].end() <= nodes[body].end()
                    {
                        // check for several cases where we introduce temporaries that require moving the name/initializer of the parameter to the body
                        // - static field in a class expression
                        // - optional chaining pre-es2020
                        // - nullish coalesce pre-es2020
                        // - spread assignment in binding pattern pre-es2017
                        let function_location = location;
                        let mut declaration_requires_scope_change = self
                            .get_requires_scope_change_cache
                            .as_mut()
                            .map_or(TS_UNKNOWN, |hook| hook(function_location));
                        if declaration_requires_scope_change == TS_UNKNOWN {
                            declaration_requires_scope_change = if nodes[function_location]
                                .parameters()
                                .unwrap_or(&[])
                                .iter()
                                .any(|&param| self.requires_scope_change(param, nodes))
                            {
                                TS_TRUE
                            } else {
                                TS_FALSE
                            };
                            if let Some(hook) = self.set_requires_scope_change_cache.as_mut() {
                                hook(function_location, declaration_requires_scope_change);
                            }
                        }
                        return declaration_requires_scope_change != TS_TRUE;
                    }
                }
            }
        }
        false
    }

    /// `func (r *NameResolver) requiresScopeChange`.
    fn requires_scope_change(&mut self, node: NodeId, nodes: &[Node]) -> bool {
        let d = nodes[node].as_parameter_declaration();
        d.name
            .is_some_and(|n| self.requires_scope_change_worker(n, nodes))
            || d.initializer
                .is_some_and(|i| self.requires_scope_change_worker(i, nodes))
    }

    /// `func (r *NameResolver) requiresScopeChangeWorker`.
    fn requires_scope_change_worker(&mut self, node: NodeId, nodes: &[Node]) -> bool {
        match nodes[node].kind {
            Kind::ArrowFunction
            | Kind::FunctionExpression
            | Kind::FunctionDeclaration
            | Kind::Constructor => false,
            Kind::MethodDeclaration
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::PropertyAssignment => nodes[node]
                .name()
                .is_some_and(|n| self.requires_scope_change_worker(n, nodes)),
            Kind::PropertyDeclaration => {
                if has_static_modifier(&nodes[node]) {
                    !self.compiler_options.get_emit_standard_class_fields()
                } else {
                    nodes[node]
                        .name()
                        .is_some_and(|n| self.requires_scope_change_worker(n, nodes))
                }
            }
            _ => {
                if is_nullish_coalesce(&nodes[node], nodes) || is_optional_chain(&nodes[node]) {
                    return self.compiler_options.get_emit_script_target() < ScriptTarget::ES2020;
                }
                if is_binding_element(&nodes[node])
                    && nodes[node].as_binding_element().dot_dot_dot_token.is_some()
                    && nodes[node]
                        .parent
                        .is_some_and(|p| is_object_binding_pattern(&nodes[p]))
                {
                    return self.compiler_options.get_emit_script_target() < ScriptTarget::ES2017;
                }
                if is_type_node(&nodes[node]) {
                    return false;
                }
                nodes[node].for_each_child(nodes, &mut |child| {
                    self.requires_scope_change_worker(child, nodes)
                })
            }
        }
    }

    /// `func (r *NameResolver) error`.
    fn error(
        &mut self,
        location: Option<NodeId>,
        message: &'static diagnostics::Message,
        args: Vec<String>,
    ) {
        if let Some(hook) = self.error_hook.as_mut() {
            hook(location, message, args);
        }
        // Default implementation does not report errors
    }

    /// `func (r *NameResolver) getSymbolOfDeclaration`.
    fn get_symbol_of_declaration(&mut self, node: NodeId, nodes: &[Node]) -> Option<SymbolId> {
        if let Some(hook) = self.get_symbol_of_declaration_hook.as_mut() {
            return hook(node, nodes);
        }
        // Default implementation does not support merged symbols
        nodes[node].symbol()
    }

    /// `func (r *NameResolver) lookup`. The `symbol_arena` parameter feeds
    /// only the default implementation's `symbol.Flags` check — the
    /// `Lookup` hook, when installed, decides validity itself (as in Go).
    fn lookup(
        &mut self,
        symbols_table: &SymbolTable,
        name: &str,
        meaning: SymbolFlags,
        symbol_arena: &[Symbol],
    ) -> Option<SymbolId> {
        if let Some(hook) = self.lookup_hook.as_mut() {
            return hook(symbols_table, name, meaning);
        }
        // Default implementation does not support following aliases or merged symbols
        if meaning != SymbolFlags::NONE {
            if let Some(symbol) = symbols_table.get(name) {
                if symbol_arena[symbol.index()].flags.intersects(meaning) {
                    return Some(*symbol);
                }
            }
        }
        None
    }

    /// `func (r *NameResolver) argumentsSymbol` — synthesizes the transient
    /// `arguments` symbol. PORT: needs `&mut Vec<Symbol>` because symbol
    /// identity is `SymbolId` into the arena.
    fn arguments_symbol(&mut self, symbols: &mut Vec<Symbol>) -> SymbolId {
        if self.arguments_symbol.is_none() {
            symbols.push(Symbol {
                name: "arguments".to_string(),
                flags: SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
                ..Default::default()
            });
            self.arguments_symbol = Some(SymbolId((symbols.len() - 1) as u32));
        }
        self.arguments_symbol.unwrap()
    }
}

/// `func GetLocalSymbolForExportDefault`.
pub fn get_local_symbol_for_export_default(
    symbol: SymbolId,
    nodes: &[Node],
    symbols: &[Symbol],
) -> Option<SymbolId> {
    if !is_export_default_symbol(&symbols[symbol.index()], nodes) {
        return None;
    }
    for &decl in &symbols[symbol.index()].declarations {
        if let Some(local_symbol) = nodes[decl].local_symbol() {
            return Some(local_symbol);
        }
    }
    None
}

/// `func isExportDefaultSymbol`.
fn is_export_default_symbol(symbol: &Symbol, nodes: &[Node]) -> bool {
    !symbol.declarations.is_empty()
        && has_syntactic_modifier(&nodes[symbol.declarations[0]], ModifierFlags::DEFAULT)
}

/// `func getIsDeferredContext`.
fn get_is_deferred_context(
    location: NodeId,
    last_location: Option<NodeId>,
    nodes: &[Node],
) -> bool {
    if nodes[location].kind != Kind::ArrowFunction
        && nodes[location].kind != Kind::FunctionExpression
    {
        // initializers in instance property declaration of class like entities are executed in constructor and thus deferred
        // A name is evaluated within the enclosing scope - so it shouldn't count as deferred
        return is_type_query_node(&nodes[location])
            || (is_function_like_declaration(Some(location), nodes)
                || nodes[location].kind == Kind::PropertyDeclaration
                    && !is_static(&nodes[location]))
                && (last_location.is_none() || last_location != nodes[location].name());
    }
    if last_location.is_some() && last_location == nodes[location].name() {
        return false;
    }
    // generator functions and async functions are not inlined in control flow when immediately invoked
    if nodes[location]
        .body_data()
        .is_some_and(|d| d.asterisk_token.is_some())
        || has_syntactic_modifier(&nodes[location], ModifierFlags::ASYNC)
    {
        return true;
    }
    get_immediately_invoked_function_expression(location, nodes).is_none()
}

/// `func isTypeParameterSymbolDeclaredInContainer`.
fn is_type_parameter_symbol_declared_in_container(
    symbol: SymbolId,
    container: NodeId,
    nodes: &[Node],
    symbols: &[Symbol],
) -> bool {
    for &decl in &symbols[symbol.index()].declarations {
        if nodes[decl].kind == Kind::TypeParameter && nodes[decl].parent == Some(container) {
            return true;
        }
    }
    false
}

/// `func isSelfReferenceLocation`.
fn is_self_reference_location(node: &Node, last_location: Option<NodeId>, _nodes: &[Node]) -> bool {
    match node.kind {
        Kind::Parameter => last_location.is_some() && last_location == node.name(),
        Kind::FunctionDeclaration
        | Kind::ClassDeclaration
        | Kind::InterfaceDeclaration
        | Kind::EnumDeclaration
        | Kind::TypeAliasDeclaration
        | Kind::JSTypeAliasDeclaration
        | Kind::ModuleDeclaration => true,
        _ => false,
    }
}

fn is_parameter_declaration_fn(node: &Node, _nodes: &[Node]) -> bool {
    is_parameter_declaration(node)
}
