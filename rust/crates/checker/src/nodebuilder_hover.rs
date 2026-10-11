// Ported from tsc/internal/checker/nodebuilder_hover.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — expandable-hover declaration
// serialization: `expandSymbolForHover` and its per-declaration-kind helpers
// (enum, class, interface, module), which build declaration nodes directly
// without the declaration-emit scaffolding (deferred privates, symbol name
// remapping, export modifier computation, alias resolution, visited symbols
// tracking).
//
// PORT notes:
//
// - Same conventions as nodebuilderimpl.rs: `*ast.Symbol` → `SymbolId`,
//   `*Type` → `TypeId`, `*ast.Node` → `Option<NodeId>` where nil-able,
//   `[]*ast.Symbol` → `Vec<SymbolId>`, `[]*ast.Node` → `Vec<NodeId>`,
//   `*ast.ModifierList` → `Option<ModifierList>`, `*ast.NodeList` →
//   `Option<NodeList>`, and the checker's `b.ch` becomes an explicit
//   `c: &mut Checker` parameter.
// - `isExpanding` lives here (its Go home file); `nodebuilderimpl.rs`'s
//   `createTypeNodesFromResolvedType` calls it via
//   `crate::nodebuilder_hover::is_expanding`.
// - `hoverStatement` is a file-local struct mirroring the Go closure-local
//   struct in `expandModuleDecl`.
// - Go `defer` blocks (`ctx.enclosingDeclaration`, `ctx.flags` restore) are
//   explicit restores at the end of the enclosing function body.

use rustc_hash::{FxHashMap, FxHashSet};

use tsc_ast::{self as ast, Kind, ModifierFlags, NodeId, SymbolFlags, SymbolId};
use tsc_core::languagevariant::LanguageVariant;
use tsc_evaluator as evaluator;
use tsc_nodebuilder as nodebuilder;
use tsc_printer as printer;
use tsc_scanner as scanner;

use crate::checker_core::Checker;
use crate::nodebuilderimpl::{
    NodeBuilderContext, NodeBuilderImpl, SignatureToSignatureDeclarationOptions,
};
use crate::relater::Comparer;
use crate::types::{IndexInfo, SignatureFlags, SignatureKind, Ternary, TypeId};

// ----------------------------------------------------------------------------
// Local arena helpers — short-borrow copies of symbol/type fields so `&mut
// Checker` calls never alias a live borrow (same pattern as
// nodebuilderimpl.rs's private helpers).
// ----------------------------------------------------------------------------

/// `symbol.flags` read through the arena.
fn symbol_flags(c: &Checker, s: SymbolId) -> SymbolFlags {
    if s == SymbolId::NONE {
        return SymbolFlags::NONE;
    }
    c.symbol_arena.borrow()[s.index()].flags
}

/// `symbol.name` (cloned) read through the arena.
fn symbol_name(c: &Checker, s: SymbolId) -> String {
    c.symbol_arena.borrow()[s.index()].name.clone()
}

/// `symbol.declarations` (cloned) read through the arena.
fn symbol_declarations(c: &Checker, s: SymbolId) -> Vec<NodeId> {
    c.symbol_arena.borrow()[s.index()].declarations.clone()
}

/// `symbol.parent` read through the arena.
fn symbol_parent(c: &Checker, s: SymbolId) -> Option<SymbolId> {
    c.symbol_arena.borrow()[s.index()].parent
}

/// `symbol.valueDeclaration` read through the arena.
fn symbol_value_declaration(c: &Checker, s: SymbolId) -> Option<NodeId> {
    c.symbol_arena.borrow()[s.index()].value_declaration
}

/// `symbol.exports` (cloned) read through the arena.
fn symbol_exports(c: &Checker, s: SymbolId) -> ast::SymbolTable {
    c.symbol_arena.borrow()[s.index()].exports.clone()
}

/// `ast.SymbolName` — the *escaped* writeable name of a symbol.
fn ast_symbol_name(c: &Checker, s: SymbolId) -> String {
    ast::symbol::escape_symbol_name(&c.symbol_arena.borrow()[s.index()].name).into_owned()
}

/// `t.symbol` read through the type arena.
fn type_symbol(c: &Checker, t: TypeId) -> Option<SymbolId> {
    c.types_handle().get(t).symbol
}

/// `isExpanding` — whether the node builder context is operating in
/// hover-expansion mode.
pub(crate) fn is_expanding(ctx: &NodeBuilderContext) -> bool {
    ctx.max_expansion_depth != -1
}

/// `isHashPrivate`.
fn is_hash_private(c: &Checker, s: SymbolId) -> bool {
    let Some(vd) = symbol_value_declaration(c, s) else {
        return false;
    };
    let __program = c.program.clone().expect("program");
    let dn = __program.nodes((vd).file_index());
    dn[vd]
        .name()
        .is_some_and(|n| ast::is_private_identifier(&dn[n]))
}

/// `typeElementsToClassElements` — converts TypeElement nodes
/// (PropertySignature, MethodSignature) to their ClassElement equivalents
/// (PropertyDeclaration, MethodDeclaration) so they can be used as members of
/// a ClassDeclaration. Nodes that are already ClassElements pass through
/// unchanged.
fn type_elements_to_class_elements(
    f: &mut ast::NodeFactory<'_>,
    nodes: &mut Vec<ast::Node>,
    mut members: Vec<NodeId>,
) -> Vec<NodeId> {
    for i in 0..members.len() {
        let m = members[i];
        match nodes[m].kind {
            Kind::PropertySignature => {
                let (modifiers, name, postfix_token, type_node) = {
                    let ps = nodes[m].as_property_signature_declaration();
                    (
                        nodes[m].modifiers().cloned(),
                        ps.named_member_base.name,
                        ps.named_member_base.postfix_token,
                        ps.type_,
                    )
                };
                members[i] = f.new_property_declaration(
                    nodes,
                    modifiers,
                    name,
                    postfix_token,
                    type_node,
                    None,
                );
            }
            Kind::MethodSignature => {
                let (modifiers, name, postfix_token, type_parameters, parameters, type_node) = {
                    let ms = nodes[m].as_method_signature_declaration();
                    (
                        nodes[m].modifiers().cloned(),
                        ms.named_member_base.name,
                        ms.named_member_base.postfix_token,
                        ms.function_like_base.type_parameters.clone(),
                        ms.function_like_base.parameters.clone(),
                        ms.function_like_base.type_,
                    )
                };
                members[i] = f.new_method_declaration(
                    nodes,
                    modifiers,
                    None,
                    name,
                    postfix_token,
                    type_parameters,
                    parameters,
                    type_node,
                    None,
                    None,
                );
            }
            _ => {}
        }
    }
    members
}

/// `hoverStatement` — the closure-local struct inside `expandModuleDecl`:
/// `isLocal` marks local declarations (e.g. alias targets) that should not
/// get an export modifier.
struct HoverStatement {
    /// `node`.
    node: NodeId,
    /// `isLocal`.
    is_local: bool,
}

impl<'a> NodeBuilderImpl<'a> {
    /// `(b *NodeBuilderImpl) expandSymbolForHover` — produces declaration
    /// nodes (class, interface, enum, module) for a symbol for expandable
    /// hover. This is a focused alternative to the full
    /// `symbolTableToDeclarationStatements` machinery used by declaration
    /// emit.
    pub fn expand_symbol_for_hover(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
    ) -> Vec<NodeId> {
        let mut results: Vec<NodeId> = Vec::new();
        let flags = symbol_flags(c, symbol);
        if flags.intersects(SymbolFlags::ENUM)
            && let Some(node) = self.expand_enum_decl(c, nodes, symbol)
        {
            results.push(node);
        }
        if flags.intersects(SymbolFlags::CLASS)
            && let Some(node) = self.expand_class_decl(c, nodes, symbol)
        {
            results.push(node);
        }
        // Module/namespace before interface (matching Strada ordering for
        // merged declarations)
        if flags.intersects(SymbolFlags::VALUE_MODULE | SymbolFlags::NAMESPACE_MODULE)
            && let Some(node) = self.expand_module_decl(c, nodes, symbol)
        {
            results.push(node);
        }
        if flags.intersects(SymbolFlags::INTERFACE)
            && !flags.intersects(SymbolFlags::CLASS)
            && let Some(node) = self.expand_interface_decl(c, nodes, symbol)
        {
            results.push(node);
        }
        results
    }

    /// `(b *NodeBuilderImpl) expandEnumDecl` — produces an EnumDeclaration
    /// node with all members.
    fn expand_enum_decl(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
    ) -> Option<NodeId> {
        let name = ast_symbol_name(c, symbol);
        self.ctx.approximate_length += 9 + name.len() as i32;
        let enum_type = c.get_type_of_symbol(symbol);
        let member_props: Vec<SymbolId> = c
            .get_properties_of_type(enum_type)
            .into_iter()
            .filter(|&p| symbol_flags(c, p).intersects(SymbolFlags::ENUM_MEMBER))
            .collect();
        let mut members: Vec<NodeId> = Vec::new();
        let mut i = 0;
        while i < member_props.len() {
            let p = member_props[i];
            if self.check_truncation_length_if_expanding() && i + 3 < member_props.len() - 1 {
                self.ctx.expansion_truncated = true;
                let text = format!(" ... {} more ... ", member_props.len() - i - 1);
                let text_lit = self
                    .f
                    .new_string_literal(nodes, &text, ast::TokenFlags::NONE);
                members.push(self.f.new_enum_member(nodes, Some(text_lit), None));
                let last = member_props[member_props.len() - 1];
                let last_name = symbol_name(c, last);
                let last_name_id = self.f.new_identifier(nodes, &last_name);
                let init = self.enum_member_initializer(c, nodes, last);
                members.push(self.f.new_enum_member(nodes, Some(last_name_id), init));
                break;
            }
            let member_decl = symbol_declarations(c, p).iter().copied().find(|&d| {
                let __program = c.program.clone().expect("program");
                let dn = __program.nodes((d).file_index());
                ast::is_enum_member(&dn[d])
            });
            let initializer = if let Some(member_decl) = member_decl {
                let decl_init = {
                    let __program = c.program.clone().expect("program");
                    let dn = __program.nodes((member_decl).file_index());
                    dn[member_decl].as_enum_member().initializer
                };
                match decl_init {
                    Some(init) => self.deep_clone_node_in(c, nodes, init),
                    None => self.enum_member_initializer(c, nodes, p),
                }
            } else {
                self.enum_member_initializer(c, nodes, p)
            };
            let p_name = symbol_name(c, p);
            self.ctx.approximate_length += 4 + p_name.len() as i32;
            if initializer.is_some() {
                self.ctx.approximate_length += 5; // " = " + value estimate
            }
            let p_name_id = self.f.new_identifier(nodes, &p_name);
            members.push(self.f.new_enum_member(nodes, Some(p_name_id), initializer));
            i += 1;
        }

        let const_modifier = if crate::checker_d::is_const_enum_symbol(c, symbol) {
            ModifierFlags::CONST
        } else {
            ModifierFlags::NONE
        };
        let mods = if !const_modifier.is_empty() {
            let modifiers =
                ast::create_modifiers_from_modifier_flags(const_modifier, &mut |kind| {
                    self.f.new_token(nodes, kind)
                });
            Some(self.f.new_modifier_list(nodes, modifiers))
        } else {
            None
        };
        let name_id = self.f.new_identifier(nodes, &name);
        let member_list = self.f.new_node_list(members);
        Some(
            self.f
                .new_enum_declaration(nodes, mods, Some(name_id), Some(member_list)),
        )
    }

    /// `(b *NodeBuilderImpl) enumMemberInitializer`.
    fn enum_member_initializer(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        p: SymbolId,
    ) -> Option<NodeId> {
        let member_decl = symbol_declarations(c, p).iter().copied().find(|&d| {
            let __program = c.program.clone().expect("program");
            let dn = __program.nodes((d).file_index());
            ast::is_enum_member(&dn[d])
        })?;
        let val = c.get_constant_value(member_decl)?;
        match val {
            evaluator::Value::String(s) => {
                Some(self.f.new_string_literal(nodes, &s, ast::TokenFlags::NONE))
            }
            evaluator::Value::Number(n) => Some(self.f.new_numeric_literal(
                nodes,
                &n.string(),
                ast::TokenFlags::NONE,
            )),
            _ => None,
        }
    }

    /// `(b *NodeBuilderImpl) expandClassDecl` — produces a ClassDeclaration
    /// node with heritage clauses and members.
    fn expand_class_decl(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
    ) -> Option<NodeId> {
        let name = ast_symbol_name(c, symbol);
        self.ctx.approximate_length += 9 + name.len() as i32;

        let class_like_declarations: Vec<NodeId> = symbol_declarations(c, symbol)
            .into_iter()
            .filter(|&d| {
                let __program = c.program.clone().expect("program");
                let dn = __program.nodes((d).file_index());
                ast::is_class_like(Some(d), &dn)
            })
            .collect();
        let original_decl = class_like_declarations.first().copied();
        let old_enclosing = self.ctx.enclosing_declaration;
        if let Some(original_decl) = original_decl {
            self.ctx.enclosing_declaration = Some(original_decl);
        }
        // Go `defer`: restore `ctx.enclosing_declaration` at the end.

        let local_params = c.get_local_type_parameters_of_class_or_interface_or_type_alias(symbol, nodes);
        let type_param_decls: Vec<NodeId> = local_params
            .iter()
            .map(|&p| self.type_parameter_to_declaration(c, nodes, p))
            .collect();

        let declared_type = c.get_declared_type_of_class_or_interface(symbol);
        let class_type = c.get_type_with_this_argument(declared_type, None, false);
        let base_types = c.get_base_types(c.get_target_type(class_type));
        let static_type = c.get_type_of_symbol(symbol);
        let is_class = type_symbol(c, static_type)
            .and_then(|s| symbol_value_declaration(c, s))
            .is_some_and(|vd| {
                let __program = c.program.clone().expect("program");
                let dn = __program.nodes((vd).file_index());
                ast::is_class_like(Some(vd), &dn)
            });
        let static_base_type = if is_class {
            c.get_base_constructor_type_of_class(declared_type)
        } else {
            c.any_type
        };

        // Heritage clauses
        let heritage_clauses = self.hover_heritage_clauses(c, nodes, &class_like_declarations);

        // Instance members via addPropertyToElementList (reusing existing
        // serialization), then convert TypeElements to ClassElements and add
        // class-specific modifiers
        let all_props = c.get_properties_of_type(class_type);
        let symbol_props = self.filter_inherited_properties(c, class_type, &base_types, all_props);
        let public_props: Vec<SymbolId> = symbol_props
            .iter()
            .copied()
            .filter(|&s| !is_hash_private(c, s))
            .collect();
        let has_private = symbol_props.iter().any(|&s| is_hash_private(c, s));

        let mut instance_members: Vec<NodeId> = Vec::new();
        instance_members =
            self.serialize_properties_with_truncation(c, nodes, public_props, instance_members);
        instance_members = type_elements_to_class_elements(&mut self.f, nodes, instance_members);
        instance_members = self.add_class_modifiers(c, nodes, instance_members, false);

        // Static members
        let static_props: Vec<SymbolId> = c
            .get_properties_of_type(static_type)
            .into_iter()
            .filter(|&p| {
                !symbol_flags(c, p).intersects(SymbolFlags::PROTOTYPE)
                    && symbol_name(c, p) != "prototype"
                    && !self.is_namespace_member(c, p)
            })
            .collect();
        let mut static_members: Vec<NodeId> = Vec::new();
        static_members =
            self.serialize_properties_with_truncation(c, nodes, static_props, static_members);
        static_members = type_elements_to_class_elements(&mut self.f, nodes, static_members);
        static_members = self.add_class_modifiers(c, nodes, static_members, true);

        // Hash-private members
        let mut private_members: Vec<NodeId> = Vec::new();
        if has_private {
            let hash_props: Vec<SymbolId> = symbol_props
                .iter()
                .copied()
                .filter(|&s| is_hash_private(c, s))
                .collect();
            private_members =
                self.serialize_properties_with_truncation(c, nodes, hash_props, private_members);
            private_members = type_elements_to_class_elements(&mut self.f, nodes, private_members);
        }

        // Constructors
        let constructors = self.serialize_constructors(
            c,
            nodes,
            static_type,
            Some(static_base_type),
            is_class,
            symbol,
        );

        // Index signatures
        let index_sigs = self.serialize_index_signatures_of_type(
            c,
            nodes,
            class_type,
            base_types.first().copied(),
        );

        let mut all_members: Vec<NodeId> = Vec::with_capacity(
            index_sigs.len()
                + static_members.len()
                + constructors.len()
                + instance_members.len()
                + private_members.len(),
        );
        all_members.extend(index_sigs);
        all_members.extend(static_members);
        all_members.extend(constructors);
        all_members.extend(instance_members);
        all_members.extend(private_members);

        // `defer func() { b.ctx.enclosingDeclaration = oldEnclosing }()`.
        self.ctx.enclosing_declaration = old_enclosing;

        let name_id = self.f.new_identifier(nodes, &name);
        let type_param_list = self.f.new_node_list(type_param_decls);
        let heritage_list = self.f.new_node_list(heritage_clauses);
        let member_list = self.f.new_node_list(all_members);
        Some(self.f.new_class_declaration(
            nodes,
            None,
            Some(name_id),
            Some(type_param_list),
            Some(heritage_list),
            Some(member_list),
        ))
    }

    /// `(b *NodeBuilderImpl) addClassModifiers` — post-processes class member
    /// nodes to add class-specific modifiers (private, protected, public,
    /// abstract, static) based on the original symbol declarations.
    fn add_class_modifiers(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        mut members: Vec<NodeId>,
        is_static: bool,
    ) -> Vec<NodeId> {
        for i in 0..members.len() {
            let m = members[i];
            // Find the symbol for this member by matching the property name
            let member_symbol = nodes[m]
                .name()
                .and_then(|name| self.id_to_symbol.get(&name).copied());
            let Some(member_symbol) = member_symbol else {
                continue;
            };
            let mut mod_flags =
                crate::utilities::get_declaration_modifier_flags_from_symbol(c, member_symbol)
                    .without(ModifierFlags::ASYNC);
            if is_static {
                mod_flags |= ModifierFlags::STATIC;
            }
            if !mod_flags.is_empty() && ast::can_have_modifiers(&nodes[m]) {
                let existing = nodes[m].modifier_flags();
                if mod_flags != existing {
                    let modifiers = ast::create_modifiers_from_modifier_flags(
                        mod_flags | existing,
                        &mut |kind| self.f.new_token(nodes, kind),
                    );
                    let modifier_list = self.f.new_modifier_list(nodes, modifiers);
                    if let Some(updated) =
                        ast::replace_modifiers(&mut self.f, nodes, m, Some(modifier_list))
                    {
                        members[i] = updated;
                    }
                }
            }
        }
        members
    }

    /// `(b *NodeBuilderImpl) expandInterfaceDecl` — produces an
    /// InterfaceDeclaration with members. Reuses `addPropertyToElementList`
    /// for property serialization and `signatureToSignatureDeclarationHelper`
    /// for signatures.
    fn expand_interface_decl(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
    ) -> Option<NodeId> {
        let name = ast_symbol_name(c, symbol);
        self.ctx.approximate_length += 14 + name.len() as i32;

        let interface_type = c.get_declared_type_of_class_or_interface(symbol);
        let interface_declarations: Vec<NodeId> = symbol_declarations(c, symbol)
            .into_iter()
            .filter(|&d| {
                let __program = c.program.clone().expect("program");
                let dn = __program.nodes((d).file_index());
                ast::is_interface_declaration(&dn[d])
            })
            .collect();
        let local_params = c.get_local_type_parameters_of_class_or_interface_or_type_alias(symbol, nodes);
        let type_param_decls: Vec<NodeId> = local_params
            .iter()
            .map(|&p| self.type_parameter_to_declaration(c, nodes, p))
            .collect();
        let base_types = c.get_base_types(interface_type);
        let base_type = if !base_types.is_empty() {
            Some(c.get_intersection_type(&base_types))
        } else {
            None
        };

        // Members: reuse existing serialization functions
        let resolved = c.resolve_structured_type_members(interface_type);
        let (construct_signatures, call_signatures, resolved_properties) = {
            let __arena_guard = c.types.clone();
            let guard = __arena_guard.get(resolved);
            let st = guard.as_structured_type().expect("structured type");
            (
                st.construct_signatures().to_vec(),
                st.call_signatures().to_vec(),
                st.properties.clone(),
            )
        };
        // Index signatures, filtering those identical to base
        let mut members =
            self.serialize_index_signatures_of_type(c, nodes, interface_type, base_type);
        // Construct signatures (skip abstract)
        for sig in construct_signatures {
            if c.signature_arena
                .get(sig)
                .flags
                .intersects(SignatureFlags::ABSTRACT)
            {
                continue;
            }
            members.push(self.signature_to_signature_declaration_helper(
                c,
                nodes,
                sig,
                Kind::ConstructSignature,
                SignatureToSignatureDeclarationOptions::default(),
            ));
        }
        // Call signatures
        for sig in call_signatures {
            members.push(self.signature_to_signature_declaration_helper(
                c,
                nodes,
                sig,
                Kind::CallSignature,
                SignatureToSignatureDeclarationOptions::default(),
            ));
        }
        // Properties, filtering inherited
        let filtered_props =
            self.filter_inherited_properties(c, interface_type, &base_types, resolved_properties);
        members = self.serialize_properties_with_truncation(c, nodes, filtered_props, members);

        // Heritage clauses
        let heritage_clauses = self.hover_heritage_clauses(c, nodes, &interface_declarations);

        let name_id = self.f.new_identifier(nodes, &name);
        let type_param_list = self.f.new_node_list(type_param_decls);
        let heritage_list = self.f.new_node_list(heritage_clauses);
        let member_list = self.f.new_node_list(members);
        Some(self.f.new_interface_declaration(
            nodes,
            None,
            Some(name_id),
            Some(type_param_list),
            Some(heritage_list),
            Some(member_list),
        ))
    }

    /// `(b *NodeBuilderImpl) hoverHeritageClauses`.
    fn hover_heritage_clauses(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        declarations: &[NodeId],
    ) -> Vec<NodeId> {
        let mut extends_types: Vec<NodeId> = Vec::new();
        let mut implements_types: Vec<NodeId> = Vec::new();
        for &declaration in declarations {
            let extends: Vec<NodeId> = {
                let __program = c.program.clone().expect("program");
                let dn = __program.nodes((declaration).file_index());
                ast::get_extends_heritage_clause_elements(&dn[declaration], &dn)
                    .map(|els| els.to_vec())
                    .unwrap_or_default()
            };
            for element in extends {
                if let Some(cloned) = self.deep_clone_node_in(c, nodes, element) {
                    extends_types.push(cloned);
                }
            }
            let implements: Vec<NodeId> = {
                let __program = c.program.clone().expect("program");
                let dn = __program.nodes((declaration).file_index());
                ast::get_implements_heritage_clause_elements(&dn[declaration], &dn)
                    .map(|els| els.to_vec())
                    .unwrap_or_default()
            };
            for element in implements {
                if let Some(cloned) = self.deep_clone_node_in(c, nodes, element) {
                    implements_types.push(cloned);
                }
            }
        }

        let mut heritage_clauses: Vec<NodeId> = Vec::new();
        if !extends_types.is_empty() {
            let type_list = self.f.new_node_list(extends_types);
            heritage_clauses.push(self.f.new_heritage_clause(
                nodes,
                Kind::ExtendsKeyword,
                Some(type_list),
            ));
        }
        if !implements_types.is_empty() {
            let type_list = self.f.new_node_list(implements_types);
            heritage_clauses.push(self.f.new_heritage_clause(
                nodes,
                Kind::ImplementsKeyword,
                Some(type_list),
            ));
        }
        heritage_clauses
    }

    /// `(b *NodeBuilderImpl) serializePropertiesWithTruncation` — iterates
    /// properties using `addPropertyToElementList`, with truncation checks
    /// matching Strada's `createTypeNodesFromResolvedType` behavior.
    fn serialize_properties_with_truncation(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        properties: Vec<SymbolId>,
        mut elements: Vec<NodeId>,
    ) -> Vec<NodeId> {
        let properties: Vec<SymbolId> = properties
            .into_iter()
            .filter(|&p| !symbol_flags(c, p).intersects(SymbolFlags::PROTOTYPE))
            .collect();
        let mut i = 0;
        while i < properties.len() {
            let p = properties[i];
            if self.check_truncation_length_if_expanding() && i + 3 < properties.len() - 1 {
                self.ctx.expansion_truncated = true;
                let text = format!("... {} more ...", properties.len() - i - 1);
                let text_id = self.f.new_identifier(nodes, &text);
                elements.push(self.f.new_property_signature_declaration(
                    nodes,
                    None,
                    Some(text_id),
                    None,
                    None,
                    None,
                ));
                elements = self.add_property_to_element_list(
                    c,
                    nodes,
                    properties[properties.len() - 1],
                    elements,
                );
                break;
            }
            elements = self.add_property_to_element_list(c, nodes, p, elements);
            i += 1;
        }
        elements
    }

    /// `(b *NodeBuilderImpl) serializeConstructors` — builds constructor
    /// signature(s) for a class, with base type filtering.
    fn serialize_constructors(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        static_type: TypeId,
        static_base_type: Option<TypeId>,
        is_class: bool,
        symbol: SymbolId,
    ) -> Vec<NodeId> {
        let is_non_constructable = !is_class
            && symbol_value_declaration(c, symbol).is_some_and(|vd| {
                let __program = c.program.clone().expect("program");
                let dn = __program.nodes((vd).file_index());
                ast::is_in_js_file(Some(vd), &dn)
            })
            && c.get_signatures_of_type(static_type, SignatureKind::Construct)
                .is_empty();
        if is_non_constructable {
            self.ctx.approximate_length += 21;
            let modifiers =
                ast::create_modifiers_from_modifier_flags(ModifierFlags::PRIVATE, &mut |kind| {
                    self.f.new_token(nodes, kind)
                });
            let modifier_list = self.f.new_modifier_list(nodes, modifiers);
            let params = self.f.new_node_list(Vec::new());
            return vec![self.f.new_constructor_declaration(
                nodes,
                Some(modifier_list),
                None,
                Some(params),
                None,
                None,
                None,
            )];
        }
        let signatures = c.get_signatures_of_type(static_type, SignatureKind::Construct);
        if let Some(static_base_type) = static_base_type {
            let base_sigs = c.get_signatures_of_type(static_base_type, SignatureKind::Construct);
            if base_sigs.is_empty()
                && signatures
                    .iter()
                    .all(|&sig| c.signature_arena.get(sig).parameters.is_empty())
            {
                return Vec::new();
            }
            if base_sigs.len() == signatures.len() {
                let mut all_match = true;
                for i in 0..base_sigs.len() {
                    if c.compare_signatures_identical(
                        signatures[i],
                        base_sigs[i],
                        false,
                        false,
                        true,
                        Comparer::Identical,
                    ) != Ternary::TRUE
                    {
                        all_match = false;
                        break;
                    }
                }
                if all_match {
                    return Vec::new();
                }
            }
            let mut private_protected = ModifierFlags::NONE;
            for &sig in &signatures {
                if let Some(decl) = c.signature_arena.get(sig).declaration {
                    let __program = c.program.clone().expect("program");
                    let dn = __program.nodes((decl).file_index());
                    private_protected |= dn[decl].modifier_flags()
                        & (ModifierFlags::PRIVATE | ModifierFlags::PROTECTED);
                }
            }
            if !private_protected.is_empty() {
                let modifiers =
                    ast::create_modifiers_from_modifier_flags(private_protected, &mut |kind| {
                        self.f.new_token(nodes, kind)
                    });
                let modifier_list = self.f.new_modifier_list(nodes, modifiers);
                let params = self.f.new_node_list(Vec::new());
                return vec![self.f.new_constructor_declaration(
                    nodes,
                    Some(modifier_list),
                    None,
                    Some(params),
                    None,
                    None,
                    None,
                )];
            }
        } else if signatures
            .iter()
            .all(|&sig| c.signature_arena.get(sig).parameters.is_empty())
        {
            return Vec::new();
        }
        let mut result: Vec<NodeId> = Vec::new();
        for sig in signatures {
            self.ctx.approximate_length += 1;
            result.push(self.signature_to_signature_declaration_helper(
                c,
                nodes,
                sig,
                Kind::Constructor,
                SignatureToSignatureDeclarationOptions::default(),
            ));
        }
        result
    }

    /// `(b *NodeBuilderImpl) serializeIndexSignaturesOfType` — builds index
    /// signature declarations, filtering those identical to `baseType`.
    fn serialize_index_signatures_of_type(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        input: TypeId,
        base_type: Option<TypeId>,
    ) -> Vec<NodeId> {
        let mut result: Vec<NodeId> = Vec::new();
        for info_id in c.get_index_infos_of_type(input) {
            let info: IndexInfo = c.index_info_arena.get(info_id).clone();
            if let Some(base_type) = base_type {
                let base_info = info
                    .key_type
                    .and_then(|key_type| c.get_index_info_of_type(base_type, key_type));
                if let Some(base_info) = base_info {
                    let base_value_type = c.index_info_arena.get(base_info).value_type;
                    if let (Some(value_type), Some(base_value_type)) =
                        (info.value_type, base_value_type)
                        && c.is_type_identical_to(value_type, base_value_type)
                    {
                        continue;
                    }
                }
            }
            result
                .push(self.index_info_to_index_signature_declaration_helper(c, nodes, &info, None));
        }
        result
    }

    /// `(b *NodeBuilderImpl) serializeNamespaceMember` — produces the
    /// appropriate declaration node for a namespace member based on its
    /// symbol flags (type alias, enum, class, interface, nested namespace, or
    /// variable).
    fn serialize_namespace_member(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        resolved: SymbolId,
        name: &str,
    ) -> Option<NodeId> {
        let flags = symbol_flags(c, resolved);
        if flags.intersects(SymbolFlags::TYPE_ALIAS) {
            self.serialize_type_alias_for_namespace(c, nodes, resolved, name)
        } else if flags.intersects(SymbolFlags::ENUM) {
            self.expand_enum_decl(c, nodes, resolved)
        } else if flags.intersects(SymbolFlags::CLASS) {
            self.expand_class_decl(c, nodes, resolved)
        } else if flags.intersects(SymbolFlags::INTERFACE) {
            self.expand_interface_decl(c, nodes, resolved)
        } else if flags.intersects(SymbolFlags::VALUE_MODULE | SymbolFlags::NAMESPACE_MODULE) {
            self.expand_module_decl(c, nodes, resolved)
        } else {
            let member_type = c.get_type_of_symbol(resolved);
            let t = c.get_widened_type(member_type);
            self.ctx.approximate_length += name.len() as i32 + 5;
            let name_id = self.f.new_identifier(nodes, name);
            let type_node =
                self.serialize_type_for_declaration(c, nodes, None, Some(t), Some(resolved), true);
            let decl =
                self.f
                    .new_variable_declaration(nodes, Some(name_id), None, Some(type_node), None);
            let decl_list = self.f.new_node_list(vec![decl]);
            let var_list =
                self.f
                    .new_variable_declaration_list(nodes, Some(decl_list), ast::NodeFlags::LET);
            Some(self.f.new_variable_statement(nodes, None, Some(var_list)))
        }
    }

    /// `(b *NodeBuilderImpl) expandModuleDecl` — produces a ModuleDeclaration
    /// with exported members.
    fn expand_module_decl(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
    ) -> Option<NodeId> {
        let exports = c.get_exports_of_symbol(symbol);
        let mut members: Vec<SymbolId> = Vec::new();
        for sym in exports.values().copied() {
            // Filter to namespace-relevant members
            if !self.is_namespace_member(c, sym) {
                continue;
            }
            if !scanner::utilities::is_identifier_text(
                &symbol_name(c, sym),
                LanguageVariant::Standard,
            ) {
                continue;
            }
            members.push(sym);
        }
        c.sort_symbols(&mut members);
        self.ctx.approximate_length += 14;

        // Use the same name as symbol display.
        let old_flags = self.ctx.flags;
        self.ctx.flags |= nodebuilder::Flags::WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME
            | nodebuilder::Flags::USE_ONLY_EXTERNAL_ALIASING;
        let local_name = self.symbol_to_node(c, nodes, symbol, SymbolFlags::ALL);
        self.ctx.flags = old_flags;

        let mut body_stmts: Vec<HoverStatement> = Vec::new();
        let mut emitted_locals: FxHashSet<SymbolId> = FxHashSet::default();
        let mut i = 0;
        while i < members.len() {
            let m = members[i];
            if self.check_truncation_length_if_expanding() && i + 3 < members.len() - 1 {
                self.ctx.expansion_truncated = true;
                let text = format!("... ({} more) ...", members.len() - i - 1);
                let text_id = self.f.new_identifier(nodes, &text);
                let stmt = self.f.new_expression_statement(nodes, Some(text_id));
                body_stmts.push(HoverStatement {
                    node: stmt,
                    is_local: false,
                });
                i = members.len() - 2; // skip to last member after `i += 1`
                i += 1;
                continue;
            }

            // Handle alias/re-export symbols
            if symbol_flags(c, m).intersects(SymbolFlags::ALIAS) {
                let alias_decl = c.get_declaration_of_alias_symbol(m);
                let target = alias_decl
                    .and_then(|decl| c.get_target_of_alias_declaration(decl))
                    .map(|t| c.get_merged_symbol(t))
                    .filter(|&t| t != SymbolId::NONE);
                if let Some(target) = target {
                    // If the alias target is a local symbol (not itself an
                    // export), emit its declaration first
                    if symbol_flags(c, target).intersects(
                        SymbolFlags::BLOCK_SCOPED_VARIABLE
                            | SymbolFlags::FUNCTION_SCOPED_VARIABLE
                            | SymbolFlags::PROPERTY,
                    ) && emitted_locals.insert(target)
                    {
                        let target_type = c.get_type_of_symbol(target);
                        let local_type = c.get_widened_type(target_type);
                        let target_name = symbol_name(c, target);
                        self.ctx.approximate_length += target_name.len() as i32 + 5;
                        let name_id = self.f.new_identifier(nodes, &target_name);
                        let type_node = self.serialize_type_for_declaration(
                            c,
                            nodes,
                            None,
                            Some(local_type),
                            Some(target),
                            true,
                        );
                        let decl = self.f.new_variable_declaration(
                            nodes,
                            Some(name_id),
                            None,
                            Some(type_node),
                            None,
                        );
                        let decl_list = self.f.new_node_list(vec![decl]);
                        let var_list = self.f.new_variable_declaration_list(
                            nodes,
                            Some(decl_list),
                            ast::NodeFlags::LET,
                        );
                        let local_stmt = self.f.new_variable_statement(nodes, None, Some(var_list));
                        body_stmts.push(HoverStatement {
                            node: local_stmt,
                            is_local: true,
                        });
                    }
                    let target_name = symbol_name(c, target);
                    self.ctx.approximate_length += 16 + symbol_name(c, m).len() as i32;
                    let property_name = if symbol_name(c, m) != target_name {
                        Some(self.f.new_identifier(nodes, &target_name))
                    } else {
                        None
                    };
                    let m_name = symbol_name(c, m);
                    let m_name_id = self.f.new_identifier(nodes, &m_name);
                    let specifier =
                        self.f
                            .new_export_specifier(nodes, false, property_name, Some(m_name_id));
                    let named_list = self.f.new_node_list(vec![specifier]);
                    let named_exports = self.f.new_named_exports(nodes, Some(named_list));
                    let stmt = self.f.new_export_declaration(
                        nodes,
                        None,
                        false,
                        Some(named_exports),
                        None,
                        None,
                    );
                    body_stmts.push(HoverStatement {
                        node: stmt,
                        is_local: false,
                    });
                    i += 1;
                    continue;
                }
            }

            let resolved = c.resolve_symbol(m);

            // Handle functions as function declarations
            if symbol_flags(c, resolved).intersects(SymbolFlags::FUNCTION | SymbolFlags::METHOD) {
                let t = c.get_type_of_symbol(resolved);
                let sigs = c.get_signatures_of_type(t, SignatureKind::Call);
                for sig in sigs {
                    self.ctx.approximate_length += 1;
                    let m_name = symbol_name(c, m);
                    let name_id = self.f.new_identifier(nodes, &m_name);
                    let decl = self.signature_to_signature_declaration_helper(
                        c,
                        nodes,
                        sig,
                        Kind::FunctionDeclaration,
                        SignatureToSignatureDeclarationOptions {
                            name: Some(name_id),
                            ..Default::default()
                        },
                    );
                    body_stmts.push(HoverStatement {
                        node: decl,
                        is_local: false,
                    });
                }
                // If the function also has namespace characteristics, emit an
                // empty namespace.
                let merged = c.get_merged_symbol(resolved);
                let has_module_exports = symbol_flags(c, merged)
                    .intersects(SymbolFlags::VALUE_MODULE | SymbolFlags::NAMESPACE_MODULE)
                    && !symbol_exports(c, merged).is_empty();
                if !has_module_exports {
                    let m_name = symbol_name(c, m);
                    let name_id = self.f.new_identifier(nodes, &m_name);
                    let empty_block = self
                        .f
                        .new_module_block(nodes, Some(self.f.new_node_list(Vec::new())));
                    let decl = self.f.new_module_declaration(
                        nodes,
                        None,
                        Kind::NamespaceKeyword,
                        Some(name_id),
                        None, /*attributes*/
                        Some(empty_block),
                    );
                    body_stmts.push(HoverStatement {
                        node: decl,
                        is_local: false,
                    });
                }
                i += 1;
                continue;
            }

            // Handle remaining member kinds (type alias, enum, class,
            // interface, namespace, variable)
            let m_name = symbol_name(c, m);
            if let Some(node) = self.serialize_namespace_member(c, nodes, resolved, &m_name) {
                body_stmts.push(HoverStatement {
                    node,
                    is_local: false,
                });
            }
            i += 1;
        }

        // Add export modifier to exported statements (skip local declarations
        // and ExportDeclarations).
        for stmt in body_stmts.iter_mut() {
            if stmt.is_local || ast::is_export_declaration(&nodes[stmt.node]) {
                continue;
            }
            if ast::can_have_modifiers(&nodes[stmt.node]) {
                let mf = nodes[stmt.node].modifier_flags() | ModifierFlags::EXPORT;
                let modifiers = ast::create_modifiers_from_modifier_flags(mf, &mut |kind| {
                    self.f.new_token(nodes, kind)
                });
                let modifier_list = self.f.new_modifier_list(nodes, modifiers);
                if let Some(updated) =
                    ast::replace_modifiers(&mut self.f, nodes, stmt.node, Some(modifier_list))
                {
                    stmt.node = updated;
                }
            }
        }

        // Collect nodes, stripping export if all statements are exported.
        let mut body_statements: Vec<NodeId> = body_stmts.iter().map(|s| s.node).collect();
        let all_exported = !body_statements.is_empty()
            && body_statements
                .iter()
                .all(|&d| ast::has_syntactic_modifier(&nodes[d], ModifierFlags::EXPORT));
        if all_exported {
            for stmt in body_statements.iter_mut() {
                if ast::can_have_modifiers(&nodes[*stmt]) {
                    let mf = nodes[*stmt].modifier_flags().without(ModifierFlags::EXPORT);
                    let modifiers = ast::create_modifiers_from_modifier_flags(mf, &mut |kind| {
                        self.f.new_token(nodes, kind)
                    });
                    let modifier_list = self.f.new_modifier_list(nodes, modifiers);
                    if let Some(updated) =
                        ast::replace_modifiers(&mut self.f, nodes, *stmt, Some(modifier_list))
                    {
                        *stmt = updated;
                    }
                }
            }
        }

        let keyword = if local_name.is_some_and(|n| ast::is_identifier(&nodes[n])) {
            Kind::NamespaceKeyword
        } else {
            Kind::ModuleKeyword
        };
        let mut attributes: Option<NodeId> = None;
        let attributes_source = symbol_declarations(c, symbol)
            .iter()
            .copied()
            .find(|&declaration| {
                let __program = c.program.clone().expect("program");
                let dn = __program.nodes((declaration).file_index());
                ast::is_module_declaration(&dn[declaration])
                    && dn[declaration].as_module_declaration().attributes.is_some()
            })
            .and_then(|declaration| {
                let __program = c.program.clone().expect("program");
                let dn = __program.nodes((declaration).file_index());
                dn[declaration].as_module_declaration().attributes
            });
        if let Some(attr) = attributes_source {
            attributes = self.deep_clone_node_in(c, nodes, attr);
            if let Some(a) = attributes {
                self.e
                    .borrow()
                    .set_emit_flags(a, printer::EmitFlags::SINGLE_LINE);
            }
        }
        let module_block = self
            .f
            .new_module_block(nodes, Some(self.f.new_node_list(body_statements)));
        Some(self.f.new_module_declaration(
            nodes,
            None,
            keyword,
            local_name,
            attributes,
            Some(module_block),
        ))
    }

    /// `(b *NodeBuilderImpl) serializeTypeAliasForNamespace` — produces a
    /// TypeAliasDeclaration for a type alias inside a namespace body.
    fn serialize_type_alias_for_namespace(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        name: &str,
    ) -> Option<NodeId> {
        let alias_type = c.get_declared_type_of_type_alias(symbol);
        let type_params = c.get_local_type_parameters_of_class_or_interface_or_type_alias(symbol, nodes);
        let type_param_decls: Vec<NodeId> = type_params
            .iter()
            .map(|&p| self.type_parameter_to_declaration(c, nodes, p))
            .collect();
        let restore_flags = self.save_restore_flags();
        self.ctx.flags |= nodebuilder::Flags::IN_TYPE_ALIAS;
        let type_node = self.type_to_type_node(c, nodes, alias_type);
        restore_flags.restore(&mut self.ctx);
        self.ctx.approximate_length += 8 + name.len() as i32;
        let name_id = self.f.new_identifier(nodes, name);
        let type_param_list = self.f.new_node_list(type_param_decls);
        Some(self.f.new_type_alias_declaration(
            nodes,
            None,
            Some(name_id),
            Some(type_param_list),
            Some(type_node),
        ))
    }

    /// `(b *NodeBuilderImpl) filterInheritedProperties` — removes properties
    /// already present in base types.
    fn filter_inherited_properties(
        &mut self,
        c: &mut Checker,
        t: TypeId,
        base_types: &[TypeId],
        properties: Vec<SymbolId>,
    ) -> Vec<SymbolId> {
        if base_types.is_empty() {
            return properties;
        }
        // Build a lookup from property name to symbol for parent-identity
        // comparison.
        let mut props_by_name: FxHashMap<String, SymbolId> =
            FxHashMap::with_capacity_and_hasher(properties.len(), Default::default());
        for &p in &properties {
            props_by_name.insert(symbol_name(c, p), p);
        }
        // Collect names of properties inherited unchanged from base types.
        let mut inherited: FxHashSet<String> = FxHashSet::default();
        for &base in base_types {
            let this_type = {
                let target = c.get_target_type(t);
                c.types_handle()
                    .get(target)
                    .as_interface_type()
                    .and_then(|i| i.this_type())
            };
            let base_with_this = c.get_type_with_this_argument(base, this_type, false);
            for prop in c.get_properties_of_type(base_with_this) {
                let prop_name = symbol_name(c, prop);
                if let Some(&existing) = props_by_name.get(&prop_name)
                    && symbol_parent(c, prop) == symbol_parent(c, existing)
                {
                    inherited.insert(prop_name);
                }
            }
        }
        if inherited.is_empty() {
            return properties;
        }
        properties
            .into_iter()
            .filter(|&p| !inherited.contains(&symbol_name(c, p)))
            .collect()
    }

    /// `(b *NodeBuilderImpl) isNamespaceMember`.
    pub(crate) fn is_namespace_member(&self, c: &Checker, p: SymbolId) -> bool {
        let flags = symbol_flags(c, p);
        if flags.intersects(SymbolFlags::TYPE | SymbolFlags::NAMESPACE | SymbolFlags::ALIAS) {
            return true;
        }
        if flags.intersects(SymbolFlags::PROTOTYPE) || symbol_name(c, p) == "prototype" {
            return false;
        }
        if let Some(vd) = symbol_value_declaration(c, p) {
            let __program = c.program.clone().expect("program");
            let dn = __program.nodes((vd).file_index());
            if ast::has_static_modifier(&dn[vd])
                && dn[vd]
                    .parent
                    .is_some_and(|parent| ast::is_class_like(Some(parent), &dn))
            {
                return false;
            }
        }
        true
    }
}
