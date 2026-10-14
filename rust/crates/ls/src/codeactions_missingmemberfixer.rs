// Ported from tsc/internal/ls/codeactions_missingmemberfixer.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `*ast.Node` → `NodeId`; `*checker.Checker` → `Rc<RefCell<Checker>>`;
//   `*checker.Type` → `TypeId`; `*ast.Symbol` → `SymbolId`;
//   `*checker.Signature` → `SignatureId`; `autoimport.ImportAdder` →
//   `Option<&mut dyn ImportAdder>` (Go's interface is nilable).
// - `preserveOptionalFlags` → plain `u8` constants.
// - Go shares `f.changeTracker.EmitContext` with the `NodeBuilder` so the
//   builder's factory sees the same generated-name bookkeeping. `EmitContext`
//   is not cloneable and its `shared` state is `pub(crate)` to tsc_printer,
//   so the builder gets a fresh `EmitContext` — functionally equivalent here
//   (the builder only reads the context for emit flags, and the missing
//   member fixer never mints generated names through it).
// - `idToSymbol` lives inside `NodeBuilderImpl`; each builder call takes it
//   out, runs `importTypeNode`, and puts it back so subsequent calls on the
//   same builder share the accumulated map exactly like Go.
// - `declaration.Name().Clone(factory)` / `DeepCloneNode` can only clone
//   inside one arena in this port. Same-file declarations clone exactly like
//   Go; names declared in a *foreign* arena (e.g. an interface in a .d.ts)
//   are recursively rebuilt for the name-shaped kinds, falling back to an
//   identifier minted from the symbol name.
// - `checker.GetSetAccessorValueParameter` is `pub(crate)` to tsc_checker and
//   tsc_transformers is not a dependency of tsc-ls, so a local copy is kept.
// - `createDummyParameters` returns `*ast.ParameterList` in Go whose `Nodes`
//   the caller then appends to; here `create_dummy_parameter_nodes` returns
//   `Vec<NodeId>` and callers wrap it in `NodeList::new`/`new_node_list`.
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::ast::Node;
use tsc_ast::checkflags::CheckFlags;
use tsc_ast::{
    self as ast, Kind, ModifierFlags, ModifierList, NodeFlags, NodeId, SymbolFlags, SymbolId,
    TokenFlags,
};
use tsc_checker::checker_core::Checker;
use tsc_checker::nodebuilder::{NodeBuilder, new_node_builder, new_node_builder_ex};
use tsc_checker::types::{SignatureId, TypeId};
use tsc_compiler::program::Program;
use tsc_diagnostics as diagnostics;
use tsc_locale::Locale;
use tsc_lsutil::{self as lsutil, QuotePreference, UserPreferences};
use tsc_nodebuilder as nodebuilder;
use tsc_printer::EmitContext;

use crate::autoimport::import_adder::{
    ImportAdder, try_get_auto_importable_reference_from_type_node,
};
use crate::change::tracker::Tracker;

/// `preserveOptionalFlagsMethod`.
pub(crate) const PRESERVE_OPTIONAL_FLAGS_METHOD: u8 = 1 << 0;
/// `preserveOptionalFlagsProperty`.
pub(crate) const PRESERVE_OPTIONAL_FLAGS_PROPERTY: u8 = 1 << 1;
/// `preserveOptionalFlagsAll`.
pub(crate) const PRESERVE_OPTIONAL_FLAGS_ALL: u8 =
    PRESERVE_OPTIONAL_FLAGS_METHOD | PRESERVE_OPTIONAL_FLAGS_PROPERTY;

/// `preserveOptionalFlags`.
pub(crate) type PreserveOptionalFlags = u8;

/// `missingMemberFixer` — ports the Go struct of the same name.
pub(crate) struct MissingMemberFixer<'a, 'c, 'h> {
    /// `changeTracker`.
    pub change_tracker: &'a mut Tracker<'c, 'h>,
    /// `typeChecker`.
    pub checker: &'a Rc<RefCell<Checker>>,
    /// `program`.
    pub program: &'a Rc<Program>,
    /// `preferences`.
    pub preferences: &'a UserPreferences,
    /// `importAdder` — `None` mirrors Go's nil.
    pub import_adder: Option<&'a mut dyn ImportAdder>,
    /// `locale`.
    pub locale: Locale,
}

/// `newMissingMemberFixer`.
pub(crate) fn new_missing_member_fixer<'a, 'c, 'h>(
    change_tracker: &'a mut Tracker<'c, 'h>,
    program: &'a Rc<Program>,
    type_checker: &'a Rc<RefCell<Checker>>,
    preferences: &'a UserPreferences,
    import_adder: Option<&'a mut dyn ImportAdder>,
    locale: Locale,
) -> MissingMemberFixer<'a, 'c, 'h> {
    MissingMemberFixer {
        change_tracker,
        checker: type_checker,
        program,
        preferences,
        import_adder,
        locale,
    }
}

impl<'a, 'c, 'h> MissingMemberFixer<'a, 'c, 'h> {
    /// Runs `f` with a mutable arena guard for `file` and the tracker's
    /// factory bound to that file, then drops the guard so subsequent
    /// checker/tracker calls see the minted nodes.
    fn with_factory<R>(
        &mut self,
        file: NodeId,
        f: impl FnOnce(&mut Vec<Node>, &mut tsc_printer::NodeFactory) -> R,
    ) -> R {
        let mut m = self.program.nodes_mut(file.file_index());
        let r = {
            let factory = self.change_tracker.node_factory(file);
            f(&mut m, factory)
        };
        drop(m);
        r
    }

    /// `createNodeBuilder` — see PORT note on the fresh `EmitContext`.
    fn create_node_builder(&self) -> NodeBuilder<'static> {
        new_node_builder_ex(
            &self.checker.borrow(),
            EmitContext::new(),
            FxHashMap::default(),
        )
    }

    /// `createMemberFromSymbol`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn create_member_from_symbol(
        &mut self,
        symbol: SymbolId,
        enclosing_declaration: NodeId,
        source_file: NodeId,
        body: Option<NodeId>,
        preserve_optional: PreserveOptionalFlags,
        abstract_: bool,
    ) -> Vec<NodeId> {
        let declarations = self.program.symbols.borrow()[symbol.index()]
            .declarations
            .clone();
        let declaration = declarations.first().copied();
        let file_index = source_file.file_index();

        let (quote_preference, ambient) = {
            let nodes = self.program.nodes(file_index);
            (
                lsutil::get_quote_preference(&nodes, source_file, self.preferences),
                nodes[enclosing_declaration]
                    .flags
                    .intersects(NodeFlags::AMBIENT),
            )
        };
        let signature_only = ambient || abstract_;
        let optional = self.program.symbols.borrow()[symbol.index()]
            .flags
            .intersects(SymbolFlags::OPTIONAL);
        let kind = declaration.map_or(Kind::PropertySignature, |d| {
            self.program.nodes(d.file_index())[d].kind
        });
        let declaration_name =
            self.create_declaration_name(symbol, declaration, source_file);
        let modifiers = self.create_modifiers(symbol, declaration, source_file);

        let mut flags = nodebuilder::Flags::NO_TRUNCATION;
        if quote_preference == QuotePreference::SINGLE {
            flags |= nodebuilder::Flags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE;
        }

        let t = {
            let mut cb = self.checker.borrow_mut();
            let inner = cb.get_type_of_symbol_at_location(symbol, Some(enclosing_declaration));
            cb.get_widened_type(inner)
        };
        let mut result: Vec<NodeId> = Vec::new();

        match kind {
            Kind::PropertySignature | Kind::PropertyDeclaration => {
                let mut node_builder = self.create_node_builder();
                // Go: typeNode is built first, then questionToken, then
                // createPropertyName inside the NewPropertyDeclaration call.
                let type_node =
                    self.create_type_node(t, enclosing_declaration, flags, &mut node_builder);
                let question_token = if optional
                    && preserve_optional & PRESERVE_OPTIONAL_FLAGS_PROPERTY != 0
                {
                    self.with_factory(source_file, |m, f| {
                        Some(f.new_token(m, Kind::QuestionToken))
                    })
                } else {
                    None
                };
                let name = declaration_name
                    .map(|n| self.create_property_name(n, &quote_preference, source_file));
                let node = self.with_factory(source_file, |m, f| {
                    f.new_property_declaration(m, modifiers, name, question_token, type_node, None)
                });
                result.push(node);
                result
            }

            Kind::GetAccessor | Kind::SetAccessor => {
                let mut node_builder = self.create_node_builder();
                let first = declaration.expect("accessor declaration");
                let accessors = {
                    let nodes = self.program.nodes(first.file_index());
                    ast::get_all_accessor_declarations(&declarations, first, &nodes)
                };
                let ordered_accessors: Vec<NodeId> = match accessors.second_accessor {
                    None => vec![accessors.first_accessor],
                    Some(second) => vec![accessors.first_accessor, second],
                };

                for accessor in ordered_accessors {
                    let accessor_kind = self.program.nodes(accessor.file_index())
                        [accessor]
                        .kind;
                    if accessor_kind == Kind::GetAccessor {
                        // Go arg order: propertyName, typeNode, body.
                        let name = declaration_name.map(|n| {
                            self.create_property_name(n, &quote_preference, source_file)
                        });
                        let type_node = self.create_type_node(
                            t,
                            enclosing_declaration,
                            flags,
                            &mut node_builder,
                        );
                        let body_node = self.create_body(
                            body,
                            &quote_preference,
                            signature_only,
                            source_file,
                        );
                        let node = self.with_factory(source_file, |m, f| {
                            f.new_get_accessor_declaration(
                                m,
                                modifiers.clone(),
                                name,
                                None,
                                None,
                                type_node,
                                None,
                                body_node,
                            )
                        });
                        result.push(node);
                    } else if accessor_kind == Kind::SetAccessor {
                        let parameter_name = {
                            let nodes = self.program.nodes(accessor.file_index());
                            let parameter = get_set_accessor_value_parameter(
                                Some(accessor),
                                &nodes,
                            )
                            .expect("Expected set accessor to have a parameter.");
                            nodes[parameter]
                                .name()
                                .map(|n| nodes[n].text(&nodes).into_owned())
                                .unwrap_or_default()
                        };
                        let in_js = {
                            let nodes =
                                self.program.nodes(enclosing_declaration.file_index());
                            ast::is_in_js_file(Some(enclosing_declaration), &nodes)
                        };
                        let name = declaration_name.map(|n| {
                            self.create_property_name(n, &quote_preference, source_file)
                        });
                        let type_node = self.create_type_node(
                            t,
                            enclosing_declaration,
                            flags,
                            &mut node_builder,
                        );
                        let parameters = {
                            let mut m = self.program.nodes_mut(file_index);
                            let factory = self.change_tracker.node_factory(source_file);
                            let params = create_dummy_parameter_nodes(
                                &mut m,
                                factory,
                                1,
                                &[parameter_name],
                                &[type_node],
                                1,
                                in_js,
                            );
                            factory.new_node_list(params)
                        };
                        let body_node = self.create_body(
                            body,
                            &quote_preference,
                            signature_only,
                            source_file,
                        );
                        let node = self.with_factory(source_file, |m, f| {
                            f.new_set_accessor_declaration(
                                m,
                                modifiers.clone(),
                                name,
                                None,
                                Some(parameters),
                                None,
                                None,
                                body_node,
                            )
                        });
                        result.push(node);
                    }
                }
                result
            }

            Kind::MethodSignature | Kind::MethodDeclaration => {
                let signatures = self.get_call_signatures(t);
                let preserve_optional = optional
                    && preserve_optional & PRESERVE_OPTIONAL_FLAGS_METHOD != 0;
                if signatures.is_empty() {
                    return Vec::new();
                }

                if declarations.len() == 1 {
                    let body_node = self.create_body(
                        body,
                        &quote_preference,
                        signature_only,
                        source_file,
                    );
                    if let Some(method) = self.create_signature_declaration_from_signature(
                        signatures[0],
                        Kind::MethodDeclaration,
                        source_file,
                        enclosing_declaration,
                        body_node,
                        modifiers,
                        declaration_name,
                        preserve_optional,
                    ) {
                        result.push(method);
                    }
                    return result;
                }

                for &signature in &signatures {
                    if let Some(decl) = self
                        .checker
                        .borrow()
                        .signature_arena
                        .get(signature)
                        .declaration()
                    {
                        if self.program.nodes(decl.file_index())[decl]
                            .flags
                            .intersects(NodeFlags::AMBIENT)
                        {
                            continue;
                        }
                    }
                    if let Some(method) = self.create_signature_declaration_from_signature(
                        signature,
                        Kind::MethodDeclaration,
                        source_file,
                        enclosing_declaration,
                        None,
                        modifiers.clone(),
                        declaration_name,
                        preserve_optional,
                    ) {
                        result.push(method);
                    }
                }

                if signature_only {
                    return result;
                }

                if declarations.len() > signatures.len() {
                    let signature = self
                        .checker
                        .borrow_mut()
                        .get_signature_from_declaration(
                            *declarations.last().unwrap(),
                        );
                    let body_node = self.create_body(
                        body,
                        &quote_preference,
                        false,
                        source_file,
                    );
                    if let Some(method) = self.create_signature_declaration_from_signature(
                        signature,
                        Kind::MethodDeclaration,
                        source_file,
                        enclosing_declaration,
                        body_node,
                        modifiers,
                        declaration_name,
                        preserve_optional,
                    ) {
                        result.push(method);
                    }
                } else if let Some(method) = self
                    .create_signature_declaration_from_signatures(
                        &signatures,
                        declaration_name,
                        preserve_optional,
                        modifiers,
                        &quote_preference,
                        body,
                        enclosing_declaration,
                        source_file,
                    )
                {
                    result.push(method);
                }

                result
            }
            _ => Vec::new(),
        }
    }

    /// `getCallSignatures`.
    fn get_call_signatures(&mut self, t: TypeId) -> Vec<SignatureId> {
        let mut cb = self.checker.borrow_mut();
        if cb.types.get(t).is_union() {
            let members = cb.types.get(t).types().to_vec();
            let mut out = Vec::new();
            for member in members {
                out.extend(cb.get_call_signatures(member));
            }
            out
        } else {
            cb.get_call_signatures(t)
        }
    }

    /// `createTypeNode` — runs `nodeBuilder.TypeToTypeNode` then
    /// `importTypeNode`. The builder's accumulated `id_to_symbol` map is
    /// taken out for the import pass and restored so later calls on the
    /// same builder keep sharing it.
    fn create_type_node(
        &mut self,
        t: TypeId,
        enclosing_declaration: NodeId,
        flags: nodebuilder::Flags,
        node_builder: &mut NodeBuilder,
    ) -> Option<NodeId> {
        let type_node = {
            let mut cb = self.checker.borrow_mut();
            let mut m = self.program.nodes_mut(enclosing_declaration.file_index());
            node_builder.type_to_type_node(
                &mut cb,
                &mut m,
                t,
                Some(enclosing_declaration),
                flags,
                nodebuilder::InternalFlags::NONE,
                None,
            )
        };
        let id_to_symbol = take_id_to_symbol(node_builder);
        let result = self.import_type_node(type_node, &id_to_symbol);
        restore_id_to_symbol(node_builder, id_to_symbol);
        result
    }

    /// `createModifiers`.
    fn create_modifiers(
        &mut self,
        symbol: SymbolId,
        declaration: Option<NodeId>,
        source_file: NodeId,
    ) -> Option<ModifierList> {
        let mut modifier_flags = ModifierFlags::NONE;
        if let Some(decl) = declaration {
            let effective = tsc_checker::utilities::get_declaration_modifier_flags_from_symbol(
                &self.checker.borrow(),
                symbol,
            );
            modifier_flags = effective & ModifierFlags::STATIC;
            if effective.intersects(ModifierFlags::PUBLIC) {
                modifier_flags |= ModifierFlags::PUBLIC;
            } else if effective.intersects(ModifierFlags::PROTECTED) {
                modifier_flags |= ModifierFlags::PROTECTED;
            }
            if {
                let nodes = self.program.nodes(decl.file_index());
                ast::is_auto_accessor_property_declaration(&nodes[decl])
            } {
                modifier_flags |= ModifierFlags::ACCESSOR;
            }
        }
        if self.should_add_override_keyword(declaration) {
            modifier_flags |= ModifierFlags::OVERRIDE;
        }
        if modifier_flags == ModifierFlags::NONE {
            return None;
        }
        Some(self.with_factory(source_file, |m, f| {
            let mods = ast::create_modifiers_from_modifier_flags(
                modifier_flags,
                &mut |kind| f.new_token(m, kind),
            );
            f.new_modifier_list(m, mods)
        }))
    }

    /// `shouldAddOverrideKeyword`.
    fn should_add_override_keyword(&self, declaration: Option<NodeId>) -> bool {
        let Some(decl) = declaration else {
            return false;
        };
        if !self.program.options().no_implicit_override.is_true() {
            return false;
        }
        let nodes = self.program.nodes(decl.file_index());
        ast::has_abstract_modifier(&nodes[decl])
    }

    /// `createSignatureDeclarationFromSignature`.
    #[allow(clippy::too_many_arguments)]
    fn create_signature_declaration_from_signature(
        &mut self,
        signature: SignatureId,
        kind: Kind,
        source_file: NodeId,
        enclosing_declaration: NodeId,
        body: Option<NodeId>,
        modifiers: Option<ModifierList>,
        name: Option<NodeId>,
        optional: bool,
    ) -> Option<NodeId> {
        let file_index = enclosing_declaration.file_index();
        let quote_preference = {
            let nodes = self.program.nodes(source_file.file_index());
            lsutil::get_quote_preference(&nodes, source_file, self.preferences)
        };
        let mut flags = nodebuilder::Flags::NO_TRUNCATION
            | nodebuilder::Flags::SUPPRESS_ANY_RETURN_TYPE
            | nodebuilder::Flags::ALLOW_EMPTY_TUPLE;
        if quote_preference == QuotePreference::SINGLE {
            flags |= nodebuilder::Flags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE;
        }

        let mut node_builder = self.create_node_builder();
        let signature_declaration = {
            let mut cb = self.checker.borrow_mut();
            let mut m = self.program.nodes_mut(file_index);
            node_builder.signature_to_signature_declaration(
                &mut cb,
                &mut m,
                signature,
                kind,
                Some(enclosing_declaration),
                flags,
                nodebuilder::InternalFlags::ALLOW_UNRESOLVED_NAMES,
                None,
            )
        }?;
        let id_to_symbol = take_id_to_symbol(&mut node_builder);

        let (parameters_list, mut type_parameters, type_node) = {
            let nodes = self.program.nodes(file_index);
            let is_js = ast::is_in_js_file(Some(enclosing_declaration), &nodes);
            (
                nodes[signature_declaration].parameter_list().cloned(),
                if is_js {
                    None
                } else {
                    nodes[signature_declaration].type_parameter_list().cloned()
                },
                if is_js {
                    None
                } else {
                    nodes[signature_declaration].type_()
                },
            )
        };
        let is_js = {
            let nodes = self.program.nodes(file_index);
            ast::is_in_js_file(Some(enclosing_declaration), &nodes)
        };

        if let Some(tps) = &type_parameters {
            if !tps.nodes.is_empty() {
                let mut new_nodes: Vec<NodeId> = Vec::with_capacity(tps.nodes.len());
                for &tp in &tps.nodes {
                    if tp.is_none() {
                        continue;
                    }
                    let fields = {
                        let nodes = self.program.nodes(file_index);
                        if ast::is_type_parameter_declaration(&nodes[tp]) {
                            let d = nodes[tp].as_type_parameter_declaration();
                            Some((
                                nodes[tp].modifiers().cloned(),
                                d.name,
                                d.constraint,
                                d.expression,
                                d.default_type,
                            ))
                        } else {
                            None
                        }
                    };
                    if let Some((tp_modifiers, tp_name, constraint, expression, default_type)) =
                        fields
                    {
                        let constraint =
                            self.import_type_node(constraint, &id_to_symbol);
                        let default_type =
                            self.import_type_node(default_type, &id_to_symbol);
                        new_nodes.push(self.with_factory(source_file, |m, f| {
                            f.update_type_parameter_declaration(
                                m,
                                tp,
                                tp_modifiers,
                                tp_name,
                                constraint,
                                expression,
                                default_type,
                            )
                            .unwrap_or(tp)
                        }));
                    } else {
                        new_nodes.push(tp);
                    }
                }
                type_parameters = Some(
                    self.change_tracker
                        .node_factory(source_file)
                        .new_node_list(new_nodes),
                );
            }
        }

        let mut parameters = parameters_list;
        if let Some(params) = &parameters {
            let mut new_nodes: Vec<NodeId> = Vec::with_capacity(params.nodes.len());
            for &p in &params.nodes {
                if p.is_none() {
                    continue;
                }
                let fields = {
                    let nodes = self.program.nodes(file_index);
                    let d = nodes[p].as_parameter_declaration();
                    (
                        nodes[p].modifiers().cloned(),
                        d.dot_dot_dot_token,
                        d.name,
                        d.question_token,
                        d.type_,
                        d.initializer,
                    )
                };
                let (
                    p_modifiers,
                    dot_dot_dot_token,
                    p_name,
                    question_token,
                    parameter_type_node,
                    initializer,
                ) = fields;
                let parameter_type_node =
                    self.import_type_node(parameter_type_node, &id_to_symbol);
                new_nodes.push(self.with_factory(source_file, |m, f| {
                    f.update_parameter_declaration(
                        m,
                        p,
                        p_modifiers,
                        dot_dot_dot_token,
                        p_name,
                        if is_js { None } else { question_token },
                        parameter_type_node,
                        initializer,
                    )
                    .unwrap_or(p)
                }));
            }
            parameters = Some(
                self.change_tracker
                    .node_factory(source_file)
                    .new_node_list(new_nodes),
            );
        }

        let type_node = self.import_type_node(type_node, &id_to_symbol);

        let question_token = if optional {
            self.with_factory(source_file, |m, f| {
                Some(f.new_token(m, Kind::QuestionToken))
            })
        } else {
            None
        };

        match kind {
            Kind::FunctionExpression => {
                let (asterisk_token, full_signature, fn_body) = {
                    let nodes = self.program.nodes(file_index);
                    let d = nodes[signature_declaration].as_function_expression();
                    (
                        d.function_like_with_body_base.body_base.asterisk_token,
                        d.function_like_with_body_base
                            .function_like_base
                            .full_signature,
                        d.function_like_with_body_base.body_base.body,
                    )
                };
                let name_arg = name.filter(|&n| {
                    let nodes = self.program.nodes(source_file.file_index());
                    ast::is_identifier(&nodes[n])
                });
                self.with_factory(source_file, |m, f| {
                    f.update_function_expression(
                        m,
                        signature_declaration,
                        modifiers,
                        asterisk_token,
                        name_arg,
                        type_parameters,
                        parameters,
                        type_node,
                        full_signature,
                        body.or(fn_body),
                    )
                    .unwrap_or(signature_declaration)
                })
                .into()
            }

            Kind::ArrowFunction => {
                let (full_signature, equals_greater_than_token, fn_body) = {
                    let nodes = self.program.nodes(file_index);
                    let d = nodes[signature_declaration].as_arrow_function();
                    (
                        d.function_like_with_body_base
                            .function_like_base
                            .full_signature,
                        d.equals_greater_than_token,
                        d.function_like_with_body_base.body_base.body,
                    )
                };
                self.with_factory(source_file, |m, f| {
                    f.update_arrow_function(
                        m,
                        signature_declaration,
                        modifiers,
                        type_parameters,
                        parameters,
                        type_node,
                        full_signature,
                        equals_greater_than_token,
                        body.or(fn_body),
                    )
                    .unwrap_or(signature_declaration)
                })
                .into()
            }

            Kind::MethodDeclaration => {
                let (asterisk_token, full_signature) = {
                    let nodes = self.program.nodes(file_index);
                    let d = nodes[signature_declaration].as_method_declaration();
                    (
                        d.function_like_with_body_base.body_base.asterisk_token,
                        d.function_like_with_body_base
                            .function_like_base
                            .full_signature,
                    )
                };
                let method_name = match name {
                    None => self.with_factory(source_file, |m, f| {
                        f.new_identifier(m, "")
                    }),
                    Some(n) => {
                        self.create_property_name(n, &quote_preference, source_file)
                    }
                };
                self.with_factory(source_file, |m, f| {
                    f.update_method_declaration(
                        m,
                        signature_declaration,
                        modifiers,
                        asterisk_token,
                        Some(method_name),
                        question_token,
                        type_parameters,
                        parameters,
                        type_node,
                        full_signature,
                        body,
                    )
                    .unwrap_or(signature_declaration)
                })
                .into()
            }

            Kind::FunctionDeclaration => {
                let (asterisk_token, full_signature, fn_body) = {
                    let nodes = self.program.nodes(file_index);
                    let d = nodes[signature_declaration].as_function_declaration();
                    (
                        d.function_like_with_body_base.body_base.asterisk_token,
                        d.function_like_with_body_base
                            .function_like_base
                            .full_signature,
                        d.function_like_with_body_base.body_base.body,
                    )
                };
                let name_arg = name.filter(|&n| {
                    let nodes = self.program.nodes(source_file.file_index());
                    ast::is_identifier(&nodes[n])
                });
                self.with_factory(source_file, |m, f| {
                    f.update_function_declaration(
                        m,
                        signature_declaration,
                        modifiers,
                        asterisk_token,
                        name_arg,
                        type_parameters,
                        parameters,
                        type_node,
                        full_signature,
                        body.or(fn_body),
                    )
                    .unwrap_or(signature_declaration)
                })
                .into()
            }

            _ => None,
        }
    }

    /// `createSignatureDeclarationFromSignatures`.
    #[allow(clippy::too_many_arguments)]
    fn create_signature_declaration_from_signatures(
        &mut self,
        signatures: &[SignatureId],
        name: Option<NodeId>,
        optional: bool,
        modifiers: Option<ModifierList>,
        quote_preference: &QuotePreference,
        body: Option<NodeId>,
        enclosing_declaration: NodeId,
        source_file: NodeId,
    ) -> Option<NodeId> {
        if signatures.is_empty() {
            return None;
        }

        let mut node_builder = self.create_node_builder();
        let cb = self.checker.borrow();
        let mut max_args_signature = signatures[0];
        let mut min_argument_count = cb.signature_arena.get(signatures[0]).min_argument_count();
        let mut has_rest_parameter = false;
        for &signature in signatures {
            let (min_args, rest, param_count, max_param_count, max_rest) = {
                let s = cb.signature_arena.get(signature);
                let max_s = cb.signature_arena.get(max_args_signature);
                (
                    s.min_argument_count(),
                    s.has_rest_parameter(),
                    s.parameters().len(),
                    max_s.parameters().len(),
                    max_s.has_rest_parameter(),
                )
            };
            min_argument_count = min_argument_count.min(min_args);
            if rest {
                has_rest_parameter = true;
            }
            if param_count >= max_param_count && (!rest || max_rest) {
                max_args_signature = signature;
            }
        }
        let (max_param_count, max_rest, parameter_names) = {
            let s = cb.signature_arena.get(max_args_signature);
            let names: Vec<String> = s
                .parameters()
                .iter()
                .map(|&p| cb.symbol_arena.borrow()[p.index()].name.to_string())
                .collect();
            (s.parameters().len(), s.has_rest_parameter(), names)
        };
        drop(cb);

        let in_js = {
            let nodes = self.program.nodes(source_file.file_index());
            ast::is_in_js_file(Some(enclosing_declaration), &nodes)
        };
        let max_non_rest_args = max_param_count - usize::from(max_rest);
        let mut parameter_nodes = {
            let mut m = self.program.nodes_mut(source_file.file_index());
            let factory = self.change_tracker.node_factory(source_file);
            create_dummy_parameter_nodes(
                &mut m,
                factory,
                max_non_rest_args,
                &parameter_names,
                &[],
                min_argument_count,
                in_js,
            )
        };

        if has_rest_parameter {
            let rest_parameter_name = if max_non_rest_args < parameter_names.len()
                && !parameter_names[max_non_rest_args].is_empty()
            {
                parameter_names[max_non_rest_args].clone()
            } else {
                "rest".to_string()
            };
            let rest_parameter = self.with_factory(source_file, |m, f| {
                let question_token = if max_non_rest_args as i32 >= min_argument_count {
                    Some(f.new_token(m, Kind::QuestionToken))
                } else {
                    None
                };
                let dot_dot_dot = f.new_token(m, Kind::DotDotDotToken);
                let name_node = f.new_identifier(m, &rest_parameter_name);
                let unknown = f.new_keyword_type_node(m, Kind::UnknownKeyword);
                let array = f.new_array_type_node(m, Some(unknown));
                f.new_parameter_declaration(
                    m,
                    None,
                    Some(dot_dot_dot),
                    Some(name_node),
                    question_token,
                    Some(array),
                    None,
                )
            });
            parameter_nodes.push(rest_parameter);
        }
        let parameters = self
            .change_tracker
            .node_factory(source_file)
            .new_node_list(parameter_nodes);

        let method_name = match name {
            None => self.with_factory(source_file, |m, f| f.new_identifier(m, "")),
            Some(n) => self.create_property_name(n, quote_preference, source_file),
        };
        let question_token = if optional {
            self.with_factory(source_file, |m, f| {
                Some(f.new_token(m, Kind::QuestionToken))
            })
        } else {
            None
        };
        let type_node = self.get_return_type_from_signatures(
            signatures,
            enclosing_declaration,
            &mut node_builder,
        );
        let body_node = self.create_body(body, quote_preference, false, source_file);
        Some(self.with_factory(source_file, |m, f| {
            f.new_method_declaration(
                m,
                modifiers,
                None,
                Some(method_name),
                question_token,
                None,
                Some(parameters),
                type_node,
                None,
                body_node,
            )
        }))
    }

    /// `getReturnTypeFromSignatures`.
    fn get_return_type_from_signatures(
        &mut self,
        signatures: &[SignatureId],
        enclosing_declaration: NodeId,
        node_builder: &mut NodeBuilder,
    ) -> Option<NodeId> {
        if signatures.is_empty() {
            return None;
        }

        let union_type = {
            let mut cb = self.checker.borrow_mut();
            let return_types: Vec<TypeId> = signatures
                .iter()
                .map(|&s| cb.get_return_type_of_signature(s))
                .collect();
            cb.get_union_type(&return_types)
        };
        let type_node = {
            let mut cb = self.checker.borrow_mut();
            let mut m = self.program.nodes_mut(enclosing_declaration.file_index());
            node_builder.type_to_type_node(
                &mut cb,
                &mut m,
                union_type,
                Some(enclosing_declaration),
                nodebuilder::Flags::NO_TRUNCATION,
                nodebuilder::InternalFlags::ALLOW_UNRESOLVED_NAMES,
                None,
            )
        };
        let id_to_symbol = take_id_to_symbol(node_builder);
        let result = self.import_type_node(type_node, &id_to_symbol);
        restore_id_to_symbol(node_builder, id_to_symbol);
        result
    }

    /// `importTypeNode`.
    fn import_type_node(
        &mut self,
        type_node: Option<NodeId>,
        id_to_symbol: &FxHashMap<NodeId, SymbolId>,
    ) -> Option<NodeId> {
        let type_node = type_node?;
        if self.import_adder.is_none() {
            return Some(type_node);
        }

        let (imported_type_node, symbols) =
            try_get_auto_importable_reference_from_type_node(
                self.checker,
                type_node,
                id_to_symbol,
            );
        if let Some(imported) = imported_type_node {
            for symbol in symbols {
                let Some(export_symbol) = self.get_exported_symbol(symbol) else {
                    continue;
                };
                self.import_adder
                    .as_deref_mut()
                    .expect("checked above")
                    .add_import_from_exported_symbol(export_symbol, true);
            }
            return Some(imported);
        }

        let mut seen: HashSet<SymbolId> = HashSet::new();
        for &symbol in id_to_symbol.values() {
            if symbol.is_none() || !seen.insert(symbol) {
                continue;
            }
            let Some(export_symbol) = self.get_exported_symbol(symbol) else {
                continue;
            };
            self.import_adder
                .as_deref_mut()
                .expect("checked above")
                .add_import_from_exported_symbol(export_symbol, true);
        }
        Some(type_node)
    }

    /// `getExportedSymbol`.
    fn get_exported_symbol(&mut self, symbol: SymbolId) -> Option<SymbolId> {
        if symbol.is_none() {
            return None;
        }
        let mut cb = self.checker.borrow_mut();
        let symbol = cb.get_export_symbol_of_symbol(symbol);
        if cb.symbol_arena.borrow()[symbol.index()].parent.is_none() {
            return None;
        }
        Some(symbol)
    }

    /// `createIndexSignatureDeclarationFromType`.
    pub(crate) fn create_index_signature_declaration_from_type(
        &mut self,
        class_declaration: NodeId,
        implemented_type: TypeId,
        key_type: TypeId,
    ) -> Option<NodeId> {
        let index_info = self
            .checker
            .borrow_mut()
            .get_index_info_of_type(implemented_type, key_type)?;

        // `checker.NewNodeBuilder(f.typeChecker, f.changeTracker.EmitContext)`
        // — the EmitContext can't be shared across the crate boundary, so a
        // fresh one stands in (see PORT note).
        let mut builder = new_node_builder(&self.checker.borrow(), EmitContext::new());
        let mut cb = self.checker.borrow_mut();
        let mut m = self.program.nodes_mut(class_declaration.file_index());
        builder.index_info_to_index_signature_declaration(
            &mut cb,
            &mut m,
            index_info,
            Some(class_declaration),
            nodebuilder::Flags::NONE,
            nodebuilder::InternalFlags::NONE,
            None,
        )
    }

    /// `createBody`.
    fn create_body(
        &mut self,
        body: Option<NodeId>,
        quote_preference: &QuotePreference,
        signature_only: bool,
        source_file: NodeId,
    ) -> Option<NodeId> {
        if signature_only {
            return None;
        }
        let body = body.and_then(|b| {
            if b.file_index() == source_file.file_index() {
                self.with_factory(source_file, |m, f| f.deep_clone_node(m, b))
            } else {
                // PORT: deep_clone_node reads and writes a single arena; a
                // body defined in another file can't be cloned across
                // arenas, so it falls back to the stub like a nil body.
                None
            }
        });
        body.or_else(|| Some(self.create_stubbed_method_body(quote_preference, source_file)))
    }

    /// `createStubbedMethodBody`.
    fn create_stubbed_method_body(
        &mut self,
        quote_preference: &QuotePreference,
        source_file: NodeId,
    ) -> NodeId {
        let token_flags = if *quote_preference == QuotePreference::SINGLE {
            TokenFlags::SINGLE_QUOTE
        } else {
            TokenFlags::NONE
        };
        let message = diagnostics::Method_not_implemented.localize(&self.locale, &[""; 0]);
        self.with_factory(source_file, |m, f| {
            let error = f.new_identifier(m, "Error");
            let literal = f.new_string_literal(m, &message, token_flags);
            let args = f.new_node_list(vec![literal]);
            let new_expr = f.new_new_expression(m, Some(error), None, Some(args));
            let throw = f.new_throw_statement(m, Some(new_expr));
            let statements = f.new_node_list(vec![throw]);
            f.new_block(m, Some(statements), true)
        })
    }

    /// `createDeclarationName` — a method here because it needs the checker,
    /// the program and the tracker's factory (Go takes them via `f`/`tsc`).
    fn create_declaration_name(
        &mut self,
        symbol: SymbolId,
        declaration: Option<NodeId>,
        source_file: NodeId,
    ) -> Option<NodeId> {
        let (is_mapped, symbol_name) = {
            let symbols = self.program.symbols.borrow();
            let s = &symbols[symbol.index()];
            (s.check_flags.intersects(CheckFlags::MAPPED), s.name.clone())
        };
        if is_mapped {
            let mut cb = self.checker.borrow_mut();
            if let Some(name_type) = cb.get_name_type_of_symbol(symbol) {
                if tsc_checker::types::is_type_usable_as_property_name(&cb.types, name_type)
                {
                    let text = tsc_checker::utilities::get_property_name_from_type(
                        &cb.types, name_type,
                    );
                    drop(cb);
                    return Some(
                        self.with_factory(source_file, |m, f| f.new_identifier(m, &text)),
                    );
                }
            }
        }
        if let Some(decl) = declaration {
            let name = {
                let nodes = self.program.nodes(decl.file_index());
                nodes[decl].name()
            };
            if let Some(name) = name {
                // Go `declaration.Name().Clone(factory)` — a shallow clone.
                return self.clone_name_into(name, source_file, &symbol_name);
            }
        }
        Some(self.with_factory(source_file, |m, f| f.new_identifier(m, &symbol_name)))
    }

    /// `createPropertyName` — `node` must already live in `source_file`'s
    /// arena (it is always minted by `create_declaration_name` above).
    fn create_property_name(
        &mut self,
        node: NodeId,
        quote_preference: &QuotePreference,
        source_file: NodeId,
    ) -> NodeId {
        let is_ctor = {
            let nodes = self.program.nodes(source_file.file_index());
            ast::is_identifier(&nodes[node]) && nodes[node].text(&nodes) == "constructor"
        };
        if is_ctor {
            let token_flags = if *quote_preference == QuotePreference::SINGLE {
                TokenFlags::SINGLE_QUOTE
            } else {
                TokenFlags::NONE
            };
            self.with_factory(source_file, |m, f| {
                let literal = f.new_string_literal(m, "constructor", token_flags);
                f.new_computed_property_name(m, Some(literal))
            })
        } else {
            self.with_factory(source_file, |m, f| {
                f.deep_clone_node(m, node).unwrap_or(node)
            })
        }
    }

    /// Clones `name` (a declaration name / property name) into
    /// `target_file`'s arena. Same-arena names go through `clone_node`
    /// exactly like Go; foreign-arena names are recursively rebuilt for
    /// the name-shaped subtree kinds (see PORT note), falling back to an
    /// identifier minted from `symbol_name` for anything else.
    fn clone_name_into(
        &mut self,
        name: NodeId,
        target_file: NodeId,
        symbol_name: &str,
    ) -> Option<NodeId> {
        if name.file_index() == target_file.file_index() {
            return Some(self.with_factory(target_file, |m, f| f.clone_node(m, name)));
        }
        self.clone_foreign_subtree(name, target_file)
            .or_else(|| {
                Some(
                    self.with_factory(target_file, |m, f| f.new_identifier(m, symbol_name)),
                )
            })
    }

    /// Recursive cross-arena clone for the kinds reachable from a
    /// declaration name: identifiers, literals, computed property names and
    /// the entity/property-access expressions they may contain.
    fn clone_foreign_subtree(&mut self, node: NodeId, target_file: NodeId) -> Option<NodeId> {
        enum Plan {
            Identifier(String, bool),
            Literal(Kind, String, TokenFlags),
            Token(Kind),
            Computed(Option<NodeId>),
            PropertyAccess(Option<NodeId>, Option<NodeId>, Option<NodeId>, NodeFlags),
            ElementAccess(Option<NodeId>, Option<NodeId>, Option<NodeId>, NodeFlags),
            Parenthesized(Option<NodeId>),
            QualifiedName(Option<NodeId>, Option<NodeId>),
            PrefixUnary(Kind, Option<NodeId>),
        }
        let plan = {
            let foreign = self.program.nodes(node.file_index());
            let n = &foreign[node];
            match n.kind {
                Kind::Identifier => Plan::Identifier(n.text(&foreign).into_owned(), false),
                Kind::PrivateIdentifier => {
                    Plan::Identifier(n.text(&foreign).into_owned(), true)
                }
                Kind::StringLiteral
                | Kind::NumericLiteral
                | Kind::BigIntLiteral
                | Kind::NoSubstitutionTemplateLiteral => {
                    let l = n.literal_like_data()?;
                    Plan::Literal(n.kind, l.text.to_string(), l.token_flags)
                }
                Kind::ComputedPropertyName => {
                    Plan::Computed(n.as_computed_property_name().expression)
                }
                Kind::PropertyAccessExpression => {
                    let d = n.as_property_access_expression();
                    Plan::PropertyAccess(d.expression, d.question_dot_token, d.name, n.flags)
                }
                Kind::ElementAccessExpression => {
                    let d = n.as_element_access_expression();
                    Plan::ElementAccess(
                        d.expression,
                        d.question_dot_token,
                        d.argument_expression,
                        n.flags,
                    )
                }
                Kind::ParenthesizedExpression => {
                    Plan::Parenthesized(n.as_parenthesized_expression().expression)
                }
                Kind::QualifiedName => {
                    let d = n.as_qualified_name();
                    Plan::QualifiedName(d.left, d.right)
                }
                Kind::PrefixUnaryExpression => {
                    let d = n.as_prefix_unary_expression();
                    Plan::PrefixUnary(d.operator, d.operand)
                }
                Kind::ThisKeyword
                | Kind::TrueKeyword
                | Kind::FalseKeyword
                | Kind::NullKeyword
                | Kind::UndefinedKeyword => Plan::Token(n.kind),
                _ => return None,
            }
        };
        match plan {
            Plan::Identifier(text, private) => Some(self.with_factory(target_file, |m, f| {
                if private {
                    f.new_private_identifier(m, &text)
                } else {
                    f.new_identifier(m, &text)
                }
            })),
            Plan::Literal(kind, text, token_flags) => {
                Some(self.with_factory(target_file, |m, f| match kind {
                    Kind::StringLiteral => f.new_string_literal(m, &text, token_flags),
                    Kind::NumericLiteral => f.new_numeric_literal(m, &text, token_flags),
                    Kind::BigIntLiteral => f.new_big_int_literal(m, &text, token_flags),
                    Kind::NoSubstitutionTemplateLiteral => {
                        f.new_no_substitution_template_literal(m, &text, token_flags)
                    }
                    _ => unreachable!(),
                }))
            }
            Plan::Token(kind) => {
                Some(self.with_factory(target_file, |m, f| f.new_token(m, kind)))
            }
            Plan::Computed(expr) => {
                let expr = expr.and_then(|e| self.clone_foreign_subtree(e, target_file))?;
                Some(self.with_factory(target_file, |m, f| {
                    f.new_computed_property_name(m, Some(expr))
                }))
            }
            Plan::PropertyAccess(expression, qdt, name, node_flags) => {
                let expression =
                    expression.and_then(|e| self.clone_foreign_subtree(e, target_file))?;
                let name = name.and_then(|n| self.clone_foreign_subtree(n, target_file))?;
                Some(self.with_factory(target_file, |m, f| {
                    f.new_property_access_expression(
                        m,
                        Some(expression),
                        qdt,
                        Some(name),
                        node_flags,
                    )
                }))
            }
            Plan::ElementAccess(expression, qdt, arg, node_flags) => {
                let expression =
                    expression.and_then(|e| self.clone_foreign_subtree(e, target_file))?;
                let arg = arg.and_then(|a| self.clone_foreign_subtree(a, target_file))?;
                Some(self.with_factory(target_file, |m, f| {
                    f.new_element_access_expression(
                        m,
                        Some(expression),
                        qdt,
                        Some(arg),
                        node_flags,
                    )
                }))
            }
            Plan::Parenthesized(expr) => {
                let expr = expr.and_then(|e| self.clone_foreign_subtree(e, target_file))?;
                Some(self.with_factory(target_file, |m, f| {
                    f.new_parenthesized_expression(m, Some(expr))
                }))
            }
            Plan::QualifiedName(left, right) => {
                let left = left.and_then(|l| self.clone_foreign_subtree(l, target_file))?;
                let right = right.and_then(|r| self.clone_foreign_subtree(r, target_file))?;
                Some(self.with_factory(target_file, |m, f| {
                    f.new_qualified_name(m, Some(left), Some(right))
                }))
            }
            Plan::PrefixUnary(operator, operand) => {
                let operand =
                    operand.and_then(|o| self.clone_foreign_subtree(o, target_file))?;
                Some(self.with_factory(target_file, |m, f| {
                    f.new_prefix_unary_expression(m, operator, Some(operand))
                }))
            }
        }
    }
}

/// `createDummyParameters` — returns the parameter nodes; callers wrap them
/// in a `NodeList` (Go mutates `parameters.Nodes` after creation).
fn create_dummy_parameter_nodes(
    m: &mut Vec<Node>,
    factory: &mut tsc_printer::NodeFactory,
    arg_count: usize,
    names: &[String],
    types: &[Option<NodeId>],
    min_argument_count: i32,
    in_js: bool,
) -> Vec<NodeId> {
    let mut parameters: Vec<NodeId> = Vec::with_capacity(arg_count);
    let mut parameter_name_counts: HashMap<String, usize> = HashMap::new();

    for i in 0..arg_count {
        let mut parameter_name = if i < names.len() && !names[i].is_empty() {
            names[i].clone()
        } else {
            format!("arg{}", i)
        };

        let count = parameter_name_counts.get(&parameter_name).copied().unwrap_or(0);
        parameter_name_counts.insert(parameter_name.clone(), count + 1);
        if count > 0 {
            parameter_name = format!("{}{}", parameter_name, count);
        }

        let question_token = if i as i32 >= min_argument_count {
            Some(factory.new_token(m, Kind::QuestionToken))
        } else {
            None
        };

        let type_node = if in_js {
            None
        } else if i < types.len() && types[i].is_some() {
            types[i]
        } else {
            Some(factory.new_keyword_type_node(m, Kind::UnknownKeyword))
        };

        let name_node = factory.new_identifier(m, &parameter_name);
        parameters.push(factory.new_parameter_declaration(
            m,
            None,
            None,
            Some(name_node),
            question_token,
            type_node,
            None,
        ));
    }
    parameters
}

/// `checker.GetSetAccessorValueParameter` — local copy (the checker helper
/// is `pub(crate)` to tsc_checker).
fn get_set_accessor_value_parameter(node: Option<NodeId>, nodes: &[Node]) -> Option<NodeId> {
    let node = node?;
    let params = nodes[node].parameters()?;
    if !params.is_empty() {
        if params.len() >= 2 && ast::is_this_parameter(&nodes[params[0]], nodes) {
            return Some(params[1]);
        }
        return Some(params[0]);
    }
    None
}

/// Takes the accumulated `id_to_symbol` map out of a `NodeBuilder` — the
/// Rust port stores it inside `NodeBuilderImpl` where Go keeps an external
/// map shared with the caller.
fn take_id_to_symbol(node_builder: &mut NodeBuilder) -> FxHashMap<NodeId, SymbolId> {
    node_builder
        .impl_
        .as_mut()
        .map(|i| std::mem::take(&mut i.id_to_symbol))
        .unwrap_or_default()
}

/// Returns the map to the builder so the next `TypeToTypeNode` call keeps
/// accumulating into the same map.
fn restore_id_to_symbol(node_builder: &mut NodeBuilder, map: FxHashMap<NodeId, SymbolId>) {
    if let Some(i) = node_builder.impl_.as_mut() {
        i.id_to_symbol = map;
    }
}
