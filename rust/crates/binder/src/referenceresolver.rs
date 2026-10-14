// Ported from tsc/internal/binder/referenceresolver.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The `ReferenceResolver` interface and its default implementation used by
// transforms. Hooks mirror Go's `ReferenceResolverHooks`; each is optional
// and the implementation falls back to the same default behavior as Go.
//
// Pointer model: `*ast.Node` -> `NodeId`/`Option<NodeId>`; `*ast.Symbol` ->
// `SymbolId`/`Option<SymbolId>`; `*ast.Declaration` -> `Option<NodeId>`;
// `[]*ast.Declaration` -> `Vec<NodeId>`. The arena slices (`nodes`,
// `symbols`) travel as parameters because identity is `NodeId`/`SymbolId`,
// not a pointer into an arena the resolver could close over.
//
// PORT: Go's `referenceResolver` lazily constructs an internal
// `*NameResolver` only when `hooks.ResolveName` is nil; here `resolver` is
// eagerly held and only invoked in that case — identical semantics since a
// hook-free `NameResolver` is cheap.

use tsc_ast::ast::Node;
use tsc_ast::ids::{NodeId, SymbolId};
use tsc_ast::kind_generated::Kind;
use tsc_ast::symbol::{SymbolArena, SymbolTable};
use tsc_ast::symbolflags::SymbolFlags;
use tsc_ast::utilities::*;
use tsc_core::options_generated::CompilerOptions;
use tsc_diagnostics as diagnostics;

use crate::nameresolver::NameResolver;

/// `type ReferenceResolver interface` — every method needs the arenas, so
/// `nodes`/`symbols` are explicit parameters (Go reads them through the
/// arena pointers stored on `*ast.Symbol`/`ast.SymbolTable`).
pub trait ReferenceResolver {
    #[allow(clippy::too_many_arguments)]
    fn get_referenced_export_container(
        &mut self,
        node: NodeId,
        prefix_locals: bool,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> Option<NodeId>;

    fn get_referenced_import_declaration(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> Option<NodeId>;

    fn get_referenced_value_declaration(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> Option<NodeId>;

    fn get_referenced_value_declarations(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> Vec<NodeId>;

    fn get_element_access_expression_name(&mut self, expression: Option<NodeId>) -> String;

    fn get_referenced_member_value_declaration(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> Option<NodeId>;

    /// PORT: resolves `id` to a cloned `Node` — checks `nodes` first (the
    /// caller's working arena), then the checker's program-arena hook.
    /// Returned declaration `NodeId`s can live outside `nodes` (the Go port
    /// dereferences node pointers freely).
    fn resolve_node(&mut self, id: NodeId, nodes: &[Node]) -> Option<Node>;
}

/// `type ReferenceResolverHooks struct`.
// PORT: leading `&[Node]` is the resolver's live node arena — the hook
// routes it to `resolve_name_via_binder_live` so resolution sees synthetic
// nodes minted into the caller's checked-out buffer (Go's shared slice).
type ResolveNameHook<'a> = Box<
    dyn for<'x> FnMut(
            &'x [Node],
            Option<NodeId>,
            &str,
            SymbolFlags,
            Option<&'static diagnostics::Message>,
            bool,
            bool,
        ) -> Option<SymbolId>
        + 'a,
>;
type TypeOnlyAliasHook<'a> = Box<dyn FnMut(SymbolId, SymbolFlags) -> Option<NodeId> + 'a>;

#[derive(Default)]
pub struct ReferenceResolverHooks<'a> {
    /// `ResolveName`
    pub resolve_name: Option<ResolveNameHook<'a>>,
    /// `GetResolvedSymbol`
    pub get_resolved_symbol: Option<Box<dyn FnMut(NodeId) -> Option<SymbolId> + 'a>>,
    /// `GetMergedSymbol` — Go's hook may itself return nil.
    pub get_merged_symbol: Option<Box<dyn FnMut(SymbolId) -> Option<SymbolId> + 'a>>,
    /// `GetParentOfSymbol`
    pub get_parent_of_symbol: Option<Box<dyn FnMut(SymbolId) -> Option<SymbolId> + 'a>>,
    /// `GetSymbolOfDeclaration`
    pub get_symbol_of_declaration: Option<Box<dyn FnMut(NodeId) -> Option<SymbolId> + 'a>>,
    /// `GetTypeOnlyAliasDeclaration`
    pub get_type_only_alias_declaration: Option<TypeOnlyAliasHook<'a>>,
    /// `GetExportSymbolOfValueSymbolIfExported`
    pub get_export_symbol_of_value_symbol_if_exported:
        Option<Box<dyn FnMut(SymbolId) -> Option<SymbolId> + 'a>>,
    /// `GetElementAccessExpressionName` — returns `Some(name)` when the
    /// checker resolved a name (`(string, bool)` in Go).
    pub get_element_access_expression_name: Option<Box<dyn FnMut(NodeId) -> Option<String> + 'a>>,
    /// PORT: resolves `id`'s kind when `id` is not in the working arena —
    /// merged-symbol declarations can live in other files (the Go port
    /// dereferences node pointers, which have no arena concept). The
    /// checker wires this to its arena lookup.
    pub get_kind_of_node: Option<Box<dyn FnMut(NodeId) -> Option<Kind> + 'a>>,
    /// PORT: resolves `id` (a cloned `Node`) when `id` is not in the working
    /// arena — like `get_kind_of_node` but for whole-node field reads.
    pub resolve_node: Option<Box<dyn FnMut(NodeId) -> Option<Node> + 'a>>,
}

/// `type referenceResolver struct` — exported under the Go constructor's
//  spelling of the interface implementation.
pub struct ReferenceResolverImpl<'a> {
    resolver: NameResolver<'a>,
    pub options: &'a CompilerOptions,
    pub hooks: ReferenceResolverHooks<'a>,
}

/// `func NewReferenceResolver`.
pub fn new_reference_resolver<'a>(
    options: &'a CompilerOptions,
    hooks: ReferenceResolverHooks<'a>,
) -> ReferenceResolverImpl<'a> {
    ReferenceResolverImpl {
        resolver: NameResolver {
            host: None,
            for_suggestion: false,
            compiler_options: std::rc::Rc::new(options.clone()),
            globals: std::rc::Rc::new(std::cell::RefCell::new(SymbolTable::default())),
            arguments_symbol: None,
            require_symbol: None,
            get_symbol_of_declaration_hook: None,
            error_hook: None,
            lookup_hook: None,
            symbol_referenced: None,
            set_requires_scope_change_cache: None,
            get_requires_scope_change_cache: None,
            on_property_with_invalid_initializer: None,
            on_failed_to_resolve_symbol: None,
            on_successfully_resolved_symbol: None,
        },
        options,
        hooks,
    }
}

impl<'a> ReferenceResolverImpl<'a> {
    /// Overrides the resolver's `globals` table. `new_reference_resolver`
    /// constructs an empty one; callers that know the program's live global
    /// table (e.g. the emit resolver, which cannot reborrow the checker in
    /// `*Unsafe` contexts) share it here so global-scope names resolve.
    pub fn with_globals(mut self, globals: std::rc::Rc<std::cell::RefCell<SymbolTable>>) -> Self {
        self.resolver.globals = globals;
        self
    }

    /// `func (r *referenceResolver) getResolvedSymbol`.
    fn get_resolved_symbol(&mut self, node: Option<NodeId>) -> Option<SymbolId> {
        if let Some(node) = node {
            if let Some(hook) = self.hooks.get_resolved_symbol.as_mut() {
                return hook(node);
            }
        }
        None
    }

    /// `func (r *referenceResolver) getMergedSymbol`.
    fn get_merged_symbol(&mut self, symbol: Option<SymbolId>) -> Option<SymbolId> {
        if let Some(symbol) = symbol {
            if let Some(hook) = self.hooks.get_merged_symbol.as_mut() {
                return hook(symbol);
            }
            return Some(symbol);
        }
        None
    }

    /// `func (r *referenceResolver) getParentOfSymbol`.
    fn get_parent_of_symbol(
        &mut self,
        symbol: Option<SymbolId>,
        symbols: &SymbolArena,
    ) -> Option<SymbolId> {
        if let Some(symbol) = symbol {
            if let Some(hook) = self.hooks.get_parent_of_symbol.as_mut() {
                return hook(symbol);
            }
            return symbols.get_ref(symbol).parent;
        }
        None
    }

    /// `func (r *referenceResolver) getSymbolOfDeclaration`.
    fn get_symbol_of_declaration(
        &mut self,
        declaration: Option<NodeId>,
        nodes: &[Node],
    ) -> Option<SymbolId> {
        if let Some(declaration) = declaration {
            if let Some(hook) = self.hooks.get_symbol_of_declaration.as_mut() {
                return hook(declaration);
            }
            return nodes[declaration].symbol();
        }
        None
    }

    /// `func (r *referenceResolver) getReferencedValueSymbol`.
    fn get_referenced_value_symbol(
        &mut self,
        reference: NodeId,
        start_in_declaration_container: bool,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> Option<SymbolId> {
        let resolved_symbol = self.get_resolved_symbol(Some(reference));
        if resolved_symbol.is_some() {
            return resolved_symbol;
        }

        let mut location = Some(reference);
        if start_in_declaration_container
            && nodes[reference].parent.is_some()
            && is_declaration(&nodes[nodes[reference].parent.unwrap()])
            && nodes[nodes[reference].parent.unwrap()].name() == Some(reference)
        {
            location = get_declaration_container(nodes[reference].parent.unwrap(), nodes);
        }

        let meaning = SymbolFlags::EXPORT_VALUE | SymbolFlags::VALUE | SymbolFlags::ALIAS;
        let text = nodes[reference].text(nodes).into_owned();

        if let Some(hook) = self.hooks.resolve_name.as_mut() {
            return hook(
                nodes,
                location, &text, meaning, None,  /*nameNotFoundMessage*/
                false, /*isUse*/
                false, /*excludeGlobals*/
            );
        }

        self.resolver.resolve(
            location, &text, meaning, None,  /*nameNotFoundMessage*/
            false, /*isUse*/
            false, /*excludeGlobals*/
            nodes, symbols,
        )
    }

    /// `func (r *referenceResolver) isTypeOnlyAliasDeclaration`.
    fn is_type_only_alias_declaration(
        &mut self,
        symbol: Option<SymbolId>,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> bool {
        if let Some(symbol) = symbol {
            if let Some(hook) = self.hooks.get_type_only_alias_declaration.as_mut() {
                return hook(symbol, SymbolFlags::VALUE).is_some();
            }

            let mut node = self.get_declaration_of_alias_symbol(symbol, nodes, symbols);
            while let Some(n) = node {
                match nodes[n].kind {
                    Kind::ImportEqualsDeclaration | Kind::ExportDeclaration => {
                        return nodes[n].is_type_only();
                    }
                    Kind::ImportClause | Kind::ImportSpecifier | Kind::ExportSpecifier => {
                        if nodes[n].is_type_only() {
                            return true;
                        }
                        node = nodes[n].parent;
                        continue;
                    }
                    Kind::NamedImports | Kind::NamedExports => {
                        node = nodes[n].parent;
                        continue;
                    }
                    _ => {}
                }
                break;
            }
        }
        false
    }

    /// `func (r *referenceResolver) getDeclarationOfAliasSymbol` —
    /// `core.FindLast(symbol.Declarations, ast.IsAliasSymbolDeclaration)`.
    fn get_declaration_of_alias_symbol(
        &mut self,
        symbol: SymbolId,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> Option<NodeId> {
        symbols.get_ref(symbol)
            .declarations
            .iter()
            .rev()
            .find(|&&decl| is_alias_symbol_declaration(decl, nodes))
            .copied()
    }

    /// `func (r *referenceResolver) getExportSymbolOfValueSymbolIfExported`.
    fn get_export_symbol_of_value_symbol_if_exported(
        &mut self,
        symbol: Option<SymbolId>,
        symbols: &SymbolArena,
    ) -> Option<SymbolId> {
        if let Some(mut symbol) = symbol {
            if let Some(hook) = self
                .hooks
                .get_export_symbol_of_value_symbol_if_exported
                .as_mut()
            {
                return hook(symbol);
            }
            if symbols.get_ref(symbol)
                .flags
                .intersects(SymbolFlags::EXPORT_VALUE)
                && symbols.get_ref(symbol).export_symbol.is_some()
            {
                symbol = symbols.get_ref(symbol).export_symbol.unwrap();
            }
            return self.get_merged_symbol(Some(symbol));
        }
        None
    }
}

impl<'a> ReferenceResolverImpl<'a> {
    /// `id`'s kind — `nodes` may not be `id`'s arena (merged symbols can
    /// span files); the checker hook resolves cross-arena lookups.
    fn node_kind(&mut self, id: NodeId, nodes: &[Node]) -> Option<Kind> {
        if nodes
            .first()
            .is_some_and(|n| n.id.file_index() == id.file_index())
            && let Some(n) = nodes.get(id.local_index() as usize)
        {
            return Some(n.kind);
        }
        self.hooks
            .get_kind_of_node
            .as_mut()
            .and_then(|hook| hook(id))
    }
}

impl<'a> ReferenceResolverImpl<'a> {
    /// Resolves `id` against `nodes` first (the caller's working arena),
    /// falling back to the `resolve_node` hook for program-arena ids.
    fn resolved_node(&mut self, id: NodeId, nodes: &[Node]) -> Option<Node> {
        if nodes
            .first()
            .is_some_and(|n| n.id.file_index() == id.file_index())
            && let Some(n) = nodes.get(id.local_index() as usize)
        {
            return Some(n.clone());
        }
        self.hooks
            .resolve_node
            .as_mut()
            .and_then(|hook| hook(id))
    }
}

impl<'a> ReferenceResolver for ReferenceResolverImpl<'a> {
    /// `func (r *referenceResolver) GetReferencedExportContainer` — returns
    /// `SourceFile|ModuleDeclaration|EnumDeclaration`.
    fn get_referenced_export_container(
        &mut self,
        node: NodeId,
        prefix_locals: bool,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> Option<NodeId> {
        // When resolving the export for the name of a module or enum
        // declaration, we need to start resolution at the declaration's container.
        // Otherwise, we could incorrectly resolve the export as the
        // declaration if it contains an exported member with the same name.
        let start_in_declaration_container = nodes[node].parent.is_some_and(|p| {
            (nodes[p].kind == Kind::ModuleDeclaration || nodes[p].kind == Kind::EnumDeclaration)
                && nodes[p].name() == Some(node)
        });
        if let Some(mut symbol) =
            self.get_referenced_value_symbol(node, start_in_declaration_container, nodes, symbols)
        {
            if symbols.get_ref(symbol)
                .flags
                .intersects(SymbolFlags::EXPORT_VALUE)
            {
                // If we reference an exported entity within the same module declaration, then whether
                // we prefix depends on the kind of entity. SymbolFlags.ExportHasLocal encompasses all the
                // kinds that we do NOT prefix.
                let export_symbol_id = symbols.get_ref(symbol).export_symbol;
                let export_symbol = self.get_merged_symbol(export_symbol_id)?;
                if !prefix_locals
                    && symbols.get_ref(export_symbol)
                        .flags
                        .intersects(SymbolFlags::EXPORT_HAS_LOCAL)
                    && !symbols.get_ref(export_symbol)
                        .flags
                        .intersects(SymbolFlags::VARIABLE)
                {
                    return None;
                }
                symbol = export_symbol;
            }
            if let Some(parent_symbol) = self.get_parent_of_symbol(Some(symbol), symbols) {
                let parent_is_value_module_source_file = {
                    let vd = symbols.get_ref(parent_symbol).value_declaration;
                    symbols.get_ref(parent_symbol)
                        .flags
                        .intersects(SymbolFlags::VALUE_MODULE)
                        && vd.is_some_and(|vd| {
                            self.node_kind(vd, nodes) == Some(Kind::SourceFile)
                        })
                };
                if parent_is_value_module_source_file {
                    let symbol_file =
                        symbols.get_ref(parent_symbol).value_declaration.unwrap();
                    let reference_file = get_source_file_of_node(Some(node), nodes);
                    // If `node` accesses an export and that export isn't in the same file, then symbol is a namespace export, so return nil.
                    let symbol_is_umd_export = Some(symbol_file) != reference_file;
                    if symbol_is_umd_export {
                        return None;
                    }
                    return Some(symbol_file);
                }
                let mut is_matching_container = |n: &Node, _nodes: &[Node]| -> bool {
                    (n.kind == Kind::ModuleDeclaration || n.kind == Kind::EnumDeclaration)
                        && n.symbol() == Some(parent_symbol)
                };
                // PORT: `is_matching_container` uses `getSymbolOfDeclaration`
                // semantics via `n.symbol()`; when the hook is installed it
                // takes precedence (below).
                if self.hooks.get_symbol_of_declaration.is_none() {
                    return find_ancestor(nodes[node].parent, nodes, &mut is_matching_container);
                }
                let parent = nodes[node].parent;
                let mut current = parent;
                while let Some(n) = current {
                    if (nodes[n].kind == Kind::ModuleDeclaration
                        || nodes[n].kind == Kind::EnumDeclaration)
                        && self.get_symbol_of_declaration(Some(n), nodes) == Some(parent_symbol)
                    {
                        return Some(n);
                    }
                    current = nodes[n].parent;
                }
                return None;
            }
        }
        None
    }

    /// `func (r *referenceResolver) GetReferencedImportDeclaration`.
    fn get_referenced_import_declaration(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> Option<NodeId> {
        if let Some(symbol) = self.get_referenced_value_symbol(
            node, false, /*startInDeclarationContainer*/
            nodes, symbols,
        ) {
            // We should only get the declaration of an alias if there isn't a local value
            // declaration for the symbol
            let is_non_local = {
                let arena = symbols.clone();
                is_non_local_alias(
                    Some(&arena[symbol.index()]),
                    SymbolFlags::VALUE, /*excludes*/
                )
            };
            if is_non_local
                && !self.is_type_only_alias_declaration(Some(symbol), nodes, symbols)
            {
                return self.get_declaration_of_alias_symbol(symbol, nodes, symbols);
            }
        }
        None
    }

    /// `func (r *referenceResolver) GetReferencedValueDeclaration`.
    fn get_referenced_value_declaration(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> Option<NodeId> {
        if let Some(symbol) = self.get_referenced_value_symbol(
            node, false, /*startInDeclarationContainer*/
            nodes, symbols,
        ) {
            return self
                .get_export_symbol_of_value_symbol_if_exported(Some(symbol), symbols)
                .and_then(|s| symbols.get_ref(s).value_declaration);
        }
        None
    }

    /// `func (r *referenceResolver) GetReferencedValueDeclarations`.
    fn get_referenced_value_declarations(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> Vec<NodeId> {
        let mut declarations = Vec::new();
        if let Some(symbol) = self.get_referenced_value_symbol(
            node, false, /*startInDeclarationContainer*/
            nodes, symbols,
        ) {
            let Some(symbol) =
                self.get_export_symbol_of_value_symbol_if_exported(Some(symbol), symbols)
            else {
                return declarations;
            };
            let symbol_declarations = symbols.get_ref(symbol).declarations.clone();
            for &declaration in &symbol_declarations {
                match self.node_kind(declaration, nodes) {
                    Some(
                        Kind::VariableDeclaration
                        | Kind::Parameter
                        | Kind::BindingElement
                        | Kind::PropertyDeclaration
                        | Kind::PropertyAssignment
                        | Kind::ShorthandPropertyAssignment
                        | Kind::EnumMember
                        | Kind::ObjectLiteralExpression
                        | Kind::FunctionDeclaration
                        | Kind::FunctionExpression
                        | Kind::ArrowFunction
                        | Kind::ClassDeclaration
                        | Kind::ClassExpression
                        | Kind::EnumDeclaration
                        | Kind::MethodDeclaration
                        | Kind::GetAccessor
                        | Kind::SetAccessor
                        | Kind::ModuleDeclaration,
                    ) => {
                        declarations.push(declaration);
                    }
                    _ => {}
                }
            }
        }
        declarations
    }

    /// `func (r *referenceResolver) GetElementAccessExpressionName`.
    fn get_element_access_expression_name(&mut self, expression: Option<NodeId>) -> String {
        if let Some(expression) = expression {
            if let Some(hook) = self.hooks.get_element_access_expression_name.as_mut() {
                if let Some(name) = hook(expression) {
                    return name;
                }
            }
        }
        String::new()
    }

    /// `func (r *referenceResolver) GetReferencedMemberValueDeclaration`.
    fn get_referenced_member_value_declaration(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &SymbolArena,
    ) -> Option<NodeId> {
        // member references are `this.something` or `this[something]`, so should always simply have a resolved symbol
        let mut s = self.get_resolved_symbol(Some(node));
        if s.is_none() && nodes[node].symbol().is_some() {
            // might be a declaration instead of a ref, get the merged declaration symbol
            s = self.get_merged_symbol(nodes[node].symbol());
        }
        s?;
        self.get_export_symbol_of_value_symbol_if_exported(s, symbols)
            .and_then(|sym| symbols.get_ref(sym).value_declaration)
    }

    /// `resolve_node` — `nodes` is checked first (the caller's working
    /// arena), then the `resolve_node` hook resolves program-arena ids.
    fn resolve_node(&mut self, id: NodeId, nodes: &[Node]) -> Option<Node> {
        self.resolved_node(id, nodes)
    }
}
