// Ported from tsc/internal/ls/findallreferences.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(idents): Go refers to AST nodes and symbols by pointer; the Rust port
// uses `NodeId`/`SymbolId` into per-file arenas (`program.nodes(file_index)`)
// and the shared symbol arena (`checker.symbol_arena`).
//
// PORT(mutation): `ReferenceEntry`/`SymbolAndEntries` are lazily resolved and
// shared between search state and callers — `Rc<RefCell<..>>` reproduces Go's
// shared mutable pointers.
//
// PORT(crossproject): `crossproject.go`'s orchestrator/work-group is ported
// here because `crossproject.rs` is sibling-owned. Go's parallel `WorkGroup`
// requires `Send + 'static` work items in Rust; `LanguageService`/`Checker`
// are `Rc<RefCell>`-based and `!Send`, so work items are processed
// sequentially in queue order — deterministic and otherwise faithful (Go's
// item ordering and dedupe are preserved).
//
// PORT(hover): `getQuickInfoAndDeclarationAtLocation` lives in the
// sibling-owned `hover.rs` (private). The VS-references display path calls
// the local `quick_info_display_parts` shim, which delegates to
// `crate::hover`'s implementation when visible, else falls back to an
// unclassified run (see `get_definition_kind_and_display_parts`).

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::rc::Rc;

use tsc_ast::ast::FileReference;
use tsc_ast::checkflags::CheckFlags;
use tsc_ast::{self as ast, Kind, ModifierFlags, Node, NodeId, SymbolFlags, SymbolId};
use tsc_astnav::tokens;
use tsc_checker::checker_core::Checker;
use tsc_collections::Set;
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::text::{TextPos, TextRange};
use tsc_lsconv::converters::Script;
use tsc_lsproto::{self as lsproto};
use tsc_spanmap::Feature;
use tsc_tspath::{PathKey, RootedFilePath};

use crate::api::Error;
use crate::import_tracker::{
    ExportInfo, ExportKind, ImpExpKind, ImportTracker, create_import_tracker,
    find_module_references, get_export_info, get_import_or_export_symbol, ModuleReferenceKind,
};
use crate::languageservice::LanguageService;
use crate::utilities::*;

/// `type refInfo struct`.
pub(crate) struct RefInfo {
    /// `file`.
    pub(crate) file: Option<NodeId>,
    /// `fileName`.
    pub(crate) file_name: RootedFilePath,
    /// `reference`.
    pub(crate) reference: Option<FileReference>,
    /// `unverified`.
    pub(crate) unverified: bool,
}

// === types for settings ===

/// `type referenceUse int`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub(crate) enum ReferenceUse {
    /// `referenceUseNone`.
    #[default]
    None,
    /// `referenceUseOther`.
    Other,
    /// `referenceUseReferences`.
    References,
    /// `referenceUseRename`.
    Rename,
}

/// `type refOptions struct`.
#[derive(Clone, Copy, Default)]
pub(crate) struct RefOptions {
    /// `findInStrings`.
    pub(crate) find_in_strings: bool,
    /// `findInComments`.
    pub(crate) find_in_comments: bool,
    /// `use`.
    pub(crate) use_: ReferenceUse,
    /// `implementations`.
    pub(crate) implementations: bool,
    /// `useAliasesForRename`.
    pub(crate) use_aliases_for_rename: bool,
}

// === types for results ===

/// `type SymbolAndEntries struct`.
pub(crate) struct SymbolAndEntries {
    /// `definition`.
    pub(crate) definition: Option<Definition>,
    /// `references`.
    pub(crate) references: Vec<Rc<RefCell<ReferenceEntry>>>,
}

/// `NewSymbolAndEntries`.
fn new_symbol_and_entries(
    kind: DefinitionKind,
    node: Option<NodeId>,
    symbol: Option<SymbolId>,
    references: Vec<Rc<RefCell<ReferenceEntry>>>,
) -> SymbolAndEntries {
    SymbolAndEntries {
        definition: Some(Definition {
            kind,
            node,
            symbol,
            triple_slash_file_ref: None,
        }),
        references,
    }
}

/// `type DefinitionKind int`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum DefinitionKind {
    /// `definitionKindSymbol`.
    Symbol,
    /// `definitionKindLabel`.
    Label,
    /// `definitionKindKeyword`.
    Keyword,
    /// `definitionKindThis`.
    This,
    /// `definitionKindString`.
    String,
    /// `definitionKindTripleSlashReference`.
    TripleSlashReference,
}

/// `type Definition struct`.
pub(crate) struct Definition {
    /// `Kind`.
    pub(crate) kind: DefinitionKind,
    /// `symbol`.
    pub(crate) symbol: Option<SymbolId>,
    /// `node`.
    pub(crate) node: Option<NodeId>,
    /// `tripleSlashFileRef`.
    pub(crate) triple_slash_file_ref: Option<TripleSlashDefinition>,
}

/// `type tripleSlashDefinition struct`.
pub(crate) struct TripleSlashDefinition {
    /// `reference`.
    pub(crate) reference: FileReference,
    /// `file`.
    pub(crate) file: Option<NodeId>,
}

/// `type entryKind int`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub(crate) enum EntryKind {
    /// `entryKindNone`.
    #[default]
    None,
    /// `entryKindRange`.
    Range,
    /// `entryKindNode`.
    Node,
    /// `entryKindStringLiteral`.
    StringLiteral,
    /// `entryKindSearchedLocalFoundProperty`.
    SearchedLocalFoundProperty,
    /// `entryKindSearchedPropertyFoundLocal`.
    SearchedPropertyFoundLocal,
}

/// `type ReferenceEntry struct`.
pub(crate) struct ReferenceEntry {
    /// `kind`.
    pub(crate) kind: EntryKind,
    /// `node`.
    pub(crate) node: Option<NodeId>,
    /// `context` — `!!! ContextWithStartAndEndNode`, optional.
    pub(crate) context: Option<NodeId>,
    /// `sourceFile` — SourceFile `NodeId`.
    pub(crate) source_file: Option<NodeId>,
    /// `textRange`.
    pub(crate) text_range: Option<TextRange>,
    /// `lspRange`.
    pub(crate) lsp_range: Option<lsproto::Location>,
    /// `unmappable`.
    pub(crate) unmappable: bool,
}

impl ReferenceEntry {
    /// `Node`.
    pub(crate) fn node(&self) -> Option<NodeId> {
        self.node
    }

    /// `IsNodeEntry`.
    pub(crate) fn is_node_entry(&self) -> bool {
        self.node.is_some()
    }
}

impl SymbolAndEntries {
    /// `References` — callers should use the `references` field directly.
    /// `DefinitionNode`.
    pub(crate) fn definition_node(&self, checker: &RefCell<Checker>) -> Option<NodeId> {
        self.definition.as_ref()?;
        let definition = self.definition.as_ref().expect("definition");
        if let Some(node) = definition.node {
            return Some(node);
        }
        if let Some(symbol) = definition.symbol {
            return checker
                .borrow()
                .symbol_arena
                .borrow()[symbol.index()]
            .declarations
            .first()
            .copied();
        }
        None
    }

    /// `DefinitionSymbol`.
    pub(crate) fn definition_symbol(&self) -> Option<SymbolId> {
        self.definition.as_ref().and_then(|d| d.symbol)
    }

    /// `canUseDefinitionSymbol`.
    pub(crate) fn can_use_definition_symbol(&self) -> bool {
        let Some(definition) = &self.definition else {
            return false;
        };
        match definition.kind {
            DefinitionKind::Symbol | DefinitionKind::This => definition.symbol.is_some(),
            DefinitionKind::TripleSlashReference => {
                // !!! TODO : need to find file reference instead?
                // May need to return true to indicate this to be file search instead and might need to do for import stuff as well
                // For now
                false
            }
            _ => false,
        }
    }
}

impl<'h> LanguageService<'h> {
    /// `getRangeOfEntry`.
    pub(crate) fn get_range_of_entry(
        &self,
        entry: &Rc<RefCell<ReferenceEntry>>,
    ) -> lsproto::Range {
        self.resolve_entry(entry);
        entry.borrow().lsp_range.clone().expect("lsp range").range
    }

    /// `getRangeOfEntryForFeature`.
    pub(crate) fn get_range_of_entry_for_feature(
        &self,
        entry: &Rc<RefCell<ReferenceEntry>>,
        feature: Feature,
    ) -> (lsproto::Range, bool) {
        let (location, ok) = self.get_location_of_entry_for_feature(entry, feature);
        (location.range, ok)
    }

    /// `getFileNameOfEntry`.
    pub(crate) fn get_file_name_of_entry(
        &self,
        entry: &Rc<RefCell<ReferenceEntry>>,
    ) -> lsproto::DocumentUri {
        self.resolve_entry(entry);
        entry.borrow().lsp_range.clone().expect("lsp range").uri
    }

    /// `getLocationOfEntryForFeature`.
    pub(crate) fn get_location_of_entry_for_feature(
        &self,
        entry: &Rc<RefCell<ReferenceEntry>>,
        feature: Feature,
    ) -> (lsproto::Location, bool) {
        self.resolve_entry_source(entry);
        let (source_file, text_range) = {
            let e = entry.borrow();
            (e.source_file.expect("source file"), e.text_range.expect("text range"))
        };
        let (location, fidelity) =
            self.source_file_range_to_lsp_location_for_feature(source_file, text_range, feature);
        (location, fidelity.is_single_segment())
    }

    /// `resolveEntrySource`.
    pub(crate) fn resolve_entry_source(&self, entry: &Rc<RefCell<ReferenceEntry>>) {
        let mut e = entry.borrow_mut();
        if e.source_file.is_none() {
            let node = e.node.expect("reference entry must have a node or source file");
            let nodes = self.program.nodes(node.file_index());
            e.source_file = ast::get_source_file_of_node(Some(node), &nodes);
        }
        if e.text_range.is_none() {
            let node = e.node.expect("node");
            let source_file = e.source_file.expect("source file");
            let nodes = self.program.nodes(source_file.file_index());
            e.text_range = Some(get_range_of_node(node, Some(source_file), None, &nodes));
        }
    }

    /// `resolveEntry`.
    pub(crate) fn resolve_entry(
        &self,
        entry: &Rc<RefCell<ReferenceEntry>>,
    ) -> Rc<RefCell<ReferenceEntry>> {
        self.resolve_entry_source(entry);
        if entry.borrow().lsp_range.is_none() {
            let (source_file, text_range) = {
                let e = entry.borrow();
                (
                    e.source_file.expect("source file"),
                    e.text_range.expect("text range"),
                )
            };
            let (location, fidelity) =
                self.source_file_range_to_lsp_location(source_file, text_range);
            let mut e = entry.borrow_mut();
            e.lsp_range = Some(location);
            e.unmappable = !fidelity.is_single_segment();
        }
        entry.clone()
    }
}

/// `newNodeEntryWithKind`.
fn new_node_entry_with_kind(
    node: NodeId,
    kind: EntryKind,
    nodes: &[Node],
) -> Rc<RefCell<ReferenceEntry>> {
    let e = new_node_entry(node, nodes);
    e.borrow_mut().kind = kind;
    e
}

/// `newNodeEntry` — creates nodeEntry with `kind == entryKindNode`.
fn new_node_entry(node: NodeId, nodes: &[Node]) -> Rc<RefCell<ReferenceEntry>> {
    Rc::new(RefCell::new(ReferenceEntry {
        kind: EntryKind::Node,
        node: Some(nodes[node].name().unwrap_or(node)),
        context: get_context_node_for_node_entry(node, nodes),
        source_file: None,
        text_range: None,
        lsp_range: None,
        unmappable: false,
    }))
}

/// `newRangeEntry` — `&ReferenceEntry{kind: entryKindRange, ...}`.
fn new_range_entry(
    source_file: NodeId,
    text_range: TextRange,
) -> Rc<RefCell<ReferenceEntry>> {
    Rc::new(RefCell::new(ReferenceEntry {
        kind: EntryKind::Range,
        node: None,
        context: None,
        source_file: Some(source_file),
        text_range: Some(text_range),
        lsp_range: None,
        unmappable: false,
    }))
}

/// `getContextNodeForNodeEntry`.
fn get_context_node_for_node_entry(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    if ast::is_declaration(&nodes[node]) {
        return get_context_node(node, nodes);
    }

    let Some(parent) = nodes[node].parent else {
        return None;
    };

    if !ast::is_declaration(&nodes[parent]) && !ast::is_export_assignment(&nodes[parent]) {
        // Special property assignment in javascript
        if ast::is_in_js_file(Some(node), nodes) {
            // !!! jsdoc: check if branch still needed
            let mut binary_expression: Option<NodeId> = None;
            if ast::is_binary_expression(&nodes[parent]) {
                binary_expression = Some(parent);
            } else if ast::is_access_expression(&nodes[parent])
                && nodes[parent].parent.is_some_and(|gp| {
                    ast::is_binary_expression(&nodes[gp])
                        && nodes[gp].as_binary_expression().left == Some(parent)
                })
            {
                binary_expression = nodes[parent].parent;
            }
            if binary_expression.is_some_and(|b| {
                ast::get_assignment_declaration_kind(b, nodes) != ast::JsDeclarationKind::None
            }) {
                return get_context_node(binary_expression.unwrap(), nodes);
            }
        }

        // Jsx Tags
        match nodes[parent].kind {
            Kind::JsxOpeningElement | Kind::JsxClosingElement => return nodes[parent].parent,
            Kind::JsxSelfClosingElement
            | Kind::LabeledStatement
            | Kind::BreakStatement
            | Kind::ContinueStatement => return Some(parent),
            Kind::StringLiteral | Kind::NoSubstitutionTemplateLiteral => {
                if let Some(valid_import) = ast::try_get_import_from_module_specifier(node, nodes)
                {
                    let decl_or_statement = ast::find_ancestor(
                        Some(valid_import),
                        nodes,
                        &mut |n, ns| {
                            ast::is_declaration(n) || ast::is_statement(n, ns) || ast::is_js_doc_tag(n)
                        },
                    );
                    if decl_or_statement.is_some_and(|d| ast::is_declaration(&nodes[d])) {
                        return get_context_node(decl_or_statement.unwrap(), nodes);
                    }
                    return decl_or_statement;
                }
            }
            _ => {}
        }

        // Handle computed property name
        let property_name = ast::find_ancestor_kind(Some(node), Kind::ComputedPropertyName, nodes);
        if let Some(property_name) = property_name {
            return get_context_node(nodes[property_name].parent.unwrap_or(property_name), nodes);
        }
        return None;
    }

    if nodes[parent].name() == Some(node) // node is name of declaration, use parent
        || nodes[parent].kind == Kind::Constructor
        || nodes[parent].kind == Kind::ExportAssignment
        // Property name of the import export specifier or binding pattern, use parent
        || ((ast::is_import_or_export_specifier(&nodes[parent])
            || nodes[parent].kind == Kind::BindingElement)
            && nodes[parent].property_name() == Some(node))
        // Is default export
        || (nodes[node].kind == Kind::DefaultKeyword
            && ast::has_syntactic_modifier(&nodes[parent], ModifierFlags::EXPORT_DEFAULT))
    {
        return get_context_node(parent, nodes);
    }

    None
}

/// `getContextNode`.
pub(crate) fn get_context_node(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    match nodes[node].kind {
        Kind::VariableDeclaration => {
            let parent = nodes[node].parent?;
            if !ast::is_variable_declaration_list(&nodes[parent])
                || nodes[parent]
                    .as_variable_declaration_list()
                    .declarations
                    .as_ref()
                    .expect("declarations")
                    .nodes
                    .len()
                    != 1
            {
                Some(node)
            } else if nodes[parent]
                .parent
                .is_some_and(|gp| ast::is_variable_statement(&nodes[gp]))
            {
                nodes[parent].parent
            } else if nodes[parent]
                .parent
                .is_some_and(|gp| ast::is_for_in_or_of_statement(Some(gp), &nodes))
            {
                get_context_node(nodes[parent].parent.unwrap(), nodes)
            } else {
                Some(parent)
            }
        }
        Kind::BindingElement => nodes[node].parent.and_then(|p| nodes[p].parent),
        Kind::ImportSpecifier => nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .and_then(|p| nodes[p].parent),
        Kind::ExportSpecifier | Kind::NamespaceImport => {
            nodes[node].parent.and_then(|p| nodes[p].parent)
        }
        Kind::ImportClause | Kind::NamespaceExport => nodes[node].parent,
        Kind::BinaryExpression => {
            if nodes[node].parent.is_some_and(|p| nodes[p].kind == Kind::ExpressionStatement) {
                nodes[node].parent
            } else {
                Some(node)
            }
        }
        Kind::ForOfStatement | Kind::ForInStatement => {
            // !!! not implemented
            None
        }
        Kind::PropertyAssignment | Kind::ShorthandPropertyAssignment => {
            if nodes[node]
                .parent
                .is_some_and(|p| is_array_literal_or_object_literal_destructuring_pattern(p, nodes))
            {
                return get_context_node(
                    ast::find_ancestor(nodes[node].parent, nodes, &mut |n, ns| {
                        n.kind == Kind::BinaryExpression
                            || ast::is_for_in_or_of_statement(Some(n.id), ns)
                    })
                    .unwrap_or(node),
                    nodes,
                );
            }
            Some(node)
        }
        Kind::SwitchStatement => {
            // !!! not implemented
            None
        }
        _ => Some(node),
    }
}

/// `getRangeOfNode`.
pub(crate) fn get_range_of_node(
    node: NodeId,
    source_file: Option<NodeId>,
    end_node: Option<NodeId>,
    nodes: &[Node],
) -> TextRange {
    let source_file = match source_file {
        Some(source_file) => source_file,
        None => {
            ast::get_source_file_of_node(Some(node), nodes).expect("source file of node")
        }
    };
    let mut start = tsc_scanner::scanner::get_token_pos_of_node(
        node,
        nodes[source_file].as_source_file(),
        false, /*includeJSDoc*/
        nodes,
    );
    let mut end = nodes[end_node.unwrap_or(node)].end();
    if ast::is_string_literal_like(&nodes[node]) && (end - start) > 2 {
        debug_assert!(
            end_node.is_none(),
            "endNode is not nil for stringLiteralLike"
        );
        start += 1;
        end -= 1;
    }
    if end_node.is_some_and(|end_node| nodes[end_node].kind == Kind::CaseBlock) {
        end = nodes[end_node.unwrap()].pos();
    }
    TextRange::new(start, end)
}

/// `isValidReferencePosition`.
fn is_valid_reference_position(node: NodeId, search_symbol_name: &str, nodes: &[Node]) -> bool {
    match nodes[node].kind {
        Kind::PrivateIdentifier => {
            // !!!
            // if (isJSDocMemberName(node.Parent)) {
            // 	return true;
            // }
            nodes[node].text(nodes).len() == search_symbol_name.len()
        }
        Kind::Identifier => nodes[node].text(nodes).len() == search_symbol_name.len(),
        Kind::NoSubstitutionTemplateLiteral | Kind::StringLiteral => {
            nodes[node].text(nodes).len() == search_symbol_name.len()
                && (is_literal_name_of_property_declaration_or_index_access(node, nodes)
                    || is_name_of_module_declaration(node, nodes)
                    || is_expression_of_external_module_import_equals_declaration(node, nodes)
                    || (nodes[node].parent.is_some_and(|p| {
                        ast::is_call_expression(&nodes[p])
                            && ast::is_bindable_object_define_property_call(p, nodes)
                            && nodes[p].arguments().is_some_and(|a| a.get(1) == Some(&node))
                    }))
                    || nodes[node]
                        .parent
                        .is_some_and(|p| ast::is_import_or_export_specifier(&nodes[p])))
        }
        Kind::NumericLiteral => {
            is_literal_name_of_property_declaration_or_index_access(node, nodes)
                && nodes[node].text(nodes).len() == search_symbol_name.len()
        }
        Kind::DefaultKeyword => "default".len() == search_symbol_name.len(),
        _ => false,
    }
}

/// `isForRenameWithPrefixAndSuffixText`.
fn is_for_rename_with_prefix_and_suffix_text(options: &RefOptions) -> bool {
    options.use_ == ReferenceUse::Rename && options.use_aliases_for_rename
}

/// `skipPastExportOrImportSpecifierOrUnion`.
fn skip_past_export_or_import_specifier_or_union(
    symbol: SymbolId,
    node: Option<NodeId>,
    checker: &Rc<RefCell<Checker>>,
    use_local_symbol_for_export_specifier: bool,
    program: &Rc<Program>,
) -> Option<SymbolId> {
    let node = node?;
    let parent = {
        let nodes = program.nodes(node.file_index());
        nodes[node].parent?
    };
    {
        let nodes = program.nodes(node.file_index());
        if nodes[parent].kind == Kind::ExportSpecifier && use_local_symbol_for_export_specifier {
            let mut c = checker.borrow_mut();
            return get_local_symbol_for_export_specifier(
                &nodes,
                node,
                Some(symbol),
                parent,
                &mut c,
            );
        }
    }
    // If the symbol is declared as part of a declaration like `{ type: "a" } | { type: "b" }`, use the property on the union type to get more references.
    let declarations = checker.borrow().symbol_arena.borrow()[symbol.index()]
        .declarations
        .clone();
    let symbol_flags = checker.borrow().symbol_arena.borrow()[symbol.index()].flags;
    let symbol_name = checker.borrow().symbol_arena.borrow()[symbol.index()]
        .name
        .clone();
    declarations.iter().copied().find_map(|decl| {
        let nodes = program.nodes(decl.file_index());
        let Some(decl_parent) = nodes[decl].parent else {
            // Ignore UMD module and global merge and CJS module end exports symbols
            if symbol_flags & (SymbolFlags::TRANSIENT | SymbolFlags::MODULE_EXPORTS)
                != SymbolFlags::NONE
            {
                return None;
            }
            // Assertions for GH#21814. We should be handling SourceFile symbols in `getReferencedSymbolsForModule` instead of getting here.
            panic!(
                "Unexpected symbol at {:?}: {}",
                nodes[node].kind, symbol_name
            );
        };
        if nodes[decl_parent].kind == Kind::TypeLiteral
            && nodes[decl_parent]
                .parent
                .is_some_and(|gp| nodes[gp].kind == Kind::UnionType)
        {
            let union_type_node = nodes[decl_parent].parent.expect("union parent");
            drop(nodes);
            let mut c = checker.borrow_mut();
            let t = c.get_type_from_type_node(union_type_node);
            c.get_property_of_type(t, &symbol_name)
        } else {
            None
        }
    })
}

/// `getSymbolScope`.
fn get_symbol_scope(symbol: SymbolId, checker: &RefCell<Checker>, program: &Rc<Program>) -> Option<NodeId> {
    // If this is the symbol of a named function expression or named class expression,
    // then named references are limited to its own scope.
    let (value_declaration, declarations, flags, parent) = {
        let arena = checker.borrow().symbol_arena.clone();
        let s = &arena.borrow()[symbol.index()];
        (s.value_declaration, s.declarations.clone(), s.flags, s.parent)
    };
    if let Some(value_declaration) = value_declaration {
        let kind = {
            let nodes = program.nodes(value_declaration.file_index());
            nodes[value_declaration].kind
        };
        if kind == Kind::FunctionExpression || kind == Kind::ClassExpression {
            return Some(value_declaration);
        }
    }

    if declarations.is_empty() {
        return None;
    }

    // If this is private property or method, the scope is the containing class
    if flags & (SymbolFlags::PROPERTY | SymbolFlags::METHOD) != SymbolFlags::NONE {
        let private_declaration = declarations.iter().copied().find(|&d| {
            let nodes = program.nodes(d.file_index());
            ast::has_modifier(&nodes[d], ModifierFlags::PRIVATE)
                || ast::is_private_identifier_class_element_declaration(&nodes[d], &nodes)
        });
        if let Some(private_declaration) = private_declaration {
            let nodes = program.nodes(private_declaration.file_index());
            return ast::find_ancestor_kind(Some(private_declaration), Kind::ClassDeclaration, &nodes);
        }
        // Else this is a public property and could be accessed from anywhere.
        return None;
    }

    // If symbol is of object binding pattern element without property name we would want to
    // look for property too and that could be anywhere
    if declarations.iter().copied().any(|d| {
        let nodes = program.nodes(d.file_index());
        is_object_binding_element_without_property_name(d, &nodes)
    }) {
        return None;
    }

    /*
        If the symbol has a parent, it's globally visible unless:
        - It's a private property (handled above).
        - It's a type parameter.
        - The parent is an external module: then we should only search in the module (and recurse on the export later).
        - But if the parent has `export as namespace`, the symbol is globally visible through that namespace.
    */
    let exposed_by_parent =
        parent.is_some() && flags & SymbolFlags::TYPE_PARAMETER == SymbolFlags::NONE;
    if exposed_by_parent {
        let parent_is_scoped_external_module = {
            let parent = parent.expect("parent");
            let c = checker.borrow();
            if !tsc_checker::utilities::is_external_module_symbol(parent, &c) {
                false
            } else {
                let parent_vd = c.symbol_arena.borrow()[parent.index()].value_declaration;
                match parent_vd {
                    Some(vd) => {
                        let nodes = program.nodes(vd.file_index());
                        !is_source_file_with_global_exports(Some(vd), &nodes)
                    }
                    None => true,
                }
            }
        };
        if !parent_is_scoped_external_module {
            return None;
        }
    }

    let mut scope: Option<NodeId> = None;
    for declaration in &declarations {
        let container = {
            let nodes = program.nodes(declaration.file_index());
            get_container_node(*declaration, &nodes)
        };
        if scope.is_some() && scope != container {
            // Different declarations have different containers, bail out
            return None;
        }

        let container_is_global = match container {
            None => true,
            Some(c) => {
                let nodes = program.nodes(c.file_index());
                nodes[c].kind == Kind::SourceFile
                    && !ast::is_external_or_commonjs_module(nodes[c].as_source_file())
            }
        };
        if container_is_global {
            // This is a global variable and not an external module, any declaration defined
            // within this scope is visible outside the file
            return None;
        }

        scope = container;
    }

    // If symbol.parent, this means we are in an export of an external module. (Otherwise we would have returned `undefined` above.)
    // For an export of a module, we may be in a declaration file, and it may be accessed elsewhere. E.g.:
    //     declare module "a" { export type T = number; }
    //     declare module "b" { import { T } from "a"; export const x: T; }
    // So we must search the whole source file. (Because we will mark the source file as seen, we we won't return to it when searching for imports.)
    if exposed_by_parent {
        let scope = scope?;
        let nodes = program.nodes(scope.file_index());
        return ast::get_source_file_of_node(Some(scope), &nodes);
    }
    scope // TODO: GH#18217
}

// === functions on (*ls) ===

/// `type position struct` — implements `HasTextDocumentPosition`.
#[derive(Clone)]
pub(crate) struct UriPosition {
    /// `uri`.
    pub(crate) uri: lsproto::DocumentUri,
    /// `pos`.
    pub(crate) pos: lsproto::Position,
}

impl lsproto::HasTextDocumentUri for UriPosition {
    fn text_document_uri(&self) -> lsproto::DocumentUri {
        self.uri.clone()
    }
}

impl lsproto::HasTextDocumentPosition for UriPosition {
    fn text_document_position(&self) -> lsproto::Position {
        self.pos
    }
}

/// `type nonLocalDefinition struct`. The `'a` lifetime ties the
/// `OnceCell`-style closures to the `&'a LanguageService` they capture (Go's
/// closures capture the `*ls` receiver directly).
pub(crate) struct NonLocalDefinition<'a> {
    /// `position`.
    pub(crate) position: UriPosition,
    /// `GetSourcePosition` — `sync.OnceValue` becomes a `RefCell` cache.
    pub(crate) get_source_position:
        Box<dyn Fn() -> Option<Rc<dyn lsproto::HasTextDocumentPosition>> + 'a>,
    /// `GetGeneratedPosition`.
    pub(crate) get_generated_position:
        Box<dyn Fn() -> Option<Rc<dyn lsproto::HasTextDocumentPosition>> + 'a>,
}

/// `getFileAndStartPosFromDeclaration`.
pub(crate) fn get_file_and_start_pos_from_declaration(
    declaration: NodeId,
    nodes: &[Node],
) -> (NodeId, TextPos) {
    let file =
        ast::get_source_file_of_node(Some(declaration), nodes).expect("source file of node");
    let name = ast::get_name_of_declaration(Some(declaration), nodes).unwrap_or(declaration);
    let text_range = get_range_of_node(name, Some(file), None, nodes);

    (file, text_range.pos())
}

/// `plainTextScript` — local copy of source_map.rs's private `PlainScript`
/// (`getScript`). Used for source-map target files that may not be in the
/// program.
struct PlainTextScript {
    file_name: RootedFilePath,
    text: String,
}

impl Script for PlainTextScript {
    fn file_name(&self) -> &RootedFilePath {
        &self.file_name
    }
    fn original_file_name(&self) -> &RootedFilePath {
        &self.file_name
    }
    fn text(&self) -> &[u8] {
        self.text.as_bytes()
    }
    fn original_text(&self) -> &[u8] {
        self.text.as_bytes()
    }
    fn span_map(&self) -> Option<std::sync::Arc<tsc_spanmap::SpanMap>> {
        None
    }
}

impl<'h> LanguageService<'h> {
    /// `getScript` — local copy (source_map.rs's `get_script` is module-private).
    fn plain_text_script(&self, file_name: &RootedFilePath) -> PlainTextScript {
        PlainTextScript {
            file_name: file_name.clone(),
            text: self.read_file(file_name).expect("file should be readable"),
        }
    }

    /// `getNonLocalDefinition`.
    pub(crate) fn get_non_local_definition<'a>(
        &'a self,
        ctx: &Context,
        entry: &SymbolAndEntries,
    ) -> Option<NonLocalDefinition<'a>> {
        if !entry.can_use_definition_symbol() {
            return None;
        }

        let program = self.get_program();
        let (checker, done) = program.get_type_checker(ctx.clone());
        let Some(symbol) = entry.definition.as_ref().expect("definition").symbol else {
            drop(checker);
            done();
            return None;
        };
        let declarations = checker.borrow().symbol_arena.borrow()[symbol.index()]
            .declarations
            .clone();
        drop(checker);
        done();
        for d in declarations {
            // !!! not implemented: `EmitResolver::is_declaration_visible` is
            // `pub(crate)` inside `tsc_checker` and not reachable from this
            // crate, so `is_definition_visible` currently always fails and
            // no non-local definition is ever produced (cross-project
            // expansion is skipped).
            if !is_definition_visible(d, &program) {
                continue;
            }
            let (file, start_pos) = {
                let nodes = program.nodes(d.file_index());
                get_file_and_start_pos_from_declaration(d, &nodes)
            };
            let file_name = {
                let nodes = program.nodes(file.file_index());
                nodes[file].as_source_file().file_name().clone()
            };
            let nodes = program.nodes(file.file_index());
            let script = tsc_lsconv::converters::source_file_script(file, &nodes);
            let (lsp_position, fidelity) = self.converters.to_lsp_position(&script, start_pos);
            if fidelity.is_none() {
                continue;
            }
            let source_pos_def =
                Rc::new(RefCell::new(None::<Option<Rc<dyn lsproto::HasTextDocumentPosition>>>));
            let gen_pos_def =
                Rc::new(RefCell::new(None::<Option<Rc<dyn lsproto::HasTextDocumentPosition>>>));
            let nld = NonLocalDefinition {
                position: UriPosition {
                    uri: tsc_lsconv::converters::file_name_to_document_uri(&file_name),
                    pos: lsp_position,
                },
                get_source_position: {
                    let file_name = file_name.clone();
                    let source_pos_def = source_pos_def.clone();
                    Box::new(move || {
                        let mut cache = source_pos_def.borrow_mut();
                        if cache.is_none() {
                            *cache = Some(
                                self.source_position_as_text_document_position(
                                    &file_name,
                                    start_pos,
                                ),
                            );
                        }
                        cache.clone().expect("cached")
                    })
                },
                get_generated_position: {
                    Box::new(move || {
                        let mut cache = gen_pos_def.borrow_mut();
                        if cache.is_none() {
                            *cache = Some(
                                self.generated_position_as_text_document_position(
                                    &file_name,
                                    start_pos,
                                ),
                            );
                        }
                        cache.clone().expect("cached")
                    })
                },
            };
            return Some(nld);
        }
        None
    }

    /// One half of `nonLocalDefinition.GetSourcePosition` — map a .d.ts
    /// position to its source position and convert to LSP.
    fn source_position_as_text_document_position(
        &self,
        file_name: &RootedFilePath,
        pos: TextPos,
    ) -> Option<Rc<dyn lsproto::HasTextDocumentPosition>> {
        let mapped = self.try_get_source_position(file_name, pos)?;
        let script = self.plain_text_script(&mapped.file_name);
        let (mapped_position, mapped_fidelity) =
            self.converters.to_lsp_position(&script, mapped.pos);
        if mapped_fidelity.is_none() {
            return None;
        }
        Some(Rc::new(UriPosition {
            uri: tsc_lsconv::converters::file_name_to_document_uri(&mapped.file_name),
            pos: mapped_position,
        }))
    }

    /// `nonLocalDefinition.GetGeneratedPosition`.
    fn generated_position_as_text_document_position(
        &self,
        file_name: &RootedFilePath,
        pos: TextPos,
    ) -> Option<Rc<dyn lsproto::HasTextDocumentPosition>> {
        let mapped = self.try_get_generated_position(file_name, pos)?;
        let script = self.plain_text_script(&mapped.file_name);
        let (mapped_position, mapped_fidelity) =
            self.converters.to_lsp_position(&script, mapped.pos);
        if mapped_fidelity.is_none() {
            return None;
        }
        Some(Rc::new(UriPosition {
            uri: tsc_lsconv::converters::file_name_to_document_uri(&mapped.file_name),
            pos: mapped_position,
        }))
    }

    /// `forEachOriginalDefinitionLocation`.
    pub(crate) fn for_each_original_definition_location(
        &self,
        ctx: &Context,
        entry: &SymbolAndEntries,
        cb: &mut dyn FnMut(lsproto::DocumentUri, lsproto::Position),
    ) {
        if !entry.can_use_definition_symbol() {
            return;
        }

        let program = self.get_program();
        let symbol = entry
            .definition
            .as_ref()
            .and_then(|d| d.symbol)
            .expect("definition symbol");
        let declarations = {
            let (checker, done) = program.get_type_checker(ctx.clone());
            let declarations = checker.borrow().symbol_arena.borrow()[symbol.index()]
                .declarations
                .clone();
            drop(checker);
            done();
            declarations
        };
        for d in declarations {
            let (file, start_pos) = {
                let nodes = program.nodes(d.file_index());
                get_file_and_start_pos_from_declaration(d, &nodes)
            };
            let (file_name, is_declaration_file, path_key) = {
                let nodes = program.nodes(file.file_index());
                let file_name = nodes[file].as_source_file().file_name().clone();
                let is_decl = file_name.is_declaration_file();
                (
                    file_name,
                    is_decl,
                    nodes[file].as_source_file().path_key().clone(),
                )
            };
            if is_declaration_file {
                // Map to ts position
                if let Some(mapped) = self.try_get_source_position(&file_name, start_pos) {
                    let script = self.plain_text_script(&mapped.file_name);
                    let (lsp_position, fidelity) =
                        self.converters.to_lsp_position(&script, mapped.pos);
                    if !fidelity.is_none() {
                        cb(
                            tsc_lsconv::converters::file_name_to_document_uri(&mapped.file_name),
                            lsp_position,
                        );
                    }
                }
            } else if program.is_source_from_project_reference(&path_key) {
                let nodes = program.nodes(file.file_index());
                let script = tsc_lsconv::converters::source_file_script(file, &nodes);
                let (lsp_position, fidelity) =
                    self.converters.to_lsp_position(&script, start_pos);
                if !fidelity.is_none() {
                    cb(
                        tsc_lsconv::converters::file_name_to_document_uri(&file_name),
                        lsp_position,
                    );
                }
            }
        }
    }
}

/// `isDefinitionVisible` — special handling to determine if we should load up
/// more projects and find location in other projects.
///
/// !!! not implemented: Go calls
/// `l.Converters().GetEmitResolver(l.program).IsDeclarationVisible(decl)`;
/// `EmitResolver::is_declaration_visible` is `pub(crate)` inside `tsc_checker`
/// and not reachable from this crate. The resolver check therefore always
/// reports "not visible", so only the parent-recursion fallback can ever
/// succeed — which means `get_non_local_definition` currently produces no
/// non-local definitions (cross-project expansion is inert).
fn is_definition_visible(declaration: NodeId, program: &Rc<Program>) -> bool {
    // if (emitResolver.IsDeclarationVisible(decl)) return true; — see above.
    let _ = declaration;
    let nodes = program.nodes(declaration.file_index());
    let Some(parent) = nodes[declaration].parent else {
        return false;
    };

    // Variable initializers are visible if variable is visible
    if ast::has_initializer(&nodes[parent]) && nodes[parent].initializer() == Some(declaration) {
        drop(nodes);
        return is_definition_visible(parent, program);
    }

    // Handle some exceptions here like arrow function, members of class and object literal expression which are technically not visible but we want the definition to be determined by its parent
    match nodes[declaration].kind {
        Kind::PropertyDeclaration | Kind::GetAccessor | Kind::SetAccessor | Kind::MethodDeclaration => {
            // Private/protected properties/methods are not visible
            if ast::has_modifier(&nodes[declaration], ModifierFlags::PRIVATE)
                || nodes[declaration]
                    .name()
                    .is_some_and(|n| ast::is_private_identifier(&nodes[n]))
            {
                return false;
            }
            // Public properties/methods are visible if its parents are visible, so:
            // falls through
            drop(nodes);
            is_definition_visible(parent, program)
        }
        Kind::Constructor
        | Kind::PropertyAssignment
        | Kind::ShorthandPropertyAssignment
        | Kind::ObjectLiteralExpression
        | Kind::ClassExpression
        | Kind::ArrowFunction
        | Kind::FunctionExpression => {
            drop(nodes);
            is_definition_visible(parent, program)
        }
        _ => false,
    }
}

/// `type symbolEntryTransformOptions struct`.
#[derive(Clone, Copy, Default)]
pub(crate) struct SymbolEntryTransformOptions {
    /// Force the result to be Location objects.
    pub(crate) require_locations_result: bool,
    /// Omit node(s) containing the original position.
    pub(crate) drop_origin_nodes: bool,
}

/// `type SymbolAndEntriesData struct`.
#[derive(Default)]
pub(crate) struct SymbolAndEntriesData {
    /// `OriginalNode`.
    pub(crate) original_node: Option<NodeId>,
    /// `SymbolsAndEntries`.
    pub(crate) symbols_and_entries: Vec<Rc<RefCell<SymbolAndEntries>>>,
    /// `Position`.
    pub(crate) position: i32,
}

impl<'h> LanguageService<'h> {
    /// `provideSymbolsAndEntries` — `findReferencedSymbols` except only
    /// computes the information needed to return reference locations.
    pub(crate) fn provide_symbols_and_entries(
        &self,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
        document_position: lsproto::Position,
        is_rename: bool,
        implementations: bool,
    ) -> (SymbolAndEntriesData, bool) {
        let (program, source_file) = self.get_program_and_file(uri);
        let feature = if implementations {
            Feature::Implementation
        } else if is_rename {
            Feature::Rename
        } else {
            Feature::References
        };
        let nodes = program.nodes(source_file.file_index());
        let positions = self.converters.from_lsp_position_for_source_file(
            source_file,
            &nodes,
            document_position,
            feature,
        );
        if positions.is_empty() {
            return (SymbolAndEntriesData::default(), false);
        }
        let mut combined = SymbolAndEntriesData::default();
        let mut ok = false;
        for mapped in positions {
            if !mapped.fidelity.is_single_segment() {
                continue;
            }
            let (data, found) = self.provide_symbols_and_entries_at_position(
                ctx,
                &program,
                mapped.script.file,
                mapped.position,
                is_rename,
                implementations,
            );
            if !found {
                continue;
            }
            if !ok {
                combined.original_node = data.original_node;
                combined.position = data.position;
                ok = true;
            }
            combined
                .symbols_and_entries
                .extend(data.symbols_and_entries);
        }
        (combined, ok)
    }

    /// `provideSymbolsAndEntriesAtPosition`.
    pub(crate) fn provide_symbols_and_entries_at_position(
        &self,
        ctx: &Context,
        program: &Rc<Program>,
        source_file: NodeId,
        position: i32,
        is_rename: bool,
        implementations: bool,
    ) -> (SymbolAndEntriesData, bool) {
        let mut node = {
            let mut nodes = program.nodes_mut(source_file.file_index());
            tokens::get_touching_property_name(&mut nodes, source_file, position)
                .unwrap_or(source_file)
        };
        if is_rename {
            // Adjust modifier/keyword nodes to the declaration name, matching Strada's findRenameLocations.
            node = {
                let mut nodes = program.nodes_mut(source_file.file_index());
                get_adjusted_location(&mut nodes, node, true, Some(source_file)).unwrap_or(node)
            };
        }
        {
            let nodes = program.nodes(source_file.file_index());
            if (is_rename && !crate::rename::node_is_eligible_for_rename(node, &nodes))
                || (implementations && ast::is_source_file(&nodes[node]))
            {
                return (
                    SymbolAndEntriesData {
                        original_node: Some(node),
                        ..Default::default()
                    },
                    false,
                );
            }
        }

        let entries =
            self.get_symbol_and_entries(ctx, position, node, program, is_rename, implementations);
        if !implementations {
            return (
                SymbolAndEntriesData {
                    original_node: Some(node),
                    symbols_and_entries: entries,
                    position,
                },
                true,
            );
        }

        let mut implementation_entries: Vec<Rc<RefCell<SymbolAndEntries>>> = Vec::new();
        let mut queue: VecDeque<Rc<RefCell<ReferenceEntry>>> = VecDeque::new();
        let mut seen_nodes: Set<Option<NodeId>> = Set::new();
        let mut seen_definitions: Set<Option<SymbolId>> = Set::new();
        let mut add_to_queue =
            |symbol_and_entries: &[Rc<RefCell<SymbolAndEntries>>],
             queue: &mut VecDeque<Rc<RefCell<ReferenceEntry>>>| {
                for s in symbol_and_entries {
                    let s = s.borrow();
                    let mut new_references: Vec<Rc<RefCell<ReferenceEntry>>> = Vec::new();
                    for reference in &s.references {
                        if seen_nodes.add_if_absent(reference.borrow().node) {
                            queue.push_back(reference.clone());
                            new_references.push(reference.clone());
                        }
                    }
                    let def_symbol = s.definition.as_ref().and_then(|d| d.symbol);
                    if !new_references.is_empty()
                        || s.definition.is_none()
                        || seen_definitions.add_if_absent(def_symbol)
                    {
                        implementation_entries.push(Rc::new(RefCell::new(SymbolAndEntries {
                            definition: s.definition.as_ref().and_then(|d| d.clone_def()),
                            references: new_references,
                        })));
                    }
                }
            };

        add_to_queue(&entries, &mut queue);
        while let Some(entry) = queue.pop_front() {
            if ctx.is_cancelled() {
                return (SymbolAndEntriesData::default(), false);
            }
            let entry_node = entry.borrow().node;
            if let Some(entry_node) = entry_node {
                let pos = {
                    let nodes = program.nodes(entry_node.file_index());
                    nodes[entry_node].pos()
                };
                let new_entries = self.get_symbol_and_entries(
                    ctx,
                    pos,
                    entry_node,
                    program,
                    is_rename,
                    implementations,
                );
                add_to_queue(&new_entries, &mut queue);
            }
        }
        (
            SymbolAndEntriesData {
                original_node: Some(node),
                symbols_and_entries: implementation_entries,
                position,
            },
            true,
        )
    }

    /// `getSymbolAndEntries`.
    fn get_symbol_and_entries(
        &self,
        ctx: &Context,
        position: i32,
        node: NodeId,
        program: &Rc<Program>,
        is_rename: bool,
        implementations: bool,
    ) -> Vec<Rc<RefCell<SymbolAndEntries>>> {
        let mut options = RefOptions::default();
        if !is_rename {
            options.use_ = ReferenceUse::References;
            if implementations {
                options.implementations = true;
            }
        } else {
            options.use_ = ReferenceUse::Rename;
            options.use_aliases_for_rename = self
                .user_preferences()
                .provide_prefix_and_suffix_text_for_rename
                .is_true_or_unknown();
        }
        let source_files = program.source_files();
        self.get_referenced_symbols_for_node(ctx, position, node, program, &source_files, options)
    }

    /// `ProvideReferences`.
    pub fn provide_references(
        &self,
        ctx: &Context,
        params: &lsproto::ReferenceParams,
        orchestrator: Option<&dyn CrossProjectOrchestrator<'h>>,
    ) -> Result<lsproto::ReferencesResponse, Error> {
        self.handle_cross_project(
            ctx,
            &params.text_document_uri(),
            params.text_document_position(),
            orchestrator,
            |l, ctx, data, options| l.symbol_and_entries_to_references(ctx, params, data, options),
            &combine_references,
            false, /*isRename*/
            false, /*implementations*/
            SymbolEntryTransformOptions::default(),
            None, /*defaultProjectData*/
        )
    }

    /// `provideReferencesFromData`.
    pub(crate) fn provide_references_from_data(
        &self,
        ctx: &Context,
        params: &lsproto::ReferenceParams,
        orchestrator: Option<&dyn CrossProjectOrchestrator<'h>>,
        data: &SymbolAndEntriesData,
    ) -> Result<lsproto::ReferencesResponse, Error> {
        self.handle_cross_project(
            ctx,
            &params.text_document_uri(),
            params.text_document_position(),
            orchestrator,
            |l, ctx, data, options| l.symbol_and_entries_to_references(ctx, params, data, options),
            &combine_references,
            false, /*isRename*/
            false, /*implementations*/
            SymbolEntryTransformOptions::default(),
            Some(data),
        )
    }

    /// `ProvideVSReferences`.
    pub fn provide_vs_references(
        &self,
        ctx: &Context,
        params: &lsproto::ReferenceParams,
        orchestrator: Option<&dyn CrossProjectOrchestrator<'h>>,
    ) -> Result<lsproto::VSReferencesResponse, Error> {
        self.handle_cross_project(
            ctx,
            &params.text_document_uri(),
            params.text_document_position(),
            orchestrator,
            |l, ctx, data, options| {
                l.symbol_and_entries_to_vsreferences(ctx, params, data, options)
            },
            &combine_vsreferences,
            false, /*isRename*/
            false, /*implementations*/
            SymbolEntryTransformOptions::default(),
            None, /*defaultProjectData*/
        )
    }

    /// `symbolAndEntriesToReferences`.
    fn symbol_and_entries_to_references(
        &self,
        _ctx: &Context,
        params: &lsproto::ReferenceParams,
        data: SymbolAndEntriesData,
        _options: SymbolEntryTransformOptions,
    ) -> Result<lsproto::ReferencesResponse, Error> {
        // `findReferencedSymbols` except only computes the information needed to return reference locations
        let mut locations: Vec<lsproto::Location> = Vec::new();
        let mut seen_locations: Vec<lsproto::Location> = Vec::new();
        for symbol in &data.symbols_and_entries {
            let include_declaration = params
                .context
                .as_ref()
                .is_some_and(|c| c.include_declaration);
            let symbol_locations = self.convert_symbol_and_entries_to_locations(
                &symbol.borrow(),
                include_declaration,
                Feature::References,
            );
            locations = combine_location_array(
                std::mem::take(&mut locations),
                &symbol_locations,
                &mut seen_locations,
            );
        }
        Ok(lsproto::LocationsOrNull {
            locations: Some(locations),
        })
    }

    /// `symbolAndEntriesToVSReferences`.
    fn symbol_and_entries_to_vsreferences(
        &self,
        ctx: &Context,
        _params: &lsproto::ReferenceParams,
        data: SymbolAndEntriesData,
        _options: SymbolEntryTransformOptions,
    ) -> Result<lsproto::VSReferencesResponse, Error> {
        let caps = lsproto::get_client_capabilities(ctx);
        let vs_capability = caps.vs_supports_visual_studio_extensions;
        let mut items: Vec<lsproto::VSReferenceItem> = Vec::new();
        let mut id: i32 = 0;
        let project_name = self.project_id.to_string();

        for s in &data.symbols_and_entries {
            let s = s.borrow();
            let Some(definition) = &s.definition else {
                continue;
            };

            // Convert definition to info
            let Some(def_info) = self.definition_to_referenced_symbol_definition_info(
                ctx,
                definition,
                data.original_node,
                vs_capability,
                Feature::References,
            ) else {
                continue;
            };

            // Create the definition item
            let definition_id = id;
            items.push(lsproto::VSReferenceItem {
                vs_id: definition_id,
                vs_definition_id: None,
                vs_location: def_info.location,
                vs_definition_text: def_info.display_text,
                vs_kind: Some(vec![lsproto::VSReferenceKind::Unknown]),
                vs_project_name: Some(project_name.clone()),
                vs_containing_type: Some(String::new()),
            });
            id += 1;

            // Create reference items grouped under the definition
            for reference in &s.references {
                // Skip the declaration itself (already represented by the definition item)
                {
                    let r = reference.borrow();
                    if definition.symbol.is_some()
                        && is_declaration_of_symbol(
                            r.node,
                            definition.symbol,
                            &self.program,
                        )
                    {
                        continue;
                    }
                }

                let (ref_location, ok) =
                    self.get_location_of_entry_for_feature(reference, Feature::References);
                if !ok {
                    continue;
                }

                // Determine read/write kind
                let mut kind = lsproto::VSReferenceKind::Read;
                {
                    let r = reference.borrow();
                    if r.kind != EntryKind::Range {
                        if let Some(node) = r.node {
                            let nodes = self.program.nodes(node.file_index());
                            if is_write_access_for_reference(node, &nodes) {
                                kind = lsproto::VSReferenceKind::Write;
                            }
                        }
                    }
                }

                items.push(lsproto::VSReferenceItem {
                    vs_id: id,
                    vs_definition_id: Some(definition_id),
                    vs_location: ref_location,
                    vs_kind: Some(vec![kind]),
                    vs_project_name: Some(project_name.clone()),
                    ..Default::default()
                });
                id += 1;
            }
        }

        Ok(lsproto::VSReferenceItemsOrNull {
            vs_reference_items: Some(items),
        })
    }

    /// `ProvideImplementations`.
    pub fn provide_implementations(
        &self,
        ctx: &Context,
        params: &lsproto::ImplementationParams,
        orchestrator: Option<&dyn CrossProjectOrchestrator<'h>>,
    ) -> Result<lsproto::ImplementationResponse, Error> {
        self.provide_implementations_ex(
            ctx,
            params,
            SymbolEntryTransformOptions::default(),
            orchestrator,
        )
    }

    /// `provideImplementationsEx`.
    pub(crate) fn provide_implementations_ex(
        &self,
        ctx: &Context,
        params: &lsproto::ImplementationParams,
        options: SymbolEntryTransformOptions,
        orchestrator: Option<&dyn CrossProjectOrchestrator<'h>>,
    ) -> Result<lsproto::ImplementationResponse, Error> {
        self.handle_cross_project(
            ctx,
            &params.text_document_uri(),
            params.text_document_position(),
            orchestrator,
            |l, ctx, data, options| {
                l.symbol_and_entries_to_implementations(ctx, params, data, options)
            },
            &combine_implementations,
            false, /*isRename*/
            true,  /*implementations*/
            options,
            None, /*defaultProjectData*/
        )
    }

    /// `provideImplementationsFromData`.
    pub(crate) fn provide_implementations_from_data(
        &self,
        ctx: &Context,
        params: &lsproto::ImplementationParams,
        options: SymbolEntryTransformOptions,
        orchestrator: Option<&dyn CrossProjectOrchestrator<'h>>,
        data: &SymbolAndEntriesData,
    ) -> Result<lsproto::ImplementationResponse, Error> {
        self.handle_cross_project(
            ctx,
            &params.text_document_uri(),
            params.text_document_position(),
            orchestrator,
            |l, ctx, data, options| {
                l.symbol_and_entries_to_implementations(ctx, params, data, options)
            },
            &combine_implementations,
            false, /*isRename*/
            true,  /*implementations*/
            options,
            Some(data),
        )
    }

    /// `symbolAndEntriesToImplementations`.
    fn symbol_and_entries_to_implementations(
        &self,
        ctx: &Context,
        _params: &lsproto::ImplementationParams,
        data: SymbolAndEntriesData,
        options: SymbolEntryTransformOptions,
    ) -> Result<lsproto::ImplementationResponse, Error> {
        let mut seen_nodes: Set<Option<NodeId>> = Set::new();
        let mut entries: Vec<Rc<RefCell<ReferenceEntry>>> = Vec::new();
        for entry in &data.symbols_and_entries {
            for reference in &entry.borrow().references {
                let (node, keep) = {
                    let r = reference.borrow();
                    let node = r.node;
                    let keep = !options.drop_origin_nodes || node.map_or(true, |n| {
                        let nodes = self.program.nodes(n.file_index());
                        !nodes[n].loc.contains_inclusive(data.position)
                    });
                    (node, keep)
                };
                if seen_nodes.add_if_absent(node) && keep {
                    entries.push(reference.clone());
                }
            }
        }

        if !options.require_locations_result
            && lsproto::get_client_capabilities(ctx)
                .text_document
                .implementation
                .link_support
        {
            let links = self.convert_entries_to_location_links(&entries, Feature::Implementation);
            return Ok(lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
                definition_links: Some(links),
                ..Default::default()
            });
        }
        let locations = self.convert_entries_to_locations(&entries, Feature::Implementation);
        Ok(lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
            locations: Some(locations),
            ..Default::default()
        })
    }

    // == functions for conversions ==

    /// `convertSymbolAndEntriesToLocations`.
    pub(crate) fn convert_symbol_and_entries_to_locations(
        &self,
        s: &SymbolAndEntries,
        include_declarations: bool,
        feature: Feature,
    ) -> Vec<lsproto::Location> {
        let mut references: Vec<Rc<RefCell<ReferenceEntry>>> = s.references.clone();

        // !!! includeDeclarations
        if !include_declarations && s.definition.is_some() {
            let symbol = s.definition.as_ref().and_then(|d| d.symbol);
            references.retain(|entry| {
                !is_declaration_of_symbol(entry.borrow().node, symbol, &self.program)
            });
        }

        self.convert_entries_to_locations(&references, feature)
    }

    /// `convertEntriesToLocations`.
    pub(crate) fn convert_entries_to_locations(
        &self,
        entries: &[Rc<RefCell<ReferenceEntry>>],
        feature: Feature,
    ) -> Vec<lsproto::Location> {
        let mut locations = Vec::with_capacity(entries.len());
        for entry in entries {
            let (location, ok) = self.get_location_of_entry_for_feature(entry, feature);
            if ok {
                locations.push(location);
            }
        }
        locations
    }

    /// `convertEntriesToLocationLinks`.
    pub(crate) fn convert_entries_to_location_links(
        &self,
        entries: &[Rc<RefCell<ReferenceEntry>>],
        feature: Feature,
    ) -> Vec<lsproto::LocationLink> {
        let mut links = Vec::with_capacity(entries.len());
        for entry in entries {
            // Get the selection range (the actual reference)
            let (loc, ok) = self.get_location_of_entry_for_feature(entry, feature);
            if !ok {
                continue;
            }
            let target_selection_range = loc.range.clone();
            let mut target_range = target_selection_range.clone();

            // For entries with nodes, compute ranges directly from the node
            {
                let e = entry.borrow();
                if e.node.is_some() {
                    // Get the context range (broader scope including declaration context)
                    let source_file = e.source_file.expect("source file");
                    let text_range = e.text_range.expect("text range");
                    let context = e.context;
                    let nodes = self.program.nodes(source_file.file_index());
                    if let Some(context_text_range) =
                        to_context_range(text_range, source_file, context, &nodes)
                    {
                        drop(nodes);
                        let (context_location, fidelity) = self
                            .source_file_range_to_lsp_location_for_feature(
                                source_file,
                                context_text_range,
                                feature,
                            );
                        if !fidelity.is_none() && context_location.uri == loc.uri {
                            target_range = context_location.range;
                        }
                    }
                }
            }

            let original_file_name = {
                let e = entry.borrow();
                let source_file = e.source_file.expect("source file");
                let nodes = self.program.nodes(source_file.file_index());
                nodes[source_file]
                    .as_source_file()
                    .original_file_name(&nodes)
                    .clone()
            };
            links.push(lsproto::LocationLink {
                target_uri: tsc_lsconv::converters::file_name_to_document_uri(
                    &original_file_name,
                ),
                target_range,
                target_selection_range,
                ..Default::default()
            });
        }
        links
    }

    /// `mergeReferences`.
    pub(crate) fn merge_references(
        &self,
        program: &Rc<Program>,
        references_to_merge: &[Vec<Rc<RefCell<SymbolAndEntries>>>],
    ) -> Vec<Rc<RefCell<SymbolAndEntries>>> {
        let mut result: Vec<Rc<RefCell<SymbolAndEntries>>> = Vec::new();
        let source_file_index_of_entry = |entry: &Rc<RefCell<ReferenceEntry>>| -> i64 {
            self.resolve_entry_source(entry);
            let source_file = entry.borrow().source_file.expect("source file");
            program
                .source_files()
                .iter()
                .position(|f| *f == source_file)
                .map(|i| i as i64)
                .unwrap_or(-1)
        };

        for references in references_to_merge {
            if references.is_empty() {
                continue;
            }
            if result.is_empty() {
                result = references.clone();
                continue;
            }
            for entry in references {
                let (is_symbol_def, symbol) = {
                    let e = entry.borrow();
                    (
                        e.definition
                            .as_ref()
                            .is_some_and(|d| d.kind == DefinitionKind::Symbol),
                        e.definition.as_ref().and_then(|d| d.symbol),
                    )
                };
                if !is_symbol_def {
                    result.push(entry.clone());
                    continue;
                }
                let ref_index = result.iter().position(|r| {
                    let r = r.borrow();
                    r.definition
                        .as_ref()
                        .is_some_and(|d| d.kind == DefinitionKind::Symbol)
                        && r.definition.as_ref().and_then(|d| d.symbol) == symbol
                });
                let Some(ref_index) = ref_index else {
                    result.push(entry.clone());
                    continue;
                };

                let mut sorted_refs: Vec<Rc<RefCell<ReferenceEntry>>> = {
                    let reference = result[ref_index].borrow();
                    let mut v = reference.references.clone();
                    v.extend(entry.borrow().references.iter().cloned());
                    v
                };
                sorted_refs.sort_by(|entry1, entry2| {
                    let entry1_file = source_file_index_of_entry(entry1);
                    let entry2_file = source_file_index_of_entry(entry2);
                    if entry1_file != entry2_file {
                        return entry1_file.cmp(&entry2_file);
                    }
                    lsproto::compare_ranges(
                        &self.get_range_of_entry(entry1),
                        &self.get_range_of_entry(entry2),
                    )
                    .cmp(&0)
                });
                let definition = result[ref_index]
                    .borrow()
                    .definition
                    .as_ref()
                    .and_then(|d| d.clone_def());
                result[ref_index] = Rc::new(RefCell::new(SymbolAndEntries {
                    definition,
                    references: sorted_refs,
                }));
            }
        }
        result
    }
}

/// `isDeclarationOfSymbol`.
fn is_declaration_of_symbol(
    node: Option<NodeId>,
    target: Option<SymbolId>,
    program: &Rc<Program>,
) -> bool {
    let (Some(node), Some(target)) = (node, target) else {
        return false;
    };

    let nodes = program.nodes(node.file_index());
    let source: Option<NodeId> = if let Some(decl) = get_declaration_from_name(node, &nodes) {
        Some(decl)
    } else if nodes[node].kind == Kind::DefaultKeyword {
        nodes[node].parent
    } else if ast::is_literal_computed_property_declaration_name(node, &nodes) {
        nodes[node].parent.and_then(|p| nodes[p].parent)
    } else if nodes[node].kind == Kind::ConstructorKeyword
        && nodes[node]
            .parent
            .is_some_and(|p| ast::is_constructor_declaration(&nodes[p]))
    {
        nodes[node].parent.and_then(|p| nodes[p].parent)
    } else {
        None
    };

    // !!!
    // const commonjsSource = source && isBinaryExpression(source) ? source.left as unknown as Declaration : undefined;

    let Some(source) = source else {
        return false;
    };
    program.symbols.borrow()[target.index()]
        .declarations
        .contains(&source)
}

/// `getDeclarationFromName` (ast.go) — local copy: `ast.GetDeclarationFromName`
/// is not yet ported in tsc_ast.
pub(crate) fn get_declaration_from_name(name: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let parent = nodes[name].parent?;
    match nodes[name].kind {
        Kind::StringLiteral | Kind::NoSubstitutionTemplateLiteral | Kind::NumericLiteral => {
            if ast::is_computed_property_name(&nodes[parent]) {
                return nodes[parent].parent;
            }
            declaration_from_name_identifier_case(name, parent, nodes)
        }
        Kind::Identifier => declaration_from_name_identifier_case(name, parent, nodes),
        Kind::PrivateIdentifier => {
            if ast::is_declaration(&nodes[parent]) && nodes[parent].name() == Some(name) {
                return Some(parent);
            }
            None
        }
        _ => None,
    }
}

/// `KindIdentifier`/`fallthrough` case of `getDeclarationFromName`.
fn declaration_from_name_identifier_case(
    name: NodeId,
    parent: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    if ast::is_declaration(&nodes[parent]) {
        if nodes[parent].name() == Some(name) {
            return Some(parent);
        }
        return None;
    }
    if ast::is_qualified_name(&nodes[parent]) {
        let tag = nodes[parent].parent;
        if tag.is_some_and(|t| {
            ast::is_js_doc_parameter_tag(&nodes[t]) && nodes[t].name() == Some(parent)
        }) {
            return tag;
        }
        return None;
    }
    let bin_exp = nodes[parent].parent;
    if let Some(bin_exp) = bin_exp {
        if ast::is_binary_expression(&nodes[bin_exp])
            && ast::get_assignment_declaration_kind(bin_exp, nodes) != ast::JsDeclarationKind::None
        {
            // (binExp.left as BindableStaticNameExpression).symbol || binExp.symbol
            let left_has_symbol = nodes[bin_exp]
                .as_binary_expression()
                .left
                .is_some_and(|l| nodes[l].symbol().is_some());
            if left_has_symbol || nodes[bin_exp].symbol().is_some() {
                if ast::get_name_of_declaration(Some(bin_exp), nodes) == Some(name) {
                    return Some(bin_exp);
                }
            }
        }
    }
    None
}

/// `declarationIsWriteAccess` (ast.go) — local copy.
pub(crate) fn declaration_is_write_access(decl: NodeId, nodes: &[Node]) -> bool {
    // Consider anything in an ambient declaration to be a write access since it may be coming from JS.
    if nodes[decl].flags.intersects(ast::NodeFlags::AMBIENT) {
        return true;
    }

    match nodes[decl].kind {
        Kind::BinaryExpression
        | Kind::BindingElement
        | Kind::ClassDeclaration
        | Kind::ClassExpression
        | Kind::DefaultKeyword
        | Kind::EnumDeclaration
        | Kind::EnumMember
        | Kind::ExportSpecifier
        | Kind::ImportClause // default import
        | Kind::ImportEqualsDeclaration
        | Kind::ImportSpecifier
        | Kind::InterfaceDeclaration
        | Kind::JSDocCallbackTag
        | Kind::JSDocTypedefTag
        | Kind::JsxAttribute
        | Kind::ModuleDeclaration
        | Kind::NamespaceExportDeclaration
        | Kind::NamespaceImport
        | Kind::NamespaceExport
        | Kind::Parameter
        | Kind::ShorthandPropertyAssignment
        | Kind::TypeAliasDeclaration
        | Kind::JSTypeAliasDeclaration
        | Kind::TypeParameter => true,

        Kind::PropertyAssignment => {
            // In `({ x: y } = 0);`, `x` is not a write access.
            !nodes[decl]
                .parent
                .is_some_and(|p| is_array_literal_or_object_literal_destructuring_pattern(p, nodes))
        }

        Kind::FunctionDeclaration
        | Kind::FunctionExpression
        | Kind::Constructor
        | Kind::MethodDeclaration
        | Kind::GetAccessor
        | Kind::SetAccessor => {
            // functions considered write if they provide a value (have a body)
            nodes[decl].body().is_some()
        }

        Kind::VariableDeclaration | Kind::PropertyDeclaration => {
            // variable/property write if initializer present or is in catch clause
            nodes[decl].initializer().is_some()
                || nodes[decl]
                    .parent
                    .is_some_and(|p| ast::is_catch_clause(&nodes[p]))
        }

        Kind::MethodSignature | Kind::PropertySignature | Kind::JSDocPropertyTag | Kind::JSDocParameterTag => false,

        _ => {
            // preserve TS behavior: crash on unexpected kinds
            panic!("Unhandled case in declarationIsWriteAccess")
        }
    }
}

/// `IsWriteAccessForReference` (ast.go) — local copy.
pub(crate) fn is_write_access_for_reference(node: NodeId, nodes: &[Node]) -> bool {
    let decl = get_declaration_from_name(node, nodes);
    (decl.is_some_and(|d| declaration_is_write_access(d, nodes)))
        || nodes[node].kind == Kind::DefaultKeyword
        || ast::is_write_access(node, nodes)
}

/// `referencedSymbolDefinitionInfo` holds the computed info for a definition.
pub(crate) struct ReferencedSymbolDefinitionInfo {
    /// `node`.
    #[allow(dead_code)]
    pub(crate) node: NodeId,
    /// `location`.
    pub(crate) location: lsproto::Location,
    /// `displayText`.
    pub(crate) display_text: Option<lsproto::VSClassifiedTextElement>,
}

impl<'h> LanguageService<'h> {
    /// `definitionToReferencedSymbolDefinitionInfo`.
    fn definition_to_referenced_symbol_definition_info(
        &self,
        ctx: &Context,
        def: &Definition,
        original_node: Option<NodeId>,
        vs_capability: bool,
        feature: Feature,
    ) -> Option<ReferencedSymbolDefinitionInfo> {
        match def.kind {
            DefinitionKind::Symbol => {
                let symbol = def.symbol?;
                // Get display parts
                let element =
                    self.get_definition_kind_and_display_parts(ctx, symbol, original_node, vs_capability);

                // Get the definition node
                let node = {
                    let declarations = self
                        .program
                        .symbols
                        .borrow()[symbol.index()]
                    .declarations
                    .clone();
                    if let Some(decl) = declarations.first().copied() {
                        let nodes = self.program.nodes(decl.file_index());
                        nodes[decl].name().unwrap_or(decl)
                    } else {
                        original_node?
                    }
                };

                let entry = Rc::new(RefCell::new(ReferenceEntry {
                    kind: EntryKind::Node,
                    node: Some(node),
                    ..empty_entry()
                }));
                let (loc, ok) = self.get_location_of_entry_for_feature(&entry, feature);
                if !ok {
                    return None;
                }
                Some(ReferencedSymbolDefinitionInfo {
                    node,
                    location: loc,
                    display_text: Some(element),
                })
            }

            DefinitionKind::Label => {
                let node = def.node?;
                let entry = Rc::new(RefCell::new(ReferenceEntry {
                    kind: EntryKind::Node,
                    node: Some(node),
                    ..empty_entry()
                }));
                let (loc, ok) = self.get_location_of_entry_for_feature(&entry, feature);
                if !ok {
                    return None;
                }
                let text = {
                    let nodes = self.program.nodes(node.file_index());
                    nodes[node].text(&nodes).into_owned()
                };
                Some(ReferencedSymbolDefinitionInfo {
                    node,
                    location: loc,
                    display_text: Some(lsproto::VSClassifiedTextElement {
                        runs: Some(vec![lsproto::VSClassifiedTextRun {
                            text,
                            classification_type_name:
                                lsproto::ClassificationTypeName::Text.to_string(),
                            ..Default::default()
                        }]),
                        ..Default::default()
                    }),
                })
            }

            DefinitionKind::Keyword => {
                let node = def.node?;
                let name = {
                    let nodes = self.program.nodes(node.file_index());
                    tsc_scanner::scanner::token_to_string(nodes[node].kind)
                };
                let entry = Rc::new(RefCell::new(ReferenceEntry {
                    kind: EntryKind::Node,
                    node: Some(node),
                    ..empty_entry()
                }));
                let (loc, ok) = self.get_location_of_entry_for_feature(&entry, feature);
                if !ok {
                    return None;
                }
                Some(ReferencedSymbolDefinitionInfo {
                    node,
                    location: loc,
                    display_text: Some(lsproto::VSClassifiedTextElement {
                        runs: Some(vec![lsproto::VSClassifiedTextRun {
                            text: name.to_string(),
                            classification_type_name:
                                lsproto::ClassificationTypeName::Keyword.to_string(),
                            ..Default::default()
                        }]),
                        ..Default::default()
                    }),
                })
            }

            DefinitionKind::This => {
                let node = def.node?;
                let symbol = def.symbol?;
                let element =
                    self.get_definition_kind_and_display_parts(ctx, symbol, Some(node), vs_capability);
                let entry = Rc::new(RefCell::new(ReferenceEntry {
                    kind: EntryKind::Node,
                    node: Some(node),
                    ..empty_entry()
                }));
                let (loc, ok) = self.get_location_of_entry_for_feature(&entry, feature);
                if !ok {
                    return None;
                }
                Some(ReferencedSymbolDefinitionInfo {
                    node,
                    location: loc,
                    display_text: Some(element),
                })
            }

            DefinitionKind::String => {
                let node = def.node?;
                let entry = Rc::new(RefCell::new(ReferenceEntry {
                    kind: EntryKind::Node,
                    node: Some(node),
                    ..empty_entry()
                }));
                let (loc, ok) = self.get_location_of_entry_for_feature(&entry, feature);
                if !ok {
                    return None;
                }
                let text = {
                    let nodes = self.program.nodes(node.file_index());
                    nodes[node].text(&nodes).into_owned()
                };
                Some(ReferencedSymbolDefinitionInfo {
                    node,
                    location: loc,
                    display_text: Some(lsproto::VSClassifiedTextElement {
                        runs: Some(vec![lsproto::VSClassifiedTextRun {
                            text,
                            classification_type_name:
                                lsproto::ClassificationTypeName::String.to_string(),
                            ..Default::default()
                        }]),
                        ..Default::default()
                    }),
                })
            }

            DefinitionKind::TripleSlashReference => {
                let triple_slash = def.triple_slash_file_ref.as_ref()?;
                let file = triple_slash.file?;
                let entry = Rc::new(RefCell::new(ReferenceEntry {
                    kind: EntryKind::Node,
                    node: Some(file),
                    ..empty_entry()
                }));
                let (loc, ok) = self.get_location_of_entry_for_feature(&entry, feature);
                if !ok {
                    return None;
                }
                Some(ReferencedSymbolDefinitionInfo {
                    node: file,
                    location: loc,
                    display_text: Some(lsproto::VSClassifiedTextElement {
                        runs: Some(vec![lsproto::VSClassifiedTextRun {
                            text: format!("\"{}\"", triple_slash.reference.file_name),
                            classification_type_name:
                                lsproto::ClassificationTypeName::String.to_string(),
                            ..Default::default()
                        }]),
                        ..Default::default()
                    }),
                })
            }
        }
    }

    /// `getDefinitionKindAndDisplayParts` — returns the classified display
    /// text for a symbol definition.
    ///
    /// !!! hover::get_quick_info_and_declaration_at_location is
    /// module-private to `crate::hover` (sibling-owned file), so the full
    /// quickinfo display-parts pipeline can't be invoked here. This shim
    /// produces the definition text via `Checker::symbol_to_string` and the
    /// shared `classification_for_symbol` classification — the text is right
    /// but lacks the multi-run quickinfo structure (parameters, punctuation
    /// runs, etc.) that hover's implementation would emit.
    fn get_definition_kind_and_display_parts(
        &self,
        ctx: &Context,
        symbol: SymbolId,
        original_node: Option<NodeId>,
        vs_capability: bool,
    ) -> lsproto::VSClassifiedTextElement {
        let program = self.get_program();
        let (checker, done) = program.get_type_checker(ctx.clone());
        {
            let Some(original_node) = original_node else {
                drop(checker);
                done();
                return lsproto::VSClassifiedTextElement::default();
            };
            let mut nodes = program.nodes_mut(original_node.file_index());
            get_intersecting_meaning_from_declarations(
                &mut nodes,
                &program,
                Some(original_node),
                symbol,
                ast::SemanticMeaning::ALL,
            );
        }
        let text = checker.borrow_mut().symbol_to_string(symbol);
        let mut dpw =
            crate::displaypartswriter::new_display_parts_writer(vs_capability, &checker.borrow(), &program);
        let classification = dpw.classification_for_symbol(Some(symbol));
        dpw.write_classified(&text, classification);
        let result = if vs_capability {
            lsproto::VSClassifiedTextElement {
                runs: Some(dpw.get_runs().to_vec()),
                ..Default::default()
            }
        } else {
            // Fallback: single unclassified run with the full text
            let text = dpw.string().to_string();
            lsproto::VSClassifiedTextElement {
                runs: Some(vec![lsproto::VSClassifiedTextRun {
                    text,
                    classification_type_name: lsproto::ClassificationTypeName::Text
                        .to_string(),
                    ..Default::default()
                }]),
                ..Default::default()
            }
        };
        drop(dpw);
        drop(checker);
        done();
        result
    }
}

/// `empty_entry` — helper for ad-hoc `ReferenceEntry` values.
fn empty_entry() -> ReferenceEntry {
    ReferenceEntry {
        kind: EntryKind::None,
        node: None,
        context: None,
        source_file: None,
        text_range: None,
        lsp_range: None,
        unmappable: false,
    }
}

impl Definition {
    /// Clone helper — `Definition` isn't `Clone` because `TripleSlashDefinition`'s
    /// `FileReference` is cloned manually.
    pub(crate) fn clone_def(&self) -> Option<Definition> {
        Some(Definition {
            kind: self.kind,
            symbol: self.symbol,
            node: self.node,
            triple_slash_file_ref: self.triple_slash_file_ref.as_ref().map(|t| {
                TripleSlashDefinition {
                    reference: t.reference.clone(),
                    file: t.file,
                }
            }),
        })
    }
}

// GetReferencedSymbolsForNode returns all referenced symbols and their reference entries for the given node.
impl<'h> LanguageService<'h> {
    /// `GetReferencedSymbolsForNode` — public variant.
    pub fn get_referenced_symbols_for_node_public(
        &self,
        ctx: &Context,
        position: i32,
        node: NodeId,
        source_files: &[NodeId],
    ) -> Vec<Rc<RefCell<SymbolAndEntries>>> {
        let program = self.get_program();
        self.get_referenced_symbols_for_node(
            ctx,
            position,
            node,
            &program,
            source_files,
            RefOptions {
                use_: ReferenceUse::References,
                ..Default::default()
            },
        )
    }
}

/// `SignatureUsage` — a single usage of a signature declaration, pairing the
/// reference name node with its containing call expression (if any).
pub struct SignatureUsage {
    /// `Name` — the identifier reference node.
    pub name: NodeId,
    /// `Call` — the containing call expression, or nil if not a call usage.
    pub call: Option<NodeId>,
}

impl<'h> LanguageService<'h> {
    /// `GetSignatureUsages` — all usages of a signature declaration as
    /// name-call pairs.
    pub fn get_signature_usages(&self, ctx: &Context, signature_decl: NodeId) -> Vec<SignatureUsage> {
        let name = {
            let nodes = self.program.nodes(signature_decl.file_index());
            match nodes[signature_decl].name() {
                Some(name) if ast::is_identifier(&nodes[name]) => name,
                _ => return Vec::new(),
            }
        };

        let source_files = self.program.source_files();
        let entries = {
            let nodes = self.program.nodes(name.file_index());
            self.get_referenced_symbols_for_node_public(ctx, nodes[name].pos(), name, &source_files)
        };

        // Collect all declaration name nodes for the target symbol so we can
        // filter them out — the caller wants usages, not declarations.
        let mut decl_names: Set<NodeId> = Set::new();
        for entry in &entries {
            let e = entry.borrow();
            if let Some(definition) = &e.definition {
                if let Some(symbol) = definition.symbol {
                    let declarations = self.program.symbols.borrow()[symbol.index()]
                        .declarations
                        .clone();
                    for decl in declarations {
                        let nodes = self.program.nodes(decl.file_index());
                        if let Some(n) = nodes[decl].name() {
                            decl_names.add(n);
                        }
                    }
                }
            }
        }

        let mut result = Vec::new();
        for entry in &entries {
            for reference in &entry.borrow().references {
                let node = {
                    let r = reference.borrow();
                    if !r.is_node_entry() {
                        None
                    } else {
                        r.node()
                    }
                };
                let Some(node) = node else {
                    continue;
                };
                if decl_names.has(&node) {
                    continue;
                }

                let call_expr = {
                    let nodes = self.program.nodes(node.file_index());
                    let called = ast::climb_past_property_access(node, &nodes);
                    match nodes[called].parent {
                        Some(parent)
                            if ast::is_call_expression(&nodes[parent])
                                && nodes[parent].expression() == Some(called) =>
                        {
                            Some(parent)
                        }
                        _ => None,
                    }
                };

                result.push(SignatureUsage {
                    name: node,
                    call: call_expr,
                });
            }
        }
        result
    }
}

// === functions for find all ref implementation ===

impl<'h> LanguageService<'h> {
    /// `getReferencedSymbolsForNode`.
    pub(crate) fn get_referenced_symbols_for_node(
        &self,
        ctx: &Context,
        position: i32,
        node: NodeId,
        program: &Rc<Program>,
        source_files: &[NodeId],
        options: RefOptions,
    ) -> Vec<Rc<RefCell<SymbolAndEntries>>> {
        // !!! cancellationToken
        let mut source_files_set: Set<RootedFilePath> = Set::new();
        {
            for &file in source_files {
                let nodes = program.nodes(file.file_index());
                source_files_set.add(nodes[file].as_source_file().file_name().clone());
            }
        }
        let source_files_set = Rc::new(source_files_set);

        let mut node = node;
        if options.use_ == ReferenceUse::References || options.use_ == ReferenceUse::Rename {
            let source_file_of_node = {
                let nodes = program.nodes(node.file_index());
                ast::get_source_file_of_node(Some(node), &nodes)
            };
            let mut nodes = program.nodes_mut(node.file_index());
            node = get_adjusted_location(
                &mut nodes,
                node,
                options.use_ == ReferenceUse::Rename,
                source_file_of_node,
            )
            .unwrap_or(node);
        }

        let (checker, done) = program.get_type_checker(ctx.clone());

        let result = self.get_referenced_symbols_for_node_worker(
            ctx,
            position,
            node,
            program,
            source_files,
            &source_files_set,
            &checker,
            options,
        );
        drop(checker);
        done();
        result
    }

    fn get_referenced_symbols_for_node_worker(
        &self,
        ctx: &Context,
        position: i32,
        node: NodeId,
        program: &Rc<Program>,
        source_files: &[NodeId],
        source_files_set: &Rc<Set<RootedFilePath>>,
        checker: &Rc<RefCell<Checker>>,
        options: RefOptions,
    ) -> Vec<Rc<RefCell<SymbolAndEntries>>> {
        if {
            let nodes = program.nodes(node.file_index());
            nodes[node].kind == Kind::SourceFile
        } {
            let resolved_ref = {
                let mut nodes = program.nodes_mut(node.file_index());
                get_reference_at_position(&mut nodes, node, position, program)
            };
            let Some(resolved_ref) = resolved_ref else {
                return Vec::new();
            };
            let Some(resolved_file) = resolved_ref.file else {
                return Vec::new();
            };

            let file_symbol = {
                let nodes = program.nodes(resolved_file.file_index());
                nodes[resolved_file].symbol()
            };
            if let Some(module_symbol) = file_symbol.map(|s| {
                checker.borrow_mut().get_merged_symbol(s)
            }) {
                return self.get_referenced_symbols_for_module(
                    checker,
                    program,
                    module_symbol,
                    false, /*excludeImportTypeOfExportEquals*/
                    source_files,
                    source_files_set,
                );
            }

            // !!! not implemented
            // fileIncludeReasons := program.getFileIncludeReasons();
            // if (!fileIncludeReasons) {
            // 	return nil
            // }
            return vec![Rc::new(RefCell::new(SymbolAndEntries {
                definition: Some(Definition {
                    kind: DefinitionKind::TripleSlashReference,
                    symbol: None,
                    node: None,
                    triple_slash_file_ref: resolved_ref.reference.map(|r| {
                        TripleSlashDefinition {
                            reference: r,
                            file: None,
                        }
                    }),
                }),
                references: get_references_for_non_module(resolved_file, program),
            }))];
        }

        if !options.implementations {
            // !!! cancellationToken
            if let Some(special) = get_referenced_symbols_special(node, source_files, program) {
                return special;
            }
        }

        // constructors should use the class symbol, detected by name, if present
        let symbol_node = {
            let nodes = program.nodes(node.file_index());
            if nodes[node].kind == Kind::Constructor
                && nodes[node]
                    .parent
                    .is_some_and(|p| nodes[p].name().is_some())
            {
                nodes[node].parent.and_then(|p| nodes[p].name()).unwrap_or(node)
            } else {
                node
            }
        };
        let symbol = checker.borrow_mut().get_symbol_at_location_api(symbol_node);
        // Could not find a symbol e.g. unknown identifier
        let Some(symbol) = symbol else {
            // String literal might be a property (and thus have a symbol), so do this here rather than in getReferencedSymbolsSpecial.
            let is_string_literal_like = {
                let nodes = program.nodes(node.file_index());
                ast::is_string_literal_like(&nodes[node])
            };
            if !options.implementations && is_string_literal_like {
                {
                    let nodes = program.nodes(node.file_index());
                    if is_module_specifier_like(node, &nodes) {
                        // !!! not implemented
                        // fileIncludeReasons := program.GetFileIncludeReasons()
                        // if referencedFile := program.GetResolvedModuleFromModuleSpecifier(node, nil /*sourceFile*/); referencedFile != nil {
                        // return []*SymbolAndEntries{{
                        // 	definition: &Definition{Kind: definitionKindString, node: node},
                        // 	references: getReferencesForNonModule(referencedFile, program /*fileIncludeReasons,*/),
                        // }}
                        // }
                        // Fall through to string literal references. This is not very likely to return
                        // anything useful, but I guess it's better than nothing, and there's an existing
                        // test that expects this to happen (fourslash/cases/untypedModuleImport.ts).
                    }
                }
                return self.get_references_for_string_literal(ctx, node, source_files, checker);
            }
            return Vec::new();
        };

        let (symbol_name, symbol_parent, symbol_flags) = {
            let arena = checker.borrow().symbol_arena.clone();
            let s = &arena.borrow()[symbol.index()];
            (s.name.clone(), s.parent, s.flags)
        };
        if symbol_name.as_ref() == ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS {
            let Some(symbol_parent) = symbol_parent else {
                return Vec::new();
            };
            return self.get_referenced_symbols_for_module(
                checker,
                program,
                symbol_parent,
                false, /*excludeImportTypeOfExportEquals*/
                source_files,
                source_files_set,
            );
        }

        let module_references = self.get_referenced_symbols_for_module_if_declared_by_source_file(
            ctx,
            symbol,
            program,
            source_files,
            checker,
            options,
            source_files_set,
        );
        if module_references.is_some()
            && symbol_flags & SymbolFlags::TRANSIENT == SymbolFlags::NONE
        {
            return module_references.expect("module references");
        }

        let aliased_symbol = get_merged_aliased_symbol_of_namespace_export_declaration(
            node,
            symbol,
            checker,
            program,
        );
        let module_references_of_export_target = aliased_symbol.and_then(|aliased| {
            self.get_referenced_symbols_for_module_if_declared_by_source_file(
                ctx,
                aliased,
                program,
                source_files,
                checker,
                options,
                source_files_set,
            )
        });

        let references = get_referenced_symbols_for_symbol(
            ctx,
            program,
            symbol,
            Some(node),
            source_files,
            source_files_set,
            checker,
            options,
        );
        self.merge_references(
            program,
            &[
                module_references.unwrap_or_default(),
                references,
                module_references_of_export_target.unwrap_or_default(),
            ],
        )
    }

    /// `getReferencesForStringLiteral`.
    fn get_references_for_string_literal(
        &self,
        ctx: &Context,
        node: NodeId,
        source_files: &[NodeId],
        checker: &Rc<RefCell<Checker>>,
    ) -> Vec<Rc<RefCell<SymbolAndEntries>>> {
        let t = {
            let mut c = checker.borrow_mut();
            get_contextual_type_from_parent_or_ancestor_type_node(node, &mut c)
        };
        let node_text = {
            let program = self.get_program();
            let nodes = program.nodes(node.file_index());
            nodes[node].text(&nodes).into_owned()
        };
        let mut references: Vec<Rc<RefCell<ReferenceEntry>>> = Vec::new();
        for &source_file in source_files {
            if ctx.is_cancelled() {
                break;
            }
            let possible_references = {
                let program = self.get_program();
                let mut nodes = program.nodes_mut(source_file.file_index());
                tsc_checker::services::get_possible_symbol_reference_nodes(
                    &mut nodes,
                    source_file,
                    &node_text,
                    None,
                )
            };
            for ref_node in possible_references {
                let program = self.get_program();
                let nodes = program.nodes(ref_node.file_index());
                if !ast::is_string_literal_like(&nodes[ref_node])
                    || nodes[ref_node].text(&nodes) != node_text
                {
                    continue;
                }
                if let Some(t) = t {
                    let ref_type = {
                        let mut c = checker.borrow_mut();
                        get_contextual_type_from_parent_or_ancestor_type_node(ref_node, &mut c)
                    };
                    let is_string_literal_property = {
                        let mut c = checker.borrow_mut();
                        is_string_literal_property_reference(ref_node, &mut c, &nodes)
                    };
                    let string_type = checker.borrow().string_type;
                    if t != string_type && (Some(t) == ref_type || is_string_literal_property) {
                        references.push(new_node_entry_with_kind(
                            ref_node,
                            EntryKind::StringLiteral,
                            &nodes,
                        ));
                    }
                } else {
                    if ast::is_no_substitution_template_literal(&nodes[ref_node])
                        && !range_is_on_single_line(
                            &nodes,
                            nodes[ref_node].loc,
                            source_file,
                        )
                    {
                        continue;
                    }
                    references.push(new_node_entry_with_kind(
                        ref_node,
                        EntryKind::StringLiteral,
                        &nodes,
                    ));
                }
            }
        }

        vec![Rc::new(RefCell::new(SymbolAndEntries {
            definition: Some(Definition {
                kind: DefinitionKind::String,
                symbol: None,
                node: Some(node),
                triple_slash_file_ref: None,
            }),
            references,
        }))]
    }

    /// `getReferencedSymbolsForModuleIfDeclaredBySourceFile`.
    fn get_referenced_symbols_for_module_if_declared_by_source_file(
        &self,
        ctx: &Context,
        symbol: SymbolId,
        program: &Rc<Program>,
        source_files: &[NodeId],
        checker: &Rc<RefCell<Checker>>,
        options: RefOptions,
        source_files_set: &Rc<Set<RootedFilePath>>,
    ) -> Option<Vec<Rc<RefCell<SymbolAndEntries>>>> {
        let (symbol_flags, declarations) = {
            let arena = checker.borrow().symbol_arena.clone();
            let s = &arena.borrow()[symbol.index()];
            (s.flags, s.declarations.clone())
        };
        if symbol_flags & SymbolFlags::MODULE == SymbolFlags::NONE || declarations.is_empty() {
            return None;
        }
        let module_source_file = declarations.iter().copied().find(|&d| {
            let nodes = program.nodes(d.file_index());
            ast::is_source_file(&nodes[d])
        })?;
        let module_source_file_name = {
            let nodes = program.nodes(module_source_file.file_index());
            nodes[module_source_file]
                .as_source_file()
                .file_name()
                .clone()
        };
        let export_equals = {
            let arena = checker.borrow().symbol_arena.clone();
            arena.borrow()[symbol.index()]
                .exports
                .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
                .copied()
        };
        // If exportEquals != nil, we're about to add references to `import("mod")` anyway, so don't double-count them.
        let module_references = self.get_referenced_symbols_for_module(
            checker,
            program,
            symbol,
            export_equals.is_some(),
            source_files,
            source_files_set,
        );
        let export_equals_is_alias = export_equals.is_some_and(|ee| {
            checker.borrow().symbol_arena.borrow()[ee.index()]
                .flags
                .intersects(SymbolFlags::ALIAS)
        });
        if !export_equals_is_alias || !source_files_set.has(&module_source_file_name) {
            return Some(module_references);
        }
        let symbol = {
            let mut c = checker.borrow_mut();
            c.get_aliased_symbol(export_equals.unwrap_or(symbol))
                .unwrap_or(export_equals.unwrap_or(symbol))
        };
        let references = get_referenced_symbols_for_symbol(
            ctx,
            program,
            symbol,
            None,
            source_files,
            source_files_set,
            checker,
            options,
        );
        Some(self.merge_references(program, &[module_references, references]))
    }

    /// `getReferencesForNonModule` — !!! not implemented.
    /// `getReferencedSymbolsForModule`.
    fn get_referenced_symbols_for_module(
        &self,
        checker: &Rc<RefCell<Checker>>,
        program: &Rc<Program>,
        symbol: SymbolId,
        exclude_import_type_of_export_equals: bool,
        source_files: &[NodeId],
        source_files_set: &Rc<Set<RootedFilePath>>,
    ) -> Vec<Rc<RefCell<SymbolAndEntries>>> {
        debug_assert!(
            checker.borrow().symbol_arena.borrow()[symbol.index()]
                .value_declaration
                .is_some()
        );

        let module_refs = {
            let mut c = checker.borrow_mut();
            find_module_references(program, source_files, symbol, &mut c)
        };
        let mut references: Vec<Rc<RefCell<ReferenceEntry>>> = Vec::new();
        for reference in module_refs {
            match reference.kind {
                ModuleReferenceKind::Import => {
                    let Some(literal) = reference.literal else {
                        continue;
                    };
                    let nodes = program.nodes(literal.file_index());
                    if let Some(parent) = nodes[literal].parent {
                        if ast::is_literal_type_node(&nodes[parent]) {
                            if let Some(import_type) = nodes[parent].parent {
                                if ast::is_import_type_node(&nodes[import_type]) {
                                    let import_type_node =
                                        nodes[import_type].as_import_type_node();
                                    if exclude_import_type_of_export_equals
                                        && import_type_node.qualifier.is_none()
                                    {
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    // import("foo") with no qualifier will reference the `export =` of the module, which may be referenced anyway.
                    references.push(new_node_entry(literal, &nodes));
                }
                ModuleReferenceKind::Implicit => {
                    // For implicit references (e.g., JSX runtime imports), return the first JSX node,
                    // the first statement, or the whole file
                    let Some(referencing_file) = reference.referencing_file else {
                        continue;
                    };
                    let mut range_node: Option<NodeId> = None;
                    let is_tslib = {
                        let nodes = program.nodes(referencing_file.file_index());
                        reference
                            .literal
                            .is_some_and(|l| nodes[l].text(&nodes) == "tslib")
                    };

                    // Skip the JSX search for tslib imports
                    if !is_tslib {
                        let nodes = program.nodes(referencing_file.file_index());
                        range_node = find_first_jsx_node(referencing_file, &nodes);
                    }

                    let nodes = program.nodes(referencing_file.file_index());
                    let range_node = range_node.or_else(|| {
                        let statements = nodes[referencing_file]
                            .statements()
                            .map(|s| s.to_vec())
                            .unwrap_or_default();
                        statements.first().copied().or(Some(referencing_file))
                    });
                    let Some(range_node) = range_node else {
                        continue;
                    };
                    references.push(new_node_entry(range_node, &nodes));
                }
                ModuleReferenceKind::Reference => {
                    let (Some(referencing_file), Some(file_ref)) =
                        (reference.referencing_file, reference.file_ref)
                    else {
                        continue;
                    };
                    references.push(new_range_entry(referencing_file, file_ref.text_range));
                }
            }
        }

        // Add references to the module declarations themselves
        let declarations = checker.borrow().symbol_arena.borrow()[symbol.index()]
            .declarations
            .clone();
        for decl in &declarations {
            let nodes = program.nodes(decl.file_index());
            match nodes[*decl].kind {
                Kind::SourceFile => {
                    // Don't include the source file itself. (This may not be ideal behavior, but awkward to include an entire file as a reference.)
                    continue;
                }
                Kind::ModuleDeclaration => {
                    let file_name = ast::get_source_file_of_node(Some(*decl), &nodes)
                        .map(|sf| nodes[sf].as_source_file().file_name().clone());
                    if file_name.is_some_and(|f| source_files_set.has(&f)) {
                        if let Some(name) = nodes[*decl].as_module_declaration().name {
                            references.push(new_node_entry(name, &nodes));
                        }
                    }
                }
                _ => {
                    // This may be merged with something (e.g. a class merged with a namespace).
                    continue;
                }
            }
        }

        // Handle export equals declarations
        let exported_decls = {
            let arena = checker.borrow().symbol_arena.clone();
            arena.borrow()[symbol.index()]
                .exports
                .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
                .copied()
                .map(|ee| arena.borrow()[ee.index()].declarations.clone())
                .unwrap_or_default()
        };
        for decl in exported_decls {
            let source_file = {
                let nodes = program.nodes(decl.file_index());
                ast::get_source_file_of_node(Some(decl), &nodes)
            };
            let Some(source_file) = source_file else {
                continue;
            };
            let file_name = {
                let nodes = program.nodes(source_file.file_index());
                nodes[source_file].as_source_file().file_name().clone()
            };
            if !source_files_set.has(&file_name) {
                continue;
            }
            let mut nodes = program.nodes_mut(decl.file_index());
            let node: NodeId = if ast::is_binary_expression(&nodes[decl])
                && nodes[decl]
                    .as_binary_expression()
                    .left
                    .is_some_and(|l| ast::is_property_access_expression(&nodes[l]))
            {
                // At `module.exports = ...`, reference node is `module`
                nodes[decl]
                    .as_binary_expression()
                    .left
                    .and_then(|l| nodes[l].expression())
                    .unwrap_or(decl)
            } else if ast::is_export_assignment(&nodes[decl]) {
                // Find the export keyword
                tokens::find_child_of_kind(&mut nodes, source_file, decl, Kind::ExportKeyword)
                    .expect("Expected to find export keyword")
            } else {
                ast::get_name_of_declaration(Some(decl), &nodes).unwrap_or(decl)
            };
            references.push(new_node_entry(node, &nodes));
        }

        if !references.is_empty() {
            return vec![Rc::new(RefCell::new(SymbolAndEntries {
                definition: Some(Definition {
                    kind: DefinitionKind::Symbol,
                    symbol: Some(symbol),
                    node: None,
                    triple_slash_file_ref: None,
                }),
                references,
            }))];
        }
        Vec::new()
    }
}

/// `IsArrayLiteralOrObjectLiteralDestructuringPattern` (ast.go) — local copy;
/// not yet ported in `tsc_ast`.
fn is_array_literal_or_object_literal_destructuring_pattern(
    node: NodeId,
    nodes: &[Node],
) -> bool {
    if !(ast::is_array_literal_expression(&nodes[node])
        || ast::is_object_literal_expression(&nodes[node]))
    {
        return false;
    }
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    // [a,b,c] from:
    // [a, b, c] = someExpression;
    if ast::is_binary_expression(&nodes[parent])
        && nodes[parent].as_binary_expression().left == Some(node)
        && nodes[parent]
            .as_binary_expression()
            .operator_token
            .is_some_and(|op| nodes[op].kind == Kind::EqualsToken)
    {
        return true;
    }
    // [a, b, c] from:
    // for([a, b, c] of expression)
    if ast::is_for_of_statement(&nodes[parent]) && nodes[parent].initializer() == Some(node) {
        return true;
    }
    // {x, a: {a, b, c} } = someExpression
    if ast::is_property_assignment(&nodes[parent]) {
        if let Some(grandparent) = nodes[parent].parent {
            return is_array_literal_or_object_literal_destructuring_pattern(grandparent, nodes);
        }
        return false;
    }
    // [a, b, c] of
    // [x, [a, b, c] ] = someExpression
    is_array_literal_or_object_literal_destructuring_pattern(parent, nodes)
}

/// `printer.RangeIsOnSingleLine` — `pub(crate)` in the printer crate, so it
/// is reimplemented here over `skip_trivia` + `positions_are_on_same_line`
/// (mirroring `organizeimports.rs`'s local copy).
fn range_is_on_single_line(nodes: &[Node], r: TextRange, source_file: NodeId) -> bool {
    let start =
        tsc_scanner::scanner::skip_trivia(nodes[source_file].as_source_file().text(), r.pos());
    crate::change::tracker::positions_are_on_same_line(start, r.end(), source_file, nodes)
}

/// `getReferencesForNonModule` — !!! not implemented.
fn get_references_for_non_module(
    _referenced_file: NodeId,
    _program: &Rc<Program>,
) -> Vec<Rc<RefCell<ReferenceEntry>>> {
    // !!! not implemented
    Vec::new()
}

/// `getReferencedSymbolsSpecial`.
fn get_referenced_symbols_special(
    node: NodeId,
    source_files: &[NodeId],
    program: &Rc<Program>,
) -> Option<Vec<Rc<RefCell<SymbolAndEntries>>>> {
    let kind = {
        let nodes = program.nodes(node.file_index());
        nodes[node].kind
    };
    if is_type_keyword(kind) {
        // A void expression (i.e., `void foo()`) is not special, but the `void` type is.
        let nodes = program.nodes(node.file_index());
        if kind == Kind::VoidKeyword
            && nodes[node]
                .parent
                .is_some_and(|p| nodes[p].kind == Kind::VoidExpression)
        {
            return None;
        }

        // A modifier readonly (like on a property declaration) is not special;
        // a readonly type keyword (like `readonly string[]`) is.
        if kind == Kind::ReadonlyKeyword && !is_readonly_type_operator(node, &nodes) {
            return None;
        }
        // Likewise, when we *are* looking for a special keyword, make sure we
        // *don't* include readonly member modifiers.
        return get_all_references_for_keyword(
            source_files,
            kind,
            kind == Kind::ReadonlyKeyword,
            program,
        );
    }

    {
        let nodes = program.nodes(node.file_index());
        if nodes[node]
            .parent
            .is_some_and(|p| ast::is_import_meta(&nodes[p], &nodes) && nodes[p].name() == Some(node))
        {
            return get_all_references_for_import_meta(source_files, program);
        }
    }

    if kind == Kind::StaticKeyword {
        let nodes = program.nodes(node.file_index());
        if nodes[node]
            .parent
            .is_some_and(|p| nodes[p].kind == Kind::ClassStaticBlockDeclaration)
        {
            return Some(vec![Rc::new(RefCell::new(SymbolAndEntries {
                definition: Some(Definition {
                    kind: DefinitionKind::Keyword,
                    symbol: None,
                    node: Some(node),
                    triple_slash_file_ref: None,
                }),
                references: vec![new_node_entry(node, &nodes)],
            }))]);
        }
    }

    // Labels
    {
        let nodes = program.nodes(node.file_index());
        if is_jump_statement_target(node, &nodes) {
            // if we have a label definition, look within its statement for references, if not, then
            // the label is undefined and we have no results..
            let parent = nodes[node].parent.expect("parent");
            let label_name = nodes[node].text(&nodes).into_owned();
            if let Some(label_definition) = get_target_label(&nodes, Some(parent), &label_name) {
                let container = nodes[label_definition]
                    .parent
                    .expect("label parent");
                drop(nodes);
                return get_label_references_in_node(container, label_definition, program);
            }
            return None;
        }
    }

    {
        let nodes = program.nodes(node.file_index());
        if is_label_of_labeled_statement(node, &nodes) {
            let container = nodes[node].parent.expect("parent");
            drop(nodes);
            // it is a label definition and not a target, search within the parent labeledStatement
            return get_label_references_in_node(container, node, program);
        }
    }

    if {
        let nodes = program.nodes(node.file_index());
        is_this(node, &nodes)
    } {
        return get_references_for_this_keyword(node, source_files, program);
    }

    if kind == Kind::SuperKeyword {
        return get_references_for_super_keyword(node, program);
    }

    None
}

/// `getLabelReferencesInNode`.
fn get_label_references_in_node(
    container: NodeId,
    target_label: NodeId,
    program: &Rc<Program>,
) -> Option<Vec<Rc<RefCell<SymbolAndEntries>>>> {
    let source_file = {
        let nodes = program.nodes(container.file_index());
        ast::get_source_file_of_node(Some(container), &nodes).expect("source file")
    };
    let label_name = {
        let nodes = program.nodes(target_label.file_index());
        nodes[target_label].text(&nodes).into_owned()
    };
    let possible = {
        let mut nodes = program.nodes_mut(source_file.file_index());
        tsc_checker::services::get_possible_symbol_reference_nodes(
            &mut nodes,
            source_file,
            &label_name,
            Some(container),
        )
    };
    let mut references: Vec<Rc<RefCell<ReferenceEntry>>> = Vec::new();
    for node in possible {
        let nodes = program.nodes(node.file_index());
        // Only pick labels that are either the target label, or have a target that is the target label
        if node == target_label
            || (is_jump_statement_target(node, &nodes)
                && get_target_label(&nodes, Some(node), &label_name) == Some(target_label))
        {
            references.push(new_node_entry(node, &nodes));
        }
    }
    Some(vec![Rc::new(RefCell::new(new_symbol_and_entries(
        DefinitionKind::Label,
        Some(target_label),
        None,
        references,
    )))])
}

/// `getReferencesForThisKeyword`.
fn get_references_for_this_keyword(
    this_or_super_keyword: NodeId,
    source_files: &[NodeId],
    program: &Rc<Program>,
) -> Option<Vec<Rc<RefCell<SymbolAndEntries>>>> {
    let mut search_space_node = {
        let nodes = program.nodes(this_or_super_keyword.file_index());
        ast::get_this_container(
            this_or_super_keyword,
            &nodes,
            false, /*includeArrowFunctions*/
            false, /*includeClassComputedPropertyName*/
        )
    };

    // Whether 'this' occurs in a static context within a class.
    let mut static_flag = ModifierFlags::STATIC;
    let is_parameter_name = |node: NodeId, nodes: &[Node]| -> bool {
        nodes[node].kind == Kind::Identifier
            && nodes[node].parent.is_some_and(|p| {
                nodes[p].kind == Kind::Parameter && nodes[p].name() == Some(node)
            })
    };

    {
        let nodes = program.nodes(search_space_node.file_index());
        match nodes[search_space_node].kind {
            Kind::MethodDeclaration
            | Kind::MethodSignature
            | Kind::PropertyDeclaration
            | Kind::PropertySignature
            | Kind::Constructor
            | Kind::GetAccessor
            | Kind::SetAccessor => {
                if (nodes[search_space_node].kind == Kind::MethodDeclaration
                    || nodes[search_space_node].kind == Kind::MethodSignature)
                    && ast::is_object_literal_method(search_space_node, &nodes)
                {
                    static_flag &= nodes[search_space_node].modifier_flags();
                    search_space_node = nodes[search_space_node]
                        .parent
                        .expect("object literal parent"); // re-assign to be the owning object literals
                } else {
                    static_flag &= nodes[search_space_node].modifier_flags();
                    search_space_node = nodes[search_space_node]
                        .parent
                        .expect("class parent"); // re-assign to be the owning class
                }
            }
            Kind::SourceFile => {
                if ast::is_external_module(nodes[search_space_node].as_source_file())
                    || is_parameter_name(this_or_super_keyword, &nodes)
                {
                    return None;
                }
            }
            Kind::FunctionDeclaration | Kind::FunctionExpression => {
                // Computed properties in classes are not handled here because references to this are illegal,
                // so there is no point finding references to them.
            }
            _ => return None,
        }
    }

    let search_space_is_file = {
        let nodes = program.nodes(search_space_node.file_index());
        nodes[search_space_node].kind == Kind::SourceFile
    };
    let files_to_search: Vec<NodeId> = if !search_space_is_file {
        let nodes = program.nodes(search_space_node.file_index());
        ast::get_source_file_of_node(Some(search_space_node), &nodes)
            .into_iter()
            .collect()
    } else {
        source_files.to_vec()
    };

    let mut references: Vec<Rc<RefCell<ReferenceEntry>>> = Vec::new();
    for source_file in &files_to_search {
        // cancellationToken.throwIfCancellationRequested();
        let possible = {
            let mut nodes = program.nodes_mut(source_file.file_index());
            let container = if search_space_is_file {
                *source_file
            } else {
                search_space_node
            };
            tsc_checker::services::get_possible_symbol_reference_nodes(
                &mut nodes,
                *source_file,
                "this",
                Some(container),
            )
        };
        for node in possible {
            let nodes = program.nodes(node.file_index());
            if !is_this(node, &nodes) {
                continue;
            }
            let container = ast::get_this_container(node, &nodes, false, false);
            if !ast::can_have_symbol(&nodes[container]) {
                continue;
            }
            let ssn_kind = nodes[search_space_node].kind;
            let keep = match ssn_kind {
                Kind::FunctionExpression | Kind::FunctionDeclaration => {
                    nodes[search_space_node].symbol() == nodes[container].symbol()
                }
                Kind::MethodDeclaration | Kind::MethodSignature => {
                    ast::is_object_literal_method(search_space_node, &nodes)
                        && nodes[search_space_node].symbol() == nodes[container].symbol()
                }
                Kind::ClassExpression | Kind::ClassDeclaration | Kind::ObjectLiteralExpression => {
                    // Make sure the container belongs to the same class/object literals
                    // and has the appropriate static modifier from the original container.
                    nodes[container].parent.is_some_and(|cp| {
                        ast::can_have_symbol(&nodes[cp])
                            && nodes[search_space_node].symbol() == nodes[cp].symbol()
                            && ast::is_static(&nodes[container])
                                == (static_flag != ModifierFlags::NONE)
                    })
                }
                Kind::SourceFile => {
                    nodes[container].kind == Kind::SourceFile
                        && !ast::is_external_module(nodes[container].as_source_file())
                        && !is_parameter_name(node, &nodes)
                }
                _ => false,
            };
            if keep {
                references.push(new_node_entry(node, &nodes));
            }
        }
    }

    let mut this_parameter: Option<NodeId> = None;
    for reference in &references {
        let r = reference.borrow();
        if let Some(n) = r.node {
            let nodes = program.nodes(n.file_index());
            if nodes[n].parent.is_some_and(|p| nodes[p].kind == Kind::Parameter) {
                this_parameter = Some(n);
                break;
            }
        }
    }
    let this_parameter = this_parameter.unwrap_or(this_or_super_keyword);
    let search_space_symbol = {
        let nodes = program.nodes(search_space_node.file_index());
        nodes[search_space_node].symbol()
    };
    Some(vec![Rc::new(RefCell::new(new_symbol_and_entries(
        DefinitionKind::This,
        Some(this_parameter),
        search_space_symbol,
        references,
    )))])
}

/// `getReferencesForSuperKeyword`.
fn get_references_for_super_keyword(
    super_keyword: NodeId,
    program: &Rc<Program>,
) -> Option<Vec<Rc<RefCell<SymbolAndEntries>>>> {
    let mut search_space_node = {
        let nodes = program.nodes(super_keyword.file_index());
        ast::get_super_container(super_keyword, &nodes, false /*stopOnFunctions*/)?
    };
    // Whether 'super' occurs in a static context within a class.
    let mut static_flag = ModifierFlags::STATIC;

    {
        let nodes = program.nodes(search_space_node.file_index());
        match nodes[search_space_node].kind {
            Kind::PropertyDeclaration
            | Kind::PropertySignature
            | Kind::MethodDeclaration
            | Kind::MethodSignature
            | Kind::Constructor
            | Kind::GetAccessor
            | Kind::SetAccessor => {
                static_flag &= nodes[search_space_node].modifier_flags();
                search_space_node = nodes[search_space_node].parent.expect("class parent"); // re-assign to be the owning class
            }
            _ => return None,
        }
    }

    let source_file = {
        let nodes = program.nodes(search_space_node.file_index());
        ast::get_source_file_of_node(Some(search_space_node), &nodes).expect("source file")
    };
    let possible = {
        let mut nodes = program.nodes_mut(source_file.file_index());
        tsc_checker::services::get_possible_symbol_reference_nodes(
            &mut nodes,
            source_file,
            "super",
            Some(search_space_node),
        )
    };
    let mut references: Vec<Rc<RefCell<ReferenceEntry>>> = Vec::new();
    for node in possible {
        let nodes = program.nodes(node.file_index());
        if nodes[node].kind != Kind::SuperKeyword {
            continue;
        }
        let Some(container) = ast::get_super_container(node, &nodes, false) else {
            continue;
        };

        // If we have a 'super' container, we must have an enclosing class.
        // Now make sure the owning class is the same as the search-space
        // and has the same static qualifier as the original 'super's owner.
        if ast::is_static(&nodes[container]) == (static_flag != ModifierFlags::NONE)
            && nodes[container].parent.is_some_and(|cp| {
                nodes[cp].symbol() == nodes[search_space_node].symbol()
            })
        {
            references.push(new_node_entry(node, &nodes));
        }
    }

    let search_space_symbol = {
        let nodes = program.nodes(search_space_node.file_index());
        nodes[search_space_node].symbol()
    };
    Some(vec![Rc::new(RefCell::new(new_symbol_and_entries(
        DefinitionKind::Symbol,
        None,
        search_space_symbol,
        references,
    )))])
}

/// `getAllReferencesForImportMeta`.
fn get_all_references_for_import_meta(
    source_files: &[NodeId],
    program: &Rc<Program>,
) -> Option<Vec<Rc<RefCell<SymbolAndEntries>>>> {
    let mut references: Vec<Rc<RefCell<ReferenceEntry>>> = Vec::new();
    for &source_file in source_files {
        let possible = {
            let mut nodes = program.nodes_mut(source_file.file_index());
            tsc_checker::services::get_possible_symbol_reference_nodes(
                &mut nodes,
                source_file,
                "meta",
                Some(source_file),
            )
        };
        for node in possible {
            let nodes = program.nodes(node.file_index());
            if let Some(parent) = nodes[node].parent {
                if ast::is_import_meta(&nodes[parent], &nodes) {
                    references.push(new_node_entry(parent, &nodes));
                }
            }
        }
    }
    if references.is_empty() {
        return None;
    }
    let def_node = references[0].borrow().node;
    Some(vec![Rc::new(RefCell::new(SymbolAndEntries {
        definition: Some(Definition {
            kind: DefinitionKind::Keyword,
            symbol: None,
            node: def_node,
            triple_slash_file_ref: None,
        }),
        references,
    }))])
}

/// `getAllReferencesForKeyword`.
fn get_all_references_for_keyword(
    source_files: &[NodeId],
    keyword_kind: Kind,
    filter_read_only_type_operator: bool,
    program: &Rc<Program>,
) -> Option<Vec<Rc<RefCell<SymbolAndEntries>>>> {
    // references is a list of NodeEntry
    let mut references: Vec<Rc<RefCell<ReferenceEntry>>> = Vec::new();
    let keyword_text = tsc_scanner::scanner::token_to_string(keyword_kind);
    for &source_file in source_files {
        // cancellationToken.throwIfCancellationRequested();
        let possible = {
            let mut nodes = program.nodes_mut(source_file.file_index());
            tsc_checker::services::get_possible_symbol_reference_nodes(
                &mut nodes,
                source_file,
                keyword_text,
                Some(source_file),
            )
        };
        for reference_location in possible {
            let nodes = program.nodes(reference_location.file_index());
            if nodes[reference_location].kind == keyword_kind
                && (!filter_read_only_type_operator
                    || is_readonly_type_operator(reference_location, &nodes))
            {
                references.push(new_node_entry(reference_location, &nodes));
            }
        }
    }
    if references.is_empty() {
        return None;
    }
    let def_node = references[0].borrow().node;
    Some(vec![Rc::new(RefCell::new(new_symbol_and_entries(
        DefinitionKind::Keyword,
        def_node,
        None,
        references,
    )))])
}

/// `findFirstJsxNode` — recursively searches for the first JSX element,
/// self-closing element, or fragment.
fn find_first_jsx_node(root: NodeId, nodes: &[Node]) -> Option<NodeId> {
    fn visit(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
        // Check if this is a JSX node we're looking for
        match nodes[node].kind {
            Kind::JsxElement | Kind::JsxSelfClosingElement | Kind::JsxFragment => {
                return Some(node);
            }
            _ => {}
        }

        // Skip subtree if it doesn't contain JSX
        if nodes[node].subtree_facts(nodes) & ast::SubtreeFacts::CONTAINS_JSX
            == ast::SubtreeFacts::NONE
        {
            return None;
        }

        // Traverse children to find JSX node
        let mut result: Option<NodeId> = None;
        nodes[node].for_each_child(nodes, &mut |child| {
            result = visit(child, nodes);
            result.is_some() // Stop if found
        });
        result
    }
    visit(root, nodes)
}

/// `getMergedAliasedSymbolOfNamespaceExportDeclaration`.
fn get_merged_aliased_symbol_of_namespace_export_declaration(
    node: NodeId,
    symbol: SymbolId,
    checker: &Rc<RefCell<Checker>>,
    program: &Rc<Program>,
) -> Option<SymbolId> {
    let is_namespace_export_decl = {
        let nodes = program.nodes(node.file_index());
        nodes[node]
            .parent
            .is_some_and(|p| nodes[p].kind == Kind::NamespaceExportDeclaration)
    };
    if !is_namespace_export_decl {
        return None;
    }
    let mut c = checker.borrow_mut();
    let aliased_symbol = c.get_aliased_symbol(symbol)?;
    if aliased_symbol == c.unknown_symbol {
        return None;
    }
    let target_symbol = c.get_merged_symbol(aliased_symbol);
    if aliased_symbol != target_symbol {
        return Some(target_symbol);
    }
    None
}

/// `specialSearchKind`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SpecialSearchKind {
    /// `"none"`.
    None,
    /// `"constructor"`.
    Constructor,
    /// `"class"`.
    Class,
}

/// `getSpecialSearchKind`.
fn get_special_search_kind(node: Option<NodeId>, program: &Rc<Program>) -> SpecialSearchKind {
    let Some(node) = node else {
        return SpecialSearchKind::None;
    };
    let nodes = program.nodes(node.file_index());
    match nodes[node].kind {
        Kind::Constructor | Kind::ConstructorKeyword => SpecialSearchKind::Constructor,
        Kind::Identifier => {
            if nodes[node]
                .parent
                .is_some_and(|p| ast::is_class_like(Some(p), &nodes))
            {
                debug_assert!(nodes[nodes[node].parent.unwrap()].name() == Some(node));
                SpecialSearchKind::Class
            } else {
                SpecialSearchKind::None
            }
        }
        _ => SpecialSearchKind::None,
    }
}

/// `getReferencedSymbolsForSymbol` — core find-all-references algorithm for
/// a normal symbol.
fn get_referenced_symbols_for_symbol(
    ctx: &Context,
    program: &Rc<Program>,
    original_symbol: SymbolId,
    node: Option<NodeId>,
    source_files: &[NodeId],
    source_files_set: &Rc<Set<RootedFilePath>>,
    checker: &Rc<RefCell<Checker>>,
    options: RefOptions,
) -> Vec<Rc<RefCell<SymbolAndEntries>>> {
    let symbol = skip_past_export_or_import_specifier_or_union(
        original_symbol,
        node,
        checker,
        !is_for_rename_with_prefix_and_suffix_text(&options),
        program,
    )
    .unwrap_or(original_symbol);

    // Compute the meaning from the location and the symbol it references
    let mut search_meaning = ast::SemanticMeaning::ALL;
    if options.use_ != ReferenceUse::Rename {
        if let Some(node) = node {
            let mut nodes = program.nodes_mut(node.file_index());
            search_meaning = get_intersecting_meaning_from_declarations(
                &mut nodes,
                program,
                Some(node),
                symbol,
                ast::SemanticMeaning::ALL,
            );
        }
    }
    let state = RefState::new(
        ctx.clone(),
        program.clone(),
        source_files.to_vec(),
        source_files_set.clone(),
        node,
        checker.clone(),
        search_meaning,
        options,
    );

    let export_specifier = if is_for_rename_with_prefix_and_suffix_text(&options) {
        let declarations = checker.borrow().symbol_arena.borrow()[symbol.index()]
            .declarations
            .clone();
        declarations.iter().copied().find(|&d| {
            let nodes = program.nodes(d.file_index());
            ast::is_export_specifier(&nodes[d])
        })
    } else {
        None
    };
    if let Some(export_specifier) = export_specifier {
        // When renaming at an export specifier, rename the export and not the thing being exported.
        let (name, _specifier) = {
            let nodes = program.nodes(export_specifier.file_index());
            (
                nodes[export_specifier].name().unwrap_or(export_specifier),
                export_specifier,
            )
        };
        let search = state.create_search(
            node,
            original_symbol,
            ImpExpKind::Unknown,
            String::new(),
            None,
        );
        state.get_references_at_export_specifier(
            name,
            symbol,
            export_specifier,
            &search,
            true, /*addReferencesHere*/
            true, /*alwaysGetReferences*/
        );
    } else {
        let (node_is_default, symbol_is_default, symbol_parent) = {
            let n_kind = node.map(|n| {
                let nodes = program.nodes(n.file_index());
                nodes[n].kind
            });
            let arena = checker.borrow().symbol_arena.clone();
            let s = &arena.borrow()[symbol.index()];
            (
                n_kind == Some(Kind::DefaultKeyword),
                s.name.as_ref() == ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT,
                s.parent,
            )
        };
        if node.is_some() && node_is_default && symbol_is_default && symbol_parent.is_some() {
            state.add_reference(node.expect("node"), symbol, EntryKind::Node);
            state.search_for_imports_of_export(
                node.expect("node"),
                symbol,
                &ExportInfo {
                    exporting_module_symbol: symbol_parent.expect("parent"),
                    export_kind: ExportKind::Default,
                },
            );
        } else {
            let all_search_symbols = state.populate_search_symbol_set(
                symbol,
                node,
                options.use_ == ReferenceUse::Rename,
                options.use_aliases_for_rename,
                options.implementations,
            );
            let search = state.create_search(
                node,
                symbol,
                ImpExpKind::Unknown,
                String::new(),
                Some(all_search_symbols),
            );
            state.get_references_in_container_or_files(symbol, &search);
        }
    }

    std::mem::take(&mut *state.result.borrow_mut())
}

/// `inheritKey`.
type InheritKey = (SymbolId, SymbolId);

/// `refState`.
struct RefState {
    /// `sourceFiles`.
    source_files: Vec<NodeId>,
    /// `sourceFilesSet`.
    source_files_set: Rc<Set<RootedFilePath>>,
    /// `specialSearchKind` — "none", "constructor", or "class".
    special_search_kind: SpecialSearchKind,
    /// `checker`.
    checker: Rc<RefCell<Checker>>,
    /// `ctx`.
    ctx: Context,
    /// `program`.
    program: Rc<Program>,
    /// `searchMeaning`.
    search_meaning: ast::SemanticMeaning,
    /// `options`.
    options: RefOptions,
    /// `result`.
    result: RefCell<Vec<Rc<RefCell<SymbolAndEntries>>>>,
    /// `inheritsFromCache`.
    inherits_from_cache: RefCell<HashMap<InheritKey, bool>>,
    /// `seenContainingTypeReferences`.
    seen_containing_type_references: RefCell<Set<NodeId>>,
    /// `seenReExportRHS`.
    seen_re_export_rhs: RefCell<Set<NodeId>>,
    /// `importTracker`.
    import_tracker: RefCell<Option<ImportTracker>>,
    /// `symbolToReferences`.
    symbol_to_references: RefCell<HashMap<SymbolId, Rc<RefCell<SymbolAndEntries>>>>,
    /// `sourceFileToSeenSymbols`.
    source_file_to_seen_symbols: RefCell<HashMap<NodeId, Set<SymbolId>>>,
}

/// `refSearch` — symbol that is currently being searched for.
struct RefSearch {
    /// `comingFrom` — if coming from an export, we will not recursively
    /// search for the imported symbol (since that's where we came from).
    coming_from: ImpExpKind,
    /// `symbol`.
    symbol: SymbolId,
    /// `text`.
    text: String,
    /// `escapedText`.
    escaped_text: String,
    /// `parents` — only set if `options.implementations` is true.
    parents: Vec<SymbolId>,
    /// `allSearchSymbols`.
    all_search_symbols: Rc<Vec<SymbolId>>,
}

impl RefSearch {
    /// `includes` — whether a symbol is in the search set.
    /// Do not compare directly to `symbol` because there may be related
    /// symbols to search for. See `populateSearchSymbolSet`.
    fn includes(&self, sym: SymbolId) -> bool {
        self.all_search_symbols.contains(&sym)
    }
}

impl RefState {
    /// `newState`.
    fn new(
        ctx: Context,
        program: Rc<Program>,
        source_files: Vec<NodeId>,
        source_files_set: Rc<Set<RootedFilePath>>,
        node: Option<NodeId>,
        checker: Rc<RefCell<Checker>>,
        search_meaning: ast::SemanticMeaning,
        options: RefOptions,
    ) -> RefState {
        RefState {
            special_search_kind: get_special_search_kind(node, &program),
            source_files,
            source_files_set,
            checker,
            ctx,
            program,
            search_meaning,
            options,
            result: RefCell::new(Vec::new()),
            inherits_from_cache: RefCell::new(HashMap::new()),
            seen_containing_type_references: RefCell::new(Set::new()),
            seen_re_export_rhs: RefCell::new(Set::new()),
            import_tracker: RefCell::new(None),
            symbol_to_references: RefCell::new(HashMap::new()),
            source_file_to_seen_symbols: RefCell::new(HashMap::new()),
        }
    }

    /// `includesSourceFile`.
    fn includes_source_file(&self, source_file: NodeId) -> bool {
        let nodes = self.program.nodes(source_file.file_index());
        self.source_files_set
            .has(nodes[source_file].as_source_file().file_name())
    }

    /// `getImportSearches`.
    fn get_import_searches(
        &self,
        export_symbol: SymbolId,
        export_info: &ExportInfo,
    ) -> Rc<crate::import_tracker::ImportsResult> {
        {
            let mut tracker = self.import_tracker.borrow_mut();
            if tracker.is_none() {
                *tracker = Some(create_import_tracker(
                    self.ctx.clone(),
                    self.program.clone(),
                    self.source_files.clone(),
                    (*self.source_files_set).clone(),
                    self.checker.clone(),
                ));
            }
        }
        let mut tracker = self.import_tracker.borrow_mut();
        tracker.as_mut().expect("import tracker")(
            export_symbol,
            export_info,
            self.options.use_ == ReferenceUse::Rename,
        )
    }

    /// `createSearch` — `allSearchSymbols` is the set of additional symbols
    /// for use by `includes`.
    fn create_search(
        &self,
        location: Option<NodeId>,
        symbol: SymbolId,
        coming_from: ImpExpKind,
        text: String,
        all_search_symbols: Option<Vec<SymbolId>>,
    ) -> RefSearch {
        // Note: if this is an external module symbol, the name doesn't include quotes.
        // Note: getLocalSymbolForExportDefault handles `export default class C {}`, but not `export default C` or `export { C as default }`.
        // The other two forms seem to be handled downstream (e.g. in `skipPastExportOrImportSpecifier`), so special-casing the first form
        // here appears to be intentional).
        let mut text = text;
        if text.is_empty() {
            let s = {
                let symbols = self.checker.borrow().symbol_arena.clone();
                let decls = symbols.borrow()[symbol.index()].declarations.clone();
                let nodes = decls
                    .first()
                    .map(|d| self.program.nodes(d.file_index()));
                let local = nodes.as_deref().and_then(|nodes| {
                    tsc_binder::nameresolver::get_local_symbol_for_export_default(
                        symbol,
                        nodes,
                        &symbols.borrow(),
                    )
                });
                local.or_else(|| {
                    let decls2 = symbols.borrow()[symbol.index()].declarations.clone();
                    let nodes2 = decls2
                        .first()
                        .map(|d| self.program.nodes(d.file_index()));
                    nodes2.as_deref().and_then(|_nodes| {
                        get_non_module_symbol_of_merged_module_symbol(&self.program, symbol)
                    })
                })
            };
            let s = s.unwrap_or(symbol);
            let symbol_name = {
                let symbols = self.checker.borrow().symbol_arena.clone();
                let decls = symbols.borrow()[s.index()].declarations.clone();
                let nodes = decls
                    .first()
                    .map(|d| self.program.nodes(d.file_index()));
                match nodes {
                    Some(nodes) => {
                        ast::symbol_name(&symbols.borrow()[s.index()], &nodes).into_owned()
                    }
                    None => symbols.borrow()[s.index()].name.to_string(),
                }
            };
            text = ast::try_get_ambient_module_name_from_symbol_name(&symbol_name)
                .unwrap_or(symbol_name);
        }
        let all_search_symbols = all_search_symbols.unwrap_or_else(|| vec![symbol]);
        let mut parents: Vec<SymbolId> = Vec::new();
        if self.options.implementations {
            if let Some(location) = location {
                let mut c = self.checker.borrow_mut();
                parents = get_parent_symbols_of_property_access(location, symbol, &mut c);
            }
        }
        RefSearch {
            coming_from,
            symbol,
            escaped_text: text.clone(),
            text,
            parents,
            all_search_symbols: Rc::new(all_search_symbols),
        }
    }

    /// `addReference`.
    fn add_reference(&self, reference_location: NodeId, symbol: SymbolId, kind: EntryKind) {
        // if rename symbol from default export anonymous function, for example `export default function() {}`, we do not need to add reference
        if self.options.use_ == ReferenceUse::Rename {
            let kind_is_default = {
                let nodes = self.program.nodes(reference_location.file_index());
                nodes[reference_location].kind == Kind::DefaultKeyword
            };
            if kind_is_default {
                return;
            }
        }

        let mut add_ref = self.reference_adder_nodes(symbol);
        if self.options.implementations {
            self.add_implementation_references(reference_location, &mut |n| {
                add_ref(n, kind)
            });
        } else {
            add_ref(reference_location, kind);
        }
    }

    /// `referenceAdder` variant that knows how to fetch the right arena for
    /// each node (entry creation needs `nodes`).
    fn reference_adder_nodes(
        &self,
        search_symbol: SymbolId,
    ) -> impl FnMut(NodeId, EntryKind) + '_ {
        let symbol_and_entries = {
            let mut map = self.symbol_to_references.borrow_mut();
            match map.get(&search_symbol) {
                Some(existing) => existing.clone(),
                None => {
                    let entry = Rc::new(RefCell::new(new_symbol_and_entries(
                        DefinitionKind::Symbol,
                        None,
                        Some(search_symbol),
                        Vec::new(),
                    )));
                    map.insert(search_symbol, entry.clone());
                    self.result.borrow_mut().push(entry.clone());
                    entry
                }
            }
        };
        move |node: NodeId, kind: EntryKind| {
            let nodes = self.program.nodes(node.file_index());
            symbol_and_entries
                .borrow_mut()
                .references
                .push(new_node_entry_with_kind(node, kind, &nodes));
        }
    }

    /// `addImplementationReferences`.
    fn add_implementation_references(
        &self,
        ref_node: NodeId,
        add_ref: &mut dyn FnMut(NodeId),
    ) {
        // Check if we found a function/propertyAssignment/method with an implementation or initializer
        {
            let nodes = self.program.nodes(ref_node.file_index());
            if ast::is_declaration_name(ref_node, &nodes)
                && nodes[ref_node]
                    .parent
                    .is_some_and(|p| is_implementation(p, &nodes))
            {
                add_ref(ref_node);
                return;
            }
        }

        {
            let nodes = self.program.nodes(ref_node.file_index());
            if nodes[ref_node].kind != Kind::Identifier {
                return;
            }
        }

        {
            let nodes = self.program.nodes(ref_node.file_index());
            if nodes[ref_node]
                .parent
                .is_some_and(|p| nodes[p].kind == Kind::ShorthandPropertyAssignment)
            {
                // Go ahead and dereference the shorthand assignment by going to its definition
                drop(nodes);
                get_reference_entries_for_shorthand_property_assignment(
                    ref_node,
                    &self.checker,
                    add_ref,
                    &self.program,
                );
            }
        }

        // Check if the node is within an extends or implements clause
        let containing_node = {
            let nodes = self.program.nodes(ref_node.file_index());
            get_containing_node_if_in_heritage_clause(ref_node, &nodes)
        };
        if let Some(containing_node) = containing_node {
            add_ref(containing_node);
            return;
        }

        // If we got a type reference, try and see if the reference applies to any expressions that can implement an interface
        // Find the first node whose parent isn't a type node -- i.e., the highest type node.
        let type_node = {
            let nodes = self.program.nodes(ref_node.file_index());
            ast::find_ancestor(Some(ref_node), &nodes, &mut |n, ns| {
                !n.parent.is_some_and(|p| ast::is_qualified_name(&ns[p]))
                    && !n.parent.is_some_and(|p| ast::is_type_node(&ns[p]))
                    && !n.parent.is_some_and(|p| ast::is_type_element(&ns[p]))
            })
        };

        let Some(type_node) = type_node else {
            return;
        };
        {
            let nodes = self.program.nodes(type_node.file_index());
            let Some(parent) = nodes[type_node].parent else {
                return;
            };
            if nodes[parent].type_() != Some(type_node) {
                return;
            }
        }

        let type_having_node = {
            let nodes = self.program.nodes(type_node.file_index());
            nodes[type_node].parent.expect("type having node")
        };
        if !self
            .seen_containing_type_references
            .borrow_mut()
            .add_if_absent(type_having_node)
        {
            return;
        }
        let nodes = self.program.nodes(type_having_node.file_index());
        let mut add_if_implementation = |e: Option<NodeId>| {
            if let Some(e) = e {
                if is_implementation_expression(e, &nodes) {
                    add_ref(e);
                }
            }
        };
        if ast::has_initializer(&nodes[type_having_node]) {
            add_if_implementation(nodes[type_having_node].initializer());
        } else if ast::is_function_like(Some(type_having_node), &nodes)
            && nodes[type_having_node].body().is_some()
        {
            let body = nodes[type_having_node].body().expect("body");
            if nodes[body].kind == Kind::Block {
                ast::for_each_return_statement(&nodes, body, &mut |return_statement| {
                    add_if_implementation(nodes[return_statement].expression());
                    false
                });
            } else {
                add_if_implementation(Some(body));
            }
        } else if ast::is_assertion_expression(&nodes[type_having_node])
            || ast::is_satisfies_expression(&nodes[type_having_node])
        {
            add_if_implementation(nodes[type_having_node].expression());
        }
    }

    /// `getReferencesInContainerOrFiles`.
    fn get_references_in_container_or_files(&self, symbol: SymbolId, search: &RefSearch) {
        // Try to get the smallest valid scope that we can limit our search to;
        // otherwise we'll need to search globally (i.e. include each file).
        if let Some(scope) = get_symbol_scope(symbol, &self.checker, &self.program) {
            let add_references_here = {
                let nodes = self.program.nodes(scope.file_index());
                nodes[scope].kind != Kind::SourceFile
                    || self.source_files.contains(&scope)
            };
            let source_file = {
                let nodes = self.program.nodes(scope.file_index());
                ast::get_source_file_of_node(Some(scope), &nodes).expect("source file")
            };
            self.get_references_in_container(scope, source_file, search, add_references_here);
        } else {
            // Global search
            for &source_file in &self.source_files {
                // state.cancellationToken.throwIfCancellationRequested();
                self.search_for_name(source_file, search);
            }
        }
    }

    /// `getReferencesInSourceFile`.
    fn get_references_in_source_file(
        &self,
        source_file: NodeId,
        search: &RefSearch,
        add_references_here: bool,
    ) {
        // state.cancellationToken.throwIfCancellationRequested();
        self.get_references_in_container(source_file, source_file, search, add_references_here);
    }

    /// `getReferencesInContainer`.
    fn get_references_in_container(
        &self,
        container: NodeId,
        source_file: NodeId,
        search: &RefSearch,
        add_references_here: bool,
    ) {
        // Search within node "container" for references for a search value, where the search value is defined as a
        //     tuple of (searchSymbol, searchText, searchLocation, and searchMeaning).
        // searchLocation: a node where the search value
        if !self.mark_searched_symbols(source_file, &search.all_search_symbols) {
            return;
        }

        let positions = {
            let nodes = self.program.nodes(source_file.file_index());
            tsc_checker::services::get_possible_symbol_reference_positions(
                &nodes,
                source_file,
                &search.text,
                Some(container),
            )
        };
        for position in positions {
            self.get_references_at_location(source_file, position, search, add_references_here);
        }
    }

    /// `markSearchedSymbols`.
    fn mark_searched_symbols(&self, source_file: NodeId, symbols: &[SymbolId]) -> bool {
        let mut map = self.source_file_to_seen_symbols.borrow_mut();
        let seen_symbols = map.entry(source_file).or_default();
        let mut any_new_symbols = false;
        for &sym in symbols {
            if seen_symbols.add_if_absent(sym) {
                any_new_symbols = true;
            }
        }
        any_new_symbols
    }

    /// `getReferencesAtLocation`.
    fn get_references_at_location(
        &self,
        source_file: NodeId,
        position: i32,
        search: &RefSearch,
        add_references_here: bool,
    ) {
        let reference_location = {
            let mut nodes = self.program.nodes_mut(source_file.file_index());
            tokens::get_touching_property_name(&mut nodes, source_file, position)
                .unwrap_or(source_file)
        };

        {
            let nodes = self.program.nodes(source_file.file_index());
            if !is_valid_reference_position(reference_location, &search.text, &nodes) {
                // This wasn't the start of a token.  Check to see if it might be a
                // match in a comment or string if that's what the caller is asking
                // for.

                // !!! not implemented
                // if (!state.options.implementations && (state.options.findInStrings && isInString(sourceFile, position) || state.options.findInComments && isInNonReferenceComment(sourceFile, position))) {
                // 	// In the case where we're looking inside comments/strings, we don't have
                // 	// an actual definition.  So just use 'undefined' here.  Features like
                // 	// 'Rename' won't care (as they ignore the definitions), and features like
                // 	// 'FindReferences' will just filter out these results.
                // 	state.addStringOrCommentReference(sourceFile.FileName, createTextSpan(position, search.text.length));
                // }

                return;
            }
        }

        {
            let mut nodes = self.program.nodes_mut(source_file.file_index());
            if get_meaning_from_location(&mut nodes, reference_location) & self.search_meaning
                == ast::SemanticMeaning::NONE
            {
                return;
            }
        }

        let Some(reference_symbol) = self
            .checker
            .borrow_mut()
            .get_symbol_at_location_api(reference_location)
        else {
            return;
        };

        {
            let nodes = self.program.nodes(source_file.file_index());
            let parent = nodes[reference_location].parent;
            if parent.is_some_and(|p| {
                nodes[p].kind == Kind::ImportSpecifier
                    && nodes[p].property_name() == Some(reference_location)
            }) {
                // This is added through `singleReferences` in ImportsResult. If we happen to see it again, don't add it again.
                return;
            }

            if parent.is_some_and(|p| nodes[p].kind == Kind::ExportSpecifier) {
                self.get_references_at_export_specifier(
                    reference_location,
                    reference_symbol,
                    parent.expect("parent"),
                    search,
                    add_references_here,
                    false, /*alwaysGetReferences*/
                );
                return;
            }
        }

        let (related_symbol, related_symbol_kind) =
            self.get_related_symbol(search, reference_symbol, reference_location);
        if related_symbol.is_none() {
            self.get_reference_for_shorthand_property(reference_symbol, search);
            return;
        }
        let related_symbol = related_symbol.expect("related symbol");

        match self.special_search_kind {
            SpecialSearchKind::None => {
                if add_references_here {
                    self.add_reference(reference_location, related_symbol, related_symbol_kind);
                }
            }
            SpecialSearchKind::Constructor => {
                self.add_constructor_references(
                    reference_location,
                    related_symbol,
                    search,
                    add_references_here,
                );
            }
            SpecialSearchKind::Class => {
                self.add_class_static_this_references(
                    reference_location,
                    related_symbol,
                    search,
                    add_references_here,
                );
            }
        }

        // Use the parent symbol if the location is commonjs require syntax on javascript files only.
        let mut reference_symbol = reference_symbol;
        {
            let nodes = self.program.nodes(source_file.file_index());
            if ast::is_in_js_file(Some(reference_location), &nodes)
                && nodes[reference_location]
                    .parent
                    .is_some_and(|p| nodes[p].kind == Kind::BindingElement)
                && nodes[reference_location]
                    .parent
                    .and_then(|p| nodes[p].parent)
                    .and_then(|p| nodes[p].parent)
                    .is_some_and(|gp| {
                        ast::is_variable_declaration_initialized_to_bare_or_accessed_require(
                            gp, &nodes,
                        )
                    })
            {
                // The parent will not have a symbol if it's an ObjectBindingPattern (when destructuring is used).  In
                // this case, just skip it, since the bound identifiers are not an alias of the import.
                let Some(parent) = nodes[reference_location].parent else {
                    return;
                };
                let Some(sym) = nodes[parent].symbol() else {
                    return;
                };
                reference_symbol = sym;
            }
        }

        self.get_import_or_export_references(reference_location, reference_symbol, search);
    }

    /// `addConstructorReferences`.
    fn add_constructor_references(
        &self,
        reference_location: NodeId,
        symbol: SymbolId,
        search: &RefSearch,
        add_references_here: bool,
    ) {
        {
            let nodes = self.program.nodes(reference_location.file_index());
            if ast::is_new_expression_target(reference_location, false, false, &nodes)
                && add_references_here
            {
                drop(nodes);
                self.add_reference(reference_location, symbol, EntryKind::Node);
            }
        }

        let class_like_parent = {
            let nodes = self.program.nodes(reference_location.file_index());
            nodes[reference_location]
                .parent
                .filter(|p| ast::is_class_like(Some(*p), &nodes))
        };
        if let Some(_class_like) = class_like_parent {
            // This is the class declaration containing the constructor.
            let source_file = {
                let nodes = self.program.nodes(reference_location.file_index());
                ast::get_source_file_of_node(Some(reference_location), &nodes)
                    .expect("source file")
            };
            find_own_constructor_references(
                search.symbol,
                source_file,
                &mut |n| {
                    self.reference_adder_nodes(search.symbol)(n, EntryKind::Node)
                },
                &self.checker,
                &self.program,
            );
        } else {
            // If this class appears in `extends C`, then the extending class' "super" calls are references.
            let class_extending = {
                let nodes = self.program.nodes(reference_location.file_index());
                try_get_class_by_extending_identifier(reference_location, &nodes)
            };
            if let Some(class_extending) = class_extending {
                find_super_constructor_accesses(
                    class_extending,
                    &mut |n| {
                        self.reference_adder_nodes(search.symbol)(n, EntryKind::Node)
                    },
                    &self.program,
                    &self.checker,
                );
                self.find_inherited_constructor_references(class_extending);
            }
        }
    }

    /// `addClassStaticThisReferences`.
    fn add_class_static_this_references(
        &self,
        reference_location: NodeId,
        symbol: SymbolId,
        search: &RefSearch,
        add_references_here: bool,
    ) {
        if add_references_here {
            self.add_reference(reference_location, symbol, EntryKind::Node);
        }

        let class_like = {
            let nodes = self.program.nodes(reference_location.file_index());
            nodes[reference_location].parent
        };
        let Some(class_like) = class_like else {
            return;
        };
        {
            let nodes = self.program.nodes(class_like.file_index());
            if self.options.use_ == ReferenceUse::Rename
                || !ast::is_class_like(Some(class_like), &nodes)
            {
                return;
            }
        }

        let members = {
            let nodes = self.program.nodes(class_like.file_index());
            nodes[class_like].members().map(|m| m.to_vec())
        };
        let Some(members) = members else {
            return;
        };
        let mut add_ref = self.reference_adder_nodes(search.symbol);
        for member in members {
            {
                let nodes = self.program.nodes(member.file_index());
                if !(is_method_or_accessor(&nodes[member])
                    && ast::has_static_modifier(&nodes[member]))
                {
                    continue;
                }
            }
            let body = {
                let nodes = self.program.nodes(member.file_index());
                nodes[member].body()
            };
            if let Some(body) = body {
                let nodes = self.program.nodes(body.file_index());
                for_each_this_keyword_without_function_or_class(body, &nodes, &mut |n| {
                    add_ref(n, EntryKind::Node)
                });
            }
        }
    }

    /// `findInheritedConstructorReferences`.
    fn find_inherited_constructor_references(&self, class_declaration: NodeId) {
        {
            let nodes = self.program.nodes(class_declaration.file_index());
            if has_own_constructor(nodes[class_declaration].symbol(), &self.checker) {
                return;
            }
        }
        let class_symbol = {
            let nodes = self.program.nodes(class_declaration.file_index());
            nodes[class_declaration].symbol()
        };
        let Some(class_symbol) = class_symbol else {
            return;
        };
        let search = self.create_search(
            None,
            class_symbol,
            ImpExpKind::Unknown,
            String::new(),
            None,
        );
        self.get_references_in_container_or_files(class_symbol, &search);
    }

    /// `getImportOrExportReferences`.
    fn get_import_or_export_references(
        &self,
        reference_location: NodeId,
        reference_symbol: SymbolId,
        search: &RefSearch,
    ) {
        let import_or_export = {
            let mut c = self.checker.borrow_mut();
            get_import_or_export_symbol(
                &self.program,
                reference_location,
                reference_symbol,
                &mut c,
                search.coming_from == ImpExpKind::Export,
            )
        };
        let Some(import_or_export) = import_or_export else {
            return;
        };
        if import_or_export.kind == ImpExpKind::Import {
            if !is_for_rename_with_prefix_and_suffix_text(&self.options) {
                self.search_for_imported_symbol(import_or_export.symbol);
            }
        } else {
            self.search_for_imports_of_export(
                reference_location,
                import_or_export.symbol,
                import_or_export.export_info.as_ref().expect("export info"),
            );
        }
    }

    /// `markSeenReExportRHS`.
    fn mark_seen_re_export_rhs(&self, node: NodeId) -> bool {
        self.seen_re_export_rhs.borrow_mut().add_if_absent(node)
    }

    /// `getReferencesAtExportSpecifier`.
    #[allow(clippy::too_many_arguments)]
    fn get_references_at_export_specifier(
        &self,
        reference_location: NodeId,
        reference_symbol: SymbolId,
        export_specifier: NodeId,
        search: &RefSearch,
        add_references_here: bool,
        always_get_references: bool,
    ) {
        debug_assert!(
            !always_get_references || self.options.use_aliases_for_rename,
            "If alwaysGetReferences is true, then prefix/suffix text must be enabled"
        );

        let (property_name, name, export_declaration_module_specifier) = {
            let nodes = self.program.nodes(export_specifier.file_index());
            let export_declaration = nodes[export_specifier]
                .parent
                .and_then(|p| nodes[p].parent)
                .expect("export declaration");
            (
                nodes[export_specifier].as_export_specifier().property_name,
                nodes[export_specifier].name().expect("export specifier name"),
                nodes[export_declaration].module_specifier(),
            )
        };
        let local_symbol = {
            let nodes = self.program.nodes(export_specifier.file_index());
            let mut c = self.checker.borrow_mut();
            get_local_symbol_for_export_specifier(
                &nodes,
                reference_location,
                Some(reference_symbol),
                export_specifier,
                &mut c,
            )
        };
        let Some(local_symbol) = local_symbol else {
            return;
        };

        if !always_get_references && !search.includes(local_symbol) {
            return;
        }

        let add_ref = || {
            if add_references_here {
                self.add_reference(reference_location, local_symbol, EntryKind::Node);
            }
        };

        if property_name.is_none() {
            // Don't rename at `export { default } from "m";`. (but do continue to search for imports of the re-export)
            let nodes = self.program.nodes(reference_location.file_index());
            let name_is_default = ast::module_export_name_is_default(&nodes[name], &nodes);
            drop(nodes);
            if !(self.options.use_ == ReferenceUse::Rename && name_is_default) {
                add_ref();
            }
        } else if property_name == Some(reference_location) {
            // For `export { foo as bar } from "baz"`, "`foo`" will be added from the singleReferences for import searches of the original export.
            // For `export { foo as bar };`, where `foo` is a local, so add it now.
            if export_declaration_module_specifier.is_none() {
                add_ref();
            }

            if add_references_here
                && self.options.use_ != ReferenceUse::Rename
                && self.mark_seen_re_export_rhs(name)
            {
                let export_symbol = {
                    let nodes = self.program.nodes(export_specifier.file_index());
                    nodes[export_specifier].symbol().expect("exportSpecifier.Symbol() should not be nil")
                };
                self.add_reference(name, export_symbol, EntryKind::Node);
            }
        } else if self.mark_seen_re_export_rhs(reference_location) {
            add_ref();
        }

        // For `export { foo as bar }`, rename `foo`, but not `bar`.
        if !is_for_rename_with_prefix_and_suffix_text(&self.options) || always_get_references {
            let (is_default_export, export_symbol) = {
                let nodes = self.program.nodes(export_specifier.file_index());
                (
                    ast::module_export_name_is_default(&nodes[reference_location], &nodes)
                        || nodes[export_specifier]
                            .name()
                            .is_some_and(|n| ast::module_export_name_is_default(&nodes[n], &nodes)),
                    nodes[export_specifier].symbol().expect("exportSpecifier.Symbol() should not be nil"),
                )
            };
            let export_kind = if is_default_export {
                ExportKind::Default
            } else {
                ExportKind::Named
            };
            let export_info = {
                let mut c = self.checker.borrow_mut();
                get_export_info(export_symbol, export_kind, &mut c)
            };
            if let Some(export_info) = export_info {
                self.search_for_imports_of_export(reference_location, export_symbol, &export_info);
            }
        }

        // At `export { x } from "foo"`, also search for the imported symbol `"foo".x`.
        if search.coming_from != ImpExpKind::Export
            && export_declaration_module_specifier.is_some()
            && property_name.is_none()
            && !is_for_rename_with_prefix_and_suffix_text(&self.options)
        {
            let imported = self
                .checker
                .borrow_mut()
                .get_export_specifier_local_target_symbol(export_specifier);
            if let Some(imported) = imported {
                self.search_for_imported_symbol(imported);
            }
        }
    }

    /// `searchForImportedSymbol` — go to the symbol we imported from and find
    /// references for it.
    fn search_for_imported_symbol(&self, symbol: SymbolId) {
        let declarations = self.checker.borrow().symbol_arena.borrow()[symbol.index()]
            .declarations
            .clone();
        for declaration in declarations {
            let exporting_file = {
                let nodes = self.program.nodes(declaration.file_index());
                ast::get_source_file_of_node(Some(declaration), &nodes).expect("exporting file")
            };
            // Need to search in the file even if it's not in the search-file set, because it might export the symbol.
            let search =
                self.create_search(Some(declaration), symbol, ImpExpKind::Import, String::new(), None);
            self.get_references_in_source_file(
                exporting_file,
                &search,
                self.includes_source_file(exporting_file),
            );
        }
    }

    /// `searchForImportsOfExport` — search for all imports of a given
    /// exported symbol using `State.getImportSearches`.
    fn search_for_imports_of_export(
        &self,
        export_location: NodeId,
        export_symbol: SymbolId,
        export_info: &ExportInfo,
    ) {
        let r = self.get_import_searches(export_symbol, export_info);

        // For `import { foo as bar }` just add the reference to `foo`, and don't otherwise search in the file.
        if !r.single_references.is_empty() {
            let mut add_ref = self.reference_adder_nodes(export_symbol);
            for &single_ref in &r.single_references {
                if self.should_add_single_reference(single_ref) {
                    add_ref(single_ref, EntryKind::Node);
                }
            }
        }

        // For each import, find all references to that import in its source file.
        for i in &r.import_searches {
            let importing_file = {
                let nodes = self.program.nodes(i.import_location.file_index());
                ast::get_source_file_of_node(Some(i.import_location), &nodes)
                    .expect("importing file")
            };
            let search = self.create_search(
                Some(i.import_location),
                i.import_symbol.expect("import symbol"),
                ImpExpKind::Export,
                String::new(),
                None,
            );
            self.get_references_in_source_file(importing_file, &search, true);
        }

        if !r.indirect_users.is_empty() {
            let indirect_search: Option<RefSearch> = match export_info.export_kind {
                ExportKind::Named => Some(self.create_search(
                    Some(export_location),
                    export_symbol,
                    ImpExpKind::Export,
                    String::new(),
                    None,
                )),
                ExportKind::Default => {
                    // Search for a property access to '.default'. This can't be renamed.
                    if self.options.use_ != ReferenceUse::Rename {
                        Some(self.create_search(
                            Some(export_location),
                            export_symbol,
                            ImpExpKind::Export,
                            "default".to_string(),
                            None,
                        ))
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(indirect_search) = indirect_search {
                for &indirect_user in &r.indirect_users {
                    self.search_for_name(indirect_user, &indirect_search);
                }
            }
        }
    }

    /// `shouldAddSingleReference`.
    fn should_add_single_reference(&self, single_ref: NodeId) -> bool {
        if !self.has_matching_meaning(single_ref) {
            return false;
        }
        if self.options.use_ != ReferenceUse::Rename {
            return true;
        }
        let nodes = self.program.nodes(single_ref.file_index());
        // Don't rename an import type `import("./module-name")` when renaming `name` in `export = name;`
        if !ast::is_identifier(&nodes[single_ref])
            && !nodes[single_ref]
                .parent
                .is_some_and(|p| ast::is_import_or_export_specifier(&nodes[p]))
        {
            return false;
        }
        // At `default` in `import { default as x }` or `export { default as x }`, do add a reference, but do not rename.
        !(nodes[single_ref]
            .parent
            .is_some_and(|p| ast::is_import_or_export_specifier(&nodes[p]))
            && ast::module_export_name_is_default(&nodes[single_ref], &nodes))
    }

    /// `hasMatchingMeaning`.
    fn has_matching_meaning(&self, reference_location: NodeId) -> bool {
        let mut nodes = self.program.nodes_mut(reference_location.file_index());
        get_meaning_from_location(&mut nodes, reference_location) & self.search_meaning
            != ast::SemanticMeaning::NONE
    }

    /// `getReferenceForShorthandProperty`.
    fn get_reference_for_shorthand_property(&self, reference_symbol: SymbolId, search: &RefSearch) {
        let (flags, value_declaration) = {
            let arena = self.checker.borrow().symbol_arena.clone();
            let s = &arena.borrow()[reference_symbol.index()];
            (s.flags, s.value_declaration)
        };
        if flags & SymbolFlags::TRANSIENT != SymbolFlags::NONE || value_declaration.is_none() {
            return;
        }
        let value_declaration = value_declaration.expect("value declaration");
        let shorthand_value_symbol = self
            .checker
            .borrow_mut()
            .get_shorthand_assignment_value_symbol(Some(value_declaration));
        let name = {
            let nodes = self.program.nodes(value_declaration.file_index());
            ast::get_name_of_declaration(Some(value_declaration), &nodes)
        };

        // Because in short-hand property assignment, an identifier which stored as name of the short-hand property assignment
        // has two meanings: property name and property value. Therefore when we do findAllReference at the position where
        // an identifier is declared, the language service should return the position of the variable declaration as well as
        // the position in short-hand property assignment excluding property accessing. However, if we do findAllReference at the
        // position of property accessing, the referenceEntry of such position will be handled in the first case.
        if let (Some(name), Some(shorthand_value_symbol)) = (name, shorthand_value_symbol) {
            if search.includes(shorthand_value_symbol) {
                self.add_reference(name, shorthand_value_symbol, EntryKind::Node);
            }
        }
    }

    // === search ===

    /// `populateSearchSymbolSet`.
    fn populate_search_symbol_set(
        &self,
        symbol: SymbolId,
        location: Option<NodeId>,
        is_for_rename: bool,
        provide_prefix_and_suffix_text: bool,
        implementations: bool,
    ) -> Vec<SymbolId> {
        let Some(location) = location else {
            return vec![symbol];
        };
        let result: RefCell<Vec<SymbolId>> = RefCell::new(Vec::new());
        self.for_each_related_symbol(
            symbol,
            location,
            is_for_rename,
            !(is_for_rename && provide_prefix_and_suffix_text),
            &mut |sym, root, base| {
                // static method/property and instance method/property might have the same name. Only include static or only include instance.
                let mut base = base;
                if let Some(b) = base {
                    if is_static_symbol(&self.program, symbol) != is_static_symbol(&self.program, b) {
                        base = None;
                    }
                }
                result
                    .borrow_mut()
                    .push(base.or(root).unwrap_or(sym));
                None
            },
            // when try to find implementation, implementations is true, and not allowed to find base class
            &mut |_| !implementations,
        );
        result.into_inner()
    }

    /// `getRelatedSymbol`.
    fn get_related_symbol(
        &self,
        search: &RefSearch,
        reference_symbol: SymbolId,
        reference_location: NodeId,
    ) -> (Option<SymbolId>, EntryKind) {
        self.for_each_related_symbol(
            reference_symbol,
            reference_location,
            false, /*isForRenamePopulateSearchSymbolSet*/
            self.options.use_ != ReferenceUse::Rename || self.options.use_aliases_for_rename,
            &mut |sym, root_symbol, base_symbol| {
                // check whether the symbol used to search itself is just the searched one.
                let mut base_symbol = base_symbol;
                if let Some(b) = base_symbol {
                    // static method/property and instance method/property might have the same name. Only check static or only check instance.
                    if is_static_symbol(&self.program, reference_symbol)
                        != is_static_symbol(&self.program, b)
                    {
                        base_symbol = None;
                    }
                }
                let search_sym = base_symbol.or(root_symbol).or(Some(sym));
                if let Some(search_sym) = search_sym {
                    if search.includes(search_sym) {
                        if root_symbol.is_some() {
                            let check_flags = self
                                .checker
                                .borrow()
                                .symbol_arena
                                .borrow()[sym.index()]
                            .check_flags;
                            if check_flags & CheckFlags::SYNTHETIC
                                == CheckFlags::NONE
                            {
                                return root_symbol;
                            }
                        }
                        return Some(sym);
                    }
                }
                // For a base type, use the symbol for the derived type. For a synthetic (e.g. union) property, use the union symbol.
                None
            },
            &mut |root_symbol| {
                !( !search.parents.is_empty() && {
                    let root_parent = self
                        .checker
                        .borrow()
                        .symbol_arena
                        .borrow()[root_symbol.index()]
                    .parent;
                    !search.parents.iter().any(|&parent| {
                        root_parent.is_some_and(|rp| self.explicitly_inherits_from(rp, parent))
                    })
                })
            },
        )
    }

    /// `forEachRelatedSymbol`.
    fn for_each_related_symbol(
        &self,
        symbol: SymbolId,
        location: NodeId,
        is_for_rename_populate_search_symbol_set: bool,
        only_include_binding_element_at_reference_location: bool,
        cb_symbol: &mut dyn FnMut(SymbolId, Option<SymbolId>, Option<SymbolId>) -> Option<SymbolId>,
        allow_base_types: &mut dyn FnMut(SymbolId) -> bool,
    ) -> (Option<SymbolId>, EntryKind) {
        let mut from_root = |state: &RefState,
                        sym: SymbolId,
                        cb_symbol: &mut dyn FnMut(
            SymbolId,
            Option<SymbolId>,
            Option<SymbolId>,
        ) -> Option<SymbolId>|
         -> Option<SymbolId> {
            // If this is a union property:
            //   - In populateSearchSymbolsSet we will add all the symbols from all its source symbols in all unioned types.
            //   - In findRelatedSymbol, we will just use the union symbol if any source symbol is included in the search.
            // If the symbol is an instantiation from a another symbol (e.g. widened symbol):
            //   - In populateSearchSymbolsSet, add the root the list
            //   - In findRelatedSymbol, return the source symbol if that is in the search. (Do not return the instantiation symbol.)
            let root_symbols = state.checker.borrow_mut().get_root_symbols(sym);
            for root_symbol in root_symbols {
                if let Some(result) = cb_symbol(sym, Some(root_symbol), None) {
                    return Some(result);
                }
                // Add symbol of properties/methods of the same name in base classes and implemented interfaces definitions
                let (root_parent, root_name, root_parent_flags) = {
                    let arena = state.checker.borrow().symbol_arena.clone();
                    let rp = arena.borrow()[root_symbol.index()].parent;
                    let name = arena.borrow()[root_symbol.index()].name.clone();
                    let flags = rp
                        .map(|p| arena.borrow()[p.index()].flags)
                        .unwrap_or(SymbolFlags::NONE);
                    (rp, name, flags)
                };
                if let Some(root_parent) = root_parent {
                    if root_parent_flags & (SymbolFlags::CLASS | SymbolFlags::INTERFACE)
                        != SymbolFlags::NONE
                        && allow_base_types(root_symbol)
                    {
                        let result = {
                            let mut c = state.checker.borrow_mut();
                            get_property_symbols_from_base_types(
                                root_parent,
                                &root_name,
                                &mut c,
                                &mut |base| cb_symbol(sym, Some(root_symbol), Some(base)),
                            )
                        };
                        if result.is_some() {
                            return result;
                        }
                    }
                }
            }
            None
        };

        let containing_object_literal_element = {
            let nodes = self.program.nodes(location.file_index());
            get_containing_object_literal_element(location, &nodes)
        };
        if let Some(containing_object_literal_element) = containing_object_literal_element {
            /* Because in short-hand property assignment, location has two meaning : property name and as value of the property
             * When we do findAllReference at the position of the short-hand property assignment, we would want to have references to position of
             * property name and variable declaration of the identifier.
             * Like in below example, when querying for all references for an identifier 'name', of the property assignment, the language service
             * should show both 'name' in 'obj' and 'name' in variable declaration
             *      const name = "Foo";
             *      const obj = { name };
             * In order to do that, we will populate the search set with the value symbol of the identifier as a value of the property assignment
             * so that when matching with potential reference symbol, both symbols from property declaration and variable declaration
             * will be included correctly.
             */
            let shorthand_value_symbol = {
                let nodes = self.program.nodes(location.file_index());
                let parent = nodes[location].parent;
                drop(nodes);
                parent.and_then(|p| {
                    self.checker
                        .borrow_mut()
                        .get_shorthand_assignment_value_symbol(Some(p))
                })
            };
            // gets the local symbol
            if shorthand_value_symbol.is_some() && is_for_rename_populate_search_symbol_set {
                // When renaming 'x' in `const o = { x }`, just rename the local variable, not the property.
                return (
                    cb_symbol(shorthand_value_symbol.expect("svs"), None, None),
                    EntryKind::SearchedLocalFoundProperty,
                );
            }
            // If the location is in a context sensitive location (i.e. in an object literal) try
            // to get a contextual type for it, and add the property symbol from the contextual
            // type to the search set
            let containing_parent = {
                let nodes = self.program.nodes(containing_object_literal_element.file_index());
                nodes[containing_object_literal_element].parent
            };
            if let Some(contextual_type) = containing_parent.and_then(|cp| {
                self.checker
                    .borrow_mut()
                    .get_contextual_type_api(cp, tsc_checker::types::ContextFlags::NONE)
            }) {
                let symbols = {
                    let mut c = self.checker.borrow_mut();
                    c.get_property_symbols_from_contextual_type(
                        containing_object_literal_element,
                        contextual_type,
                        true, /*unionSymbolOk*/
                    )
                };
                for sym in symbols {
                    if let Some(res) = from_root(self, sym, cb_symbol) {
                        return (Some(res), EntryKind::SearchedPropertyFoundLocal);
                    }
                }
            }
            // If the location is name of property symbol from object literal destructuring pattern
            // Search the property symbol
            //      for ( { property: p2 } of elems) { }
            if let Some(property_symbol) = self
                .checker
                .borrow_mut()
                .get_property_symbol_of_destructuring_assignment(location)
            {
                if let Some(res) = cb_symbol(property_symbol, None, None) {
                    return (Some(res), EntryKind::SearchedPropertyFoundLocal);
                }
            }
            if let Some(shorthand_value_symbol) = shorthand_value_symbol {
                if let Some(res) = cb_symbol(shorthand_value_symbol, None, None) {
                    return (Some(res), EntryKind::SearchedLocalFoundProperty);
                }
            }
        }

        if let Some(aliased_symbol) = get_merged_aliased_symbol_of_namespace_export_declaration(
            location,
            symbol,
            &self.checker,
            &self.program,
        ) {
            // In case of UMD module and global merging, search for global as well
            if let Some(res) = cb_symbol(aliased_symbol, None, None) {
                return (Some(res), EntryKind::Node);
            }
        }

        if let Some(res) = from_root(self, symbol, cb_symbol) {
            return (Some(res), EntryKind::Node);
        }

        let (value_declaration, symbol_flags, symbol_name) = {
            let arena = self.checker.borrow().symbol_arena.clone();
            let s = &arena.borrow()[symbol.index()];
            (s.value_declaration, s.flags, s.name.clone())
        };
        if let Some(value_declaration) = value_declaration {
            let is_param_prop = {
                let nodes = self.program.nodes(value_declaration.file_index());
                nodes[value_declaration].parent.is_some_and(|p| {
                    ast::is_parameter_property_declaration(&nodes[value_declaration], &nodes[p])
                })
            };
            if is_param_prop {
                let (param_prop1, param_prop2) = {
                    let mut c = self.checker.borrow_mut();
                    c.get_symbols_of_parameter_property_declaration(
                        value_declaration,
                        &symbol_name,
                    )
                };
                debug_assert!(
                    self.checker.borrow().symbol_arena.borrow()[param_prop1.index()].flags
                        & SymbolFlags::FUNCTION_SCOPED_VARIABLE
                        != SymbolFlags::NONE
                        && self.checker.borrow().symbol_arena.borrow()[param_prop2.index()].flags
                            & SymbolFlags::CLASS_MEMBER
                            != SymbolFlags::NONE,
                    "GetSymbolsOfParameterPropertyDeclaration must return (parameter, member) pair"
                );
                let which = if symbol_flags & SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    != SymbolFlags::NONE
                {
                    param_prop2
                } else {
                    param_prop1
                };
                return (from_root(self, which, cb_symbol), EntryKind::Node);
            }
        }

        let export_specifier = {
            let arena = self.checker.borrow().symbol_arena.clone();
            let nodes = {
                let decls = arena.borrow()[symbol.index()].declarations.clone();
                decls.first().map(|d| self.program.nodes(d.file_index()))
            };
            nodes.and_then(|nodes| {
                ast::get_declaration_of_kind(
                    &arena.borrow()[symbol.index()],
                    Kind::ExportSpecifier,
                    &nodes,
                )
            })
        };
        if let Some(export_specifier) = export_specifier {
            let has_property_name = {
                let nodes = self.program.nodes(export_specifier.file_index());
                nodes[export_specifier].property_name().is_some()
            };
            if !is_for_rename_populate_search_symbol_set || !has_property_name {
                let local_symbol = {
                    let mut c = self.checker.borrow_mut();
                    c.get_export_specifier_local_target_symbol(export_specifier)
                };
                if let Some(local_symbol) = local_symbol {
                    if let Some(res) = cb_symbol(local_symbol, None, None) {
                        return (Some(res), EntryKind::Node);
                    }
                }
            }
        }

        // symbolAtLocation for a binding element is the local symbol. See if the search symbol is the property.
        // Don't do this when populating search set for a rename when prefix and suffix text will be provided -- just rename the local.
        if !is_for_rename_populate_search_symbol_set {
            let binding_element_property_symbol = if only_include_binding_element_at_reference_location {
                let parent_ok = {
                    let nodes = self.program.nodes(location.file_index());
                    nodes[location]
                        .parent
                        .is_some_and(|p| is_object_binding_element_without_property_name(p, &nodes))
                };
                if !parent_ok {
                    return (None, EntryKind::None);
                }
                let parent = {
                    let nodes = self.program.nodes(location.file_index());
                    nodes[location].parent.expect("parent")
                };
                let mut c = self.checker.borrow_mut();
                get_property_symbol_from_binding_element(&mut c, parent)
            } else {
                let mut c = self.checker.borrow_mut();
                get_property_symbol_of_object_binding_pattern_without_property_name(
                    symbol, &mut c,
                )
            };
            let Some(binding_element_property_symbol) = binding_element_property_symbol else {
                return (None, EntryKind::None);
            };
            return (
                from_root(self, binding_element_property_symbol, cb_symbol),
                EntryKind::SearchedPropertyFoundLocal,
            );
        }

        debug_assert!(is_for_rename_populate_search_symbol_set);

        // due to the above assert and the arguments at the uses of this function,
        // (onlyIncludeBindingElementAtReferenceLocation <=> !providePrefixAndSuffixTextForRename) holds
        let include_original_symbol_of_binding_element = only_include_binding_element_at_reference_location;

        if include_original_symbol_of_binding_element {
            let binding_element_property_symbol = {
                let mut c = self.checker.borrow_mut();
                get_property_symbol_of_object_binding_pattern_without_property_name(
                    symbol, &mut c,
                )
            };
            if let Some(binding_element_property_symbol) = binding_element_property_symbol {
                return (
                    from_root(self, binding_element_property_symbol, cb_symbol),
                    EntryKind::SearchedPropertyFoundLocal,
                );
            }
        }
        (None, EntryKind::None)
    }

    /// `searchForName` — search for all occurrences of an identifier in a
    /// source file (and filter out the ones that match).
    fn search_for_name(&self, source_file: NodeId, search: &RefSearch) {
        let contains = {
            let mut nodes = self.program.nodes_mut(source_file.file_index());
            ast::get_name_table(&mut nodes, source_file).contains_key(&search.escaped_text)
        };
        if contains {
            self.get_references_in_source_file(source_file, search, true);
        }
    }

    /// `explicitlyInheritsFrom`.
    fn explicitly_inherits_from(&self, symbol: SymbolId, parent: SymbolId) -> bool {
        if symbol == parent {
            return true;
        }

        // Check cache first
        let key: InheritKey = (symbol, parent);
        if let Some(&cached) = self.inherits_from_cache.borrow().get(&key) {
            return cached;
        }

        // Set to false initially to prevent infinite recursion
        self.inherits_from_cache.borrow_mut().insert(key, false);

        let declarations = self.checker.borrow().symbol_arena.borrow()[symbol.index()]
            .declarations
            .clone();

        let inherits = declarations.iter().copied().any(|declaration| {
            let super_type_nodes = {
                let nodes = self.program.nodes(declaration.file_index());
                get_all_super_type_nodes(&nodes[declaration], &nodes)
            };
            super_type_nodes.iter().copied().any(|type_reference| {
                let typ = self.checker.borrow_mut().get_type_at_location(type_reference);
                let type_symbol = self.checker.borrow().types.get(typ).symbol;
                type_symbol.is_some_and(|ts| self.explicitly_inherits_from(ts, parent))
            })
        });

        // Update cache with the actual result
        self.inherits_from_cache.borrow_mut().insert(key, inherits);
        inherits
    }
}

/// `getReferenceEntriesForShorthandPropertyAssignment`.
fn get_reference_entries_for_shorthand_property_assignment(
    node: NodeId,
    checker: &Rc<RefCell<Checker>>,
    add_reference: &mut dyn FnMut(NodeId),
    program: &Rc<Program>,
) {
    let ref_symbol = checker.borrow_mut().get_symbol_at_location_api(node);
    let Some(ref_symbol) = ref_symbol else {
        return;
    };
    let value_declaration = checker.borrow().symbol_arena.borrow()[ref_symbol.index()]
        .value_declaration;
    let Some(value_declaration) = value_declaration else {
        return;
    };
    let shorthand_symbol = checker
        .borrow_mut()
        .get_shorthand_assignment_value_symbol(Some(value_declaration));
    let Some(shorthand_symbol) = shorthand_symbol else {
        return;
    };
    let declarations = checker.borrow().symbol_arena.borrow()[shorthand_symbol.index()]
        .declarations
        .clone();
    for declaration in declarations {
        let nodes = program.nodes(declaration.file_index());
        if get_meaning_from_declaration(&nodes[declaration], &nodes)
            & ast::SemanticMeaning::VALUE
            != ast::SemanticMeaning::NONE
        {
            add_reference(declaration);
        }
    }
}

/// `isMethodOrAccessor`.
fn is_method_or_accessor(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::MethodDeclaration | Kind::GetAccessor | Kind::SetAccessor
    )
}

/// `tryGetClassByExtendingIdentifier`.
fn try_get_class_by_extending_identifier(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let parent = nodes[ast::climb_past_property_access(node, nodes)].parent?;
    ast::try_get_class_extending_expression_with_type_arguments(parent, nodes)
}

/// `getClassConstructorSymbol`.
fn get_class_constructor_symbol(class_symbol: SymbolId, checker: &RefCell<Checker>) -> Option<SymbolId> {
    checker.borrow().symbol_arena.borrow()[class_symbol.index()]
        .members
        .get(ast::symbol::INTERNAL_SYMBOL_NAME_CONSTRUCTOR)
        .copied()
}

/// `hasOwnConstructor`.
fn has_own_constructor(class_symbol: Option<SymbolId>, checker: &RefCell<Checker>) -> bool {
    class_symbol
        .and_then(|s| get_class_constructor_symbol(s, checker))
        .is_some()
}

/// `findOwnConstructorReferences`.
fn find_own_constructor_references(
    class_symbol: SymbolId,
    source_file: NodeId,
    add_node: &mut dyn FnMut(NodeId),
    checker: &Rc<RefCell<Checker>>,
    program: &Rc<Program>,
) {
    let constructor_symbol = get_class_constructor_symbol(class_symbol, checker);
    if let Some(constructor_symbol) = constructor_symbol {
        let declarations = checker.borrow().symbol_arena.borrow()[constructor_symbol.index()]
            .declarations
            .clone();
        for decl in declarations {
            let is_constructor = {
                let nodes = program.nodes(decl.file_index());
                nodes[decl].kind == Kind::Constructor
            };
            if is_constructor {
                let mut nodes = program.nodes_mut(decl.file_index());
                if let Some(ctr_keyword) =
                    tokens::find_child_of_kind(&mut nodes, source_file, decl, Kind::ConstructorKeyword)
                {
                    add_node(ctr_keyword);
                }
            }
        }
    }

    let export_members: Vec<SymbolId> = {
        let arena = checker.borrow().symbol_arena.clone();
        arena.borrow()[class_symbol.index()]
            .exports
            .values()
            .copied()
            .collect()
    };
    for member in export_members {
        let decl = checker.borrow().symbol_arena.borrow()[member.index()].value_declaration;
        if let Some(decl) = decl {
            let is_method = {
                let nodes = program.nodes(decl.file_index());
                nodes[decl].kind == Kind::MethodDeclaration
            };
            if is_method {
                let body = {
                    let nodes = program.nodes(decl.file_index());
                    nodes[decl].body()
                };
                if let Some(body) = body {
                    let nodes = program.nodes(body.file_index());
                    for_each_descendant_of_kind(body, Kind::ThisKeyword, &nodes, &mut |this_keyword| {
                        if ast::is_new_expression_target(this_keyword, false, false, &nodes) {
                            add_node(this_keyword);
                        }
                    });
                }
            }
        }
    }
}

/// `findSuperConstructorAccesses`.
fn find_super_constructor_accesses(
    class_declaration: NodeId,
    add_node: &mut dyn FnMut(NodeId),
    program: &Rc<Program>,
    checker: &RefCell<Checker>,
) {
    let class_symbol = {
        let nodes = program.nodes(class_declaration.file_index());
        nodes[class_declaration].symbol()
    };
    let Some(class_symbol) = class_symbol else {
        return;
    };
    let constructor_symbol = get_class_constructor_symbol(class_symbol, checker);
    let Some(constructor_symbol) = constructor_symbol else {
        return;
    };
    let declarations = checker.borrow().symbol_arena.borrow()[constructor_symbol.index()]
        .declarations
        .clone();
    for decl in declarations {
        let nodes = program.nodes(decl.file_index());
        if nodes[decl].kind != Kind::Constructor {
            continue;
        }
        if let Some(body) = nodes[decl].body() {
            for_each_descendant_of_kind(body, Kind::SuperKeyword, &nodes, &mut |node| {
                if ast::is_call_expression_target(node, false, false, &nodes) {
                    add_node(node);
                }
            });
        }
    }
}

/// `forEachDescendantOfKind`.
fn for_each_descendant_of_kind(
    node: NodeId,
    kind: Kind,
    nodes: &[Node],
    action: &mut dyn FnMut(NodeId),
) {
    nodes[node].for_each_child(nodes, &mut |child| {
        if nodes[child].kind == kind {
            action(child);
        }
        for_each_descendant_of_kind(child, kind, nodes, action);
        false
    });
}

/// `for_each_this_keyword_without_function_or_class` — the `cb` closure from
/// `addClassStaticThisReferences`.
fn for_each_this_keyword_without_function_or_class(
    node: NodeId,
    nodes: &[Node],
    action: &mut dyn FnMut(NodeId),
) {
    if nodes[node].kind == Kind::ThisKeyword {
        action(node);
    } else if !ast::is_function_like(Some(node), nodes) && !ast::is_class_like(Some(node), nodes) {
        nodes[node].for_each_child(nodes, &mut |child| {
            for_each_this_keyword_without_function_or_class(child, nodes, action);
            false
        });
    }
}

/// `isImplementation`.
fn is_implementation(node: NodeId, nodes: &[Node]) -> bool {
    if nodes[node].flags.intersects(ast::NodeFlags::AMBIENT) {
        return !(nodes[node].kind == Kind::InterfaceDeclaration
            || nodes[node].kind == Kind::TypeAliasDeclaration);
    }
    if ast::is_variable_like(&nodes[node]) {
        return ast::has_initializer(&nodes[node]);
    }
    if ast::is_function_like_declaration(Some(node), nodes) {
        return nodes[node].body().is_some();
    }
    ast::is_class_like(Some(node), nodes) || ast::is_module_or_enum_declaration(&nodes[node])
}

/// `isImplementationExpression`.
fn is_implementation_expression(node: NodeId, nodes: &[Node]) -> bool {
    match nodes[node].kind {
        Kind::ParenthesizedExpression => nodes[node]
            .expression()
            .is_some_and(|e| is_implementation_expression(e, nodes)),
        Kind::ArrowFunction
        | Kind::FunctionExpression
        | Kind::ObjectLiteralExpression
        | Kind::ClassExpression
        | Kind::ArrayLiteralExpression => true,
        _ => false,
    }
}

/// `isStringLiteralPropertyReference`.
fn is_string_literal_property_reference(
    node: NodeId,
    checker: &mut Checker,
    nodes: &[Node],
) -> bool {
    if let Some(parent) = nodes[node].parent {
        if ast::is_property_signature_declaration(&nodes[parent]) {
            if let Some(grandparent) = nodes[parent].parent {
                let t = checker.get_type_at_location(grandparent);
                return checker
                    .get_property_of_type(t, &nodes[node].text(nodes))
                    .is_some();
            }
        }
    }
    false
}

// ===========================================================================
// crossproject.go — local copy (crossproject.rs is a sibling-owned skeleton).
// PORT: sequential work-queue instead of Go's parallel WorkGroup — see file
// header PORT(crossproject).
// ===========================================================================

/// `type Project interface`.
pub(crate) trait Project {
    /// `Id`.
    fn id(&self) -> String;
    /// `GetProgram`.
    fn get_program(&self) -> Option<Rc<Program>>;
    /// `HasFile`.
    fn has_file(&self, file_name: &RootedFilePath) -> bool;
}

/// `type CrossProjectOrchestrator interface`.
pub(crate) trait CrossProjectOrchestrator<'h> {
    /// `GetDefaultProject`.
    fn get_default_project(&self) -> Rc<dyn Project>;
    /// `GetAllProjectsForInitialRequest`.
    fn get_all_projects_for_initial_request(&self) -> Vec<Rc<dyn Project>>;
    /// `GetLanguageServiceForProjectWithFile`.
    fn get_language_service_for_project_with_file(
        &self,
        ctx: &Context,
        project: &Rc<dyn Project>,
        uri: &lsproto::DocumentUri,
    ) -> Option<Rc<LanguageService<'h>>>;
    /// `GetProjectsForFile`.
    fn get_projects_for_file(
        &self,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
    ) -> Result<Vec<Rc<dyn Project>>, Error>;
    /// `GetProjectsLoadingProjectTree`.
    fn get_projects_loading_project_tree(
        &self,
        ctx: &Context,
        requested_project_trees: &Set<PathKey>,
    ) -> Vec<Rc<dyn Project>>;
}

/// `response[Resp]`.
struct CrossProjectResponse<Resp> {
    /// `complete`.
    complete: bool,
    /// `result`.
    result: Option<Resp>,
    /// `forOriginalLocation`.
    for_original_location: bool,
}

impl<'h> LanguageService<'h> {
    /// `handleCrossProject`.
    ///
    /// PORT: `WorkGroup` parallelism is collapsed to a FIFO queue (the
    /// language service is `!Send`); Go's per-item `recover()` becomes
    /// ordinary panic propagation, and `results` is an insertion-ordered map
    /// keyed by project id.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn handle_cross_project<Resp>(
        &self,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
        position: lsproto::Position,
        orchestrator: Option<&dyn CrossProjectOrchestrator<'h>>,
        symbol_and_entries_to_resp: impl Fn(
            &LanguageService<'h>,
            &Context,
            SymbolAndEntriesData,
            SymbolEntryTransformOptions,
        ) -> Result<Resp, Error>,
        combine_results: &dyn Fn(Vec<Resp>) -> Resp,
        is_rename: bool,
        implementations: bool,
        options: SymbolEntryTransformOptions,
        default_project_data: Option<&SymbolAndEntriesData>,
    ) -> Result<Resp, Error> {
        // Single project
        let Some(orchestrator) = orchestrator else {
            let data = match default_project_data {
                Some(data) => clone_symbol_and_entries_data(data),
                None => {
                    self.provide_symbols_and_entries(
                        ctx,
                        uri,
                        position,
                        is_rename,
                        implementations,
                    )
                    .0
                }
            };
            return symbol_and_entries_to_resp(self, ctx, data, options);
        };

        let default_project = orchestrator.get_default_project();
        let all_projects = orchestrator.get_all_projects_for_initial_request();
        let default_project_id = default_project.id();
        // `results` — insertion-ordered map, Go's `collections.SyncMap`.
        let mut results: Vec<(String, CrossProjectResponse<Resp>)> = Vec::new();
        let mut results_index: HashMap<String, usize> = HashMap::new();
        let mut default_definition: Option<NonLocalDefinition<'_>> = None;
        let mut first_err: Option<Error> = None;

        // `work` — FIFO queue of (project, useSelf, uri, position, symbol_data, forOriginalLocation).
        // `useSelf` marks the initial default-project item: Go presets
        // `item.ls = defaultLs` (the receiver) instead of going through the
        // orchestrator. PORT: Go enqueues work items on a parallel WorkGroup;
        // here they are processed sequentially but newly discovered items are
        // appended to the same queue, preserving Go's order.
        let mut queue: VecDeque<(
            Rc<dyn Project>,
            bool,
            lsproto::DocumentUri,
            lsproto::Position,
            Option<SymbolAndEntriesData>,
            bool,
        )> = VecDeque::new();

        // `enqueueItem` — dedupe by project id, then push.
        macro_rules! enqueue_item {
            ($project:expr, $use_self:expr, $uri:expr, $pos:expr, $data:expr, $for_orig:expr) => {{
                let project: Rc<dyn Project> = $project;
                let id = project.id();
                if !results_index.contains_key(&id) {
                    let idx = results.len();
                    results_index.insert(id.clone(), idx);
                    results.push((
                        id,
                        CrossProjectResponse {
                            complete: false,
                            result: None,
                            for_original_location: false,
                        },
                    ));
                    queue.push_back((project, $use_self, $uri, $pos, $data, $for_orig));
                }
            }};
        }

        // Initial set of projects and locations in the queue, starting with default project
        enqueue_item!(
            default_project.clone(),
            true,
            uri.clone(),
            position,
            default_project_data.map(clone_symbol_and_entries_data),
            false
        );
        for project in &all_projects {
            if project.id() != default_project_id {
                enqueue_item!(project.clone(), false, uri.clone(), position, None, false);
            }
        }

        // `processQueue` — drains the queue; nested enqueues append to it.
        macro_rules! process_queue {
            () => {{
                while let Some((project, use_self, item_uri, item_position, symbol_data, for_original_location)) =
                    queue.pop_front()
                {
                    if ctx.is_cancelled() {
                        break;
                    }
                    let ls_owned = if use_self {
                        None
                    } else {
                        // Get it now
                        orchestrator.get_language_service_for_project_with_file(
                            ctx, &project, &item_uri,
                        )
                    };
                    let Some(ls_ref) = (if use_self { Some(self) } else { ls_owned.as_deref() })
                    else {
                        continue;
                    };
                    let (data, ok) = match symbol_data {
                        Some(data) => (data, true),
                        None => ls_ref.provide_symbols_and_entries(
                            ctx,
                            &item_uri,
                            item_position,
                            is_rename,
                            implementations,
                        ),
                    };
                    if ctx.is_cancelled() {
                        break;
                    }
                    if ok {
                        for entry in &data.symbols_and_entries {
                            // Find the default definition that can be in another project
                            // Later we will use this load ancestor tree that references this location and expand search
                            if project.id() == default_project_id
                                && default_definition.is_none()
                            {
                                // `use_self` is true here (default project item),
                                // so `self` is the same language service as `ls_ref`.
                                default_definition =
                                    self.get_non_local_definition(ctx, &entry.borrow());
                            }
                            let mut enqueued: Vec<(
                                Rc<dyn Project>,
                                lsproto::DocumentUri,
                                lsproto::Position,
                            )> = Vec::new();
                            ls_ref.for_each_original_definition_location(
                                ctx,
                                &entry.borrow(),
                                &mut |def_uri, def_position| {
                                    // Get default configured project for this file
                                    let Ok(def_projects) =
                                        orchestrator.get_projects_for_file(ctx, &def_uri)
                                    else {
                                        return;
                                    };
                                    for def_project in def_projects {
                                        // Optimization: don't enqueue if will be discarded
                                        if !results_index.contains_key(&def_project.id()) {
                                            enqueued.push((
                                                def_project,
                                                def_uri.clone(),
                                                def_position,
                                            ));
                                        }
                                    }
                                },
                            );
                            for (def_project, def_uri, def_position) in enqueued {
                                enqueue_item!(def_project, false, def_uri, def_position, None, true);
                            }
                        }
                    }

                    match symbol_and_entries_to_resp(ls_ref, ctx, data, options) {
                        Ok(result) => {
                            let idx = *results_index.get(&project.id()).expect("result index");
                            results[idx].1.complete = true;
                            results[idx].1.result = Some(result);
                            results[idx].1.for_original_location = for_original_location;
                        }
                        Err(err_search) => {
                            if first_err.is_none() {
                                first_err = Some(err_search);
                            }
                        }
                    }
                }
            }};
        }

        // Outer loop - to complete work if more is added after completing existing queue
        loop {
            // Process existing known projects first
            process_queue!();
            if ctx.is_cancelled() {
                return Err(Error::Message("context cancelled".to_string()));
            }
            if let Some(err) = first_err {
                return Err(err);
            }

            let mut has_more_work = false;
            if let Some(default_definition) = &default_definition {
                let mut requested_project_trees: Set<PathKey> = Set::new();
                for (id, response) in &results {
                    if response.complete {
                        requested_project_trees.add(tsc_tspath::path_key_from_canonical(id));
                    }
                }

                // Load more projects based on default definition found
                for loaded_project in
                    orchestrator.get_projects_loading_project_tree(ctx, &requested_project_trees)
                {
                    if ctx.is_cancelled() {
                        return Err(Error::Message("context cancelled".to_string()));
                    }

                    // Can loop forever without this (enqueue here, dequeue above, repeat)
                    if results_index.contains_key(&loaded_project.id())
                        || loaded_project.get_program().is_none()
                    {
                        continue;
                    }

                    // Enqueue the project and location for further processing
                    if loaded_project.has_file(&default_definition.position.uri.file_name()) {
                        let (u, p) = (
                            default_definition.position.uri.clone(),
                            default_definition.position.pos,
                        );
                        enqueue_item!(loaded_project.clone(), false, u, p, None, false);
                        has_more_work = true;
                    } else if let Some(source_pos) =
                        (default_definition.get_source_position)()
                    {
                        if loaded_project.has_file(&source_pos.text_document_uri().file_name()) {
                            let (u, p) = (
                                source_pos.text_document_uri(),
                                source_pos.text_document_position(),
                            );
                            enqueue_item!(loaded_project.clone(), false, u, p, None, false);
                            has_more_work = true;
                        } else if let Some(generated_pos) =
                            (default_definition.get_generated_position)()
                        {
                            if loaded_project
                                .has_file(&generated_pos.text_document_uri().file_name())
                            {
                                let (u, p) = (
                                    generated_pos.text_document_uri(),
                                    generated_pos.text_document_position(),
                                );
                                enqueue_item!(loaded_project.clone(), false, u, p, None, false);
                                has_more_work = true;
                            }
                        }
                    } else if let Some(generated_pos) =
                        (default_definition.get_generated_position)()
                    {
                        if loaded_project
                            .has_file(&generated_pos.text_document_uri().file_name())
                        {
                            let (u, p) = (
                                generated_pos.text_document_uri(),
                                generated_pos.text_document_position(),
                            );
                            enqueue_item!(loaded_project.clone(), false, u, p, None, false);
                            has_more_work = true;
                        }
                    }
                }
            }
            if !has_more_work {
                break;
            }
        }

        // `getResultsIterator` — default project first, then allProjects in
        // order, then non-original-location results, then original-location
        // results (insertion order, mirroring `SyncMap.Range` + queue order).
        let mut ordered_results: Vec<Resp> = Vec::new();
        let mut seen_projects: Set<String> = Set::new();
        if let Some(idx) = results_index.get(&default_project_id).copied() {
            if results[idx].1.complete {
                if let Some(r) = results[idx].1.result.take() {
                    ordered_results.push(r);
                }
            }
        }
        seen_projects.add(default_project_id.clone());
        for project in &all_projects {
            if seen_projects.add_if_absent(project.id()) {
                if let Some(idx) = results_index.get(&project.id()).copied() {
                    if results[idx].1.complete {
                        if let Some(r) = results[idx].1.result.take() {
                            ordered_results.push(r);
                        }
                    }
                }
            }
        }
        // Prefer the searches from locations for default definition
        for (id, response) in &mut results {
            if !response.for_original_location
                && seen_projects.add_if_absent(id.clone())
                && response.complete
            {
                if let Some(r) = response.result.take() {
                    ordered_results.push(r);
                }
            }
        }
        // Then the searches from original locations
        for (id, response) in &mut results {
            if response.for_original_location
                && seen_projects.add_if_absent(id.clone())
                && response.complete
            {
                if let Some(r) = response.result.take() {
                    ordered_results.push(r);
                }
            }
        }

        if results.len() > 1 {
            Ok(combine_results(ordered_results))
        } else {
            // Single result, return that directly
            Ok(ordered_results.into_iter().next().unwrap_or_else(|| {
                // `var resp Resp` — Go zero value. Combine over empty is the
                // closest Rust equivalent for the response types used here.
                combine_results(Vec::new())
            }))
        }
    }
}

/// `clone_symbol_and_entries_data` — `data = *defaultProjectData` is a shallow
/// copy in Go (the `SymbolAndEntries`/`ReferenceEntry` pointers are shared).
fn clone_symbol_and_entries_data(data: &SymbolAndEntriesData) -> SymbolAndEntriesData {
    SymbolAndEntriesData {
        original_node: data.original_node,
        symbols_and_entries: data.symbols_and_entries.clone(),
        position: data.position,
    }
}

/// `combineLocationArray`.
///
/// PORT: Go dedupes via `collections.Set[lsproto.Location]`; `Location` is
/// `PartialEq`-only in `tsc_lsproto` (no `Hash`), so the seen-set is a `Vec`
/// scanned linearly — same dedup semantics.
pub(crate) fn combine_location_array(
    combined: Vec<lsproto::Location>,
    locations: &[lsproto::Location],
    seen: &mut Vec<lsproto::Location>,
) -> Vec<lsproto::Location> {
    let mut combined = combined;
    for loc in locations {
        if !seen.contains(loc) {
            seen.push(loc.clone());
            combined.push(loc.clone());
        }
    }
    combined
}

/// `combineLocationArray` for `LocationLink` — dedupe key is the target
/// location (`{uri: targetUri, range: targetRange}`), Go's
/// `LocationLink.GetLocation()`.
pub(crate) fn combine_location_link_array(
    combined: Vec<lsproto::LocationLink>,
    links: &[lsproto::LocationLink],
    seen: &mut Vec<lsproto::Location>,
) -> Vec<lsproto::LocationLink> {
    let mut combined = combined;
    for link in links {
        let loc = lsproto::Location {
            uri: link.target_uri.clone(),
            range: link.target_range.clone(),
        };
        if !seen.contains(&loc) {
            seen.push(loc);
            combined.push(link.clone());
        }
    }
    combined
}

/// `combineResponseLocations`.
fn combine_response_locations(
    results: &[lsproto::ReferencesResponse],
) -> Option<Vec<lsproto::Location>> {
    let mut combined: Vec<lsproto::Location> = Vec::new();
    let mut seen_locations: Vec<lsproto::Location> = Vec::new();
    for resp in results {
        if let Some(locations) = &resp.locations {
            combined = combine_location_array(combined, locations, &mut seen_locations);
        }
    }
    Some(combined)
}

/// `combineResponseLocations` for implementation responses whose
/// `locations` arm is set.
fn combine_implementation_response_locations(
    results: &[lsproto::ImplementationResponse],
) -> Option<Vec<lsproto::Location>> {
    let mut combined: Vec<lsproto::Location> = Vec::new();
    let mut seen_locations: Vec<lsproto::Location> = Vec::new();
    for resp in results {
        if let Some(locations) = &resp.locations {
            combined = combine_location_array(combined, locations, &mut seen_locations);
        }
    }
    Some(combined)
}

/// `combineReferences`.
pub(crate) fn combine_references(
    results: Vec<lsproto::ReferencesResponse>,
) -> lsproto::ReferencesResponse {
    lsproto::LocationsOrNull {
        locations: combine_response_locations(&results),
    }
}

/// `combineVSReferences`.
pub(crate) fn combine_vsreferences(
    results: Vec<lsproto::VSReferencesResponse>,
) -> lsproto::VSReferencesResponse {
    let mut combined: Vec<lsproto::VSReferenceItem> = Vec::new();
    // Re-number IDs across projects to maintain unique IDs and correct definition references
    let mut next_id: i32 = 0;
    for resp in &results {
        let Some(items) = &resp.vs_reference_items else {
            continue;
        };
        // Map old IDs to new IDs for this batch
        let mut id_map: HashMap<i32, i32> = HashMap::new();
        for item in items {
            let old_id = item.vs_id;
            let new_id = next_id;
            id_map.insert(old_id, new_id);
            next_id += 1;

            let mut new_item = item.clone();
            new_item.vs_id = new_id;
            if let Some(def_id) = item.vs_definition_id {
                new_item.vs_definition_id = id_map.get(&def_id).copied();
            }
            combined.push(new_item);
        }
    }
    lsproto::VSReferenceItemsOrNull {
        vs_reference_items: Some(combined),
    }
}

/// `combineImplementations`.
pub(crate) fn combine_implementations(
    results: Vec<lsproto::ImplementationResponse>,
) -> lsproto::ImplementationResponse {
    let mut combined: Vec<lsproto::LocationLink> = Vec::new();
    let mut seen_locations: Vec<lsproto::Location> = Vec::new();
    for resp in &results {
        if let Some(definition_links) = &resp.definition_links {
            combined = combine_location_link_array(combined, definition_links, &mut seen_locations);
        } else if resp.locations.is_some() {
            return lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
                locations: combine_implementation_response_locations(&results),
                ..Default::default()
            };
        }
    }
    lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
        definition_links: Some(combined),
        ..Default::default()
    }
}

/// `combineRenameResponse`.
pub(crate) fn combine_rename_response(
    results: Vec<lsproto::RenameResponse>,
) -> lsproto::RenameResponse {
    let mut combined: BTreeMap<lsproto::DocumentUri, Vec<lsproto::TextEdit>> = BTreeMap::new();
    let mut seen_changes: HashMap<lsproto::DocumentUri, Vec<lsproto::Range>> = HashMap::new();
    let mut document_changes: Vec<
        lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile,
    > = Vec::new();
    let mut seen_renames: Set<(lsproto::DocumentUri, lsproto::DocumentUri)> = Set::new();

    for resp in &results {
        if let Some(workspace_edit) = &resp.workspace_edit {
            if let Some(changes) = &workspace_edit.document_changes {
                for change in changes {
                    if let Some(rename_file) = &change.rename_file {
                        let key = (rename_file.old_uri.clone(), rename_file.new_uri.clone());
                        if seen_renames.add_if_absent(key) {
                            document_changes.push(change.clone());
                        }
                    } else {
                        document_changes.push(change.clone());
                    }
                }
            }
            if let Some(changes) = &workspace_edit.changes {
                for (doc, doc_changes) in changes {
                    let seen_set = seen_changes.entry(doc.clone()).or_default();
                    let changes_for_doc = combined.entry(doc.clone()).or_default();
                    for change in doc_changes {
                        if !seen_set.contains(&change.range) {
                            seen_set.push(change.range.clone());
                            changes_for_doc.push(change.clone());
                        }
                    }
                }
            }
        }
    }
    if !document_changes.is_empty() || !combined.is_empty() {
        let mut workspace_edit = lsproto::WorkspaceEdit::default();
        if !document_changes.is_empty() {
            workspace_edit.document_changes = Some(document_changes);
        }
        if !combined.is_empty() {
            workspace_edit.changes = Some(combined);
        }
        lsproto::WorkspaceEditOrNull {
            workspace_edit: Some(workspace_edit),
        }
    } else {
        lsproto::WorkspaceEditOrNull::default()
    }
}
