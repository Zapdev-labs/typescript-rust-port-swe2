// Ported from tsc/internal/transformers/moduletransforms/utilities.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Helpers shared across the module transforms: enum/namespace declaration
// name detection, `--rewriteRelativeImportExtensions` specifier rewriting,
// the `export {}` sentinel, and external-module-name resolution stubs.

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::{self as ast, Kind, Node, NodeId};
use tsc_core::options_generated::CompilerOptions;
use tsc_printer::{EmitContext, EmitResolver, NodeFactory};

/// `isDeclarationNameOfEnumOrNamespace(emitContext, node)` — `node` must be
/// an `Identifier`.
pub fn is_declaration_name_of_enum_or_namespace(
    emit_context: &EmitContext,
    nodes: &[Node],
    node: NodeId,
) -> bool {
    // PORT: `MostOriginal` yields parse-tree nodes; as in Go, this helper
    // intentionally inspects parse-tree parents.
    if let Some(original) = emit_context.most_original(Some(node))
        && let Some(parent) = nodes[original].parent
    {
        match nodes[parent].kind {
            Kind::EnumDeclaration | Kind::ModuleDeclaration => {
                return nodes[parent].name() == Some(original);
            }
            _ => {}
        }
    }
    false
}

/// `rewriteModuleSpecifier(emitContext, node, compilerOptions)` —
/// `emit_context` is `&mut` for the `NewStringLiteral` mint inside.
pub fn rewrite_module_specifier(
    emit_context: &mut EmitContext,
    nodes: &mut Vec<Node>,
    node: Option<NodeId>,
    compiler_options: &CompilerOptions,
) -> Option<NodeId> {
    let node = node?;
    if !ast::is_string_literal(&nodes[node])
        || !tsc_core::core::should_rewrite_module_specifier(
            &nodes[node].text(nodes),
            compiler_options,
        )
    {
        return Some(node);
    }
    let text = nodes[node].text(nodes).into_owned();
    let updated_text = tsc_tspath::change_extension(
        &text,
        tsc_outputpaths::get_output_extension(&text, compiler_options.jsx),
    );
    if updated_text != text {
        let token_flags = nodes[node].literal_like_data().map(|d| d.token_flags);
        let updated = emit_context.factory.new_string_literal(
            nodes,
            &updated_text,
            token_flags.unwrap_or_default(),
        );
        emit_context.set_original(updated, node);
        emit_context.assign_comment_and_source_map_ranges(nodes, updated, node);
        return Some(updated);
    }
    Some(node)
}

/// `createEmptyImports(factory)` — the `export {}` sentinel emitted to keep
/// a file an external module.
pub fn create_empty_imports(factory: &mut NodeFactory, nodes: &mut Vec<Node>) -> NodeId {
    let elements = factory.new_node_list([]);
    let named_exports = factory.new_named_exports(nodes, Some(elements));
    factory.new_export_declaration(
        nodes,
        None,  /* modifiers */
        false, /* isTypeOnly */
        Some(named_exports),
        None, /* moduleSpecifier */
        None, /* attributes */
    )
}

/// Get the name of a target module from an import/export declaration as
/// should be written in the emitted output. The emitted output name can be
/// different from the input if:
///  1. The module has a `/// <amd-module name="<new name>" />`
///  2. --out or --outFile is used, making the name relative to the rootDir
///     3- The containing SourceFile has an entry in renamedDependencies for
///        the import as requested by some module loaders (e.g. System).
///
/// Otherwise, a new StringLiteral node representing the module name will be
/// returned.
///
/// `getExternalModuleNameLiteral(factory, importNode, sourceFile, host, resolver, compilerOptions)`
///
/// PORT: `host` is `Option<&dyn EmitHost>` for the (currently unreachable)
/// `tryGetModuleNameFromFile` path; `resolver` mirrors Go's nilable
/// `printer.EmitResolver`. Every in-package call site passes `None`/`None`.
#[allow(clippy::too_many_arguments)]
pub fn get_external_module_name_literal(
    factory: &mut NodeFactory,
    nodes: &mut Vec<Node>,
    import_node: NodeId, /* ImportDeclaration | ExportDeclaration | ImportEqualsDeclaration | ImportCall */
    source_file: Option<NodeId>,
    host: Option<&dyn tsc_printer::EmitHost>,
    resolver: Option<&Rc<RefCell<dyn EmitResolver + '_>>>,
    _compiler_options: &CompilerOptions,
) -> Option<NodeId> {
    let module_name = ast::get_external_module_name(&nodes[import_node], nodes)?;
    if !ast::is_string_literal(&nodes[module_name]) {
        return None;
    }
    let mut name = try_get_module_name_from_declaration(
        factory,
        nodes,
        import_node,
        host,
        resolver,
        _compiler_options,
    );
    if name.is_none() {
        name = try_rename_external_module(factory, module_name, source_file);
    }
    if name.is_none() {
        // !!! propagate token flags (will produce new diffs)
        let text = nodes[module_name].text(nodes).into_owned();
        name = Some(factory.new_string_literal(nodes, &text, ast::TokenFlags::NONE));
    }
    name
}

/// Get the name of a module as should be written in the emitted output.
/// The emitted output name can be different from the input if:
///  1. The module has a `/// <amd-module name="<new name>" />`
///  2. --out or --outFile is used, making the name relative to the rootDir
///
/// Otherwise, a new StringLiteral node representing the module name will be
/// returned.
///
/// `tryGetModuleNameFromFile(factory, file, host, options)`
#[allow(dead_code)]
pub fn try_get_module_name_from_file(
    _factory: &mut NodeFactory,
    file: Option<NodeId>,
    _host: Option<&dyn tsc_printer::EmitHost>,
    _compiler_options: &CompilerOptions,
) -> Option<NodeId> {
    file?;
    // !!!
    // if file.moduleName {
    // 	return factory.createStringLiteral(file.moduleName)
    // }
    None
}

/// `tryGetModuleNameFromDeclaration(declaration, host, factory, resolver, compilerOptions)`
pub fn try_get_module_name_from_declaration(
    factory: &mut NodeFactory,
    nodes: &mut Vec<Node>,
    declaration: NodeId, /* ImportEqualsDeclaration | ImportDeclaration | ExportDeclaration | ImportCall */
    host: Option<&dyn tsc_printer::EmitHost>,
    resolver: Option<&Rc<RefCell<dyn EmitResolver + '_>>>,
    compiler_options: &CompilerOptions,
) -> Option<NodeId> {
    let resolver = resolver?;
    let file = resolver
        .borrow()
        .get_external_module_file_from_declaration(declaration, nodes);
    try_get_module_name_from_file(factory, file, host, compiler_options)
}

/// `getExternalModuleNameFromPath(host, fileName, referencePath)` — resolves
/// a local path to a path which is absolute to the base of the emit.
#[allow(dead_code)]
pub fn get_external_module_name_from_path(
    _host: Option<&dyn tsc_printer::EmitHost>,
    _file_name: &str,
    _reference_path: &str,
) -> String {
    // !!!
    String::new()
}

/// `tryRenameExternalModule(factory, moduleName, sourceFile)` — some
/// bundlers (SystemJS builder) sometimes want to rename dependencies. Here
/// we check if an alternative name was provided for a given moduleName and
/// return it if possible.
pub fn try_rename_external_module(
    _factory: &mut NodeFactory,
    _module_name: NodeId,
    _source_file: Option<NodeId>,
) -> Option<NodeId> {
    // !!!
    None
}

/// `isFileLevelReservedGeneratedIdentifier(emitContext, name)` — `name`
/// must be an `Identifier`.
pub fn is_file_level_reserved_generated_identifier(
    emit_context: &EmitContext,
    name: NodeId,
) -> bool {
    emit_context
        .get_auto_generate_info(Some(name))
        .is_some_and(|info| {
            info.flags.is_file_level()
                && info.flags.is_optimistic()
                && info.flags.is_reserved_in_nested_scopes()
        })
}

/// `isSimpleInlineableExpression(expression)` — a simple inlinable
/// expression is an expression which can be copied into multiple locations
/// without risk of repeating any side-effects and whose value could not
/// possibly change between any such locations.
///
/// PORT: `moduletransforms/utilities.go` carries its own package-local copy
/// of `IsSimpleInlineableExpression`; it is identical to
/// `crate::utilities::is_simple_inlineable_expression` and delegates here to
/// avoid a second copy.
pub fn is_simple_inlineable_expression(expression: &Node) -> bool {
    !ast::is_identifier(expression) && crate::is_simple_copiable_expression(expression)
}
