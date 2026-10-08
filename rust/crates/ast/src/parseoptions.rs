// Ported from tsc/internal/ast/parseoptions.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `*SourceFile` parameters become `NodeId` (the node's arena id); nodes are
// resolved through `nodes: &[Node]`/`&mut Vec<Node>` appended to the Go
// parameter list. Go's `*Node` results are `Option<NodeId>`.

use tsc_core::options_generated::{CompilerOptions, JsxEmit, ModuleDetectionKind, ModuleKind};
use tsc_core::scriptkind::ScriptKind;
use tsc_tspath::{self as tspath, PathKey, RootedFilePath};

use crate::ast::{Node, SourceFileMetaData};
use crate::ast_generated::{
    is_export_assignment, is_export_declaration, is_external_module_reference,
    is_import_declaration, is_import_equals_declaration, is_jsx_fragment,
};
use crate::ids::NodeId;
use crate::modifierflags::ModifierFlags;
use crate::nodeflags::NodeFlags;
use crate::subtreefacts::SubtreeFacts;
use crate::utilities::{
    get_implied_node_format_for_emit_worker, has_syntactic_modifier, is_import_meta,
    is_jsx_opening_like_element,
};

/// `type SourceFileParseOptions struct`
#[derive(Clone, Default)]
pub struct SourceFileParseOptions {
    pub file_name: RootedFilePath,
    pub path_key: PathKey,
    pub external_module_indicator_options: ExternalModuleIndicatorOptions,
}

/// `type ExternalModuleIndicatorOptions struct`
#[derive(Clone, Copy, Default)]
pub struct ExternalModuleIndicatorOptions {
    pub jsx: bool,
    pub force: bool,
}

/// `GetExternalModuleIndicatorOptions(fileName, options, metadata)`.
pub fn get_external_module_indicator_options(
    file_name: &RootedFilePath,
    options: &CompilerOptions,
    metadata: &SourceFileMetaData,
) -> ExternalModuleIndicatorOptions {
    if file_name.is_declaration_file() {
        return ExternalModuleIndicatorOptions::default();
    }

    match options.get_emit_module_detection_kind() {
        ModuleDetectionKind::Force => {
            // All non-declaration files are modules, declaration files still do the usual isFileProbablyExternalModule
            ExternalModuleIndicatorOptions {
                jsx: false,
                force: true,
            }
        }
        ModuleDetectionKind::Legacy => {
            // Files are modules if they have imports, exports, or import.meta
            ExternalModuleIndicatorOptions::default()
        }
        ModuleDetectionKind::Auto => {
            // If module is nodenext or node16, all esm format files are modules
            // If jsx is react-jsx or react-jsxdev then jsx tags force module-ness
            // otherwise, the presence of import or export statments (or import.meta) implies module-ness
            ExternalModuleIndicatorOptions {
                jsx: options.jsx == JsxEmit::ReactJSX || options.jsx == JsxEmit::ReactJSXDev,
                force: is_file_forced_to_be_module_by_format(file_name, options, metadata),
            }
        }
        _ => ExternalModuleIndicatorOptions::default(),
    }
}

/// `isFileForcedToBeModuleByFormatExtensions`
const IS_FILE_FORCED_TO_BE_MODULE_BY_FORMAT_EXTENSIONS: &[&str] = &[
    tspath::EXTENSION_CJS,
    tspath::EXTENSION_CTS,
    tspath::EXTENSION_MJS,
    tspath::EXTENSION_MTS,
];

fn is_file_forced_to_be_module_by_format(
    file_name: &RootedFilePath,
    options: &CompilerOptions,
    metadata: &SourceFileMetaData,
) -> bool {
    // Excludes declaration files - they still require an explicit `export {}` or the like
    // for back compat purposes. The only non-declaration files _not_ forced to be a module are `.js` files
    // that aren't esm-mode (meaning not in a `type: module` scope).
    get_implied_node_format_for_emit_worker(
        file_name,
        options.get_emit_module_kind(),
        metadata,
    ) == ModuleKind::ESNext
        || file_name.extension_is_one_of(IS_FILE_FORCED_TO_BE_MODULE_BY_FORMAT_EXTENSIONS)
}

/// `SetExternalModuleIndicator(file, opts)`
pub fn set_external_module_indicator(
    file: NodeId,
    opts: ExternalModuleIndicatorOptions,
    nodes: &mut Vec<Node>,
) {
    let indicator = get_external_module_indicator(file, opts, nodes);
    nodes[file].as_source_file_mut().external_module_indicator = indicator;
}

fn get_external_module_indicator(
    file: NodeId,
    opts: ExternalModuleIndicatorOptions,
    nodes: &[Node],
) -> Option<NodeId> {
    let file_data = nodes[file].as_source_file();
    if file_data.script_kind == ScriptKind::Json {
        return None;
    }

    if let Some(node) = is_file_probably_external_module(file, nodes) {
        return Some(node);
    }

    if file_data.is_declaration_file {
        return None;
    }

    if opts.jsx
        && let Some(node) = is_file_module_from_using_jsx_tag(file, nodes)
    {
        return Some(node);
    }

    if opts.force {
        return Some(file);
    }

    None
}

fn is_file_probably_external_module(source_file: NodeId, nodes: &[Node]) -> Option<NodeId> {
    if let Some(statements) = &nodes[source_file].as_source_file().statements {
        for &statement in statements.nodes() {
            if is_an_external_module_indicator_node(&nodes[statement], nodes) {
                return Some(statement);
            }
        }
    }
    get_import_meta_if_necessary(source_file, nodes)
}

fn is_an_external_module_indicator_node(node: &Node, nodes: &[Node]) -> bool {
    has_syntactic_modifier(node, ModifierFlags::EXPORT)
        || is_import_equals_declaration(node)
            && node
                .as_import_equals_declaration()
                .module_reference
                .is_some_and(|m| is_external_module_reference(&nodes[m]))
        || is_import_declaration(node)
        || is_export_assignment(node)
        || is_export_declaration(node)
}

fn get_import_meta_if_necessary(source_file: NodeId, nodes: &[Node]) -> Option<NodeId> {
    if nodes[source_file]
        .flags
        .intersects(NodeFlags::POSSIBLY_CONTAINS_IMPORT_META)
    {
        return find_child_node(source_file, &mut |n| is_import_meta(n, nodes), nodes);
    }
    None
}

fn find_child_node(
    root: NodeId,
    check: &mut dyn FnMut(&Node) -> bool,
    nodes: &[Node],
) -> Option<NodeId> {
    fn visit(
        node: NodeId,
        check: &mut dyn FnMut(&Node) -> bool,
        nodes: &[Node],
        result: &mut Option<NodeId>,
    ) -> bool {
        if check(&nodes[node]) {
            *result = Some(node);
            return true;
        }
        nodes[node].for_each_child(nodes, &mut |child| visit(child, check, nodes, result))
    }

    let mut result = None;
    visit(root, check, nodes, &mut result);
    result
}

fn is_file_module_from_using_jsx_tag(file: NodeId, nodes: &[Node]) -> Option<NodeId> {
    walk_tree_for_jsx_tags(file, nodes)
}

// This is a somewhat unavoidable full tree walk to locate a JSX tag - `import.meta` requires the same,
// but we avoid that walk (or parts of it) if at all possible using the `PossiblyContainsImportMeta` node flag.
// Unfortunately, there's no `NodeFlag` space to do the same for JSX.
fn walk_tree_for_jsx_tags(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    fn visitor(node: NodeId, nodes: &[Node], found: &mut Option<NodeId>) -> bool {
        if found.is_some() {
            return true;
        }
        if !nodes[node]
            .subtree_facts(nodes)
            .intersects(SubtreeFacts::CONTAINS_JSX)
        {
            return false;
        }
        if is_jsx_opening_like_element(&nodes[node]) || is_jsx_fragment(&nodes[node]) {
            *found = Some(node);
            return true;
        }
        nodes[node].for_each_child(nodes, &mut |child| visitor(child, nodes, found))
    }

    let mut found = None;
    visitor(node, nodes, &mut found);
    found
}
