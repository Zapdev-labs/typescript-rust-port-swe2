// Ported from tsc/internal/parser/references.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Go `*ast.SourceFile`/`*ast.Node` parameters are `NodeId`s resolved through
// the `nodes` arena.

use tsc_ast::ast_generated::{is_module_declaration, is_string_literal};
use tsc_ast::utilities::{
    for_each_dynamic_import_or_require_call, get_external_module_name, has_syntactic_modifier,
    is_ambient_module, is_any_import_or_re_export, is_external_module, is_in_js_file,
    set_imports_of_source_file,
};
use tsc_ast::{ModifierFlags, Node, NodeFlags, NodeId};
use tsc_core::nodemodules::{EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES, UNPREFIXED_NODE_CORE_MODULES};
use tsc_core::tristate::{TS_FALSE, TS_TRUE, TS_UNKNOWN};
use tsc_tspath as tspath;

/// `func collectExternalModuleReferences(file *ast.SourceFile)`
pub fn collect_external_module_references(nodes: &mut Vec<Node>, file: NodeId) {
    let statements = nodes[file]
        .as_source_file()
        .statements
        .as_ref()
        .map(|s| s.nodes.to_vec())
        .unwrap_or_default();
    for node in statements {
        collect_module_references(nodes, file, node, false /*inAmbientModule*/);
    }

    if nodes[file]
        .flags
        .intersects(NodeFlags::POSSIBLY_CONTAINS_DYNAMIC_IMPORT)
        || is_in_js_file(Some(file), nodes)
    {
        // PORT: Go's callback mutates `file.imports` mid-iteration; the arena
        // borrow only allows `&[Node]` inside the callback, so specifiers are
        // gathered and appended afterwards (same order, same result).
        let mut extra: Vec<NodeId> = Vec::new();
        for_each_dynamic_import_or_require_call(
            file,
            true, /*includeTypeSpaceImports*/
            true, /*requireStringLiteralLikeArgument*/
            &mut |_node, module_specifier| {
                extra.push(module_specifier);
                false
            },
            nodes,
        );
        if !extra.is_empty() {
            let mut imports = nodes[file].as_source_file().imports.to_vec();
            imports.extend(extra);
            set_imports_of_source_file(nodes, file, imports);
        }
    }
}

/// `func collectModuleReferences(file *ast.SourceFile, node *ast.Statement, inAmbientModule bool)`
fn collect_module_references(
    nodes: &mut Vec<Node>,
    file: NodeId,
    node: NodeId,
    in_ambient_module: bool,
) {
    if is_any_import_or_re_export(&nodes[node]) {
        let module_name_expr = get_external_module_name(&nodes[node], nodes);
        // TypeScript 1.0 spec (April 2014): 12.1.6
        // An ExternalImportDeclaration in an AmbientExternalModuleDeclaration may reference other external modules
        // only through top - level external module names. Relative external module names are not permitted.
        if let Some(module_name_expr) = module_name_expr
            && is_string_literal(&nodes[module_name_expr])
        {
            let module_name = nodes[module_name_expr].text(nodes).into_owned();
            if !module_name.is_empty()
                && (!in_ambient_module || !tspath::is_external_module_name_relative(&module_name))
            {
                let mut imports = nodes[file].as_source_file().imports.to_vec();
                imports.push(module_name_expr);
                set_imports_of_source_file(nodes, file, imports);
                // !!! removed `&& p.currentNodeModulesDepth == 0`
                if nodes[file]
                    .as_source_file()
                    .uses_uri_style_node_core_modules
                    != TS_TRUE
                    && !nodes[file].as_source_file().is_declaration_file
                {
                    if module_name.starts_with("node:")
                        && !EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES.contains(module_name.as_str())
                    {
                        // Presence of `node:` prefix takes precedence over unprefixed node core modules
                        nodes[file]
                            .as_source_file_mut()
                            .uses_uri_style_node_core_modules = TS_TRUE;
                    } else if nodes[file]
                        .as_source_file()
                        .uses_uri_style_node_core_modules
                        == TS_UNKNOWN
                        && UNPREFIXED_NODE_CORE_MODULES.contains(module_name.as_str())
                    {
                        // Avoid `unprefixedNodeCoreModules.has` for every import
                        nodes[file]
                            .as_source_file_mut()
                            .uses_uri_style_node_core_modules = TS_FALSE;
                    }
                }
            }
        }
        return;
    }
    if is_module_declaration(&nodes[node])
        && is_ambient_module(&nodes[node], nodes)
        && (in_ambient_module
            || has_syntactic_modifier(&nodes[node], ModifierFlags::AMBIENT)
            || nodes[file].as_source_file().is_declaration_file)
    {
        // `node.AsModuleDeclaration().Name()` — `Node::name` dispatches.
        let name = nodes[node].name().unwrap();
        let name_text = nodes[name].text(nodes).into_owned();
        // Ambient module declarations can be interpreted as augmentations for some existing external modules.
        // This will happen in two cases:
        // - if current file is external module then module augmentation is a ambient module declaration defined in the top level scope
        // - if current file is not external module then module augmentation is an ambient module declaration with non-relative module name
        //   immediately nested in top level ambient module declaration .
        if is_external_module(nodes[file].as_source_file())
            || (in_ambient_module && !tspath::is_external_module_name_relative(&name_text))
        {
            let mut augmentations = nodes[file].as_source_file().module_augmentations.to_vec();
            augmentations.push(name);
            nodes[file].as_source_file_mut().module_augmentations = augmentations.into();
        } else if !in_ambient_module {
            let mut ambient_names = nodes[file].as_source_file().ambient_module_names.to_vec();
            ambient_names.push(name_text);
            nodes[file].as_source_file_mut().ambient_module_names = ambient_names.into();
            // An AmbientExternalModuleDeclaration declares an external module.
            // This type of declaration is permitted only in the global module.
            // The StringLiteral must specify a top - level external module name.
            // Relative external module names are not permitted
            // NOTE: body of ambient module is always a module block, if it exists
            if let Some(body) = nodes[node].body() {
                let body_statements = nodes[body]
                    .statements()
                    .map(|s| s.to_vec())
                    .unwrap_or_default();
                for statement in body_statements {
                    collect_module_references(
                        nodes, file, statement, true, /*inAmbientModule*/
                    );
                }
            }
        }
    }
}
