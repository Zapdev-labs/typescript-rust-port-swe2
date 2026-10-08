// Ported from tsc/internal/checker/services.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// — free (non-method) functions and data only.
//
// PORT: all `(c *Checker)` methods in services.go are deferred to checker.rs
// (they depend on the full checker: `getSymbolsInScope`, `getPropertyOfType`,
// program state, etc.). This file ports the package-level items:
//
// - `GetResolvedSignatureForSignatureHelp` — routes through the ported
//   `Checker::run_without_resolved_signature_caching` and the
//   `PORT(deferred)` `get_resolved_signature_worker` stub.
// - `isExportSpecifierAlias`.
// - `getPossibleSymbolReferenceNodes` / `getPossibleSymbolReferencePositions`.
// - `knownGenericTypeNames` / `isKnownGenericTypeName`.
//
// `*ast.Node`/`*ast.SourceFile` → `NodeId` + the `nodes` arena parameter;
// `*ast.Identifier`/`*ast.ExportSpecifier` similarly become `NodeId`s.

use tsc_ast::{self as ast, NodeId};
use tsc_core::text::TextPos;
use tsc_debug as debug;

use crate::checker_core::{Checker, CheckMode};
use crate::types::SignatureId;

/// `GetResolvedSignatureForSignatureHelp(node, argumentCount, c)`.
/// `argument_count` is Go's `int` — `-1` is a valid input (unknown arity).
pub fn get_resolved_signature_for_signature_help(
    c: &mut Checker,
    nodes: &[ast::Node],
    node: NodeId,
    argument_count: i32,
) -> (Option<SignatureId>, Vec<SignatureId>) {
    c.run_without_resolved_signature_caching(nodes, node, |c| {
        c.get_resolved_signature_worker(node, CheckMode::IS_FOR_SIGNATURE_HELP, argument_count)
    })
}

/// `isExportSpecifierAlias` — `referenceLocation`/`exportSpecifier` are the
/// nodes Go passes as `*ast.Identifier`/`*ast.ExportSpecifier`.
pub fn is_export_specifier_alias(
    nodes: &[ast::Node],
    reference_location: NodeId,
    export_specifier: NodeId,
) -> bool {
    let export_specifier_data = nodes[export_specifier].as_export_specifier();
    debug::assert_!(
        export_specifier_data.property_name == Some(reference_location)
            || nodes[export_specifier].name() == Some(reference_location),
        "referenceLocation is not export specifier name or property name"
    );
    if let Some(property_name) = export_specifier_data.property_name {
        // Given `export { foo as bar } [from "someModule"]`: It's an alias at
        // `foo`, but at `bar` it's a new symbol.
        property_name == reference_location
    } else {
        // `export { foo } from "foo"` is a re-export.
        // `export { foo };` is not a re-export, it creates an alias for the
        // local variable `foo`.
        // `exportSpecifier.Parent.Parent.ModuleSpecifier() == nil`
        let export_declaration = nodes[export_specifier]
            .parent
            .and_then(|p| nodes[p].parent);
        export_declaration.is_none_or(|d| nodes[d].module_specifier().is_none())
    }
}

/// `getPossibleSymbolReferenceNodes` — `MapNonNil` over
/// `GetTouchingPropertyName` results, dropping the source file node.
pub fn get_possible_symbol_reference_nodes(
    nodes: &mut Vec<ast::Node>,
    source_file: NodeId,
    symbol_name: &str,
    container: Option<NodeId>,
) -> Vec<NodeId> {
    get_possible_symbol_reference_positions(nodes, source_file, symbol_name, container)
        .into_iter()
        .filter_map(|pos| {
            let reference_location =
                tsc_astnav::tokens::get_touching_property_name(nodes, source_file, pos)?;
            if reference_location != source_file {
                Some(reference_location)
            } else {
                None
            }
        })
        .collect()
}

/// `getPossibleSymbolReferencePositions` — text-scan candidate positions.
///
/// PORT: `container.Pos()` slicing is verbatim — Go's
/// `strings.Index(text[container.Pos():], symbolName)` yields a
/// container-relative index for the *first* match while every later position
/// is absolute (the re-search slices `text[startIndex:]`). That asymmetry is
/// preserved rather than "fixed" (call sites always pass the whole source
/// file as `container`, where `Pos() == 0`).
pub fn get_possible_symbol_reference_positions(
    nodes: &[ast::Node],
    source_file: NodeId,
    symbol_name: &str,
    container: Option<NodeId>,
) -> Vec<TextPos> {
    let mut positions: Vec<TextPos> = Vec::new();

    // TODO: Cache symbol existence for files to save text search
    // Also, need to make this work for unicode escapes.

    // Be resilient in the face of a symbol with no name or zero length name.
    if symbol_name.is_empty() {
        return positions;
    }

    let text = &nodes[source_file].as_source_file().text;
    let bytes = text.as_bytes();
    let source_length = bytes.len();
    let symbol_name_length = symbol_name.len();

    let container = container.unwrap_or(source_file);
    let (container_pos, container_end) = {
        let c = &nodes[container];
        (c.pos(), c.end())
    };

    // See the PORT note above: the first index is relative to
    // `container.pos()`; all later positions are absolute, as in Go.
    let mut position: i64 = text[container_pos as usize..]
        .find(symbol_name)
        .map(|i| i as i64)
        .unwrap_or(-1);
    let end_pos = container_end as i64;
    while position >= 0 && position < end_pos {
        // We found a match. Make sure it's not part of a larger word (i.e. the
        // char before and after it have to be a non-identifier char).
        let end_position = position + symbol_name_length as i64;

        // `rune(text[i])` — Go zero-extends the *byte* (not a decoded rune).
        let before_ok = position == 0
            || !tsc_scanner::scanner::is_identifier_part(bytes[position as usize - 1] as i32);
        let after_ok = end_position as usize == source_length
            || !tsc_scanner::scanner::is_identifier_part(bytes[end_position as usize] as i32);
        if before_ok && after_ok {
            // Found a real match. Keep searching.
            positions.push(position as TextPos);
        }
        let start_index = position + symbol_name_length as i64 + 1;
        if start_index as usize > bytes.len() {
            break;
        }
        match text[start_index as usize..].find(symbol_name) {
            Some(found_index) => position = start_index + found_index as i64,
            None => break,
        }
    }

    positions
}

/// `knownGenericTypeNames` (services.go package var).
pub const KNOWN_GENERIC_TYPE_NAMES: &[&str] = &[
    "Array",
    "ArrayLike",
    "ReadonlyArray",
    "Promise",
    "PromiseLike",
    "Iterable",
    "IterableIterator",
    "AsyncIterable",
    "Set",
    "WeakSet",
    "ReadonlySet",
    "Map",
    "WeakMap",
    "ReadonlyMap",
    "Partial",
    "Required",
    "Readonly",
    "Pick",
    "Omit",
    "NonNullable",
];

/// `isKnownGenericTypeName`.
pub fn is_known_generic_type_name(name: &str) -> bool {
    KNOWN_GENERIC_TYPE_NAMES.contains(&name)
}
