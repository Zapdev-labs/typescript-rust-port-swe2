// Ported from tsc/internal/printer/syntheticfile.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::{self as ast, Kind, Node, NodeId};
use tsc_core::text::TextRange;

use crate::change_tracker_writer::ChangeTrackerWriter;
use crate::emit_context::EmitContext;
use crate::printer::{Printer, PrinterOptions};

/// `PrintAndPositionNode` — prints a synthesized node to text using the
/// standard change-tracker printer options, trims the trailing newline, and
/// assigns positions to the resulting node tree.
/// `source_file` may be `None`; when `Some` it is passed to the printer for
/// comment preservation.
/// The returned text is the printed source, and `positioned` is the node with
/// concrete source positions assigned to it and all descendants.
pub fn print_and_position_node(
    nodes: &mut Vec<Node>,
    factory: &mut ast::NodeFactory<'_>,
    node: NodeId,
    source_file: Option<NodeId>,
    new_line: &str,
    indent_size: i32,
    emit_context: &mut EmitContext,
) -> (String, NodeId) {
    let mut writer = ChangeTrackerWriter::new(new_line.to_string(), indent_size);
    let handlers = writer.get_print_handlers();
    Printer::new(
        PrinterOptions {
            new_line: tsc_core::compileroptions::get_new_line_kind(new_line),
            never_ascii_escape: true,
            preserve_source_newlines: true,
            terminate_unterminated_literals: true,
            ..Default::default()
        },
        handlers,
        emit_context,
        nodes,
        &[],
    )
    .write(
        Some(node),
        source_file,
        &mut writer,
        None,
    );

    let mut text = writer.to_string_owned();
    if let Some(stripped) = text.strip_suffix(new_line) {
        text = stripped.to_string();
    }
    let positioned = writer.assign_positions_to_node(nodes, node, factory);
    (text, positioned)
}

/// `CreateSyntheticSourceFile` — wraps a positioned node in a synthetic
/// source file suitable for use with the formatter. The node must already
/// have valid source positions assigned (e.g. via `PrintAndPositionNode` or
/// `AssignPositionsToNode`).
pub fn create_synthetic_source_file(
    nodes: &mut Vec<Node>,
    factory: &mut ast::NodeFactory<'_>,
    node: NodeId,
    text: &str,
    parse_options: &SourceFileParseOptions,
) -> NodeId {
    let eof = factory.new_token(nodes, Kind::EndOfFile);
    nodes[eof].loc = TextRange::new(text.len() as i32, text.len() as i32);
    let mut statements = factory.new_node_list([node]);
    statements.loc = TextRange::new(nodes[node].pos(), nodes[node].end());
    let synthetic_file = factory.new_source_file(
        nodes,
        parse_options,
        text,
        Some(statements),
        Some(eof),
    );
    nodes[synthetic_file].loc = TextRange::new(0, text.len() as i32);
    ast::set_parent_in_children(nodes, synthetic_file);
    synthetic_file
}
