// Ported from tsc/internal/printer/changetrackerwriter.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// An `EmitTextWriter` that records the generated text positions of each
// emitted node/node-list so `AssignPositionsToNode` can stamp real source
// positions onto a synthesized tree.
//
// PORT: Go keys its `pos`/`end` maps by pointer identity (`*ast.Node` /
// `*ast.NodeList`). The Rust AST is arena-based and `NodeList` is a value
// type, so keys are `TriviaKey::Node(NodeId)` /
// `TriviaKey::List(pos, end)` — list positions are unique within a print
// session. The maps + `lastNonTriviaPosition` live in `Rc<RefCell<..>>` so
// the `PrintHandlers` closures Go binds to the writer can mutate them.

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::visitor::{NodeVisitor, NodeVisitorHooks, VisitorCx};
use tsc_ast::{self as ast, Node, NodeId};
use tsc_core::core::UTF16Offset;
use tsc_core::text::TextRange;
use tsc_stringutil as stringutil;

use crate::emit_text_writer::EmitTextWriter;
use crate::printer::PrintHandlers;
use crate::text_writer::{TextWriter, get_default_indent_size};

/// `type triviaPositionKey interface { Pos() int; End() int }`
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum TriviaKey {
    /// `*ast.Node` / `*ast.TokenNode`
    Node(NodeId),
    /// `*ast.NodeList` — keyed by its `loc` (unique per print session).
    List(i32, i32),
}

/// The position tables shared between the writer and its print handlers.
#[derive(Default)]
struct Tracked {
    last_non_trivia_position: i32,
    pos: FxHashMap<TriviaKey, i32>,
    end: FxHashMap<TriviaKey, i32>,
}

/// `type ChangeTrackerWriter struct`
pub struct ChangeTrackerWriter {
    text_writer: TextWriter,
    tracked: Rc<RefCell<Tracked>>,
}

impl ChangeTrackerWriter {
    /// `NewChangeTrackerWriter`
    pub fn new(new_line: String, indent_size: i32) -> ChangeTrackerWriter {
        // TODO: Callers passing -1 should pass actual indent options once indent-related formatting is ported.
        let indent_size = if indent_size < 0 {
            get_default_indent_size()
        } else {
            indent_size
        };
        ChangeTrackerWriter {
            text_writer: TextWriter::new(&new_line, indent_size),
            tracked: Rc::new(RefCell::new(Tracked::default())),
        }
    }

    /// `GetPrintHandlers`
    pub fn get_print_handlers(&self) -> PrintHandlers<'static> {
        let tracked = self.tracked.clone();
        let tracked2 = tracked.clone();
        let tracked3 = tracked.clone();
        let tracked4 = tracked.clone();
        let tracked5 = tracked.clone();
        let tracked6 = tracked.clone();
        PrintHandlers {
            on_before_emit_node: Some(Box::new(move |node| {
                if let Some(node) = node {
                    tracked
                        .borrow_mut()
                        .pos
                        .insert(TriviaKey::Node(node), tracked.borrow().last_non_trivia_position);
                }
            })),
            on_after_emit_node: Some(Box::new(move |node| {
                if let Some(node) = node {
                    tracked2
                        .borrow_mut()
                        .end
                        .insert(TriviaKey::Node(node), tracked2.borrow().last_non_trivia_position);
                }
            })),
            on_before_emit_node_list: Some(Box::new(move |nodes| {
                if let Some(nodes) = nodes {
                    let last = tracked3.borrow().last_non_trivia_position;
                    tracked3.borrow_mut().pos.insert(
                        TriviaKey::List(nodes.loc.pos(), nodes.loc.end()),
                        last,
                    );
                }
            })),
            on_after_emit_node_list: Some(Box::new(move |nodes| {
                if let Some(nodes) = nodes {
                    let last = tracked4.borrow().last_non_trivia_position;
                    tracked4.borrow_mut().end.insert(
                        TriviaKey::List(nodes.loc.pos(), nodes.loc.end()),
                        last,
                    );
                }
            })),
            on_before_emit_token: Some(Box::new(move |node| {
                if let Some(node) = node {
                    let last = tracked5.borrow().last_non_trivia_position;
                    tracked5.borrow_mut().pos.insert(TriviaKey::Node(node), last);
                }
            })),
            on_after_emit_token: Some(Box::new(move |node| {
                if let Some(node) = node {
                    let last = tracked6.borrow().last_non_trivia_position;
                    tracked6.borrow_mut().end.insert(TriviaKey::Node(node), last);
                }
            })),
            ..Default::default()
        }
    }

    /// `ct.getPos(node)` / `ct.getPos(nodes)`
    fn get_pos(&self, key: TriviaKey) -> i32 {
        self.tracked.borrow().pos.get(&key).copied().unwrap_or_default()
    }

    /// `ct.getEnd(node)` / `ct.getEnd(nodes)`
    fn get_end(&self, key: TriviaKey) -> i32 {
        self.tracked.borrow().end.get(&key).copied().unwrap_or_default()
    }

    /// `setLastNonTriviaPosition`
    fn set_last_non_trivia_position(&self, s: &str, force: bool) {
        if force || tsc_scanner::scanner::skip_trivia(s, 0) as usize != s.len() {
            let mut tracked = self.tracked.borrow_mut();
            tracked.last_non_trivia_position = self.text_writer.get_text_pos();
            // trim trailing whitespaces
            let bytes = s.as_bytes();
            let mut pos = bytes.len();
            while pos > 0 {
                let (r, size) = decode_last_rune(&s[..pos]);
                if stringutil::is_white_space_like(r) {
                    pos -= size;
                } else {
                    break;
                }
            }
            tracked.last_non_trivia_position -= (s.len() - pos) as i32;
        }
    }

    /// `AssignPositionsToNode`
    pub fn assign_positions_to_node(
        &self,
        nodes: &mut Vec<Node>,
        node: NodeId,
        factory: &mut ast::NodeFactory<'_>,
    ) -> NodeId {
        let tracked = self.tracked.clone();
        let tracked2 = self.tracked.clone();
        let tracked3 = self.tracked.clone();
        let tracked4 = self.tracked.clone();
        let tracked5 = self.tracked.clone();
        let visitor = NodeVisitor::new(
            Box::new(
                move |v: &NodeVisitor<'_>, cx: &mut VisitorCx<'_, '_>, n: NodeId| {
                    Some(assign_positions_to_node_worker(&tracked, cx, n, v))
                },
            ),
            NodeVisitorHooks {
                visit_node: Some(Box::new(move |cx, n, v| {
                    Some(assign_positions_to_node_worker(&tracked2, cx, n, v))
                })),
                visit_token: Some(Box::new(move |cx, n, v| {
                    Some(assign_positions_to_node_worker(&tracked3, cx, n, v))
                })),
                visit_nodes: Some(Box::new(move |cx, ns, v| {
                    assign_positions_to_node_array(&tracked4, cx, ns, v)
                })),
                visit_modifiers: Some(Box::new(move |cx, modifiers, v| {
                    if let Some(modifiers) = modifiers {
                        let node_list = tsc_ast::NodeList {
                            loc: modifiers.loc,
                            nodes: modifiers.nodes,
                            is_missing: false,
                        };
                        let new_node_list = assign_positions_to_node_array(
                            &tracked5,
                            cx,
                            Some(node_list),
                            v,
                        )?;
                        // Return a new ModifierList so that VisitEachChild/Update detects the
                        // change and creates a new node with reassigned child positions.
                        let mut ml =
                            cx.factory
                                .new_modifier_list(cx.nodes, new_node_list.nodes);
                        ml.loc = new_node_list.loc;
                        return Some(ml);
                    }
                    modifiers
                })),
                ..Default::default()
            },
        );
        let mut cx = VisitorCx { nodes, factory };
        assign_positions_to_node_worker(&self.tracked, &mut cx, node, &visitor)
    }

    /// `writer.String()` — Go returns the buffer contents.
    pub fn to_string_owned(&self) -> String {
        self.text_writer.get_text()
    }
}

impl EmitTextWriter for ChangeTrackerWriter {
    /// `ct.Write`
    fn write(&mut self, text: &str) {
        self.text_writer.write(text);
        self.set_last_non_trivia_position(text, false);
    }

    /// `ct.WriteTrailingSemicolon`
    fn write_trailing_semicolon(&mut self, text: &str) {
        self.text_writer.write_trailing_semicolon(text);
        self.set_last_non_trivia_position(text, false);
    }

    /// `ct.WriteComment`
    fn write_comment(&mut self, text: &str) {
        self.text_writer.write_comment(text);
    }

    /// `ct.WriteKeyword`
    fn write_keyword(&mut self, text: &str) {
        self.text_writer.write_keyword(text);
        self.set_last_non_trivia_position(text, false);
    }

    /// `ct.WriteOperator`
    fn write_operator(&mut self, text: &str) {
        self.text_writer.write_operator(text);
        self.set_last_non_trivia_position(text, false);
    }

    /// `ct.WritePunctuation`
    fn write_punctuation(&mut self, text: &str) {
        self.text_writer.write_punctuation(text);
        self.set_last_non_trivia_position(text, false);
    }

    /// `ct.WriteSpace`
    fn write_space(&mut self, text: &str) {
        self.text_writer.write_space(text);
        self.set_last_non_trivia_position(text, false);
    }

    /// `ct.WriteStringLiteral`
    fn write_string_literal(&mut self, text: &str) {
        self.text_writer.write_string_literal(text);
        self.set_last_non_trivia_position(text, false);
    }

    /// `ct.WriteParameter`
    fn write_parameter(&mut self, text: &str) {
        self.text_writer.write_parameter(text);
        self.set_last_non_trivia_position(text, false);
    }

    /// `ct.WriteProperty`
    fn write_property(&mut self, text: &str) {
        self.text_writer.write_property(text);
        self.set_last_non_trivia_position(text, false);
    }

    /// `ct.WriteSymbol`
    fn write_symbol(&mut self, text: &str, symbol: tsc_ast::SymbolId) {
        self.text_writer.write_symbol(text, symbol);
        self.set_last_non_trivia_position(text, false);
    }

    /// `ct.WriteLine`
    fn write_line(&mut self) {
        self.text_writer.write_line();
    }

    /// `ct.WriteLineForce`
    fn write_line_force(&mut self, force: bool) {
        self.text_writer.write_line_force(force);
    }

    /// `ct.IncreaseIndent`
    fn increase_indent(&mut self) {
        self.text_writer.increase_indent();
    }

    /// `ct.DecreaseIndent`
    fn decrease_indent(&mut self) {
        self.text_writer.decrease_indent();
    }

    /// `ct.Clear`
    fn clear(&mut self) {
        self.text_writer.clear();
        self.tracked.borrow_mut().last_non_trivia_position = 0;
    }

    /// `ct.RawWrite`
    fn raw_write(&mut self, s: &str) {
        self.text_writer.raw_write(s);
        self.set_last_non_trivia_position(s, false);
    }

    /// `ct.WriteLiteral`
    fn write_literal(&mut self, s: &str) {
        self.text_writer.write_literal(s);
        self.set_last_non_trivia_position(s, true);
    }

    /// `ct.GetTextPos`
    fn get_text_pos(&self) -> i32 {
        self.text_writer.get_text_pos()
    }

    /// `ct.GetLine`
    fn get_line(&self) -> i32 {
        self.text_writer.get_line()
    }

    /// `ct.GetColumn`
    fn get_column(&self) -> UTF16Offset {
        self.text_writer.get_column()
    }

    /// `ct.GetIndent`
    fn get_indent(&self) -> i32 {
        self.text_writer.get_indent()
    }

    /// `ct.IsAtStartOfLine`
    fn is_at_start_of_line(&self) -> bool {
        self.text_writer.is_at_start_of_line()
    }

    /// `ct.HasTrailingComment`
    fn has_trailing_comment(&self) -> bool {
        self.text_writer.has_trailing_comment()
    }

    /// `ct.HasTrailingWhitespace`
    fn has_trailing_whitespace(&self) -> bool {
        self.text_writer.has_trailing_whitespace()
    }

    /// `ct.String`
    fn get_text(&self) -> String {
        self.text_writer.get_text()
    }

    fn into_any(self: Box<Self>) -> Box<dyn std::any::Any> {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

/// `(ct *ChangeTrackerWriter) assignPositionsToNodeWorker`
fn assign_positions_to_node_worker(
    tracked: &Rc<RefCell<Tracked>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    v: &NodeVisitor<'_>,
) -> NodeId {
    let visited = v.visit_each_child(cx, node).unwrap_or(node);
    // Assigning positions must not mutate the caller's node: it may be printed again (a change in a
    // content-mapped file is formatted once per virtual projection of its insertion point), and a node
    // that has acquired positions is printed by reading text back out of the source file. VisitEachChild
    // returns a fresh node only when a child changed, so clone whenever it hands back the input.
    let new_node = if visited == node {
        cx.factory.clone_node(cx.nodes, visited)
    } else {
        visited
    };
    // PORT: Go sets `child.Parent = newNode` for each direct child;
    // `set_parent_in_children` assigns parents to all descendants, which the
    // recursive workers would compute anyway.
    ast::set_parent_in_children(cx.nodes, new_node);
    let (pos, end) = {
        let t = tracked.borrow();
        (
            t.pos.get(&TriviaKey::Node(node)).copied().unwrap_or_default(),
            t.end.get(&TriviaKey::Node(node)).copied().unwrap_or_default(),
        )
    };
    cx.nodes[new_node].loc = TextRange::new(pos, end);
    new_node
}

/// `(ct *ChangeTrackerWriter) assignPositionsToNodeArray`
fn assign_positions_to_node_array(
    tracked: &Rc<RefCell<Tracked>>,
    cx: &mut VisitorCx<'_, '_>,
    nodes: Option<tsc_ast::NodeList>,
    v: &NodeVisitor<'_>,
) -> Option<tsc_ast::NodeList> {
    let nodes = nodes?;
    let visited = v.visit_nodes(cx, Some(nodes.clone()));
    let Some(visited) = visited else {
        return None;
    };
    // clone nodearray if necessary
    let mut node_array = if visited == nodes {
        visited.clone_list(&mut cx.factory)
    } else {
        visited
    };
    let (pos, end) = {
        let t = tracked.borrow();
        let key = TriviaKey::List(nodes.loc.pos(), nodes.loc.end());
        (
            t.pos.get(&key).copied().unwrap_or_default(),
            t.end.get(&key).copied().unwrap_or_default(),
        )
    };
    node_array.loc = TextRange::new(pos, end);
    Some(node_array)
}

/// `utf8.DecodeLastRuneInString`
fn decode_last_rune(s: &str) -> (char, usize) {
    match s.chars().next_back() {
        Some(ch) => (ch, ch.len_utf8()),
        None => ('\u{FFFD}', 0),
    }
}