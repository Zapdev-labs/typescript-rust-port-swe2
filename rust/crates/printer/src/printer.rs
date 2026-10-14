// Ported from tsc/internal/printer/printer.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// A Printer for pretty-printing TS ASTs and writer interfaces and
// implementations for using them.
//
// PORT: Go's `Printer` both owns long-lived configuration (options, handlers,
// emit context, name generator, the node arena) and accumulates per-write emit
// state (the writer, source-map state, comment containers). Go can mutate the
// interface-valued `writer` field at will; Rust cannot reassign a
// `&mut dyn EmitTextWriter` field borrowed from a caller across arbitrary
// `&mut self` calls, so emission happens on a per-`write()` `Emitter` value
// that borrows the `Printer` and the writer. `enterNode`/`exitNode` state is
// `Option<CommentState>`/`Option<SourceMapState>` instead of arena cells
// (`commentStateArena`/`sourceMapStateArena` were allocation caches only).
// `NodeId` replaces `*ast.Node`; `Option<NodeId>`/`Option<NodeList>` replace
// nil pointers and nil lists.

use std::ops::{Deref, DerefMut};

use rustc_hash::FxHashMap;
use tsc_ast::precedence::{
    OperatorPrecedence, TypePrecedence, get_expression_precedence, get_leftmost_expression,
    get_type_node_precedence,
};
use tsc_ast::{
    self as ast, CommentRange, FileReference, Kind, ModifierList, Node, NodeFlags, NodeId,
    NodeList, SymbolId,
};
use tsc_core::options_generated::{NewLineKind, ScriptTarget};
use tsc_core::scriptkind::ScriptKind;
use tsc_core::text::{TextPos, TextRange};
use tsc_core::tristate::Tristate;
use tsc_scanner::scanner;
use tsc_sourcemap as sourcemap;
use tsc_stringutil as stringutil;

use crate::emit_context::{EmitContext, SnippetElement, SnippetKind, SynthesizedComment};
use crate::emit_flags::EmitFlags;
use crate::emit_helpers::{UniqueNameFn, compare_emit_helpers};
use crate::emit_text_writer::EmitTextWriter;
use crate::name_generator::NameGenerator;
use crate::semicolon_writer::get_trailing_semicolon_deferring_writer;
use crate::text_writer::{TextWriter, get_default_indent_size, get_indent_string};
use crate::utilities::{
    self as util, GET_LITERAL_TEXT_FLAGS_NEVER_ASCII_ESCAPE, GET_LITERAL_TEXT_FLAGS_NONE,
    GET_LITERAL_TEXT_FLAGS_TERMINATE_UNTERMINATED_LITERALS, GetLiteralTextFlags, greatest_end,
};

/// `type PrinterOptions struct`
#[derive(Clone, Default)]
pub struct PrinterOptions {
    pub remove_comments: bool,
    pub new_line: NewLineKind,
    pub omit_trailing_semicolon: bool,
    pub no_emit_helpers: bool,
    // pub module: ModuleKind,
    // pub module_resolution: ModuleResolutionKind,
    pub target: ScriptTarget,
    pub source_map: bool,
    pub inline_source_map: bool,
    pub inline_sources: bool,
    pub omit_brace_source_map_positions: bool,
    // pub extended_diagnostics: bool,
    pub only_print_jsdoc_style: bool,
    pub never_ascii_escape: bool,
    // pub strip_internal: bool,
    pub preserve_source_newlines: bool,
    /// !!!
    pub terminate_unterminated_literals: bool,
}

/// `sourcemap.Source` as seen by the printer — either an arena source file
/// (`Node`) or a synthetic file entry such as the declaration-map original
/// source (Go's `declarationMapSource`, a `sourcemap.Source` impl with only
/// file name + text + line map).
#[derive(Clone)]
pub enum SourceMapSource {
    Node(NodeId),
    Synthetic(std::rc::Rc<SyntheticSourceFile>),
}

impl SourceMapSource {
    /// `source.FileName()`.
    pub fn file_name<'a>(&'a self, nodes: &'a [ast::Node]) -> &'a tsc_tspath::RootedFilePath {
        match self {
            Self::Node(id) => nodes[*id].as_source_file().file_name(),
            Self::Synthetic(s) => &s.file_name,
        }
    }
}

/// Go's `declarationMapSource` — the original (pre-mapping) text of a
/// content-mapped file, used as the `sourcemap.Source` for mapped positions.
pub struct SyntheticSourceFile {
    pub file_name: tsc_tspath::RootedFilePath,
    pub text: String,
    pub line_map: Vec<tsc_core::text::TextPos>,
}

impl PartialEq for SourceMapSource {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Node(a), Self::Node(b)) => a == b,
            (Self::Synthetic(a), Self::Synthetic(b)) => std::rc::Rc::ptr_eq(a, b),
            _ => false,
        }
    }
}

/// `MapSourcePosition` composes source-map positions before they reach the
/// generator. The first argument is the in-flight source's `FileName()` —
/// Go's handler compares it against the content-mapped file's name. Returning
/// `None` for the mapped position emits a generated-only mapping.
pub type MapSourcePosition<'a> = Box<
    dyn FnMut(
            &tsc_tspath::RootedFilePath,
            SourceMapSource,
            i32,
        ) -> (Option<SourceMapSource>, Option<i32>)
        + 'a,
>;

/// `type PrintHandlers struct`
///
/// PORT: Go's `func` fields are boxed `FnMut` closures.
#[derive(Default)]
pub struct PrintHandlers<'a> {
    /// A hook used by the Printer when generating unique names to avoid
    /// collisions with globally defined names that exist outside of the
    /// current source file.
    pub has_global_name: Option<Box<dyn FnMut(&str) -> bool + 'a>>,
    /// `MapSourcePosition`
    pub map_source_position: Option<MapSourcePosition<'a>>,
    // !!!
    /////on_emit_node ...
    /////is_emit_notification_enabled ...
    /////substitute_node ...
    /////on_emit_source_map_of_node ...
    /// `OnBeforeEmitNode`
    pub on_before_emit_node: Option<Box<dyn FnMut(Option<NodeId>) + 'a>>,
    /// `OnAfterEmitNode`
    pub on_after_emit_node: Option<Box<dyn FnMut(Option<NodeId>) + 'a>>,
    /// `OnBeforeEmitNodeList`
    pub on_before_emit_node_list: Option<Box<dyn FnMut(Option<&NodeList>) + 'a>>,
    /// `OnAfterEmitNodeList`
    pub on_after_emit_node_list: Option<Box<dyn FnMut(Option<&NodeList>) + 'a>>,
    /// `OnBeforeEmitToken`
    pub on_before_emit_token: Option<Box<dyn FnMut(Option<NodeId>) + 'a>>,
    /// `OnAfterEmitToken`
    pub on_after_emit_token: Option<Box<dyn FnMut(Option<NodeId>) + 'a>>,
    /// Correlates `which` member list on `original_parent` when that node
    /// lives in another file's arena; returns whether the original list
    /// has a trailing comma. `None` = the host could not resolve the
    /// foreign node (Go dereferences raw pointers instead of arena ids).
    /// Args: `(original_parent, which)`.
    pub original_list_has_trailing_comma:
        Option<Box<dyn FnMut(NodeId, OriginalListKind) -> Option<bool> + 'a>>,
}

/// Which member list an emitted `NodeList` corresponds to on its parent —
/// the result of Go's `switch children { case parentNode.XList(): }`
/// pointer comparisons in `p.hasTrailingComma`, computed in the printer's
/// own arena so it also applies when the original node lives in a
/// foreign file arena.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum OriginalListKind {
    /// `originalList := children` — no parent list candidate matched.
    Children,
    PropertyList,
    ElementList,
    TypeArgumentList,
    ArgumentList,
    TypeParameterList,
    ParameterList,
    Attributes,
}

/// Fetches `which` member list from `parent` — the counterpart of the
/// candidate selection in `Printer::has_trailing_comma`, usable on the
/// original node's arena whether or not it is the printer's own.
pub fn original_list_for_kind(
    nodes: &[Node],
    parent: NodeId,
    which: OriginalListKind,
) -> Option<NodeList> {
    let pn = &nodes[parent];
    match which {
        OriginalListKind::Children => None,
        OriginalListKind::PropertyList => pn.property_list().cloned(),
        OriginalListKind::ElementList => pn.element_list().cloned(),
        OriginalListKind::TypeArgumentList => pn.type_argument_list().cloned(),
        OriginalListKind::ArgumentList => pn.argument_list().cloned(),
        OriginalListKind::TypeParameterList => pn.type_parameter_list().cloned(),
        OriginalListKind::ParameterList => pn.parameter_list().cloned(),
        OriginalListKind::Attributes => pn.as_import_attributes().attributes.clone(),
    }
}

/// `type detachedCommentsInfo struct`
#[derive(Clone, Copy)]
struct DetachedCommentsInfo {
    node_pos: TextPos,
    detached_comment_end_pos: TextPos,
}

/// `type commentState struct`
#[derive(Clone, Copy, Default)]
pub(crate) struct CommentState {
    /// holds the emit flags for the current node
    pub(crate) emit_flags: EmitFlags,
    /// holds the comment range calculated for the current node
    pub(crate) comment_range: TextRange,
    /// captures the value of containerPos prior to entering an node
    pub(crate) container_pos: TextPos,
    /// captures the value of containerEnd prior to entering an node
    pub(crate) container_end: TextPos,
    /// captures the value of declarationListContainerEnd prior to entering an
    /// node
    pub(crate) declaration_list_container_end: TextPos,
}

/// `type sourceMapState struct`
#[derive(Clone, Copy)]
struct SourceMapState {
    /// holds the emit flags for the current node
    emit_flags: EmitFlags,
    /// holds the source map range calculated for the current node
    source_map_range: TextRange,
    /// captures whether the source map range was set for the current node
    has_token_source_map_range: bool,
}

/// `type printerState struct`
#[derive(Clone, Copy, Default)]
pub(crate) struct PrinterState {
    pub(crate) comment_state: Option<CommentState>,
    pub(crate) source_map_state: Option<SourceMapState>,
}

/// `type WriteKind int`
#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum WriteKind {
    /// `WriteKindNone`
    #[default]
    None,
    /// `WriteKindKeyword`
    Keyword,
    /// `WriteKindOperator`
    Operator,
    /// `WriteKindPunctuation`
    Punctuation,
    /// `WriteKindStringLiteral`
    StringLiteral,
    /// `WriteKindParameter`
    Parameter,
    /// `WriteKindProperty`
    Property,
    /// `WriteKindComment`
    Comment,
    /// `WriteKindLiteral`
    Literal,
}

/// `type tokenEmitFlags uint32`
pub(crate) type TokenEmitFlags = u32;

/// `tefNoComments`
pub(crate) const TEF_NO_COMMENTS: TokenEmitFlags = 1 << 0;
/// `tefIndentLeadingComments`
pub(crate) const TEF_INDENT_LEADING_COMMENTS: TokenEmitFlags = 1 << 1;
/// `tefNoSourceMaps`
pub(crate) const TEF_NO_SOURCE_MAPS: TokenEmitFlags = 1 << 2;
/// `tefNone`
pub(crate) const TEF_NONE: TokenEmitFlags = 0;

/// `type commentSeparator uint32`
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum CommentSeparator {
    /// `commentSeparatorNone`
    None,
    /// `commentSeparatorBefore`
    Before,
    /// `commentSeparatorAfter`
    After,
}

/// `type Printer struct` — the long-lived printer value.
///
/// PORT: `nodes` and `symbols` are borrowed arenas (Go threads pointers
/// through the graph instead). `writer`, the current-source-map state, and
/// the comment containers live on the per-`write()` [`Emitter`].
pub struct Printer<'a> {
    /// `PrintHandlers` — embedded in Go.
    pub handlers: PrintHandlers<'a>,
    /// `Options`
    pub options: PrinterOptions,
    /// `emitContext *EmitContext`
    pub(crate) emit_context: &'a mut EmitContext,
    /// The node arena (`NodeId` indices).
    pub(crate) nodes: &'a mut Vec<Node>,
    /// The binder-owned symbol arena used by name generation's
    /// `isUniqueLocalName`.
    pub(crate) symbols: &'a ast::SymbolArena,
    /// `currentSourceFile *ast.SourceFile` — the `NodeId` of the SourceFile
    /// node.
    pub(crate) current_source_file: Option<NodeId>,
    /// `nameGenerator NameGenerator`
    pub(crate) name_generator: NameGenerator,
    /// `IdToSymbol map[*ast.IdentifierNode]*ast.Symbol` — optional external
    /// map used by `emitIdentifierText`.
    pub id_to_symbol: Option<&'a FxHashMap<NodeId, SymbolId>>,
    /// `ownWriter EmitTextWriter` — a reusable writer for `Emit`.
    own_writer: Option<TextWriter>,
    /// `mostRecentSourceMapSourceIndex`
    most_recent_source_map_source: Option<SourceMapSource>,
    most_recent_source_map_source_index: i32,
}

impl<'a> Printer<'a> {
    /// `NewPrinter(options, handlers, emitContext)`
    ///
    /// PORT: `nodes` and `symbols` are borrowed here since the Go code
    /// navigates the arena via `*ast.Node`/`SymbolTable` pointers.
    pub fn new(
        options: PrinterOptions,
        handlers: PrintHandlers<'a>,
        emit_context: &'a mut EmitContext,
        nodes: &'a mut Vec<Node>,
        symbols: &'a ast::SymbolArena,
    ) -> Printer<'a> {
        // wire up name generator
        let name_generator = NameGenerator {
            shared: emit_context.shared(),
            ..Default::default()
        };
        Printer {
            options,
            handlers,
            emit_context,
            nodes,
            symbols,
            name_generator,
            current_source_file: None,
            id_to_symbol: None,
            own_writer: None,
            most_recent_source_map_source: None,
            most_recent_source_map_source_index: -1,
        }
    }

    /// `p.Emit(node, sourceFile)`
    pub fn emit(&mut self, node: Option<NodeId>, source_file: Option<NodeId>) -> String {
        // ensure a reusable writer
        let mut own_writer = self
            .own_writer
            .take()
            .unwrap_or_else(|| TextWriter::new(self.options.new_line.get_new_line_character(), 0));

        self.write(node, source_file, &mut own_writer, None);
        let text = own_writer.get_text();
        own_writer.clear();
        self.own_writer = Some(own_writer);
        text
    }

    /// `p.EmitSourceFile(sourceFile)`
    pub fn emit_source_file(&mut self, source_file: NodeId) -> String {
        self.emit(Some(source_file), Some(source_file))
    }

    /// `p.Write(node, sourceFile, writer, sourceMapGenerator)`
    pub fn write(
        &mut self,
        node: Option<NodeId>,
        source_file: Option<NodeId>,
        writer: &mut (dyn EmitTextWriter + '_),
        source_map_generator: Option<&mut sourcemap::Generator>,
    ) {
        if self.options.omit_trailing_semicolon {
            let mut deferring = get_trailing_semicolon_deferring_writer(writer);
            self.write_inner(node, source_file, &mut deferring, source_map_generator);
        } else {
            self.write_inner(node, source_file, writer, source_map_generator);
        }
    }

    /// `p.Write` with the final `EmitTextWriter` resolved.
    fn write_inner(
        &mut self,
        node: Option<NodeId>,
        source_file: Option<NodeId>,
        writer: &mut (dyn EmitTextWriter + '_),
        source_map_generator: Option<&mut sourcemap::Generator>,
    ) {
        let saved_current_source_file = self.current_source_file;
        let saved_source_map_source_index = self.most_recent_source_map_source_index;
        let saved_most_recent_source_map_source = self.most_recent_source_map_source.clone();
        let comments_disabled = self.options.remove_comments;

        let mut emitter = Emitter {
            p: self,
            writer,
            source_maps_disabled: source_map_generator.is_none(),
            source_map_generator,
            source_map_source: None,
            source_map_source_index: -1,
            source_map_source_is_json: false,
            source_map_line_char_cache: None,
            unique_helper_names: None,
            external_helpers_module_name: None,
            next_list_element_pos: -1,
            write_kind: WriteKind::None,
            container_pos: -1,
            container_end: -1,
            declaration_list_container_end: -1,
            detached_comments_info: Vec::new(),
            comments_disabled,
            in_extends: false,
        };
        emitter.writer.clear();
        emitter.set_source_file(source_file);
        emitter.emit_node_dispatch(node);

        self.current_source_file = saved_current_source_file;
        self.most_recent_source_map_source_index = saved_source_map_source_index;
        self.most_recent_source_map_source = saved_most_recent_source_map_source;
    }
}

/// `p.writer` during a `Write` — the session that owns emit state.
///
/// PORT: see the module-level note; this replaces Go's practice of
/// saving/restoring a dozen `Printer` fields in `Write`.
pub(crate) struct Emitter<'p, 'a> {
    pub(crate) p: &'p mut Printer<'a>,
    /// `p.writer`
    pub(crate) writer: &'p mut (dyn EmitTextWriter + 'p),
    /// `p.sourceMapsDisabled`
    source_maps_disabled: bool,
    /// `p.sourceMapGenerator`
    source_map_generator: Option<&'p mut sourcemap::Generator>,
    /// `p.sourceMapSource`
    source_map_source: Option<SourceMapSource>,
    /// `p.sourceMapSourceIndex`
    source_map_source_index: i32,
    /// `p.sourceMapSourceIsJson`
    source_map_source_is_json: bool,
    /// `p.sourceMapLineCharCache`
    source_map_line_char_cache: Option<LineCharacterCache>,
    /// `p.uniqueHelperNames` — `Some` iff the `EFExternalHelpers` flag was
    /// present on the file (Go tracks map nil-ness).
    unique_helper_names: Option<FxHashMap<String, NodeId>>,
    /// `p.externalHelpersModuleName`
    external_helpers_module_name: Option<NodeId>,
    /// `p.nextListElementPos`
    next_list_element_pos: TextPos,
    /// `p.writeKind`
    write_kind: WriteKind,
    /// `p.containerPos`
    container_pos: TextPos,
    /// `p.containerEnd`
    container_end: TextPos,
    /// `p.declarationListContainerEnd`
    declaration_list_container_end: TextPos,
    /// `p.detachedCommentsInfo` — a stack.
    detached_comments_info: Vec<DetachedCommentsInfo>,
    /// `p.commentsDisabled`
    comments_disabled: bool,
    /// `p.inExtends`
    in_extends: bool,
}

impl<'p, 'a> Deref for Emitter<'p, 'a> {
    type Target = Printer<'a>;

    fn deref(&self) -> &Self::Target {
        self.p
    }
}

impl<'p, 'a> DerefMut for Emitter<'p, 'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.p
    }
}

/// `lineCharacterCache` — cached line/character lookups for a source file,
/// optimized for monotonically increasing positions during source-map emit.
pub(crate) struct LineCharacterCache {
    line_map: Vec<TextPos>,
    text: String,
    cached_line: i32,
    cached_pos: i32,
    cached_char: i32,
    has_cached: bool,
}

impl LineCharacterCache {
    /// `newLineCharacterCache(source)`
    fn new(line_map: Vec<TextPos>, text: String) -> Self {
        LineCharacterCache {
            line_map,
            text,
            cached_line: 0,
            cached_pos: 0,
            cached_char: 0,
            has_cached: false,
        }
    }

    /// `(c *lineCharacterCache) getLineAndCharacter` — returns the 0-based
    /// line number and UTF-16 code unit offset from the start of that line.
    fn get_line_and_character(&mut self, pos: i32) -> (i32, i32) {
        let line = scanner::compute_line_of_position(&self.line_map, pos);
        let line_start = self.line_map[line as usize];
        let end_pos = pos.min(self.text.len() as i32);
        let character;
        if self.has_cached && line == self.cached_line && end_pos >= self.cached_pos {
            character = self.cached_char
                + tsc_core::core::utf16_len(&self.text[self.cached_pos as usize..end_pos as usize]);
        } else {
            character =
                tsc_core::core::utf16_len(&self.text[line_start as usize..end_pos as usize]);
        }
        let cached_char = character;
        let character = character + (pos - end_pos);
        self.cached_line = line;
        self.cached_pos = end_pos;
        self.cached_char = cached_char;
        self.has_cached = true;
        (line, character)
    }
}

impl<'p, 'a> Emitter<'p, 'a> {
    /// `p.setSourceFile(sourceFile)`
    fn set_source_file(&mut self, source_file: Option<NodeId>) {
        self.p.current_source_file = source_file;
        self.unique_helper_names = None;
        self.external_helpers_module_name = None;
        if let Some(source_file) = source_file {
            let most_original = self
                .p
                .emit_context
                .most_original(Some(source_file))
                .unwrap_or(source_file);
            if self
                .p
                .emit_context
                .emit_flags(most_original)
                .has(EmitFlags::EXTERNAL_HELPERS)
            {
                self.unique_helper_names = Some(FxHashMap::default());
            }
            self.external_helpers_module_name = self
                .p
                .emit_context
                .get_external_helpers_module_name(self.p.nodes, source_file);
            self.set_source_map_source(SourceMapSource::Node(source_file));
        }
        // !!!
    }

    #[inline]
    fn w(&mut self) -> &mut (dyn EmitTextWriter + 'p) {
        &mut *self.writer
    }

    //
    // Low-level writing
    //

    /// `p.writeAs`
    fn write_as(&mut self, text: &str, write_kind: WriteKind) {
        match write_kind {
            WriteKind::None => self.w().write(text),
            WriteKind::Parameter => self.write_parameter(text),
            WriteKind::Keyword => self.write_keyword(text),
            WriteKind::Operator => self.write_operator(text),
            WriteKind::Property => self.write_property(text),
            WriteKind::Punctuation => self.write_punctuation(text),
            WriteKind::StringLiteral => self.w().write_string_literal(text),
            WriteKind::Comment => self.write_comment(text),
            WriteKind::Literal => self.write_literal(text),
        }
    }

    /// `p.write`
    fn write(&mut self, text: &str) {
        self.write_as(text, self.write_kind);
    }

    /// `p.setWriteKind`
    fn set_write_kind(&mut self, kind: WriteKind) -> WriteKind {
        let previous = self.write_kind;
        self.write_kind = kind;
        previous
    }

    /// `p.writeSymbol`
    fn write_symbol(&mut self, text: &str, opt_symbol: Option<SymbolId>) {
        match opt_symbol {
            None => self.write(text),
            Some(symbol) => self.w().write_symbol(text, symbol),
        }
    }

    /// `p.writeLiteral`
    fn write_literal(&mut self, text: &str) {
        self.w().write_literal(text)
    }
    /// `p.writePunctuation`
    fn write_punctuation(&mut self, text: &str) {
        self.w().write_punctuation(text)
    }
    /// `p.writeOperator`
    fn write_operator(&mut self, text: &str) {
        self.w().write_operator(text)
    }
    /// `p.writeKeyword`
    fn write_keyword(&mut self, text: &str) {
        self.w().write_keyword(text)
    }
    /// `p.writeProperty`
    fn write_property(&mut self, text: &str) {
        self.w().write_property(text)
    }
    /// `p.writeParameter`
    fn write_parameter(&mut self, text: &str) {
        self.w().write_parameter(text)
    }
    /// `p.writeComment`
    fn write_comment(&mut self, text: &str) {
        self.w().write_comment(text)
    }
    /// `p.writeSpace`
    fn write_space(&mut self) {
        self.w().write_space(" ")
    }
    /// `p.writeLine`
    fn write_line(&mut self) {
        self.w().write_line()
    }

    /// `p.writeLineRepeat`
    fn write_line_repeat(&mut self, count: i32) {
        for _ in 0..count {
            self.write_line();
        }
    }

    /// `p.writeLines`
    fn write_lines(&mut self, text: &str) {
        let lines = stringutil::split_lines(text.as_bytes());
        let indentation = stringutil::guess_indentation(&lines);
        for line in lines {
            let line = if indentation > 0 {
                &line[(indentation as usize).min(line.len())..]
            } else {
                line
            };
            if !line.is_empty() {
                self.write_line();
                // PORT: `lines` borrows `text.as_bytes()`, which is valid UTF-8.
                self.write(std::str::from_utf8(line).expect("line is utf8"));
            }
        }
    }

    /// `p.writeTrailingSemicolon`
    fn write_trailing_semicolon(&mut self) {
        self.w().write_trailing_semicolon(";")
    }
    /// `p.increaseIndent`
    fn increase_indent(&mut self) {
        self.w().increase_indent()
    }
    /// `p.decreaseIndent`
    fn decrease_indent(&mut self) {
        self.w().decrease_indent()
    }

    /// `p.increaseIndentIf`
    fn increase_indent_if(&mut self, indent_requested: bool) {
        if indent_requested {
            self.increase_indent();
        }
    }

    /// `p.decreaseIndentIf`
    fn decrease_indent_if(&mut self, indent_requested: bool) {
        if indent_requested {
            self.decrease_indent();
        }
    }

    /// `p.writeLineOrSpace`
    fn write_line_or_space(
        &mut self,
        parent_node: Option<NodeId>,
        prev_child_node: Option<NodeId>,
        next_child_node: Option<NodeId>,
    ) {
        if self.should_emit_on_single_line(parent_node) {
            self.write_space();
        } else if self.p.options.preserve_source_newlines {
            let lines = self.get_lines_between_nodes(parent_node, prev_child_node, next_child_node);
            if lines > 0 {
                self.write_line_repeat(lines);
            } else {
                self.write_space();
            }
        } else {
            self.write_line();
        }
    }

    /// `p.writeLinesAndIndent`
    fn write_lines_and_indent(&mut self, line_count: i32, write_space_if_not_indenting: bool) {
        if line_count > 0 {
            self.increase_indent();
            self.write_line_repeat(line_count);
        } else if write_space_if_not_indenting {
            self.write_space();
        }
    }

    /// `p.writeLineSeparatorsAndIndentBefore`
    fn write_line_separators_and_indent_before(
        &mut self,
        node: Option<NodeId>,
        parent: Option<NodeId>,
    ) -> bool {
        if self.p.options.preserve_source_newlines {
            let leading_newlines = self.get_leading_line_terminator_count(parent, node, LF_NONE);
            if leading_newlines > 0 {
                self.write_lines_and_indent(
                    leading_newlines,
                    false, /*writeSpaceIfNotIndenting*/
                );
                return true;
            }
        }
        false
    }

    /// `p.writeLineSeparatorsAfter`
    fn write_line_separators_after(&mut self, node: Option<NodeId>, parent: Option<NodeId>) {
        if self.p.options.preserve_source_newlines {
            let trailing_newlines = self.get_closing_line_terminator_count(
                parent,
                node,
                LF_NONE,
                TextRange::new(-1, -1), /*childrenTextRange*/
            );
            if trailing_newlines > 0 {
                self.write_line_repeat(trailing_newlines);
            }
        }
    }

    /// `p.getLinesBetweenNodes`
    fn get_lines_between_nodes(
        &mut self,
        parent: Option<NodeId>,
        node1: Option<NodeId>,
        node2: Option<NodeId>,
    ) -> i32 {
        let Some(parent) = parent else { return 0 };
        if self.should_elide_indentation(Some(parent)) {
            return 0;
        }
        let Some(node1) = node1 else { return 0 };
        let Some(node2) = node2 else { return 0 };

        let parent = util::skip_synthesized_parentheses(self.p.nodes, parent);
        let node1 = util::skip_synthesized_parentheses(self.p.nodes, node1);
        let node2 = util::skip_synthesized_parentheses(self.p.nodes, node2);

        // Always use a newline for synthesized code if the synthesizer desires it.
        if self.should_emit_on_new_line(Some(node2), LF_NONE) {
            return 1;
        }

        if let Some(sf) = self.p.current_source_file
            && !ast::node_is_synthesized(&self.p.nodes[parent])
            && !ast::node_is_synthesized(&self.p.nodes[node1])
            && !ast::node_is_synthesized(&self.p.nodes[node2])
        {
            if self.p.options.preserve_source_newlines {
                let l1 = self.p.nodes[node1].loc;
                let l2 = self.p.nodes[node2].loc;
                let sf_ref = self.p.nodes[sf].as_source_file();
                return self.get_effective_lines(|include_comments| {
                    util::get_lines_between_range_end_and_range_start(
                        l1,
                        l2,
                        sf_ref,
                        include_comments,
                    )
                });
            }
            return i32::from(!util::range_end_is_on_same_line_as_range_start(
                self.p.nodes[node1].loc,
                self.p.nodes[node2].loc,
                self.p.nodes[sf].as_source_file(),
            ));
        }
        0
    }

    /// `p.getEffectiveLines`
    fn get_effective_lines(&self, get_line_difference: impl Fn(bool) -> i32) -> i32 {
        // If 'preserveSourceNewlines' is disabled, we should never call this function
        // because it could be more expensive than alternative approximations.
        debug_assert!(self.p.options.preserve_source_newlines);
        // We start by measuring the line difference from a position to its adjacent comments,
        // so that this is counted as a one-line difference, not two:
        //
        //   node1;
        //   // NODE2 COMMENT
        //   node2;
        let lines = get_line_difference(/*includeComments*/ true);
        if lines == 0 {
            // However, if the line difference considering comments was 0, we might have this:
            //
            //   node1; // NODE2 COMMENT
            //   node2;
            //
            // in which case we should be ignoring node2's comment, so this too is counted as
            // a one-line difference, not zero.
            return get_line_difference(/*includeComments*/ false);
        }
        lines
    }

    /// `p.getLeadingLineTerminatorCount`
    fn get_leading_line_terminator_count(
        &mut self,
        parent_node: Option<NodeId>,
        first_child: Option<NodeId>,
        format: ListFormat,
    ) -> i32 {
        if format & LF_PRESERVE_LINES != 0 || self.p.options.preserve_source_newlines {
            if format & LF_PREFER_NEW_LINE != 0 {
                return 1;
            }

            let Some(first_child) = first_child else {
                return i32::from(
                    !(parent_node.is_none()
                        || (self.p.current_source_file.is_some()
                            && parent_node.is_some_and(|p| {
                                util::range_is_on_single_line(
                                    self.p.nodes[p].loc,
                                    self.p.nodes[self.p.current_source_file.unwrap()]
                                        .as_source_file(),
                                )
                            }))),
                );
            };
            if self.next_list_element_pos > 0
                && self.p.nodes[first_child].pos() == self.next_list_element_pos
            {
                // If this child starts at the beginning of a list item in a parent list, its leading
                // line terminators have already been written as the separating line terminators of the
                // parent list.
                return 0;
            }
            if self.p.nodes[first_child].kind == Kind::JsxText {
                // JsxText will be written with its leading whitespace, so don't add more manually.
                return 0;
            }
            if let (Some(sf), Some(parent_node)) = (self.p.current_source_file, parent_node)
                && !ast::position_is_synthesized(self.p.nodes[parent_node].pos())
                && !ast::node_is_synthesized(&self.p.nodes[first_child])
                && self.p.nodes[first_child].parent.is_none()
            {
                if self.p.options.preserve_source_newlines {
                    let first_pos = self.p.nodes[first_child].pos();
                    let parent_pos = self.p.nodes[parent_node].pos();
                    let sf_ref = self.p.nodes[sf].as_source_file();
                    return self.get_effective_lines(|include_comments| {
                        util::get_lines_between_position_and_preceding_non_whitespace_character(
                            first_pos,
                            parent_pos,
                            sf_ref,
                            include_comments,
                        )
                    });
                }
                return i32::from(!util::range_start_positions_are_on_same_line(
                    self.p.nodes[parent_node].loc,
                    self.p.nodes[first_child].loc,
                    self.p.nodes[sf].as_source_file(),
                ));
            }
            if self.should_emit_on_new_line(Some(first_child), format) {
                return 1;
            }
        }
        i32::from(format & LF_MULTI_LINE != 0)
    }

    /// `p.getSeparatingLineTerminatorCount`
    fn get_separating_line_terminator_count(
        &mut self,
        previous_node: Option<NodeId>,
        next_node: Option<NodeId>,
        format: ListFormat,
    ) -> i32 {
        if format & LF_PRESERVE_LINES != 0 || self.p.options.preserve_source_newlines {
            let (Some(previous_node), Some(next_node)) = (previous_node, next_node) else {
                return 0;
            };
            if self.p.nodes[next_node].kind == Kind::JsxText {
                // JsxText will be written with its leading whitespace, so don't add more manually.
                return 0;
            } else if let Some(sf) = self.p.current_source_file
                && !ast::node_is_synthesized(&self.p.nodes[previous_node])
                && !ast::node_is_synthesized(&self.p.nodes[next_node])
            {
                if self.p.options.preserve_source_newlines
                    && util::sibling_node_positions_are_comparable(
                        &self.p.emit_context.shared(),
                        self.p.nodes,
                        previous_node,
                        next_node,
                    )
                {
                    let l1 = self.p.nodes[previous_node].loc;
                    let l2 = self.p.nodes[next_node].loc;
                    let sf_ref = self.p.nodes[sf].as_source_file();
                    return self.get_effective_lines(|include_comments| {
                        util::get_lines_between_range_end_and_range_start(
                            l1,
                            l2,
                            sf_ref,
                            include_comments,
                        )
                    });
                } else if !self.p.options.preserve_source_newlines
                    && util::original_nodes_have_same_parent(
                        &self.p.emit_context.shared(),
                        self.p.nodes,
                        previous_node,
                        next_node,
                    )
                {
                    return i32::from(!util::range_end_is_on_same_line_as_range_start(
                        self.p.nodes[previous_node].loc,
                        self.p.nodes[next_node].loc,
                        self.p.nodes[sf].as_source_file(),
                    ));
                }
                // If the two nodes are not comparable, add a line terminator based on the format
                // that can indicate whether new lines are preferred or not.
                return i32::from(format & LF_PREFER_NEW_LINE != 0);
            } else if self.should_emit_on_new_line(Some(previous_node), format)
                || self.should_emit_on_new_line(Some(next_node), format)
            {
                return 1;
            }
        } else if next_node.is_some_and(|n| self.should_emit_on_new_line(Some(n), LF_NONE)) {
            return 1;
        }
        i32::from(format & LF_MULTI_LINE != 0)
    }

    /// `p.getClosingLineTerminatorCount`
    fn get_closing_line_terminator_count(
        &mut self,
        parent_node: Option<NodeId>,
        last_child: Option<NodeId>,
        format: ListFormat,
        children_text_range: TextRange,
    ) -> i32 {
        if format & LF_PRESERVE_LINES != 0 || self.p.options.preserve_source_newlines {
            if format & LF_PREFER_NEW_LINE != 0 {
                return 1;
            }
            let Some(last_child) = last_child else {
                return i32::from(
                    !(parent_node.is_none()
                        || (self.p.current_source_file.is_some()
                            && parent_node.is_some_and(|p| {
                                util::range_is_on_single_line(
                                    self.p.nodes[p].loc,
                                    self.p.nodes[self.p.current_source_file.unwrap()]
                                        .as_source_file(),
                                )
                            }))),
                );
            };
            if let (Some(sf), Some(parent_node)) = (self.p.current_source_file, parent_node)
                && !ast::position_is_synthesized(self.p.nodes[parent_node].pos())
                && !ast::node_is_synthesized(&self.p.nodes[last_child])
                && (self.p.nodes[last_child].parent.is_none()
                    || self.p.nodes[last_child].parent == Some(parent_node))
            {
                if self.p.options.preserve_source_newlines {
                    let end = greatest_end(
                        self.p.nodes[last_child].end(),
                        [Some(children_text_range.end())],
                    );
                    let parent_end = self.p.nodes[parent_node].end();
                    let sf_ref = self.p.nodes[sf].as_source_file();
                    return self.get_effective_lines(|include_comments| {
                        util::get_lines_between_position_and_next_non_whitespace_character(
                            end,
                            parent_end,
                            sf_ref,
                            include_comments,
                        )
                    });
                }
                return i32::from(!util::range_end_positions_are_on_same_line(
                    self.p.nodes[parent_node].loc,
                    self.p.nodes[last_child].loc,
                    self.p.nodes[sf].as_source_file(),
                ));
            }
            if self.should_emit_on_new_line(Some(last_child), format) {
                return 1;
            }
        }
        if format & LF_MULTI_LINE != 0 && format & LF_NO_TRAILING_NEW_LINE == 0 {
            return 1;
        }
        0
    }

    /// `p.writeCommentRange`
    fn write_comment_range(&mut self, comment: CommentRange) {
        let Some(sf) = self.p.current_source_file else {
            return;
        };
        let text = self.p.nodes[sf].as_source_file().text().to_string();
        let line_map = self.p.nodes[sf].as_source_file().ecma_line_map().to_vec();
        self.write_comment_range_worker(&text, &line_map, comment.kind, comment.text_range);
    }

    /// `p.writeCommentRangeWorker`
    fn write_comment_range_worker(
        &mut self,
        text: &str,
        line_map: &[TextPos],
        kind: Kind,
        loc: TextRange,
    ) {
        if kind == Kind::MultiLineCommentTrivia {
            let indent_size = get_default_indent_size();
            let first_line = scanner::compute_line_of_position(line_map, loc.pos());
            let line_count = line_map.len();
            let mut first_comment_line_indent = -1i32;
            let mut pos = loc.pos();
            let mut current_line = first_line;
            while pos < loc.end() {
                let next_line_start = if current_line as usize + 1 == line_count {
                    text.len() as i32 + 1
                } else {
                    line_map[current_line as usize + 1]
                };

                if pos != loc.pos() {
                    // If we are not emitting first line, we need to write the spaces to adjust the alignment
                    if first_comment_line_indent == -1 {
                        first_comment_line_indent = util::calculate_indent(
                            text,
                            line_map[first_line as usize].max(0) as usize,
                            loc.pos().max(0) as usize,
                        );
                    }

                    // These are number of spaces writer is going to write at current indent
                    let current_writer_indent_spacing = self.w().get_indent() * indent_size;

                    let spaces_to_emit = current_writer_indent_spacing - first_comment_line_indent
                        + util::calculate_indent(
                            text,
                            pos.max(0) as usize,
                            next_line_start.max(0) as usize,
                        );
                    if spaces_to_emit > 0 {
                        let mut number_of_single_spaces_to_emit = spaces_to_emit % indent_size;
                        let indent_size_space_string = get_indent_string(
                            (spaces_to_emit - number_of_single_spaces_to_emit) / indent_size,
                            indent_size,
                        );

                        // Write indent size string
                        self.w().raw_write(&indent_size_space_string);

                        // Emit the single spaces
                        while number_of_single_spaces_to_emit > 0 {
                            self.w().raw_write(" ");
                            number_of_single_spaces_to_emit -= 1;
                        }
                    } else {
                        // No spaces to emit write empty string
                        self.w().raw_write("");
                    }
                }

                // Write the comment line text
                let mut end = loc.end().min(next_line_start);
                let mut scan = pos;
                while scan < end {
                    let ch = text[scan as usize..].chars().next().unwrap();
                    let size = ch.len_utf8() as i32;
                    if size == 0 {
                        break;
                    }
                    if stringutil::is_line_break(ch) {
                        end = scan;
                        break;
                    }
                    scan += size;
                }
                let current_line_text = text[pos as usize..end as usize].trim();
                if !current_line_text.is_empty() {
                    self.write_comment(current_line_text);
                    if end != loc.end() {
                        self.write_line();
                    }
                } else {
                    // Empty string - make sure we write empty line
                    self.w().write_line_force(true);
                }

                pos = next_line_start;
                current_line += 1;
            }
        } else {
            // Single line comment of style //....
            self.write_comment(&text[loc.pos() as usize..loc.end() as usize]);
        }
    }

    //
    // Custom emit behavior stubs (i.e., from `EmitNode`, `EmitFlags`, etc.)
    //

    /// `p.shouldEmitComments`
    fn should_emit_comments(&self, node: Option<NodeId>) -> bool {
        !self.comments_disabled
            && self.p.current_source_file.is_some()
            && !node.is_some_and(|n| ast::is_source_file(&self.p.nodes[n]))
    }

    /// `p.shouldWriteComment`
    fn should_write_comment(&self, comment: CommentRange) -> bool {
        !self.p.options.only_print_jsdoc_style
            || (self.p.current_source_file.is_some()
                && util::is_jsdoc_like_text(
                    self.p.nodes[self.p.current_source_file.unwrap()]
                        .as_source_file()
                        .text(),
                    comment,
                ))
            || (self.p.current_source_file.is_some()
                && util::is_pinned_comment(
                    self.p.nodes[self.p.current_source_file.unwrap()]
                        .as_source_file()
                        .text(),
                    comment,
                ))
    }

    /// `p.shouldEmitIndented`
    fn should_emit_indented(&self, node: Option<NodeId>) -> bool {
        node.is_some_and(|n| self.p.emit_context.emit_flags(n).has(EmitFlags::INDENTED))
    }

    /// `p.shouldElideIndentation`
    fn should_elide_indentation(&self, node: Option<NodeId>) -> bool {
        node.is_some_and(|n| {
            self.p
                .emit_context
                .emit_flags(n)
                .has(EmitFlags::NO_INDENTATION)
        })
    }

    /// `p.shouldEmitOnSingleLine`
    fn should_emit_on_single_line(&self, node: Option<NodeId>) -> bool {
        node.is_some_and(|n| {
            self.p
                .emit_context
                .emit_flags(n)
                .has(EmitFlags::SINGLE_LINE)
        })
    }

    /// `p.shouldEmitOnMultipleLines`
    fn should_emit_on_multiple_lines(&self, node: Option<NodeId>) -> bool {
        node.is_some_and(|n| self.p.emit_context.emit_flags(n).has(EmitFlags::MULTI_LINE))
    }

    /// `p.shouldEmitBlockFunctionBodyOnSingleLine`
    fn should_emit_block_function_body_on_single_line(&mut self, body: NodeId) -> bool {
        // We must emit a function body as a single-line body in the following case:
        // * The body has NodeEmitFlags.SingleLine specified.

        // We must emit a function body as a multi-line body in the following cases:
        // * The body is explicitly marked as multi-line.
        // * A non-synthesized body's start and end position are on different lines.
        // * Any statement in the body starts on a new line.

        if self.should_emit_on_single_line(Some(body)) {
            return true;
        }

        let b = self.p.nodes[body].as_block();
        if b.multi_line {
            return false;
        }

        if !ast::node_is_synthesized(&self.p.nodes[body])
            && let Some(sf) = self.p.current_source_file
            && !util::range_is_on_single_line(
                self.p.nodes[body].loc,
                self.p.nodes[sf].as_source_file(),
            )
        {
            return false;
        }

        let statements = self.p.nodes[body].as_block().statements.clone();
        let first = statements.as_ref().and_then(|s| s.nodes.first().copied());
        let last = statements.as_ref().and_then(|s| s.nodes.last().copied());
        let statements_loc = statements.as_ref().map(|s| s.loc).unwrap_or_default();
        if self.get_leading_line_terminator_count(Some(body), first, LF_PRESERVE_LINES) > 0
            || self.get_closing_line_terminator_count(
                Some(body),
                last,
                LF_PRESERVE_LINES,
                statements_loc,
            ) > 0
        {
            return false;
        }

        let mut previous_statement = None;
        if let Some(statements) = statements {
            for &statement in statements.nodes.iter() {
                if self.get_separating_line_terminator_count(
                    previous_statement,
                    Some(statement),
                    LF_PRESERVE_LINES,
                ) > 0
                {
                    return false;
                }
                previous_statement = Some(statement);
            }
        }
        true
    }

    /// `p.shouldEmitOnNewLine`
    fn should_emit_on_new_line(&self, node: Option<NodeId>, format: ListFormat) -> bool {
        if node.is_some_and(|n| {
            self.p
                .emit_context
                .emit_flags(n)
                .has(EmitFlags::START_ON_NEW_LINE)
        }) {
            return true;
        }
        format & LF_PREFER_NEW_LINE != 0
    }

    /// `p.shouldEmitSourceMaps`
    fn should_emit_source_maps(&self, node: NodeId) -> bool {
        !self.source_maps_disabled
            && self.p.current_source_file.is_some()
            && !ast::is_source_file(&self.p.nodes[node])
            && !ast::is_in_json_file(&self.p.nodes[node])
    }

    /// `p.shouldEmitTokenSourceMaps`
    fn should_emit_token_source_maps(
        &self,
        token: Kind,
        pos: i32,
        context_node: NodeId,
        flags: TokenEmitFlags,
    ) -> bool {
        // We don't emit source positions for most tokens as it tends to be quite noisy, however
        // we need to emit source positions for open and close braces so that tools like istanbul
        // can map branches for code coverage. However, we still omit brace source positions when
        // the output is a declaration file.
        flags & TEF_NO_SOURCE_MAPS == 0
            && self.should_emit_source_maps(context_node)
            && !self.p.options.omit_brace_source_map_positions
            && (token == Kind::OpenBraceToken || token == Kind::CloseBraceToken)
    }

    /// `p.shouldEmitLeadingComments`
    fn should_emit_leading_comments(&self, node: NodeId) -> bool {
        !self
            .p
            .emit_context
            .emit_flags(node)
            .has(EmitFlags::NO_LEADING_COMMENTS)
    }

    /// `p.shouldEmitTrailingComments`
    fn should_emit_trailing_comments(&self, node: NodeId) -> bool {
        !self
            .p
            .emit_context
            .emit_flags(node)
            .has(EmitFlags::NO_TRAILING_COMMENTS)
    }

    /// `p.shouldEmitDetachedComments`
    fn should_emit_detached_comments(&self, node: NodeId) -> bool {
        if !ast::is_source_file(&self.p.nodes[node]) {
            return true;
        }

        let file = self.p.nodes[node].as_source_file();

        // Emit detached comment if there are no prologue directives or if the first node is synthesized.
        // The synthesized node will have no leading comment so some comments may be missed.
        let statements = file.statements.as_ref();
        statements.is_none_or(|s| {
            s.nodes.is_empty()
                || !ast::is_prologue_directive(&self.p.nodes[s.nodes[0]], self.p.nodes)
                || ast::node_is_synthesized(&self.p.nodes[s.nodes[0]])
        })
    }

    /// `p.hasCommentsAtPosition`
    fn has_comments_at_position(&mut self, pos: i32) -> bool {
        let Some(sf) = self.p.current_source_file else {
            return false;
        };
        let text = self.p.nodes[sf].as_source_file().text().to_string();
        !scanner::get_trailing_comment_ranges(&self.p.emit_context.factory, &text, pos + 1)
            .is_empty()
            || !scanner::get_leading_comment_ranges(&self.p.emit_context.factory, &text, pos + 1)
                .is_empty()
    }

    /// `p.shouldEmitIndirectCall`
    fn should_emit_indirect_call(&self, node: NodeId) -> bool {
        self.p
            .emit_context
            .emit_flags(node)
            .has(EmitFlags::INDIRECT_CALL)
    }

    /// `p.shouldAllowTrailingComma`
    fn should_allow_trailing_comma(&self, node: NodeId, list: Option<&NodeList>) -> bool {
        let Some(sf) = self.p.current_source_file else {
            return false;
        };
        if self.p.nodes[sf].as_source_file().script_kind == ScriptKind::Json {
            return false;
        }

        match self.p.nodes[node].kind {
            Kind::ObjectLiteralExpression => true,
            Kind::ArrayLiteralExpression
            | Kind::ArrowFunction
            | Kind::Constructor
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::TypeAliasDeclaration
            | Kind::JSTypeAliasDeclaration
            | Kind::FunctionType
            | Kind::ConstructorType
            | Kind::CallSignature
            | Kind::ConstructSignature
            | Kind::TaggedTemplateExpression
            | Kind::ObjectBindingPattern
            | Kind::ArrayBindingPattern
            | Kind::NamedImports
            | Kind::NamedExports
            | Kind::ImportAttributes => true,
            Kind::ClassExpression | Kind::ClassDeclaration | Kind::InterfaceDeclaration => {
                list.map(|l| l.loc) == self.p.nodes[node].type_parameter_list().map(|l| l.loc)
            }
            Kind::FunctionDeclaration | Kind::FunctionExpression | Kind::MethodDeclaration => true,
            Kind::CallExpression => true,
            Kind::NewExpression => true,
            _ => false,
        }
    }

    //
    // Tokens/Keywords
    //

    /// `p.writeTokenText`
    fn write_token_text(&mut self, token: Kind, write_kind: WriteKind, pos: i32) -> i32 {
        // !!! emit leading and trailing comments
        // !!! emit leading and trailing source maps
        let token_string = scanner::token_to_string(token);
        self.write_as(token_string, write_kind);
        if ast::position_is_synthesized(pos) {
            pos
        } else {
            pos + token_string.len() as i32
        }
    }

    /// `p.emitToken`
    fn emit_token(
        &mut self,
        token: Kind,
        pos: i32,
        write_kind: WriteKind,
        context_node: NodeId,
    ) -> i32 {
        self.emit_token_ex(token, pos, write_kind, context_node, TEF_NONE)
    }

    /// `p.emitTokenEx`
    fn emit_token_ex(
        &mut self,
        token: Kind,
        pos: i32,
        write_kind: WriteKind,
        context_node: NodeId,
        flags: TokenEmitFlags,
    ) -> i32 {
        let (state, pos) = self.enter_token(token, pos, context_node, flags);
        let pos = self.write_token_text(token, write_kind, pos);
        self.exit_token(token, pos, context_node, state);
        pos
    }

    /// `p.emitKeywordNode`
    fn emit_keyword_node(&mut self, node: NodeId) {
        self.emit_keyword_node_ex(node, TEF_NONE)
    }

    /// `p.emitKeywordNodeEx`
    fn emit_keyword_node_ex(&mut self, node: NodeId, flags: TokenEmitFlags) {
        let state = self.enter_token_node(node, flags);
        self.write_token_text(
            self.p.nodes[node].kind,
            WriteKind::Keyword,
            self.p.nodes[node].pos(),
        );
        self.exit_token_node(node, state);
    }

    /// `p.emitPunctuationNode`
    fn emit_punctuation_node(&mut self, node: NodeId) {
        self.emit_punctuation_node_ex(node, TEF_NONE)
    }

    /// `p.emitPunctuationNode(nil)` — Go tolerates nil tokens.
    fn emit_punctuation_node_opt(&mut self, node: Option<NodeId>) {
        if let Some(node) = node {
            self.emit_punctuation_node(node)
        }
    }

    /// `p.emitPunctuationNodeEx`
    fn emit_punctuation_node_ex(&mut self, node: NodeId, flags: TokenEmitFlags) {
        let state = self.enter_token_node(node, flags);
        self.write_token_text(
            self.p.nodes[node].kind,
            WriteKind::Punctuation,
            self.p.nodes[node].pos(),
        );
        self.exit_token_node(node, state);
    }

    /// `p.emitTokenNode`
    fn emit_token_node(&mut self, node: Option<NodeId>) {
        self.emit_token_node_ex(node, TEF_NONE)
    }

    /// `p.emitTokenNodeEx`
    fn emit_token_node_ex(&mut self, node: Option<NodeId>, flags: TokenEmitFlags) {
        let Some(node) = node else {
            return;
        };
        let kind = self.p.nodes[node].kind;
        if kind.is_keyword_kind() {
            self.emit_keyword_node_ex(node, flags);
        } else if kind.is_punctuation_kind() {
            self.emit_punctuation_node_ex(node, flags);
        } else {
            panic!("unexpected TokenNode: {:?}", kind)
        }
    }

    //
    // Literals
    //

    /// `p.emitLiteral`
    ///
    /// Emits literals of the following kinds
    ///
    ///	SyntaxKindNumericLiteral
    ///	SyntaxKindBigIntLiteral
    ///	SyntaxKindStringLiteral
    ///	SyntaxKindNoSubstitutionTemplateLiteral
    ///	SyntaxKindRegularExpressionLiteral
    ///	SyntaxKindTemplateHead
    ///	SyntaxKindTemplateMiddle
    ///	SyntaxKindTemplateTail
    fn emit_literal(&mut self, node: NodeId, mut flags: GetLiteralTextFlags) {
        // Add NeverAsciiEscape flag if the printer option is set
        if self.p.options.never_ascii_escape {
            flags |= GET_LITERAL_TEXT_FLAGS_NEVER_ASCII_ESCAPE;
        }
        if self.p.options.terminate_unterminated_literals {
            flags |= GET_LITERAL_TEXT_FLAGS_TERMINATE_UNTERMINATED_LITERALS;
        }

        let text = self.get_literal_text_of_node(node, None /*sourceFile*/, flags);

        // Quick info expects all literals to be called with writeStringLiteral, as there's no
        // specific type for numberLiterals
        self.w().write_string_literal(&text)
    }

    /// `p.emitNumericLiteral`
    fn emit_numeric_literal(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.emit_literal(node, GET_LITERAL_TEXT_FLAGS_NONE);
        self.exit_node(node, state);
    }

    /// `p.emitBigIntLiteral`
    fn emit_big_int_literal(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.emit_literal(node, GET_LITERAL_TEXT_FLAGS_NONE); // TODO: Preserve numeric literal separators after Strada migration
        self.exit_node(node, state);
    }

    /// `p.emitStringLiteral`
    fn emit_string_literal(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.emit_literal(node, GET_LITERAL_TEXT_FLAGS_NONE);
        self.exit_node(node, state);
    }

    /// `p.emitNoSubstitutionTemplateLiteral`
    fn emit_no_substitution_template_literal(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.emit_literal(node, GET_LITERAL_TEXT_FLAGS_NONE);
        self.exit_node(node, state);
    }

    /// `p.emitRegularExpressionLiteral`
    fn emit_regular_expression_literal(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.emit_literal(node, GET_LITERAL_TEXT_FLAGS_NONE);
        self.exit_node(node, state);
    }

    //
    // Pseudo-literals
    //

    /// `p.emitTemplateHead`
    fn emit_template_head(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.emit_literal(node, GET_LITERAL_TEXT_FLAGS_NONE);
        self.exit_node(node, state);
    }

    /// `p.emitTemplateMiddle`
    fn emit_template_middle(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.emit_literal(node, GET_LITERAL_TEXT_FLAGS_NONE);
        self.exit_node(node, state);
    }

    /// `p.emitTemplateTail`
    fn emit_template_tail(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.emit_literal(node, GET_LITERAL_TEXT_FLAGS_NONE);
        self.exit_node(node, state);
    }

    /// `p.emitTemplateMiddleTail`
    fn emit_template_middle_tail(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::TemplateMiddle => self.emit_template_middle(node),
            Kind::TemplateTail => self.emit_template_tail(node),
            _ => {}
        }
    }

    //
    // Snippet Elements
    //

    /// `p.emitSnippetNode`
    fn emit_snippet_node(&mut self, node: NodeId, snippet_element: &SnippetElement) {
        match snippet_element.kind {
            SnippetKind::TabStop => self.emit_tab_stop(node, snippet_element),
            _ => panic!("Unhandled snippet element kind: {:?}", snippet_element.kind),
        }
    }

    /// `p.emitTabStop`
    fn emit_tab_stop(&mut self, node: NodeId, snippet_element: &SnippetElement) {
        debug_assert!(
            self.p.nodes[node].kind == Kind::EmptyStatement,
            "Snippet tab stops can only be emitted on empty statements"
        );
        self.w().raw_write(&format!("${}", snippet_element.order));
    }

    //
    // Names
    //

    /// `p.emitIdentifierText`
    fn emit_identifier_text(&mut self, node: NodeId) {
        let f = ast::get_source_file_of_node(Some(node), self.p.nodes);
        debug_assert!(
            f.is_none()
                || self.p.current_source_file.is_none()
                || self.p.nodes[f.unwrap()].as_source_file().file_name()
                    == self.p.nodes[self.p.current_source_file.unwrap()]
                        .as_source_file()
                        .file_name()
        );
        let text = self.get_text_of_node(node, false /*includeTrivia*/);

        if let Some(id_to_symbol) = self.p.id_to_symbol
            && let Some(symbol) = id_to_symbol.get(&node)
        {
            self.write_symbol(&text, Some(*symbol));
            return;
        }
        self.write(&text)
    }

    /// `p.emitIdentifierName`
    fn emit_identifier_name(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.emit_identifier_text(node);
        self.exit_node(node, state);
    }

    /// `p.emitIdentifierNameNode`
    fn emit_identifier_name_node(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        self.emit_identifier_name(node);
    }

    /// `p.getUniqueHelperName`
    fn get_unique_helper_name(&mut self, name: &str) -> NodeId {
        if let Some(&helper_name) = self.unique_helper_names.as_ref().and_then(|m| m.get(name)) {
            let helper_name = self
                .p
                .emit_context
                .factory
                .clone_node(self.p.nodes, helper_name);
            return helper_name;
        }
        let helper_name = self.p.emit_context.factory.new_unique_name_ex(
            self.p.nodes,
            name,
            &crate::emit_context::AutoGenerateOptions {
                flags: crate::emit_flags::GeneratedIdentifierFlags::FILE_LEVEL
                    | crate::emit_flags::GeneratedIdentifierFlags::OPTIMISTIC,
                ..Default::default()
            },
        );
        self.generate_name(helper_name);
        self.unique_helper_names
            .as_mut()
            .expect("uniqueHelperNames must be allocated")
            .insert(name.to_string(), helper_name);
        helper_name
    }

    /// `p.emitIdentifierReference`
    fn emit_identifier_reference(&mut self, node: NodeId) {
        let has_helper_names =
            self.external_helpers_module_name.is_some() || self.unique_helper_names.is_some();
        if has_helper_names
            && self
                .p
                .emit_context
                .emit_flags(node)
                .has(EmitFlags::HELPER_NAME)
        {
            if let Some(external_helpers_module_name) = self.external_helpers_module_name {
                // Substitute `__helper` with `tslib_1.__helper`
                let module_name = self
                    .p
                    .emit_context
                    .factory
                    .clone_node(self.p.nodes, external_helpers_module_name);
                let node_clone = self.p.emit_context.factory.clone_node(self.p.nodes, node);
                let helper = self.p.emit_context.factory.new_property_access_expression(
                    self.p.nodes,
                    Some(module_name),
                    None, /*questionDotToken*/
                    Some(node_clone),
                    NodeFlags::NONE,
                );
                self.p.emit_context.assign_comment_and_source_map_ranges(
                    self.p.nodes,
                    helper,
                    node,
                );
                self.emit_property_access_expression(helper);
                return;
            }
            if self.unique_helper_names.is_some() {
                // Substitute `__helper` with `__helper_1` if there is a conflict in an ES module.
                let text = self.p.nodes[node].text(self.p.nodes).into_owned();
                let helper_name = self.get_unique_helper_name(&text);
                self.p.emit_context.assign_comment_and_source_map_ranges(
                    self.p.nodes,
                    helper_name,
                    node,
                );
                let node = helper_name;
                let state = self.enter_node(node);
                self.emit_identifier_text(node);
                self.exit_node(node, state);
                return;
            }
        }

        let state = self.enter_node(node);
        self.emit_identifier_text(node);
        self.exit_node(node, state);
    }

    /// `p.emitBindingIdentifier`
    fn emit_binding_identifier(&mut self, node: NodeId) {
        if self.unique_helper_names.is_some()
            && self
                .p
                .emit_context
                .emit_flags(node)
                .has(EmitFlags::HELPER_NAME)
        {
            // Substitute `__helper` with `__helper_1` if there is a conflict in an ES module.
            let text = self.p.nodes[node].text(self.p.nodes).into_owned();
            let helper_name = self.get_unique_helper_name(&text);
            self.p.emit_context.assign_comment_and_source_map_ranges(
                self.p.nodes,
                helper_name,
                node,
            );
            let node = helper_name;
            let state = self.enter_node(node);
            self.emit_identifier_text(node);
            self.exit_node(node, state);
            return;
        }

        let state = self.enter_node(node);
        self.emit_identifier_text(node);
        self.exit_node(node, state);
    }

    /// `p.emitLabelIdentifier`
    fn emit_label_identifier(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.emit_identifier_text(node);
        self.exit_node(node, state);
    }

    /// `p.emitPrivateIdentifier`
    fn emit_private_identifier(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        let text = self.get_text_of_node(node, false /*includeTrivia*/);
        self.write(&text);
        self.exit_node(node, state);
    }

    /// `p.emitQualifiedName`
    fn emit_qualified_name(&mut self, node: NodeId) {
        let (left, right) = {
            let d = self.p.nodes[node].as_qualified_name();
            (d.left, d.right)
        };
        let state = self.enter_node(node);
        self.emit_entity_name(left);
        self.write_punctuation(".");
        self.emit_member_name(right);
        self.exit_node(node, state);
    }

    /// `p.emitComputedPropertyName`
    fn emit_computed_property_name(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_computed_property_name().expression;
        let state = self.enter_node(node);
        self.write_punctuation("[");
        self.emit_expression(expression, OperatorPrecedence::DISALLOW_COMMA);
        self.write_punctuation("]");
        self.exit_node(node, state);
    }

    /// `p.emitEntityName`
    fn emit_entity_name(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        match self.p.nodes[node].kind {
            Kind::Identifier => self.emit_identifier_reference(node),
            Kind::QualifiedName => self.emit_qualified_name(node),
            Kind::PropertyAccessExpression => {
                // TypeQuery nodes may have PropertyAccessExpression as exprName (e.g. typeof foo.x).
                // TS's emitter handles this via generic emit(); we dispatch to expression emitter here.
                self.emit_expression(Some(node), OperatorPrecedence::DISALLOW_COMMA)
            }
            _ => {
                let parent = self.p.nodes[node].parent;
                let n = &self.p.nodes[node];
                panic!(
                    "unexpected EntityName: {:?} node={:?} loc={:?} flags={:?} parent={:?} parent_kind={:?}",
                    n.kind,
                    node,
                    n.loc,
                    n.flags,
                    parent,
                    parent.map(|p| self.p.nodes[p].kind)
                )
            }
        }
    }

    /// `p.emitBindingName`
    fn emit_binding_name(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        match self.p.nodes[node].kind {
            Kind::Identifier => self.emit_binding_identifier(node),
            Kind::ObjectBindingPattern => self.emit_object_binding_pattern(node),
            Kind::ArrayBindingPattern => self.emit_array_binding_pattern(node),
            _ => panic!("unexpected BindingName: {:?}", self.p.nodes[node].kind),
        }
    }

    /// `p.emitPropertyName`
    fn emit_property_name(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        let saved_write_kind = self.write_kind;
        self.write_kind = WriteKind::Property;

        match self.p.nodes[node].kind {
            Kind::Identifier => self.emit_identifier_name(node),
            Kind::PrivateIdentifier => self.emit_private_identifier(node),
            Kind::StringLiteral => self.emit_string_literal(node),
            Kind::NoSubstitutionTemplateLiteral => self.emit_no_substitution_template_literal(node),
            Kind::NumericLiteral => self.emit_numeric_literal(node),
            Kind::BigIntLiteral => self.emit_big_int_literal(node),
            Kind::ComputedPropertyName => self.emit_computed_property_name(node),
            _ => panic!("unexpected PropertyName: {:?}", self.p.nodes[node].kind),
        }

        self.write_kind = saved_write_kind;
    }

    /// `p.emitMemberName`
    fn emit_member_name(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        match self.p.nodes[node].kind {
            Kind::Identifier => self.emit_identifier_name(node),
            Kind::PrivateIdentifier => self.emit_private_identifier(node),
            _ => panic!("unexpected MemberName: {:?}", self.p.nodes[node].kind),
        }
    }

    /// `p.emitModuleName`
    fn emit_module_name(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        match self.p.nodes[node].kind {
            Kind::Identifier => self.emit_binding_identifier(node),
            Kind::StringLiteral => self.emit_string_literal(node),
            _ => panic!("unexpected ModuleName: {:?}", self.p.nodes[node].kind),
        }
    }

    /// `p.emitModuleExportName`
    fn emit_module_export_name(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        match self.p.nodes[node].kind {
            Kind::Identifier => self.emit_identifier_name(node),
            Kind::StringLiteral => self.emit_string_literal(node),
            _ => panic!("unexpected ModuleExportName: {:?}", self.p.nodes[node].kind),
        }
    }

    /// `p.emitImportAttributeName`
    fn emit_import_attribute_name(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::Identifier => self.emit_identifier_name(node),
            Kind::StringLiteral => self.emit_string_literal(node),
            _ => panic!(
                "unexpected ImportAttributeName: {:?}",
                self.p.nodes[node].kind
            ),
        }
    }

    /// `p.emitNestedModuleName`
    fn emit_nested_module_name(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        match self.p.nodes[node].kind {
            Kind::Identifier => self.emit_identifier_name(node),
            Kind::StringLiteral => self.emit_string_literal(node),
            _ => panic!("unexpected ModuleName: {:?}", self.p.nodes[node].kind),
        }
    }

    //
    // Signature elements
    //

    /// `p.emitModifierList`
    fn emit_modifier_list(
        &mut self,
        parent_node: NodeId,
        modifiers: Option<&ModifierList>,
        allow_decorators: bool,
    ) -> i32 {
        let Some(modifiers) = modifiers else {
            return self.p.nodes[parent_node].pos();
        };
        if modifiers.nodes.is_empty() {
            return self.p.nodes[parent_node].pos();
        }

        let modifiers = modifiers.clone();

        if modifiers
            .nodes
            .iter()
            .all(|&m| ast::is_modifier(&self.p.nodes[m]))
        {
            // if all modifier-likes are `Modifier`, simply emit the list as modifiers.
            let node_list = NodeList {
                loc: modifiers.loc,
                nodes: modifiers.nodes.clone(),
                is_missing: false,
            };
            self.emit_list(
                Self::emit_keyword_node,
                Some(parent_node),
                Some(&node_list),
                LF_MODIFIERS,
            );
        } else if modifiers
            .nodes
            .iter()
            .all(|&m| ast::is_decorator(&self.p.nodes[m]))
        {
            if !allow_decorators {
                return self.p.nodes[parent_node].pos();
            }
            // if all modifier-likes are `Decorator`, simply emit the list as decorators.
            let node_list = NodeList {
                loc: modifiers.loc,
                nodes: modifiers.nodes.clone(),
                is_missing: false,
            };
            self.emit_list(
                Self::emit_modifier_like,
                Some(parent_node),
                Some(&node_list),
                LF_DECORATORS,
            );
        } else {
            {
                let nl = NodeList {
                    loc: modifiers.loc,
                    nodes: modifiers.nodes.clone(),
                    is_missing: false,
                };
                if let Some(h) = self.p.handlers.on_before_emit_node_list.as_mut() {
                    h(Some(&nl));
                }
            }

            // partition modifiers into contiguous chunks of `Modifier` or `Decorator` so as to
            // use consistent formatting for each chunk
            #[derive(PartialEq, Clone, Copy)]
            enum Mode {
                None,
                Modifiers,
                Decorators,
            }

            let mut last_mode = Mode::None;
            let mut mode = Mode::None;
            let mut start = 0usize;
            let mut pos = 0usize;

            while start < modifiers.nodes.len() {
                let mut last_modifier;
                while pos < modifiers.nodes.len() {
                    last_modifier = modifiers.nodes[pos];
                    mode = if ast::is_decorator(&self.p.nodes[last_modifier]) {
                        Mode::Decorators
                    } else {
                        Mode::Modifiers
                    };
                    if last_mode == Mode::None {
                        last_mode = mode;
                    } else if mode != last_mode {
                        break;
                    }
                    pos += 1;
                }

                let mut text_range = TextRange::new(-1, -1);
                if start == 0 {
                    text_range = TextRange::new(modifiers.loc.pos(), text_range.end());
                }
                if pos == modifiers.nodes.len() - 1 {
                    text_range = TextRange::new(text_range.pos(), modifiers.loc.end());
                }
                if allow_decorators || last_mode == Mode::Modifiers {
                    self.emit_list_items(
                        Self::emit_modifier_like,
                        Some(parent_node),
                        &modifiers.nodes[start..pos],
                        if last_mode == Mode::Modifiers {
                            LF_MODIFIERS
                        } else {
                            LF_DECORATORS
                        },
                        false, /*hasTrailingComma*/
                        text_range,
                    );
                }
                start = pos;
                last_mode = mode;
                pos += 1;
            }

            {
                let nl = NodeList {
                    loc: modifiers.loc,
                    nodes: modifiers.nodes.clone(),
                    is_missing: false,
                };
                if let Some(h) = self.p.handlers.on_after_emit_node_list.as_mut() {
                    h(Some(&nl));
                }
            }
        }

        greatest_end(
            self.p.nodes[parent_node].pos(),
            [modifiers.nodes.last().map(|&m| self.p.nodes[m].end())],
        )
    }

    /// `p.emitTypeParameter`
    fn emit_type_parameter(&mut self, node: NodeId) {
        let (name, constraint, default_type) = {
            let d = self.p.nodes[node].as_type_parameter_declaration();
            (d.name, d.constraint, d.default_type)
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        self.emit_binding_identifier(name.expect("type parameter name"));
        if let Some(constraint) = constraint {
            self.write_space();
            self.write_keyword("extends");
            self.write_space();
            self.emit_type_node_outside_extends(constraint);
        }
        if let Some(default_type) = default_type {
            self.write_space();
            self.write_operator("=");
            self.write_space();
            self.emit_type_node_outside_extends(default_type);
        }
        self.exit_node(node, state);
    }

    /// `p.emitTypeParameterDeclarationNode`
    fn emit_type_parameter_declaration_node(&mut self, node: NodeId) {
        // NOTE: QuickInfo uses TypeFormatFlagsWriteTypeArgumentsOfSignature to instruct the
        // NodeBuilder to store type arguments (i.e. type nodes) instead of type parameter
        // declarations in the type parameter list.
        if ast::is_type_parameter_declaration(&self.p.nodes[node]) {
            self.emit_type_parameter(node);
        } else {
            self.emit_type_argument(node);
        }
    }

    /// `p.emitParameterName`
    fn emit_parameter_name(&mut self, node: Option<NodeId>) {
        let saved_write_kind = self.write_kind;
        self.write_kind = WriteKind::Parameter;
        self.emit_binding_name(node);
        self.write_kind = saved_write_kind;
    }

    /// `p.emitParameter`
    fn emit_parameter(&mut self, node: NodeId) {
        let (dot_dot_dot_token, name, question_token, type_, initializer) = {
            let d = self.p.nodes[node].as_parameter_declaration();
            (
                d.dot_dot_dot_token,
                d.name,
                d.question_token,
                d.type_,
                d.initializer,
            )
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), true /*allowDecorators*/);
        self.emit_token_node(dot_dot_dot_token);
        self.emit_parameter_name(name);
        self.emit_token_node(question_token);

        self.emit_type_annotation(type_);

        // The comment position has to fallback to any present node within the parameter
        // declaration because as it turns out, the parser can make parameter declarations
        // with _just_ an initializer.
        let equal_token_pos = greatest_end(
            self.p.nodes[node].pos(),
            [
                type_.map(|t| self.p.nodes[t].end()),
                question_token.map(|t| self.p.nodes[t].end()),
                name.map(|t| self.p.nodes[t].end()),
                modifiers.map(|m| m.loc.end()),
            ],
        );
        self.emit_initializer(initializer, equal_token_pos, node);
        self.exit_node(node, state);
    }

    /// `p.emitParameterDeclarationNode`
    fn emit_parameter_declaration_node(&mut self, node: NodeId) {
        self.emit_parameter(node);
    }

    /// `p.emitDecorator`
    fn emit_decorator(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_decorator().expression;
        let state = self.enter_node(node);
        self.write_punctuation("@");
        self.emit_expression(expression, OperatorPrecedence::LEFT_HAND_SIDE);
        self.exit_node(node, state);
    }

    /// `p.emitModifierLike`
    fn emit_modifier_like(&mut self, node: NodeId) {
        if ast::is_decorator(&self.p.nodes[node]) {
            self.emit_decorator(node);
        } else if ast::is_modifier(&self.p.nodes[node]) {
            self.emit_keyword_node(node);
        } else {
            panic!("unhandled ModifierLike: {:?}", self.p.nodes[node].kind)
        }
    }

    /// `p.emitTypeParameters`
    fn emit_type_parameters(&mut self, parent_node: NodeId, nodes: Option<NodeList>) {
        let Some(nodes) = nodes else {
            return;
        };
        let format = if ast::is_arrow_function(&self.p.nodes[parent_node]) {
            LF_TYPE_PARAMETERS | LF_ALLOW_TRAILING_COMMA
        } else {
            LF_TYPE_PARAMETERS | LF_NONE
        };
        // TODO: preserve trailing comma after Strada migration
        self.emit_list(
            Self::emit_type_parameter_declaration_node,
            Some(parent_node),
            Some(&nodes),
            format,
        );
    }

    /// `p.emitTypeAnnotation`
    fn emit_type_annotation(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        self.write_punctuation(":");
        self.write_space();
        self.emit_type_node_outside_extends(node);
    }

    /// `p.emitInitializer`
    fn emit_initializer(
        &mut self,
        node: Option<NodeId>,
        equal_token_pos: i32,
        context_node: NodeId,
    ) {
        let Some(node) = node else {
            return;
        };
        self.write_space();
        self.emit_token(
            Kind::EqualsToken,
            equal_token_pos,
            WriteKind::Operator,
            context_node,
        );
        self.write_space();
        self.emit_expression(Some(node), OperatorPrecedence::DISALLOW_COMMA);
    }

    /// `p.emitParameters`
    fn emit_parameters(&mut self, parent_node: NodeId, parameters: Option<&NodeList>) {
        self.generate_all_names(parameters);
        self.emit_list(
            Self::emit_parameter_declaration_node,
            Some(parent_node),
            parameters,
            LF_PARAMETERS, /*|core.IfElse(p.shouldAllowTrailingComma(parentNode, parameters), LFAllowTrailingComma, LFNone)*/ // TODO: preserve trailing comma after Strada migration
        );
    }

    /// `p.emitParametersForArrow` — `parentNode` is
    /// FunctionType | ConstructorType | ArrowFunction.
    fn emit_parameters_for_arrow(&mut self, parent_node: NodeId, parameters: Option<&NodeList>) {
        if can_emit_simple_arrow_head(self.p.nodes, parent_node, parameters) {
            self.generate_all_names(parameters);
            self.emit_list(
                Self::emit_parameter_declaration_node,
                Some(parent_node),
                parameters,
                LF_SINGLE_ARROW_PARAMETER,
            );
        } else {
            self.emit_parameters(parent_node, parameters);
        }
    }

    /// `p.emitParametersForIndexSignature`
    fn emit_parameters_for_index_signature(
        &mut self,
        parent_node: NodeId,
        parameters: Option<&NodeList>,
    ) {
        self.generate_all_names(parameters);
        self.emit_list(
            Self::emit_parameter_declaration_node,
            Some(parent_node),
            parameters,
            LF_INDEX_SIGNATURE_PARAMETERS,
        );
    }

    /// `p.emitSignature`
    fn emit_signature(&mut self, node: NodeId) {
        let (type_parameters, parameters, type_) = {
            let n = self.p.nodes[node]
                .function_like_data()
                .expect("emitSignature on non-function-like");
            (n.type_parameters.clone(), n.parameters.clone(), n.type_)
        };

        // !!! In old emitter, quickinfo used type arguments in place of type parameters on
        // instantiated signatures
        self.emit_type_parameters(node, type_parameters);
        self.emit_parameters(node, parameters.as_ref());
        self.emit_type_annotation(type_);
    }

    /// `p.emitFunctionBody`
    fn emit_function_body(&mut self, body: NodeId) {
        self.p
            .emit_context
            .add_emit_flags(body, EmitFlags::NO_SOURCE_MAP);

        // Use only notification hooks for the body block, not the full comment pipeline.
        // Without this, trailing comments from the original method declaration
        // (e.g., "// Error") leak into synthesized comma expressions when methods
        // are hoisted into pending expressions.
        if let Some(h) = self.p.handlers.on_before_emit_node.as_mut() {
            h(Some(body));
        }

        self.generate_names(Some(body));

        // !!! Emit with comment after Strada migration
        ////p.emitTokenWithComment(ast.KindOpenBraceToken, body.Pos(), WriteKindPunctuation, body.AsNode())
        self.write_punctuation("{");

        self.increase_indent();
        let statements = self.p.nodes[body].as_block().statements.clone();
        let statements_loc = statements.as_ref().map(|s| s.loc).unwrap_or_default();
        let detached_state =
            self.emit_detached_comments_before_statement_list(body, statements_loc);
        let statement_offset = self.emit_prologue_directives(statements.as_ref());
        let pos = self.w().get_text_pos();
        self.emit_helpers(body);

        if self.should_emit_block_function_body_on_single_line(body)
            && statement_offset == 0
            && pos == self.w().get_text_pos()
        {
            self.decrease_indent();
            self.emit_list_range(
                Self::emit_statement,
                Some(body),
                statements.as_ref(),
                LF_SINGLE_LINE_FUNCTION_BODY_STATEMENTS,
                statement_offset as i32,
                -1,
            );
            self.increase_indent();
        } else {
            self.emit_list_range(
                Self::emit_statement,
                Some(body),
                statements.as_ref(),
                LF_MULTI_LINE_FUNCTION_BODY_STATEMENTS,
                statement_offset as i32,
                -1,
            );
        }

        self.emit_detached_comments_after_statement_list(body, statements_loc, detached_state);
        self.decrease_indent();

        // !!! Emit comment after Strada migration
        let statements_end = statements.map(|s| s.loc.end()).unwrap_or_default();
        self.emit_token_ex(
            Kind::CloseBraceToken,
            statements_end,
            WriteKind::Punctuation,
            body,
            TEF_NO_COMMENTS,
        );

        if let Some(h) = self.p.handlers.on_after_emit_node.as_mut() {
            h(Some(body));
        }
    }

    /// `p.emitFunctionBodyNode`
    fn emit_function_body_node(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            self.write_trailing_semicolon();
            return;
        };

        self.write_space();
        self.emit_function_body(node);
    }

    //
    // Type Members
    //

    /// `p.emitPropertySignature`
    fn emit_property_signature(&mut self, node: NodeId) {
        let (name, postfix_token, type_) = {
            let d = self.p.nodes[node].as_property_signature_declaration();
            (
                d.named_member_base.name,
                d.named_member_base.postfix_token,
                d.type_,
            )
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        self.emit_property_name(name);
        self.emit_token_node(postfix_token);
        self.emit_type_annotation(type_);
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitPropertyDeclaration`
    fn emit_property_declaration(&mut self, node: NodeId) {
        let (name, postfix_token, type_, initializer) = {
            let d = self.p.nodes[node].as_property_declaration();
            (
                d.named_member_base.name,
                d.named_member_base.postfix_token,
                d.type_,
                d.initializer,
            )
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), true /*allowDecorators*/);
        self.emit_property_name(name);
        self.emit_token_node(postfix_token);
        self.emit_type_annotation(type_);
        let equal_token_pos = greatest_end(
            name.map(|n| self.p.nodes[n].end()).unwrap_or(-1),
            [
                type_.map(|t| self.p.nodes[t].end()),
                postfix_token.map(|t| self.p.nodes[t].end()),
            ],
        );
        self.emit_initializer(initializer, equal_token_pos, node);
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitMethodSignature`
    fn emit_method_signature(&mut self, node: NodeId) {
        let (name, postfix_token) = {
            let d = self.p.nodes[node].as_method_signature_declaration();
            (d.named_member_base.name, d.named_member_base.postfix_token)
        };
        let state = self.enter_node(node);
        let modifiers = self.p.nodes[node].modifiers().cloned();
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        self.emit_property_name(name);
        self.emit_token_node(postfix_token);
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.write_trailing_semicolon();
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitMethodDeclaration`
    fn emit_method_declaration(&mut self, node: NodeId) {
        let (name, postfix_token, asterisk_token, body) = {
            let d = self.p.nodes[node].as_method_declaration();
            (
                d.named_member_base.name,
                d.named_member_base.postfix_token,
                d.function_like_with_body_base.body_base.asterisk_token,
                d.function_like_with_body_base.body_base.body,
            )
        };
        let state = self.enter_node(node);
        let modifiers = self.p.nodes[node].modifiers().cloned();
        self.emit_modifier_list(node, modifiers.as_ref(), true /*allowDecorators*/);
        self.emit_token_node(asterisk_token);
        self.emit_property_name(name);
        self.emit_token_node(postfix_token);
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.emit_function_body_node(body);
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitClassStaticBlockDeclaration`
    fn emit_class_static_block_declaration(&mut self, node: NodeId) {
        let body = self.p.nodes[node].as_class_static_block_declaration().body;
        let state = self.enter_node(node);
        self.write_keyword("static");
        self.push_name_generation_scope(node);
        self.emit_function_body_node(body);
        self.pop_name_generation_scope(node);
        self.exit_node(node, state);
    }

    /// `p.emitConstructor`
    fn emit_constructor(&mut self, node: NodeId) {
        let body = self.p.nodes[node]
            .as_constructor_declaration()
            .function_like_with_body_base
            .body_base
            .body;
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        self.write_keyword("constructor");
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.emit_function_body_node(body);
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitAccessorDeclaration`
    fn emit_accessor_declaration(&mut self, token: Kind, node: NodeId) {
        let (name, body) = {
            let n = &self.p.nodes[node];
            let d = if n.kind == Kind::GetAccessor {
                &n.as_get_accessor_declaration().accessor_declaration_base
            } else {
                &n.as_set_accessor_declaration().accessor_declaration_base
            };
            (
                d.named_member_base.name,
                d.function_like_with_body_base.body_base.body,
            )
        };
        let state = self.enter_node(node);
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let pos = self.emit_modifier_list(node, modifiers.as_ref(), true /*allowDecorators*/);
        self.emit_token(token, pos, WriteKind::Keyword, node);
        self.write_space();
        self.emit_property_name(name);
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.emit_function_body_node(body);
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitGetAccessorDeclaration`
    fn emit_get_accessor_declaration(&mut self, node: NodeId) {
        self.emit_accessor_declaration(Kind::GetKeyword, node)
    }

    /// `p.emitSetAccessorDeclaration`
    fn emit_set_accessor_declaration(&mut self, node: NodeId) {
        self.emit_accessor_declaration(Kind::SetKeyword, node)
    }

    /// `p.emitCallSignature`
    fn emit_call_signature(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.write_trailing_semicolon();
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitConstructSignature`
    fn emit_construct_signature(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.write_keyword("new");
        self.write_space();
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.write_trailing_semicolon();
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitIndexSignature`
    fn emit_index_signature(&mut self, node: NodeId) {
        let (parameters, type_) = {
            let d = self.p.nodes[node].as_index_signature_declaration();
            (
                d.function_like_base.parameters.clone(),
                d.function_like_base.type_,
            )
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_parameters_for_index_signature(node, parameters.as_ref());
        self.emit_type_annotation(type_);
        self.write_trailing_semicolon();
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitClassElement`
    fn emit_class_element(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::PropertyDeclaration => self.emit_property_declaration(node),
            Kind::MethodDeclaration => self.emit_method_declaration(node),
            Kind::ClassStaticBlockDeclaration => self.emit_class_static_block_declaration(node),
            Kind::Constructor => self.emit_constructor(node),
            Kind::GetAccessor => self.emit_get_accessor_declaration(node),
            Kind::SetAccessor => self.emit_set_accessor_declaration(node),
            Kind::IndexSignature => self.emit_index_signature(node),
            Kind::SemicolonClassElement => self.emit_semicolon_class_element(node),
            Kind::NotEmittedStatement => self.emit_not_emitted_statement(node),
            Kind::JSTypeAliasDeclaration => self.emit_type_alias_declaration(node),
            _ => panic!("unexpected ClassElement: {:?}", self.p.nodes[node].kind),
        }
    }

    /// `p.emitTypeElement`
    fn emit_type_element(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::PropertySignature => self.emit_property_signature(node),
            Kind::MethodSignature => self.emit_method_signature(node),
            Kind::CallSignature => self.emit_call_signature(node),
            Kind::ConstructSignature => self.emit_construct_signature(node),
            Kind::GetAccessor => self.emit_get_accessor_declaration(node),
            Kind::SetAccessor => self.emit_set_accessor_declaration(node),
            Kind::IndexSignature => self.emit_index_signature(node),
            Kind::NotEmittedTypeElement => self.emit_not_emitted_type_element(node),
            _ => panic!("unexpected TypeElement: {:?}", self.p.nodes[node].kind),
        }
    }

    /// `p.emitObjectLiteralElement`
    fn emit_object_literal_element(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::PropertyAssignment => self.emit_property_assignment(node),
            Kind::ShorthandPropertyAssignment => self.emit_shorthand_property_assignment(node),
            Kind::SpreadAssignment => self.emit_spread_assignment(node),
            Kind::MethodDeclaration => self.emit_method_declaration(node),
            Kind::GetAccessor => self.emit_get_accessor_declaration(node),
            Kind::SetAccessor => self.emit_set_accessor_declaration(node),
            _ => panic!(
                "unhandled ObjectLiteralElement: {:?}",
                self.p.nodes[node].kind
            ),
        }
    }

    /// `node.AsGetAccessorDeclaration().AccessorDeclarationBase` /
    /// `node.AsSetAccessorDeclaration().AccessorDeclarationBase`.
    fn accessor_declaration_base(nodes: &[Node], node: NodeId) -> &ast::AccessorDeclarationBase {
        match nodes[node].kind {
            Kind::GetAccessor => {
                &nodes[node]
                    .as_get_accessor_declaration()
                    .accessor_declaration_base
            }
            Kind::SetAccessor => {
                &nodes[node]
                    .as_set_accessor_declaration()
                    .accessor_declaration_base
            }
            _ => panic!("unexpected accessor: {:?}", nodes[node].kind),
        }
    }

    //
    // Types
    //

    /// `p.emitKeywordTypeNode`
    fn emit_keyword_type_node(&mut self, node: NodeId) {
        self.emit_keyword_node(node)
    }

    /// `p.emitTypePredicateParameterName`
    fn emit_type_predicate_parameter_name(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        match self.p.nodes[node].kind {
            Kind::Identifier => self.emit_identifier_reference(node),
            Kind::ThisType => self.emit_this_type(node),
            _ => panic!(
                "unexpected TypePredicateParameterName: {:?}",
                self.p.nodes[node].kind
            ),
        }
    }

    /// `p.emitTypePredicate`
    fn emit_type_predicate(&mut self, node: NodeId) {
        let (asserts_modifier, parameter_name, type_) = {
            let d = self.p.nodes[node].as_type_predicate_node();
            (d.asserts_modifier, d.parameter_name, d.type_)
        };
        let state = self.enter_node(node);
        if let Some(asserts_modifier) = asserts_modifier {
            self.emit_token_node(Some(asserts_modifier));
            self.write_space();
        }
        self.emit_type_predicate_parameter_name(parameter_name);
        if let Some(type_) = type_ {
            self.write_space();
            self.write_keyword("is");
            self.write_space();
            self.emit_type_node_outside_extends(type_);
        }
        self.exit_node(node, state);
    }

    /// `p.emitTypeArgument`
    fn emit_type_argument(&mut self, node: NodeId) {
        self.emit_type_node_outside_extends(node)
    }

    /// `p.emitTypeArguments`
    fn emit_type_arguments(&mut self, parent_node: NodeId, nodes: Option<NodeList>) {
        let Some(nodes) = nodes else {
            return;
        };
        // TODO: preserve trailing comma after Strada migration
        self.emit_list(
            Self::emit_type_parameter_declaration_node,
            Some(parent_node),
            Some(&nodes),
            LF_TYPE_ARGUMENTS,
        );
    }

    /// `p.emitTypeReference`
    fn emit_type_reference(&mut self, node: NodeId) {
        let (type_name, type_arguments) = {
            let d = self.p.nodes[node].as_type_reference_node();
            (
                d.type_name,
                d.node_with_type_arguments_base.type_arguments.clone(),
            )
        };
        let state = self.enter_node(node);
        self.emit_entity_name(type_name);
        self.emit_type_arguments(node, type_arguments);
        self.exit_node(node, state);
    }

    /// `p.emitReturnType` — emits the return type of a FunctionTypeNode or
    /// ConstructorTypeNode, including the arrow (`=>`)
    fn emit_return_type(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        self.write_punctuation("=>");
        self.write_space();
        if self.in_extends
            && self.p.nodes[node].kind == Kind::InferType
            && self.p.nodes[node]
                .as_infer_type_node()
                .type_parameter
                .is_some_and(|tp| {
                    self.p.nodes[tp]
                        .as_type_parameter_declaration()
                        .constraint
                        .is_some()
                })
        {
            // if the parent FunctionTypeNode or ConstructorTypeNode is in the `extends` clause of
            // a ConditionalTypeNode, we must parenthesize `infer ... extends ...` so as not to
            // result in an ambiguous parse.
            self.emit_type_node_preserving_extends(node, TypePrecedence::HIGHEST);
        } else {
            self.emit_type_node_preserving_extends(node, TypePrecedence::LOWEST);
        }
    }

    /// `p.emitFunctionType`
    fn emit_function_type(&mut self, node: NodeId) {
        let (type_parameters, parameters, type_) = {
            let d = self.p.nodes[node].as_function_type_node();
            (
                d.function_or_constructor_type_node_base
                    .function_like_base
                    .type_parameters
                    .clone(),
                d.function_or_constructor_type_node_base
                    .function_like_base
                    .parameters
                    .clone(),
                d.function_or_constructor_type_node_base
                    .function_like_base
                    .type_,
            )
        };
        let state = self.enter_node(node);
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        // !!! in the old emitter, quickinfo uses type arguments in place of type parameters for
        // instantiated signatures
        self.emit_type_parameters(node, type_parameters);
        self.emit_parameters(node, parameters.as_ref());
        self.write_space();
        self.emit_return_type(type_);
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitConstructorType`
    fn emit_constructor_type(&mut self, node: NodeId) {
        let (type_parameters, parameters, type_) = {
            let d = self.p.nodes[node].as_constructor_type_node();
            (
                d.function_or_constructor_type_node_base
                    .function_like_base
                    .type_parameters
                    .clone(),
                d.function_or_constructor_type_node_base
                    .function_like_base
                    .parameters
                    .clone(),
                d.function_or_constructor_type_node_base
                    .function_like_base
                    .type_,
            )
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        self.write_keyword("new");
        self.write_space();
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        // !!! in the old emitter, quickinfo uses type arguments in place of type parameters for
        // instantiated signatures
        self.emit_type_parameters(node, type_parameters);
        self.emit_parameters(node, parameters.as_ref());
        self.write_space();
        self.emit_return_type(type_);
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitTypeQuery`
    fn emit_type_query(&mut self, node: NodeId) {
        let (expr_name, type_arguments) = {
            let d = self.p.nodes[node].as_type_query_node();
            (
                d.expr_name,
                d.node_with_type_arguments_base.type_arguments.clone(),
            )
        };
        let state = self.enter_node(node);
        self.write_keyword("typeof");
        self.write_space();
        self.emit_entity_name(expr_name);
        self.emit_type_arguments(node, type_arguments);
        self.exit_node(node, state);
    }

    /// `p.emitTypeLiteral`
    fn emit_type_literal(&mut self, node: NodeId) {
        let members = self.p.nodes[node].as_type_literal_node().members.clone();
        let state = self.enter_node(node);
        self.push_name_generation_scope(node);
        self.generate_all_member_names(members.as_ref());
        self.write_punctuation("{");
        let flags = if self.should_emit_on_single_line(Some(node)) {
            LF_SINGLE_LINE_TYPE_LITERAL_MEMBERS
        } else {
            LF_MULTI_LINE_TYPE_LITERAL_MEMBERS
        };
        self.emit_list(
            Self::emit_type_element,
            Some(node),
            members.as_ref(),
            flags | LF_NO_SPACE_IF_EMPTY,
        );
        self.write_punctuation("}");
        self.pop_name_generation_scope(node);
        self.exit_node(node, state);
    }

    /// `p.emitArrayType`
    fn emit_array_type(&mut self, node: NodeId) {
        let element_type = self.p.nodes[node].as_array_type_node().element_type;
        let state = self.enter_node(node);
        self.emit_postfix_type_operand(element_type, node);
        self.write_punctuation("[");
        self.write_punctuation("]");
        self.exit_node(node, state);
    }

    /// `p.emitPostfixTypeOperand` — emits the operand of a postfix type
    /// (ArrayType, IndexedAccessType, OptionalType). It is equivalent to
    /// `emitTypeNode(operand, TypePrecedencePostfix)` except that it preserves
    /// a parsed `typeof X` operand without adding parentheses (e.g.,
    /// `typeof C[K]` instead of `(typeof C)[K]`).
    fn emit_postfix_type_operand(&mut self, operand: Option<NodeId>, parent: NodeId) {
        if ast::is_parse_tree_node(&self.p.nodes[parent])
            && operand.is_some_and(|o| self.p.nodes[o].kind == Kind::TypeQuery)
        {
            self.emit_type_node(operand, TypePrecedence::TYPE_OPERATOR);
            return;
        }
        self.emit_type_node(operand, TypePrecedence::POSTFIX);
    }

    /// `p.emitTupleElementType`
    fn emit_tuple_element_type(&mut self, node: NodeId) {
        self.emit_type_node_outside_extends(node)
    }

    /// `p.emitTupleType`
    fn emit_tuple_type(&mut self, node: NodeId) {
        let elements = self.p.nodes[node].as_tuple_type_node().elements.clone();
        let state = self.enter_node(node);
        self.emit_token(
            Kind::OpenBracketToken,
            self.p.nodes[node].pos(),
            WriteKind::Punctuation,
            node,
        );
        let flags = if self.should_emit_on_single_line(Some(node)) {
            LF_SINGLE_LINE_TUPLE_TYPE_ELEMENTS
        } else {
            LF_MULTI_LINE_TUPLE_TYPE_ELEMENTS
        };
        self.emit_list(
            Self::emit_tuple_element_type,
            Some(node),
            elements.as_ref(),
            flags | LF_NO_SPACE_IF_EMPTY,
        );
        self.emit_token(
            Kind::CloseBracketToken,
            elements.map(|e| e.loc.end()).unwrap_or_default(),
            WriteKind::Punctuation,
            node,
        );
        self.exit_node(node, state);
    }

    /// `p.emitRestType`
    fn emit_rest_type(&mut self, node: NodeId) {
        let type_ = self.p.nodes[node].as_rest_type_node().type_;
        let state = self.enter_node(node);
        self.write_punctuation("...");
        self.emit_type_node_outside_extends_opt(type_);
        self.exit_node(node, state);
    }

    /// `p.emitOptionalType`
    fn emit_optional_type(&mut self, node: NodeId) {
        let type_ = self.p.nodes[node].as_optional_type_node().type_;
        let state = self.enter_node(node);
        // !!! May need extra parenthesization if we also have JSDocNullableType
        self.emit_postfix_type_operand(type_, node);
        self.write_punctuation("?");
        self.exit_node(node, state);
    }

    /// `p.emitNamedTupleMember`
    fn emit_named_tuple_member(&mut self, node: NodeId) {
        let (dot_dot_dot_token, name, question_token, type_) = {
            let d = self.p.nodes[node].as_named_tuple_member();
            (d.dot_dot_dot_token, d.name, d.question_token, d.type_)
        };
        let state = self.enter_node(node);
        self.emit_punctuation_node_opt(dot_dot_dot_token);
        self.emit_identifier_name_node(name);
        self.emit_punctuation_node_opt(question_token);
        self.emit_token(
            Kind::ColonToken,
            greatest_end(
                name.map(|n| self.p.nodes[n].end()).unwrap_or(-1),
                [question_token.map(|t| self.p.nodes[t].end())],
            ),
            WriteKind::Punctuation,
            node,
        );
        self.write_space();
        self.emit_type_node_outside_extends_opt(type_);
        self.exit_node(node, state);
    }

    /// `p.emitUnionTypeConstituent`
    fn emit_union_type_constituent(&mut self, node: NodeId) {
        self.emit_type_node(Some(node), TypePrecedence::TYPE_OPERATOR)
    }

    /// `p.emitUnionType`
    fn emit_union_type(&mut self, node: NodeId) {
        let types = self.p.nodes[node]
            .as_union_type_node()
            .union_or_intersection_type_node_base
            .types
            .clone();
        let state = self.enter_node(node);
        self.emit_list(
            Self::emit_union_type_constituent,
            Some(node),
            types.as_ref(),
            LF_UNION_TYPE_CONSTITUENTS,
        );
        self.exit_node(node, state);
    }

    /// `p.emitIntersectionTypeConstituent`
    fn emit_intersection_type_constituent(&mut self, node: NodeId) {
        self.emit_type_node(Some(node), TypePrecedence::TYPE_OPERATOR)
    }

    /// `p.emitIntersectionType`
    fn emit_intersection_type(&mut self, node: NodeId) {
        let types = self.p.nodes[node]
            .as_intersection_type_node()
            .union_or_intersection_type_node_base
            .types
            .clone();
        let state = self.enter_node(node);
        self.emit_list(
            Self::emit_intersection_type_constituent,
            Some(node),
            types.as_ref(),
            LF_INTERSECTION_TYPE_CONSTITUENTS, /*, parenthesizer.parenthesizeConstituentTypeOfIntersectionType*/ // !!!
        );
        self.exit_node(node, state);
    }

    /// `p.emitConditionalType`
    fn emit_conditional_type(&mut self, node: NodeId) {
        let (check_type, extends_type, true_type, false_type) = {
            let d = self.p.nodes[node].as_conditional_type_node();
            (d.check_type, d.extends_type, d.true_type, d.false_type)
        };
        let state = self.enter_node(node);
        self.emit_type_node(check_type, TypePrecedence::UNION);
        self.write_space();
        self.write_keyword("extends");
        self.write_space();
        self.emit_type_node_in_extends_opt(extends_type);
        self.write_space();
        self.write_punctuation("?");
        self.write_space();
        self.emit_type_node_outside_extends_opt(true_type);
        self.write_space();
        self.write_punctuation(":");
        self.write_space();
        self.emit_type_node_outside_extends_opt(false_type);
        self.exit_node(node, state);
    }

    /// `p.emitInferTypeParameter`
    fn emit_infer_type_parameter(&mut self, node: NodeId) {
        let (name, constraint) = {
            let d = self.p.nodes[node].as_type_parameter_declaration();
            (d.name, d.constraint)
        };
        let state = self.enter_node(node);
        self.emit_binding_identifier(name.expect("infer type parameter name"));
        if let Some(constraint) = constraint {
            self.write_space();
            self.write_keyword("extends");
            self.write_space();
            self.emit_type_node_in_extends(constraint);
        }
        self.exit_node(node, state);
    }

    /// `p.emitInferType`
    fn emit_infer_type(&mut self, node: NodeId) {
        let type_parameter = self.p.nodes[node].as_infer_type_node().type_parameter;
        let state = self.enter_node(node);
        self.write_keyword("infer");
        self.write_space();
        self.emit_infer_type_parameter(type_parameter.expect("infer type parameter"));
        self.exit_node(node, state);
    }

    /// `p.emitParenthesizedType`
    fn emit_parenthesized_type(&mut self, node: NodeId) {
        let type_ = self.p.nodes[node].as_parenthesized_type_node().type_;
        let state = self.enter_node(node);
        self.write_punctuation("(");
        self.emit_type_node_outside_extends_opt(type_);
        self.write_punctuation(")");
        self.exit_node(node, state);
    }

    /// `p.emitThisType`
    fn emit_this_type(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.write_keyword("this");
        self.exit_node(node, state);
    }

    /// `p.emitTypeOperator`
    fn emit_type_operator(&mut self, node: NodeId) {
        let (operator, type_) = {
            let d = self.p.nodes[node].as_type_operator_node();
            (d.operator, d.type_)
        };
        let state = self.enter_node(node);
        self.emit_token(operator, self.p.nodes[node].pos(), WriteKind::Keyword, node);
        self.write_space();
        self.emit_type_node(
            type_,
            if operator == Kind::ReadonlyKeyword {
                TypePrecedence::POSTFIX
            } else {
                TypePrecedence::TYPE_OPERATOR
            },
        );
        self.exit_node(node, state);
    }

    /// `p.emitIndexedAccessType`
    fn emit_indexed_access_type(&mut self, node: NodeId) {
        let (object_type, index_type) = {
            let d = self.p.nodes[node].as_indexed_access_type_node();
            (d.object_type, d.index_type)
        };
        let state = self.enter_node(node);
        self.emit_postfix_type_operand(object_type, node);
        self.write_punctuation("[");
        self.emit_type_node_outside_extends_opt(index_type);
        self.write_punctuation("]");
        self.exit_node(node, state);
    }

    /// `p.emitMappedTypeParameter`
    fn emit_mapped_type_parameter(&mut self, node: NodeId) {
        let (name, constraint) = {
            let d = self.p.nodes[node].as_type_parameter_declaration();
            (d.name, d.constraint)
        };
        let state = self.enter_node(node);
        self.emit_binding_identifier(name.expect("mapped type parameter name"));
        self.write_space();
        self.write_keyword("in");
        self.write_space();
        self.emit_type_node_outside_extends_opt(constraint);
        self.exit_node(node, state);
    }

    /// `p.emitMappedType`
    fn emit_mapped_type(&mut self, node: NodeId) {
        let (readonly_token, type_parameter, name_type, question_token, type_, members) = {
            let d = self.p.nodes[node].as_mapped_type_node();
            (
                d.readonly_token,
                d.type_parameter,
                d.name_type,
                d.question_token,
                d.type_,
                d.members.clone(),
            )
        };
        let state = self.enter_node(node);
        let single_line = self.should_emit_on_single_line(Some(node));
        self.write_punctuation("{");
        if single_line {
            self.write_space();
        } else {
            self.write_line();
            self.increase_indent();
        }
        if let Some(readonly_token) = readonly_token {
            self.emit_token_node(Some(readonly_token));
            if self.p.nodes[readonly_token].kind != Kind::ReadonlyKeyword {
                self.write_keyword("readonly");
            }
            self.write_space();
        }
        self.write_punctuation("[");
        self.emit_mapped_type_parameter(type_parameter.expect("mapped type parameter"));
        if let Some(name_type) = name_type {
            self.write_space();
            self.write_keyword("as");
            self.write_space();
            self.emit_type_node_outside_extends(name_type);
        }
        self.write_punctuation("]");
        if let Some(question_token) = question_token {
            self.emit_punctuation_node_opt(Some(question_token));
            if self.p.nodes[question_token].kind != Kind::QuestionToken {
                self.write_punctuation("?");
            }
        }
        if let Some(type_) = type_ {
            self.write_punctuation(":");
            self.write_space();
            self.emit_type_node_outside_extends(type_);
        }
        self.write_trailing_semicolon();
        if let Some(members) = members
            && !members.nodes.is_empty()
        {
            if single_line {
                self.write_space();
            } else {
                self.write_line();
            }
            self.emit_list(
                Self::emit_type_element,
                Some(node),
                Some(&members),
                LF_PRESERVE_LINES,
            );
        }
        if single_line {
            self.write_space();
        } else {
            self.write_line();
            self.decrease_indent();
        }
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    /// `p.emitLiteralType`
    fn emit_literal_type(&mut self, node: NodeId) {
        let literal = self.p.nodes[node].as_literal_type_node().literal;
        let state = self.enter_node(node);
        self.emit_expression(literal, OperatorPrecedence::COMMA);
        self.exit_node(node, state);
    }

    /// `p.emitTemplateTypeSpan`
    fn emit_template_type_span(&mut self, node: NodeId) {
        let (type_, literal) = {
            let d = self.p.nodes[node].as_template_literal_type_span();
            (d.type_, d.literal)
        };
        let state = self.enter_node(node);
        self.emit_type_node_outside_extends_opt(type_);
        self.emit_template_middle_tail(literal.expect("template type span literal"));
        self.exit_node(node, state);
    }

    /// `p.emitTemplateTypeSpanNode`
    fn emit_template_type_span_node(&mut self, node: NodeId) {
        self.emit_template_type_span(node)
    }

    /// `p.emitTemplateType`
    fn emit_template_type(&mut self, node: NodeId) {
        let (head, template_spans) = {
            let d = self.p.nodes[node].as_template_literal_type_node();
            (d.head, d.template_spans.clone())
        };
        let state = self.enter_node(node);
        self.emit_template_head(head.expect("template literal type head"));
        self.emit_list(
            Self::emit_template_type_span_node,
            Some(node),
            template_spans.as_ref(),
            LF_TEMPLATE_EXPRESSION_SPANS,
        );
        self.exit_node(node, state);
    }

    /// `p.emitImportTypeNodeAttributes`
    fn emit_import_type_node_attributes(&mut self, node: NodeId) {
        let (token, attributes) = {
            let d = self.p.nodes[node].as_import_attributes();
            (d.token, d.attributes.clone())
        };
        let state = self.enter_node(node);
        self.write_punctuation("{");
        self.write_space();
        self.write_keyword(if token == Kind::AssertKeyword {
            "assert"
        } else {
            "with"
        });
        self.write_punctuation(":");
        self.write_space();
        self.emit_list(
            Self::emit_import_attribute_node,
            Some(node),
            attributes.as_ref(),
            LF_IMPORT_ATTRIBUTES,
        );
        self.write_space();
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    /// `p.emitImportTypeNode`
    fn emit_import_type_node(&mut self, node: NodeId) {
        let (is_type_of, argument, attributes, qualifier, type_arguments) = {
            let d = self.p.nodes[node].as_import_type_node();
            (
                d.is_type_of,
                d.argument,
                d.attributes,
                d.qualifier,
                d.node_with_type_arguments_base.type_arguments.clone(),
            )
        };
        let state = self.enter_node(node);
        if is_type_of {
            self.write_keyword("typeof");
            self.write_space();
        }
        self.write_keyword("import");
        self.write_punctuation("(");
        self.emit_type_node_outside_extends_opt(argument);
        if let Some(attributes) = attributes {
            self.write_punctuation(",");
            self.write_space();
            self.emit_import_type_node_attributes(attributes);
        }
        self.write_punctuation(")");
        if let Some(qualifier) = qualifier {
            self.write_punctuation(".");
            self.emit_entity_name(Some(qualifier));
        }
        self.emit_type_arguments(node, type_arguments);
        self.exit_node(node, state);
    }

    /// `p.emitTypeNodeInExtends` — emits a Type node in the `extends` clause of
    /// a ConditionalType
    fn emit_type_node_in_extends(&mut self, node: NodeId) {
        let saved_in_extends = self.in_extends;
        self.in_extends = true;
        self.emit_type_node_preserving_extends(node, TypePrecedence::LOWEST);
        self.in_extends = saved_in_extends;
    }

    fn emit_type_node_in_extends_opt(&mut self, node: Option<NodeId>) {
        let saved_in_extends = self.in_extends;
        self.in_extends = true;
        self.emit_type_node(node, TypePrecedence::LOWEST);
        self.in_extends = saved_in_extends;
    }

    /// `p.emitTypeNodeOutsideExtends` — emits a Type node not in the `extends`
    /// clause of a ConditionalType or InferType
    fn emit_type_node_outside_extends(&mut self, node: NodeId) {
        self.emit_type_node_outside_extends_opt(Some(node))
    }

    fn emit_type_node_outside_extends_opt(&mut self, node: Option<NodeId>) {
        let saved_in_extends = self.in_extends;
        self.in_extends = false;
        self.emit_type_node(node, TypePrecedence::LOWEST);
        self.in_extends = saved_in_extends;
    }

    /// `p.emitTypeNodePreservingExtends` — emits a Type node preserving whether
    /// or not we are currently in the `extends` clause of a ConditionalType or
    /// InferType
    fn emit_type_node_preserving_extends(&mut self, node: NodeId, precedence: TypePrecedence) {
        self.emit_type_node(Some(node), precedence)
    }

    /// `p.emitTypeNode`
    fn emit_type_node(&mut self, node: Option<NodeId>, mut precedence: TypePrecedence) {
        let Some(node) = node else {
            return;
        };
        if self.in_extends && precedence <= TypePrecedence::CONDITIONAL {
            // in the `extends` clause of a ConditionalType or InferType, a ConditionalType must
            // be parenthesized
            precedence = TypePrecedence::FUNCTION;
        }

        let saved_in_extends = self.in_extends;
        let parens = get_type_node_precedence(&self.p.nodes[node], self.p.nodes) < precedence;
        if parens {
            self.in_extends = false;
            self.write_punctuation("(");
        }

        match self.p.nodes[node].kind {
            // Keyword Types
            Kind::AnyKeyword
            | Kind::UnknownKeyword
            | Kind::NumberKeyword
            | Kind::BigIntKeyword
            | Kind::ObjectKeyword
            | Kind::BooleanKeyword
            | Kind::StringKeyword
            | Kind::SymbolKeyword
            | Kind::VoidKeyword
            | Kind::UndefinedKeyword
            | Kind::NeverKeyword
            | Kind::IntrinsicKeyword => self.emit_keyword_type_node(node),

            // Types
            Kind::TypePredicate => self.emit_type_predicate(node),
            Kind::TypeReference => self.emit_type_reference(node),
            Kind::FunctionType => self.emit_function_type(node),
            Kind::ConstructorType => self.emit_constructor_type(node),
            Kind::TypeQuery => self.emit_type_query(node),
            Kind::TypeLiteral => self.emit_type_literal(node),
            Kind::ArrayType => self.emit_array_type(node),
            Kind::TupleType => self.emit_tuple_type(node),
            Kind::OptionalType => self.emit_optional_type(node),
            Kind::RestType => self.emit_rest_type(node),
            Kind::UnionType => self.emit_union_type(node),
            Kind::IntersectionType => self.emit_intersection_type(node),
            Kind::ConditionalType => self.emit_conditional_type(node),
            Kind::InferType => self.emit_infer_type(node),
            Kind::ParenthesizedType => self.emit_parenthesized_type(node),
            Kind::ThisType => self.emit_this_type(node),
            Kind::TypeOperator => self.emit_type_operator(node),
            Kind::IndexedAccessType => self.emit_indexed_access_type(node),
            Kind::MappedType => self.emit_mapped_type(node),
            Kind::LiteralType => self.emit_literal_type(node),
            Kind::NamedTupleMember => self.emit_named_tuple_member(node),
            Kind::TemplateLiteralType => self.emit_template_type(node),
            Kind::TemplateLiteralTypeSpan => self.emit_template_type_span(node),
            Kind::ImportType => self.emit_import_type_node(node),

            Kind::PropertyAccessExpression => {
                // Occurs in pseudo-types such as `f<T>.C`, where `f` is a generic function and `C`
                // is a local type
                self.emit_property_access_expression(node)
            }
            Kind::ExpressionWithTypeArguments => {
                // !!! Should this actually be considered a type?
                self.emit_expression_with_type_arguments(node)
            }

            Kind::JSDocAllType => self.emit_js_doc_all_type(node),
            Kind::JSDocNonNullableType => self.emit_js_doc_non_nullable_type(node),
            Kind::JSDocNullableType => self.emit_js_doc_nullable_type(node),
            Kind::JSDocOptionalType => self.emit_js_doc_optional_type(node),
            Kind::JSDocVariadicType => self.emit_js_doc_variadic_type(node),

            _ => panic!("unhandled TypeNode: {:?}", self.p.nodes[node].kind),
        }

        if parens {
            self.write_punctuation(")");
        }

        self.in_extends = saved_in_extends;
    }

    //
    // Binding patterns
    //

    /// `p.emitObjectBindingPattern`
    fn emit_object_binding_pattern(&mut self, node: NodeId) {
        let elements = self.p.nodes[node].as_binding_pattern().elements.clone();
        let state = self.enter_node(node);
        self.write_punctuation("{");
        self.emit_list(
            Self::emit_binding_element_node,
            Some(node),
            elements.as_ref(),
            LF_OBJECT_BINDING_PATTERN_ELEMENTS,
        );
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    /// `p.emitArrayBindingPattern`
    fn emit_array_binding_pattern(&mut self, node: NodeId) {
        let elements = self.p.nodes[node].as_binding_pattern().elements.clone();
        let state = self.enter_node(node);
        self.write_punctuation("[");
        self.emit_list(
            Self::emit_binding_element_node,
            Some(node),
            elements.as_ref(),
            LF_ARRAY_BINDING_PATTERN_ELEMENTS,
        );
        self.write_punctuation("]");
        self.exit_node(node, state);
    }

    /// `p.emitBindingElement`
    fn emit_binding_element(&mut self, node: NodeId) {
        let (dot_dot_dot_token, property_name, name, initializer) = {
            let d = self.p.nodes[node].as_binding_element();
            (d.dot_dot_dot_token, d.property_name, d.name, d.initializer)
        };
        let state = self.enter_node(node);
        self.emit_token_node(dot_dot_dot_token);
        if let Some(property_name) = property_name {
            self.emit_property_name(Some(property_name));
            self.write_punctuation(":");
            self.write_space();
        }
        // Old parser used `OmittedExpression` as a substitute for `Elision`. New parser uses a
        // `BindingElement` with nil members
        if let Some(name) = name {
            self.emit_binding_name(Some(name));
            self.emit_initializer(initializer, self.p.nodes[name].end(), node);
        }
        self.exit_node(node, state);
    }

    /// `p.emitBindingElementNode`
    fn emit_binding_element_node(&mut self, node: NodeId) {
        self.emit_binding_element(node)
    }

    /// `p.emitJSDocAllType`
    fn emit_js_doc_all_type(&mut self, node: NodeId) {
        self.emit_keyword_node(node)
    }

    /// `p.emitJSDocNonNullableType`
    fn emit_js_doc_non_nullable_type(&mut self, node: NodeId) {
        let type_ = self.p.nodes[node].as_js_doc_non_nullable_type().type_;
        let state = self.enter_node(node);
        self.write_punctuation("!");
        self.emit_type_node(type_, TypePrecedence::NON_ARRAY);
        self.exit_node(node, state);
    }

    /// `p.emitJSDocNullableType`
    fn emit_js_doc_nullable_type(&mut self, node: NodeId) {
        let type_ = self.p.nodes[node].as_js_doc_nullable_type().type_;
        let state = self.enter_node(node);
        self.write_punctuation("?");
        self.emit_type_node(type_, TypePrecedence::NON_ARRAY);
        self.exit_node(node, state);
    }

    /// `p.emitJSDocOptionalType`
    fn emit_js_doc_optional_type(&mut self, node: NodeId) {
        let type_ = self.p.nodes[node].as_js_doc_optional_type().type_;
        let state = self.enter_node(node);
        self.emit_type_node(type_, TypePrecedence::JSDOC);
        self.write_punctuation("=");
        self.exit_node(node, state);
    }

    /// `p.emitJSDocVariadicType`
    fn emit_js_doc_variadic_type(&mut self, node: NodeId) {
        let type_ = self.p.nodes[node].as_js_doc_variadic_type().type_;
        let state = self.enter_node(node);
        self.write_punctuation("...");
        self.emit_type_node(type_, TypePrecedence::JSDOC);
        self.exit_node(node, state);
    }

    //
    // Expressions
    //

    /// `p.emitKeywordExpression`
    fn emit_keyword_expression(&mut self, node: NodeId) {
        self.emit_keyword_node(node)
    }

    /// `p.emitArrayLiteralExpressionElement`
    fn emit_array_literal_expression_element(&mut self, node: NodeId) {
        self.emit_expression(Some(node), OperatorPrecedence::SPREAD)
    }

    /// `p.emitArrayLiteralExpression`
    fn emit_array_literal_expression(&mut self, node: NodeId) {
        let (elements, multi_line) = {
            let d = self.p.nodes[node].as_array_literal_expression();
            (d.elements.clone(), d.multi_line)
        };
        let state = self.enter_node(node);
        self.emit_list(
            Self::emit_array_literal_expression_element,
            Some(node),
            elements.as_ref(),
            LF_ARRAY_LITERAL_EXPRESSION_ELEMENTS
                | if multi_line {
                    LF_PREFER_NEW_LINE
                } else {
                    LF_NONE
                },
        );
        self.exit_node(node, state);
    }

    /// `p.emitObjectLiteralExpression`
    fn emit_object_literal_expression(&mut self, node: NodeId) {
        let (properties, multi_line) = {
            let d = self.p.nodes[node].as_object_literal_expression();
            (d.properties.clone(), d.multi_line)
        };
        let state = self.enter_node(node);
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.generate_all_member_names(properties.as_ref());
        self.emit_list(
            Self::emit_object_literal_element,
            Some(node),
            properties.as_ref(),
            LF_OBJECT_LITERAL_EXPRESSION_PROPERTIES
                | if multi_line {
                    LF_PREFER_NEW_LINE
                } else {
                    LF_NONE
                }
                | if self.should_allow_trailing_comma(node, properties.as_ref()) {
                    LF_ALLOW_TRAILING_COMMA
                } else {
                    LF_NONE
                },
        );
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    // 1..toString is a valid property access, emit a dot after the literal
    // Also emit a dot if expression is a integer const enum value - it will appear in generated code as numeric literal
    /// `p.mayNeedDotDotForPropertyAccess`
    fn may_need_dot_dot_for_property_access(&mut self, expression: NodeId) -> bool {
        let expression = ast::skip_partially_emitted_expressions(expression, self.p.nodes);
        if ast::is_numeric_literal(&self.p.nodes[expression]) {
            // check if numeric literal is a decimal literal that was originally written with a dot
            let text = self.get_literal_text_of_node(
                expression,
                None, /*sourceFile*/
                GET_LITERAL_TEXT_FLAGS_NEVER_ASCII_ESCAPE,
            );
            // If the number will be printed verbatim and it doesn't already contain a dot or an exponent indicator, add one
            // if the expression doesn't have any comments that will be emitted.
            return self.p.nodes[expression]
                .as_numeric_literal()
                .literal_expression_base
                .literal_like_node_base
                .token_flags
                .0
                & tsc_ast::TokenFlags::WITH_SPECIFIER.0
                == 0
                && !text.contains(".")
                && !text.contains("E")
                && !text.contains("e");
        }
        false
    }

    /// `p.emitPropertyAccessExpression`
    fn emit_property_access_expression(&mut self, node: NodeId) {
        let (expression, question_dot_token, name) = {
            let d = self.p.nodes[node].as_property_access_expression();
            (d.expression, d.question_dot_token, d.name)
        };
        let state = self.enter_node(node);
        let expression = expression.expect("property access expression");
        self.emit_expression(
            Some(expression),
            if ast::is_optional_chain(&self.p.nodes[node]) {
                OperatorPrecedence::OPTIONAL_CHAIN
            } else {
                OperatorPrecedence::MEMBER
            },
        );
        let mut token = question_dot_token;
        if token.is_none() {
            let t = self
                .p
                .emit_context
                .factory
                .new_token(self.p.nodes, Kind::DotToken);
            self.p.nodes[t].loc = TextRange::new(
                self.p.nodes[expression].end(),
                self.p.nodes[name.unwrap()].pos(),
            );
            self.p
                .emit_context
                .add_emit_flags(t, EmitFlags::NO_SOURCE_MAP);
            token = Some(t);
        }
        let token = token.unwrap();
        let lines_before_dot =
            self.get_lines_between_nodes(Some(node), Some(expression), Some(token));
        self.write_line_repeat(lines_before_dot);
        self.increase_indent_if(lines_before_dot > 0);
        let should_emit_dot_dot = self.p.nodes[token].kind != Kind::QuestionDotToken
            && self.may_need_dot_dot_for_property_access(expression)
            && !self.w().has_trailing_comment()
            && !self.w().has_trailing_whitespace();
        if should_emit_dot_dot {
            self.write_punctuation(".");
        }
        if question_dot_token.is_some() {
            self.emit_token_node(Some(token));
        } else {
            self.emit_token(
                Kind::DotToken,
                self.p.nodes[expression].end(),
                WriteKind::Punctuation,
                node,
            );
        }
        let lines_after_dot = self.get_lines_between_nodes(Some(node), Some(token), name);
        self.write_line_repeat(lines_after_dot);
        self.increase_indent_if(lines_after_dot > 0);
        self.emit_member_name(name);
        self.decrease_indent_if(lines_after_dot > 0);
        self.decrease_indent_if(lines_before_dot > 0);
        self.exit_node(node, state);
    }

    /// `p.emitElementAccessExpression`
    fn emit_element_access_expression(&mut self, node: NodeId) {
        let (expression, question_dot_token, argument_expression) = {
            let d = self.p.nodes[node].as_element_access_expression();
            (d.expression, d.question_dot_token, d.argument_expression)
        };
        let state = self.enter_node(node);
        let expression = expression.expect("element access expression");
        self.emit_expression(
            Some(expression),
            if ast::is_optional_chain(&self.p.nodes[node]) {
                OperatorPrecedence::OPTIONAL_CHAIN
            } else {
                OperatorPrecedence::MEMBER
            },
        );
        self.emit_token_node(question_dot_token);
        self.emit_token(
            Kind::OpenBracketToken,
            greatest_end(
                -1,
                [
                    Some(self.p.nodes[expression].end()),
                    question_dot_token.map(|t| self.p.nodes[t].end()),
                ],
            ),
            WriteKind::Punctuation,
            node,
        );
        self.emit_expression(argument_expression, OperatorPrecedence::COMMA);
        self.emit_token(
            Kind::CloseBracketToken,
            argument_expression
                .map(|a| self.p.nodes[a].end())
                .unwrap_or_default(),
            WriteKind::Punctuation,
            node,
        );
        self.exit_node(node, state);
    }

    /// `p.emitArgument`
    fn emit_argument(&mut self, node: NodeId) {
        self.emit_expression(Some(node), OperatorPrecedence::SPREAD)
    }

    /// `p.emitCallee`
    fn emit_callee(&mut self, callee: Option<NodeId>, parent_node: NodeId) {
        if self.should_emit_indirect_call(parent_node) {
            self.write_punctuation("(");
            self.write_literal("0");
            self.write_punctuation(",");
            self.write_space();
            self.emit_expression(callee, OperatorPrecedence::COMMA);
            self.write_punctuation(")");
        } else if self.p.nodes[parent_node].kind == Kind::CallExpression
            && callee.is_some_and(|callee| {
                util::is_new_expression_without_arguments(
                    self.p.nodes,
                    ast::skip_partially_emitted_expressions(callee, self.p.nodes),
                )
            })
        {
            // Parenthesize `new C` inside of a CallExpression so it is treated as `(new C)()` and not `new C()`
            self.emit_expression(callee, OperatorPrecedence::PARENTHESES);
        } else {
            self.emit_expression(
                callee,
                if ast::is_optional_chain(&self.p.nodes[parent_node]) {
                    OperatorPrecedence::OPTIONAL_CHAIN
                } else {
                    OperatorPrecedence::MEMBER
                },
            );
        }
    }

    /// `p.emitCallExpression`
    fn emit_call_expression(&mut self, node: NodeId) {
        let (expression, question_dot_token, type_arguments, arguments) = {
            let d = self.p.nodes[node].as_call_expression();
            (
                d.expression,
                d.question_dot_token,
                d.type_arguments.clone(),
                d.arguments.clone(),
            )
        };
        let state = self.enter_node(node);
        self.emit_callee(expression, node);
        self.emit_token_node(question_dot_token);
        self.emit_type_arguments(node, type_arguments);
        self.emit_list(
            Self::emit_argument,
            Some(node),
            arguments.as_ref(),
            LF_CALL_EXPRESSION_ARGUMENTS,
        );
        self.exit_node(node, state);
    }

    /// `p.emitNewExpression`
    fn emit_new_expression(&mut self, node: NodeId) {
        let (expression, type_arguments, arguments) = {
            let d = self.p.nodes[node].as_new_expression();
            (
                d.expression.unwrap_or_default(),
                d.type_arguments.clone(),
                d.arguments.clone(),
            )
        };
        let state = self.enter_node(node);
        self.emit_token(
            Kind::NewKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        if self.p.nodes[ast::skip_partially_emitted_expressions(expression, self.p.nodes)].kind
            == Kind::CallExpression
        {
            // Parenthesize `C()` inside of a NewExpression so it is treated as `new (C())` and not `new C()`
            self.emit_expression(Some(expression), OperatorPrecedence::PARENTHESES);
        } else {
            self.emit_expression(Some(expression), OperatorPrecedence::MEMBER);
        }
        self.emit_type_arguments(node, type_arguments);
        self.emit_list(
            Self::emit_argument,
            Some(node),
            arguments.as_ref(),
            LF_NEW_EXPRESSION_ARGUMENTS,
        );
        self.exit_node(node, state);
    }

    /// `p.emitTemplateLiteral`
    fn emit_template_literal(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::NoSubstitutionTemplateLiteral => self.emit_no_substitution_template_literal(node),
            Kind::TemplateExpression => self.emit_template_expression(node),
            _ => panic!("unhandled TemplateLiteral: {:?}", self.p.nodes[node].kind),
        }
    }

    /// `p.emitTaggedTemplateExpression`
    fn emit_tagged_template_expression(&mut self, node: NodeId) {
        let (tag, question_dot_token, type_arguments, template) = {
            let d = self.p.nodes[node].as_tagged_template_expression();
            (
                d.tag,
                d.question_dot_token,
                d.type_arguments.clone(),
                d.template,
            )
        };
        let _ = question_dot_token;
        let state = self.enter_node(node);
        self.emit_callee(tag, node);
        self.emit_type_arguments(node, type_arguments);
        self.write_space();
        self.emit_template_literal(template.expect("tagged template template"));
        self.exit_node(node, state);
    }

    /// `p.emitTypeAssertionExpression`
    fn emit_type_assertion_expression(&mut self, node: NodeId) {
        let (type_, expression) = {
            let d = self.p.nodes[node].as_type_assertion();
            (d.type_, d.expression)
        };
        let state = self.enter_node(node);
        self.write_punctuation("<");
        self.emit_type_node_outside_extends_opt(type_);
        self.write_punctuation(">");
        self.emit_expression(expression, OperatorPrecedence::UPDATE);
        self.exit_node(node, state);
    }

    /// `p.emitParenthesizedExpression`
    fn emit_parenthesized_expression(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_parenthesized_expression().expression;
        let state = self.enter_node(node);
        let open_paren_pos = self.emit_token(
            Kind::OpenParenToken,
            self.p.nodes[node].pos(),
            WriteKind::Punctuation,
            node,
        );
        let indented = self.write_line_separators_and_indent_before(expression, Some(node));
        self.emit_expression(expression, OperatorPrecedence::COMMA);
        self.write_line_separators_after(expression, Some(node));
        self.decrease_indent_if(indented);
        let close_paren_pos = expression
            .map(|e| self.p.nodes[e].end())
            .unwrap_or(open_paren_pos);
        self.emit_token(
            Kind::CloseParenToken,
            close_paren_pos,
            WriteKind::Punctuation,
            node,
        );
        self.exit_node(node, state);
    }

    /// `p.emitFunctionExpression`
    fn emit_function_expression(&mut self, node: NodeId) {
        let (name, asterisk_token, body) = {
            let d = self.p.nodes[node].as_function_expression();
            (
                d.name,
                d.function_like_with_body_base.body_base.asterisk_token,
                d.function_like_with_body_base.body_base.body,
            )
        };
        let state = self.enter_node(node);
        self.generate_name_if_needed(name);
        let modifiers = self.p.nodes[node].modifiers().cloned();
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        self.write_keyword("function");
        self.emit_token_node(asterisk_token);
        self.write_space();
        self.emit_identifier_name_node(name);
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.emit_function_body_node(body);
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitConciseBody`
    fn emit_concise_body(&mut self, node: NodeId) {
        if ast::is_block(&self.p.nodes[node]) {
            self.emit_function_body(node);
        } else if ast::is_object_literal_expression(
            &self.p.nodes[get_leftmost_expression(node, false, self.p.nodes)],
        ) {
            // Wrap in ParenthesizedExpression to ensure parens are emitted after any leading
            // PartiallyEmittedExpression comments, matching TypeScript's factory-time wrapping
            // via parenthesizeConciseBodyOfArrowFunction.
            let paren = self
                .p
                .emit_context
                .factory
                .new_parenthesized_expression(self.p.nodes, Some(node));
            self.p.nodes[paren].loc = self.p.nodes[node].loc;
            self.emit_expression(Some(paren), OperatorPrecedence::LOWEST);
        } else if ast::is_expression(&self.p.nodes[node], self.p.nodes) {
            self.emit_expression(Some(node), OperatorPrecedence::YIELD);
        } else {
            panic!("unexpected ConciseBody: {:?}", self.p.nodes[node].kind)
        }
    }

    /// `p.emitArrowFunction`
    fn emit_arrow_function(&mut self, node: NodeId) {
        let (type_parameters, parameters, type_, equals_greater_than_token, body) = {
            let d = self.p.nodes[node].as_arrow_function();
            (
                d.function_like_with_body_base
                    .function_like_base
                    .type_parameters
                    .clone(),
                d.function_like_with_body_base
                    .function_like_base
                    .parameters
                    .clone(),
                d.function_like_with_body_base.function_like_base.type_,
                d.equals_greater_than_token,
                d.function_like_with_body_base.body_base.body,
            )
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_type_parameters(node, type_parameters);
        self.emit_parameters_for_arrow(node, parameters.as_ref());
        self.emit_type_annotation(type_);
        self.write_space();
        self.emit_token_node(equals_greater_than_token);
        self.write_space();
        self.emit_concise_body(body.expect("arrow function body"));
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitDeleteExpression`
    fn emit_delete_expression(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_delete_expression().expression;
        let state = self.enter_node(node);
        self.emit_token(
            Kind::DeleteKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_expression(expression, OperatorPrecedence::UNARY);
        self.exit_node(node, state);
    }

    /// `p.emitTypeOfExpression`
    fn emit_type_of_expression(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_type_of_expression().expression;
        let state = self.enter_node(node);
        self.emit_token(
            Kind::TypeOfKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_expression(expression, OperatorPrecedence::UNARY);
        self.exit_node(node, state);
    }

    /// `p.emitVoidExpression`
    fn emit_void_expression(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_void_expression().expression;
        let state = self.enter_node(node);
        self.emit_token(
            Kind::VoidKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_expression(expression, OperatorPrecedence::UNARY);
        self.exit_node(node, state);
    }

    /// `p.emitAwaitExpression`
    fn emit_await_expression(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_await_expression().expression;
        let state = self.enter_node(node);
        self.emit_token(
            Kind::AwaitKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_expression(expression, OperatorPrecedence::UNARY);
        self.exit_node(node, state);
    }

    /// `p.emitPrefixUnaryExpression`
    fn emit_prefix_unary_expression(&mut self, node: NodeId) {
        let (operator, operand) = {
            let d = self.p.nodes[node].as_prefix_unary_expression();
            (d.operator, d.operand)
        };
        let state = self.enter_node(node);
        self.emit_token(
            operator,
            self.p.nodes[node].pos(),
            WriteKind::Operator,
            node,
        );

        // In some cases, we need to emit a space between the operator and the operand. One obvious case
        // is when the operator is an identifier, like delete or typeof. We also need to do this for plus
        // and minus expressions in certain cases. Specifically, consider the following two cases (parens
        // are just for clarity of exposition, and not part of the source code):
        //
        //  (+(+1))
        //  (+(++1))
        //
        // We need to emit a space in both cases. In the first case, the absence of a space will make
        // the resulting expression a prefix increment operation. And in the second, it will make the resulting
        // expression a prefix increment whose operand is a plus expression - (++(+x))
        // The same is true of minus of course.
        if let Some(operand) = operand
            && self.p.nodes[operand].kind == Kind::PrefixUnaryExpression
        {
            let inner = self.p.nodes[operand].as_prefix_unary_expression().operator;
            if (operator == Kind::PlusToken
                && (inner == Kind::PlusToken || inner == Kind::PlusPlusToken))
                || (operator == Kind::MinusToken
                    && (inner == Kind::MinusToken || inner == Kind::MinusMinusToken))
            {
                self.write_space();
            }
        }

        self.emit_expression(operand, OperatorPrecedence::UNARY);
        self.exit_node(node, state);
    }

    /// `p.emitPostfixUnaryExpression`
    fn emit_postfix_unary_expression(&mut self, node: NodeId) {
        let (operand, operator) = {
            let d = self.p.nodes[node].as_postfix_unary_expression();
            (d.operand.expect("postfix operand"), d.operator)
        };
        let state = self.enter_node(node);
        self.emit_expression(Some(operand), OperatorPrecedence::LEFT_HAND_SIDE);
        self.emit_token(
            operator,
            self.p.nodes[operand].end(),
            WriteKind::Operator,
            node,
        );
        self.exit_node(node, state);
    }

    // This function determines whether an expression consists of a homogeneous set of
    // literal expressions or binary plus expressions that all share the same literal kind.
    // It is used to determine whether the right-hand operand of a binary plus expression can be
    // emitted without parentheses.
    /// `p.getLiteralKindOfBinaryPlusOperand`
    fn get_literal_kind_of_binary_plus_operand(&mut self, node: NodeId) -> Kind {
        let node = ast::skip_partially_emitted_expressions(node, self.p.nodes);

        if self.p.nodes[node].kind.is_literal_kind() {
            return self.p.nodes[node].kind;
        }

        if self.p.nodes[node].kind == Kind::BinaryExpression {
            let (left, right, plus) = {
                let n = self.p.nodes[node].as_binary_expression();
                (
                    n.left,
                    n.right,
                    n.operator_token
                        .is_some_and(|t| self.p.nodes[t].kind == Kind::PlusToken),
                )
            };
            if plus {
                // !!! Determine if caching this is worthwhile over recomputing
                let left_kind = self
                    .get_literal_kind_of_binary_plus_operand(left.expect("binary expression left"));
                let mut literal_kind = Kind::Unknown;
                if left_kind.is_literal_kind()
                    && left_kind
                        == self.get_literal_kind_of_binary_plus_operand(
                            right.expect("binary expression right"),
                        )
                {
                    literal_kind = left_kind;
                }
                return literal_kind;
            }
        }

        Kind::Unknown
    }

    /// `p.getBinaryExpressionPrecedence`
    fn get_binary_expression_precedence(
        &mut self,
        node: NodeId,
    ) -> (OperatorPrecedence, OperatorPrecedence) {
        let (left, operator_kind, right) = {
            let d = self.p.nodes[node].as_binary_expression();
            (
                d.left,
                d.operator_token
                    .map(|t| self.p.nodes[t].kind)
                    .unwrap_or_default(),
                d.right,
            )
        };
        let precedence = get_expression_precedence(&self.p.nodes[node], self.p.nodes);
        let mut left_prec = precedence;
        let mut right_prec = precedence;
        match precedence {
            OperatorPrecedence::COMMA => {
                // No need to parenthesize the right operand when the binary operator and
                // operand are both ,:
                //  x,(a,b)     => x,a,b
            }
            OperatorPrecedence::ASSIGNMENT => {
                // assignment is right-associative
                left_prec = OperatorPrecedence::CONDITIONAL;
                right_prec = OperatorPrecedence::YIELD;
            }
            OperatorPrecedence::LOGICAL_OR => {
                right_prec = OperatorPrecedence::LOGICAL_AND;
            }
            OperatorPrecedence::LOGICAL_AND => {
                right_prec = OperatorPrecedence::BITWISE_OR;
            }
            OperatorPrecedence::BITWISE_OR => {
                // No need to parenthesize the right operand when the binary operator and
                // operand are both | due to the associative property of mathematics:
                //  x|(a|b)     => x|a|b
            }
            OperatorPrecedence::BITWISE_XOR => {
                // No need to parenthesize the right operand when the binary operator and
                // operand are both ^ due to the associative property of mathematics:
                //  x^(a^b)     => x^a^b
            }
            OperatorPrecedence::BITWISE_AND => {
                // No need to parenthesize the right operand when the binary operator and
                // operand are both & due to the associative property of mathematics:
                //  x&(a&b)     => x&a&b
            }
            OperatorPrecedence::EQUALITY => {
                right_prec = OperatorPrecedence::RELATIONAL;
            }
            OperatorPrecedence::RELATIONAL => {
                right_prec = OperatorPrecedence::SHIFT;
            }
            OperatorPrecedence::SHIFT => {
                right_prec = OperatorPrecedence::ADDITIVE;
            }
            OperatorPrecedence::ADDITIVE => {
                if operator_kind == Kind::PlusToken
                    && util::is_binary_operation(
                        self.p.nodes,
                        right.expect("binary expression right"),
                        Kind::PlusToken,
                    )
                {
                    let left_kind =
                        self.get_literal_kind_of_binary_plus_operand(left.expect("binary left"));
                    if left_kind.is_literal_kind()
                        && left_kind
                            == self.get_literal_kind_of_binary_plus_operand(
                                right.expect("binary right"),
                            )
                    {
                        // No need to parenthesize the right operand when the binary operator
                        // is plus (+) if both the left and right operands consist solely of either
                        // literals of the same kind or binary plus (+) expressions for literals of
                        // the same kind (recursively).
                        //  "a"+(1+2)       => "a"+(1+2)
                        //  "a"+("b"+"c")   => "a"+"b"+"c"
                        return (left_prec, right_prec);
                    }
                }
                right_prec = OperatorPrecedence::MULTIPLICATIVE;
            }
            OperatorPrecedence::MULTIPLICATIVE => {
                if operator_kind == Kind::AsteriskToken
                    && util::is_binary_operation(
                        self.p.nodes,
                        right.expect("binary expression right"),
                        Kind::AsteriskToken,
                    )
                {
                    // No need to parenthesize the right operand when the binary operator and
                    // operand are both * due to the associative property of mathematics:
                    //  x*(a*b)     => x*a*b
                    return (left_prec, right_prec);
                }
                right_prec = OperatorPrecedence::EXPONENTIATION;
            }
            OperatorPrecedence::EXPONENTIATION => {
                // exponentiation is right-associative
                left_prec = OperatorPrecedence::UPDATE;
            }
            _ => panic!("unhandled precedence: {:?}", precedence),
        }
        (left_prec, right_prec)
    }

    /// `p.emitBinaryExpression`
    fn emit_binary_expression(&mut self, node: NodeId) {
        let (mut left_prec, mut right_prec) = self.get_binary_expression_precedence(node);
        let (left, operator_token, right) = {
            let d = self.p.nodes[node].as_binary_expression();
            (d.left, d.operator_token, d.right)
        };
        let operator_kind = operator_token
            .map(|t| self.p.nodes[t].kind)
            .unwrap_or_default();
        let emitted_left =
            ast::skip_partially_emitted_expressions(left.expect("binary left"), self.p.nodes);
        if ast::node_is_synthesized(&self.p.nodes[emitted_left])
            && self.p.nodes[emitted_left].kind == Kind::BinaryExpression
            && util::mixing_binary_operators_requires_parentheses(
                operator_kind,
                self.p.nodes[emitted_left]
                    .as_binary_expression()
                    .operator_token
                    .map(|t| self.p.nodes[t].kind)
                    .unwrap_or_default(),
            )
        {
            left_prec = OperatorPrecedence::HIGHEST;
        }
        let emitted_right =
            ast::skip_partially_emitted_expressions(right.expect("binary right"), self.p.nodes);
        if ast::node_is_synthesized(&self.p.nodes[emitted_right])
            && self.p.nodes[emitted_right].kind == Kind::BinaryExpression
            && util::mixing_binary_operators_requires_parentheses(
                operator_kind,
                self.p.nodes[emitted_right]
                    .as_binary_expression()
                    .operator_token
                    .map(|t| self.p.nodes[t].kind)
                    .unwrap_or_default(),
            )
        {
            right_prec = OperatorPrecedence::HIGHEST;
        }
        let state = self.enter_node(node);
        self.emit_expression(left, left_prec);
        let lines_before_operator = self.get_lines_between_nodes(Some(node), left, operator_token);
        let lines_after_operator = self.get_lines_between_nodes(Some(node), operator_token, right);
        self.write_lines_and_indent(
            lines_before_operator,
            operator_kind != Kind::CommaToken, /*writeSpaceIfNotIndenting*/
        );
        self.emit_token_node_ex(operator_token, TEF_NO_SOURCE_MAPS);
        // Binary operators should have a space before the comment starts
        self.write_lines_and_indent(lines_after_operator, true /*writeSpaceIfNotIndenting*/);
        self.emit_expression(right, right_prec);
        self.decrease_indent_if(lines_after_operator > 0);
        self.decrease_indent_if(lines_before_operator > 0);
        self.exit_node(node, state);
    }

    /// `p.emitShortCircuitExpression`
    fn emit_short_circuit_expression(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        if util::is_binary_operation(
            self.p.nodes,
            ast::skip_partially_emitted_expressions(node, self.p.nodes),
            Kind::QuestionQuestionToken,
        ) {
            self.emit_expression(Some(node), OperatorPrecedence::COALESCE);
        } else {
            self.emit_expression(Some(node), OperatorPrecedence::LOGICAL_OR);
        }
    }

    /// `p.emitConditionalExpression`
    fn emit_conditional_expression(&mut self, node: NodeId) {
        let (condition, question_token, when_true, colon_token, when_false) = {
            let d = self.p.nodes[node].as_conditional_expression();
            (
                d.condition,
                d.question_token,
                d.when_true,
                d.colon_token,
                d.when_false,
            )
        };
        let state = self.enter_node(node);
        let lines_before_question =
            self.get_lines_between_nodes(Some(node), condition, question_token);
        let lines_after_question =
            self.get_lines_between_nodes(Some(node), question_token, when_true);
        let lines_before_colon = self.get_lines_between_nodes(Some(node), when_true, colon_token);
        let lines_after_colon = self.get_lines_between_nodes(Some(node), colon_token, when_false);
        self.emit_short_circuit_expression(condition);
        self.write_lines_and_indent(lines_before_question, true);
        self.emit_punctuation_node_opt(question_token);
        self.write_lines_and_indent(lines_after_question, true);
        self.emit_expression(when_true, OperatorPrecedence::YIELD);
        self.decrease_indent_if(lines_after_question > 0);
        self.decrease_indent_if(lines_before_question > 0);
        self.write_lines_and_indent(lines_before_colon, true);
        self.emit_punctuation_node_opt(colon_token);
        self.write_lines_and_indent(lines_after_colon, true);
        self.emit_expression(when_false, OperatorPrecedence::YIELD);
        self.decrease_indent_if(lines_after_colon > 0);
        self.decrease_indent_if(lines_before_colon > 0);
        self.exit_node(node, state);
    }

    /// `p.emitTemplateExpression`
    fn emit_template_expression(&mut self, node: NodeId) {
        let (head, template_spans) = {
            let d = self.p.nodes[node].as_template_expression();
            (d.head, d.template_spans.clone())
        };
        let state = self.enter_node(node);
        self.emit_template_head(head.expect("template expression head"));
        self.emit_list(
            Self::emit_template_span_node,
            Some(node),
            template_spans.as_ref(),
            LF_TEMPLATE_EXPRESSION_SPANS,
        );
        self.exit_node(node, state);
    }

    /// `p.emitYieldExpression`
    fn emit_yield_expression(&mut self, node: NodeId) {
        let (asterisk_token, expression) = {
            let d = self.p.nodes[node].as_yield_expression();
            (d.asterisk_token, d.expression)
        };
        let state = self.enter_node(node);
        self.emit_token(
            Kind::YieldKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.emit_punctuation_node_opt(asterisk_token);
        if let Some(expression) = expression {
            self.write_space();
            self.emit_expression_no_asi(expression, OperatorPrecedence::DISALLOW_COMMA);
        }
        self.exit_node(node, state);
    }

    /// `p.emitSpreadElement`
    fn emit_spread_element(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_spread_element().expression;
        let state = self.enter_node(node);
        self.emit_token(
            Kind::DotDotDotToken,
            self.p.nodes[node].pos(),
            WriteKind::Punctuation,
            node,
        );
        self.emit_expression(expression, OperatorPrecedence::DISALLOW_COMMA);
        self.exit_node(node, state);
    }

    /// `p.emitClassExpression`
    fn emit_class_expression(&mut self, node: NodeId) {
        let (name, type_parameters, heritage_clauses, members) = {
            let d = self.p.nodes[node].as_class_expression();
            (
                d.class_like_base.name,
                d.class_like_base.type_parameters.clone(),
                d.class_like_base.heritage_clauses.clone(),
                d.class_like_base.members.clone(),
            )
        };
        let state = self.enter_node(node);
        self.generate_name_if_needed(name);

        let modifiers = self.p.nodes[node].modifiers().cloned();
        let pos = self.emit_modifier_list(node, modifiers.as_ref(), true /*allowDecorators*/);
        self.emit_token(Kind::ClassKeyword, pos, WriteKind::Keyword, node);

        if name.is_some() {
            self.write_space();
            self.emit_identifier_name(name.unwrap());
        }

        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);

        self.emit_type_parameters(node, type_parameters);
        self.emit_list(
            Self::emit_heritage_clause_node,
            Some(node),
            heritage_clauses.as_ref(),
            LF_CLASS_HERITAGE_CLAUSES,
        );
        self.write_space();
        self.write_punctuation("{");
        self.push_name_generation_scope(node);
        self.generate_all_member_names(members.as_ref());
        self.emit_list(
            Self::emit_class_element,
            Some(node),
            members.as_ref(),
            LF_CLASS_MEMBERS,
        );
        self.pop_name_generation_scope(node);
        self.write_punctuation("}");

        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitOmittedExpression`
    fn emit_omitted_expression(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.exit_node(node, state);
    }

    /// `p.emitExpressionWithTypeArguments`
    fn emit_expression_with_type_arguments(&mut self, node: NodeId) {
        let (expression, type_arguments) = {
            let d = self.p.nodes[node].as_expression_with_type_arguments();
            (d.expression.unwrap_or_default(), d.type_arguments.clone())
        };
        let state = self.enter_node(node);
        self.emit_expression(Some(expression), OperatorPrecedence::MEMBER);
        self.emit_type_arguments(node, type_arguments);
        self.exit_node(node, state);
    }

    /// `p.emitAsExpression`
    fn emit_as_expression(&mut self, node: NodeId) {
        let (expression, type_) = {
            let d = self.p.nodes[node].as_as_expression();
            (d.expression, d.type_)
        };
        let state = self.enter_node(node);
        self.emit_expression(expression, OperatorPrecedence::RELATIONAL);
        self.write_space();
        self.write_keyword("as");
        self.write_space();
        self.emit_type_node_outside_extends_opt(type_);
        self.exit_node(node, state);
    }

    /// `p.emitSatisfiesExpression`
    fn emit_satisfies_expression(&mut self, node: NodeId) {
        let (expression, type_) = {
            let d = self.p.nodes[node].as_satisfies_expression();
            (d.expression, d.type_)
        };
        let state = self.enter_node(node);
        self.emit_expression(expression, OperatorPrecedence::RELATIONAL);
        self.write_space();
        self.write_keyword("satisfies");
        self.write_space();
        self.emit_type_node_outside_extends_opt(type_);
        self.exit_node(node, state);
    }

    /// `p.emitNonNullExpression`
    fn emit_non_null_expression(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_non_null_expression().expression;
        let state = self.enter_node(node);
        self.emit_expression(expression, OperatorPrecedence::MEMBER);
        self.write_operator("!");
        self.exit_node(node, state);
    }

    /// `p.emitMetaProperty`
    fn emit_meta_property(&mut self, node: NodeId) {
        let (keyword_token, name) = {
            let d = self.p.nodes[node].as_meta_property();
            (d.keyword_token, d.name)
        };
        let state = self.enter_node(node);
        let pos = self.emit_token(
            keyword_token,
            self.p.nodes[node].pos(),
            WriteKind::Punctuation,
            node,
        );
        self.emit_token(Kind::DotToken, pos, WriteKind::Punctuation, node);
        self.emit_identifier_name(name.expect("meta property name"));
        self.exit_node(node, state);
    }

    /// `p.emitPartiallyEmittedExpression`
    fn emit_partially_emitted_expression(&mut self, mut node: NodeId) {
        // avoid reprinting parens for nested partially emitted expressions
        let mut stack: Vec<(NodeId, PrinterState)> = Vec::new();
        loop {
            let state = self.enter_node(node);
            let expression = self.p.nodes[node]
                .as_partially_emitted_expression()
                .expression
                .expect("partially emitted expression");
            let emit_flags = self.p.emit_context.emit_flags(node);
            if !emit_flags.has(EmitFlags::NO_LEADING_COMMENTS)
                && self.p.nodes[node].pos() != self.p.nodes[expression].pos()
            {
                self.emit_trailing_comments_of_position(
                    self.p.nodes[expression].pos(),
                    false, /*prefixSpace*/
                    false, /*forceNoNewline*/
                );
            }
            stack.push((node, state));
            if !ast::is_partially_emitted_expression(&self.p.nodes[expression]) {
                break;
            }
            node = expression;
        }

        let innermost = self.p.nodes[node]
            .as_partially_emitted_expression()
            .expression
            .expect("partially emitted expression");
        self.emit_expression(Some(innermost), OperatorPrecedence::LOWEST);

        // unwind stack
        while let Some((entry_node, entry_state)) = stack.pop() {
            let expression = self.p.nodes[node]
                .as_partially_emitted_expression()
                .expression
                .expect("partially emitted expression");
            let emit_flags = self.p.emit_context.emit_flags(node);
            if !emit_flags.has(EmitFlags::NO_TRAILING_COMMENTS)
                && self.p.nodes[node].end() != self.p.nodes[expression].end()
            {
                self.emit_leading_comments_of_position(self.p.nodes[expression].end());
            }
            self.exit_node(node, entry_state);
            node = entry_node;
        }
    }

    /// `p.commentWillEmitNewLine`
    fn comment_will_emit_new_line(comment: &CommentRange) -> bool {
        comment.kind == Kind::SingleLineCommentTrivia || comment.has_trailing_new_line
    }

    /// `p.syntheticCommentWillEmitNewLine`
    fn synthetic_comment_will_emit_new_line(comment: &SynthesizedComment) -> bool {
        comment.kind == Kind::SingleLineCommentTrivia || comment.has_trailing_new_line
    }

    /// `p.willEmitLeadingNewLine`
    fn will_emit_leading_new_line(&mut self, node: NodeId) -> bool {
        let Some(source_file) = self.p.current_source_file else {
            return false;
        };
        let mut has_leading_comment_ranges = false;
        let mut has_new_line_comment = false;
        for comment in scanner::get_leading_comment_ranges(
            &self.p.emit_context.factory.inner,
            self.p.nodes[source_file].as_source_file().text(),
            self.p.nodes[node].pos(),
        ) {
            has_leading_comment_ranges = true;
            if Self::comment_will_emit_new_line(&comment) {
                has_new_line_comment = true;
            }
        }
        if has_leading_comment_ranges {
            if let Some(parse_node) = self.p.emit_context.parse_node(self.p.nodes, node)
                && self.p.nodes[parse_node]
                    .parent
                    .is_some_and(|p| ast::is_parenthesized_expression(&self.p.nodes[p]))
            {
                return true;
            }
        }
        if has_new_line_comment {
            return true;
        }
        if self
            .p
            .emit_context
            .get_synthetic_leading_comments(node)
            .iter()
            .any(Self::synthetic_comment_will_emit_new_line)
        {
            return true;
        }
        if ast::is_partially_emitted_expression(&self.p.nodes[node]) {
            let expression = self.p.nodes[node]
                .as_partially_emitted_expression()
                .expression
                .expect("partially emitted expression");
            if self.p.nodes[node].pos() != self.p.nodes[expression].pos() {
                for comment in scanner::get_trailing_comment_ranges(
                    &self.p.emit_context.factory.inner,
                    self.p.nodes[source_file].as_source_file().text(),
                    self.p.nodes[expression].pos(),
                ) {
                    if Self::comment_will_emit_new_line(&comment) {
                        return true;
                    }
                }
            }
            return self.will_emit_leading_new_line(expression);
        }
        false
    }

    // parenthesizeExpressionForNoAsi wraps an expression in parens if we would emit a leading comment
    // that would introduce a line separator between the node and its parent.
    /// `p.parenthesizeExpressionForNoAsi`
    fn parenthesize_expression_for_no_asi(&mut self, node: NodeId) -> NodeId {
        if !self.comments_disabled {
            match self.p.nodes[node].kind {
                Kind::PartiallyEmittedExpression => {
                    if self.will_emit_leading_new_line(node) {
                        let expression = self.p.nodes[node]
                            .as_partially_emitted_expression()
                            .expression
                            .unwrap_or_default();
                        let parse_node = self.p.emit_context.parse_node(self.p.nodes, node);
                        if let Some(parse_node) = parse_node
                            && ast::is_parenthesized_expression(&self.p.nodes[parse_node])
                        {
                            // If the original node was a parenthesized expression, restore it to preserve comment and source map emit
                            let parens = self
                                .p
                                .emit_context
                                .factory
                                .new_parenthesized_expression(self.p.nodes, Some(expression));
                            self.p.emit_context.set_original(parens, node);
                            self.p.nodes[parens].loc = self.p.nodes[parse_node].loc;
                            return parens;
                        }
                        return self
                            .p
                            .emit_context
                            .factory
                            .new_parenthesized_expression(self.p.nodes, Some(node));
                    }
                    let expression = self.p.nodes[node]
                        .as_partially_emitted_expression()
                        .expression
                        .unwrap_or_default();
                    let new_expression = self.parenthesize_expression_for_no_asi(expression);
                    return self
                        .p
                        .emit_context
                        .factory
                        .update_partially_emitted_expression(
                            self.p.nodes,
                            node,
                            Some(new_expression),
                        )
                        .unwrap_or(node);
                }
                Kind::PropertyAccessExpression => {
                    let (expression, question_dot_token, name) = {
                        let d = self.p.nodes[node].as_property_access_expression();
                        (d.expression, d.question_dot_token, d.name)
                    };
                    let flags = self.p.nodes[node].flags;
                    let new_expression =
                        self.parenthesize_expression_for_no_asi(expression.unwrap_or_default());
                    return self
                        .p
                        .emit_context
                        .factory
                        .update_property_access_expression(
                            self.p.nodes,
                            node,
                            Some(new_expression),
                            question_dot_token,
                            name,
                            flags,
                        )
                        .unwrap_or(node);
                }
                Kind::ElementAccessExpression => {
                    let (expression, question_dot_token, argument_expression) = {
                        let d = self.p.nodes[node].as_element_access_expression();
                        (d.expression, d.question_dot_token, d.argument_expression)
                    };
                    let flags = self.p.nodes[node].flags;
                    let new_expression =
                        self.parenthesize_expression_for_no_asi(expression.unwrap_or_default());
                    return self
                        .p
                        .emit_context
                        .factory
                        .update_element_access_expression(
                            self.p.nodes,
                            node,
                            Some(new_expression),
                            question_dot_token,
                            argument_expression,
                            flags,
                        )
                        .unwrap_or(node);
                }
                Kind::CallExpression => {
                    let (expression, question_dot_token, type_arguments, arguments) = {
                        let d = self.p.nodes[node].as_call_expression();
                        (
                            d.expression,
                            d.question_dot_token,
                            d.type_arguments.clone(),
                            d.arguments.clone(),
                        )
                    };
                    let flags = self.p.nodes[node].flags;
                    let new_expression =
                        self.parenthesize_expression_for_no_asi(expression.unwrap_or_default());
                    return self
                        .p
                        .emit_context
                        .factory
                        .update_call_expression(
                            self.p.nodes,
                            node,
                            Some(new_expression),
                            question_dot_token,
                            type_arguments,
                            arguments,
                            flags,
                        )
                        .unwrap_or(node);
                }
                Kind::TaggedTemplateExpression => {
                    let (tag, question_dot_token, type_arguments, template) = {
                        let d = self.p.nodes[node].as_tagged_template_expression();
                        (
                            d.tag,
                            d.question_dot_token,
                            d.type_arguments.clone(),
                            d.template,
                        )
                    };
                    let flags = self.p.nodes[node].flags;
                    let new_tag = self.parenthesize_expression_for_no_asi(tag.unwrap_or_default());
                    return self
                        .p
                        .emit_context
                        .factory
                        .update_tagged_template_expression(
                            self.p.nodes,
                            node,
                            Some(new_tag),
                            question_dot_token,
                            type_arguments,
                            template,
                            flags,
                        )
                        .unwrap_or(node);
                }
                Kind::PostfixUnaryExpression => {
                    let (operand, operator) = {
                        let d = self.p.nodes[node].as_postfix_unary_expression();
                        (d.operand, d.operator)
                    };
                    let new_operand =
                        self.parenthesize_expression_for_no_asi(operand.unwrap_or_default());
                    return self
                        .p
                        .emit_context
                        .factory
                        .update_postfix_unary_expression(
                            self.p.nodes,
                            node,
                            Some(new_operand),
                            operator,
                        )
                        .unwrap_or(node);
                }
                Kind::BinaryExpression => {
                    let (modifiers, left, type_, operator_token, right) = {
                        let d = self.p.nodes[node].as_binary_expression();
                        (
                            d.modifiers_base.modifiers.clone(),
                            d.left,
                            d.type_,
                            d.operator_token,
                            d.right,
                        )
                    };
                    let new_left =
                        self.parenthesize_expression_for_no_asi(left.unwrap_or_default());
                    return self
                        .p
                        .emit_context
                        .factory
                        .update_binary_expression(
                            self.p.nodes,
                            node,
                            modifiers,
                            Some(new_left),
                            type_,
                            operator_token,
                            right,
                        )
                        .unwrap_or(node);
                }
                Kind::ConditionalExpression => {
                    let (condition, question_token, when_true, colon_token, when_false) = {
                        let d = self.p.nodes[node].as_conditional_expression();
                        (
                            d.condition,
                            d.question_token,
                            d.when_true,
                            d.colon_token,
                            d.when_false,
                        )
                    };
                    let new_condition =
                        self.parenthesize_expression_for_no_asi(condition.unwrap_or_default());
                    return self
                        .p
                        .emit_context
                        .factory
                        .update_conditional_expression(
                            self.p.nodes,
                            node,
                            Some(new_condition),
                            question_token,
                            when_true,
                            colon_token,
                            when_false,
                        )
                        .unwrap_or(node);
                }
                Kind::AsExpression => {
                    let (expression, type_) = {
                        let d = self.p.nodes[node].as_as_expression();
                        (d.expression, d.type_)
                    };
                    let new_expression =
                        self.parenthesize_expression_for_no_asi(expression.unwrap_or_default());
                    return self
                        .p
                        .emit_context
                        .factory
                        .update_as_expression(self.p.nodes, node, Some(new_expression), type_)
                        .unwrap_or(node);
                }
                Kind::SatisfiesExpression => {
                    let (expression, type_) = {
                        let d = self.p.nodes[node].as_satisfies_expression();
                        (d.expression, d.type_)
                    };
                    let new_expression =
                        self.parenthesize_expression_for_no_asi(expression.unwrap_or_default());
                    return self
                        .p
                        .emit_context
                        .factory
                        .update_satisfies_expression(
                            self.p.nodes,
                            node,
                            Some(new_expression),
                            type_,
                        )
                        .unwrap_or(node);
                }
                Kind::NonNullExpression => {
                    let expression = self.p.nodes[node].as_non_null_expression().expression;
                    let flags = self.p.nodes[node].flags;
                    let new_expression =
                        self.parenthesize_expression_for_no_asi(expression.unwrap_or_default());
                    return self
                        .p
                        .emit_context
                        .factory
                        .update_non_null_expression(self.p.nodes, node, Some(new_expression), flags)
                        .unwrap_or(node);
                }
                _ => {}
            }
        }
        node
    }

    /// `p.emitExpressionNoASI`
    fn emit_expression_no_asi(&mut self, node: NodeId, precedence: OperatorPrecedence) {
        let node = self.parenthesize_expression_for_no_asi(node);
        self.emit_expression(Some(node), precedence);
    }

    /// `p.emitExpression`
    fn emit_expression(&mut self, node: Option<NodeId>, precedence: OperatorPrecedence) {
        let Some(node) = node else {
            return;
        };
        let parens = get_expression_precedence(
            &self.p.nodes[ast::skip_partially_emitted_expressions(node, self.p.nodes)],
            self.p.nodes,
        ) < precedence;
        if parens {
            self.write_punctuation("(");
        }

        match self.p.nodes[node].kind {
            // Keywords
            Kind::TrueKeyword | Kind::FalseKeyword | Kind::NullKeyword => {
                self.emit_token_node(Some(node))
            }
            Kind::ThisKeyword | Kind::SuperKeyword | Kind::ImportKeyword => {
                self.emit_keyword_expression(node)
            }

            // Literals
            Kind::NumericLiteral => self.emit_numeric_literal(node),
            Kind::BigIntLiteral => self.emit_big_int_literal(node),
            Kind::StringLiteral => self.emit_string_literal(node),
            Kind::RegularExpressionLiteral => self.emit_regular_expression_literal(node),
            Kind::NoSubstitutionTemplateLiteral => self.emit_no_substitution_template_literal(node),

            // Identifiers
            Kind::Identifier => self.emit_identifier_reference(node),
            Kind::PrivateIdentifier => self.emit_private_identifier(node),

            // Expressions
            Kind::ArrayLiteralExpression => self.emit_array_literal_expression(node),
            Kind::ObjectLiteralExpression => self.emit_object_literal_expression(node),
            Kind::PropertyAccessExpression => self.emit_property_access_expression(node),
            Kind::ElementAccessExpression => self.emit_element_access_expression(node),
            Kind::CallExpression => self.emit_call_expression(node),
            Kind::NewExpression => self.emit_new_expression(node),
            Kind::TaggedTemplateExpression => self.emit_tagged_template_expression(node),
            Kind::TypeAssertionExpression => self.emit_type_assertion_expression(node),
            Kind::ParenthesizedExpression => self.emit_parenthesized_expression(node),
            Kind::FunctionExpression => self.emit_function_expression(node),
            Kind::ArrowFunction => self.emit_arrow_function(node),
            Kind::DeleteExpression => self.emit_delete_expression(node),
            Kind::TypeOfExpression => self.emit_type_of_expression(node),
            Kind::VoidExpression => self.emit_void_expression(node),
            Kind::AwaitExpression => self.emit_await_expression(node),
            Kind::PrefixUnaryExpression => self.emit_prefix_unary_expression(node),
            Kind::PostfixUnaryExpression => self.emit_postfix_unary_expression(node),
            Kind::BinaryExpression => self.emit_binary_expression(node),
            Kind::ConditionalExpression => self.emit_conditional_expression(node),
            Kind::TemplateExpression => self.emit_template_expression(node),
            Kind::YieldExpression => self.emit_yield_expression(node),
            Kind::SpreadElement => self.emit_spread_element(node),
            Kind::ClassExpression => self.emit_class_expression(node),
            Kind::OmittedExpression => self.emit_omitted_expression(node),
            Kind::AsExpression => self.emit_as_expression(node),
            Kind::NonNullExpression => self.emit_non_null_expression(node),
            Kind::ExpressionWithTypeArguments => self.emit_expression_with_type_arguments(node),
            Kind::SatisfiesExpression => self.emit_satisfies_expression(node),
            Kind::MetaProperty => self.emit_meta_property(node),
            Kind::SyntheticExpression => {
                panic!("SyntheticExpression should never be printed.")
            }
            Kind::MissingDeclaration => {
                // Missing declarations do not emit an expression.
            }

            // JSX
            Kind::JsxElement => self.emit_jsx_element(node),
            Kind::JsxSelfClosingElement => self.emit_jsx_self_closing_element(node),
            Kind::JsxFragment => self.emit_jsx_fragment(node),

            // Synthesized list
            Kind::SyntaxList => panic!("SyntaxList should not be printed"),

            // Transformation nodes
            Kind::NotEmittedStatement => return,
            Kind::PartiallyEmittedExpression => self.emit_partially_emitted_expression(node),
            Kind::SyntheticReferenceExpression => {
                panic!("SyntheticReferenceExpression should not be printed")
            }

            _ => panic!("unexpected Expression: {:?}", self.p.nodes[node].kind),
        }

        if parens {
            self.write_punctuation(")");
        }
    }

    //
    // Misc
    //

    /// `p.emitTemplateSpan`
    fn emit_template_span(&mut self, node: NodeId) {
        let (expression, literal) = {
            let d = self.p.nodes[node].as_template_span();
            (d.expression, d.literal)
        };
        let state = self.enter_node(node);
        self.emit_expression(expression, OperatorPrecedence::COMMA);
        self.emit_template_middle_tail(literal.expect("template span literal"));
        self.exit_node(node, state);
    }

    /// `p.emitTemplateSpanNode`
    fn emit_template_span_node(&mut self, node: NodeId) {
        self.emit_template_span(node)
    }

    /// `p.emitSemicolonClassElement`
    fn emit_semicolon_class_element(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    //
    // Statements
    //

    /// `p.isEmptyBlock`
    fn is_empty_block(&mut self, block: NodeId, statements: Option<&NodeList>) -> bool {
        statements.is_none_or(|s| s.nodes.is_empty())
            && (self.p.current_source_file.is_none()
                || util::range_end_is_on_same_line_as_range_start(
                    self.p.nodes[block].loc,
                    self.p.nodes[block].loc,
                    self.p.nodes[self.p.current_source_file.unwrap()].as_source_file(),
                ))
    }

    /// `p.emitBlock`
    fn emit_block(&mut self, node: NodeId) {
        let (statements, multi_line) = {
            let d = self.p.nodes[node].as_block();
            (d.statements.clone(), d.multi_line)
        };
        let state = self.enter_node(node);
        self.generate_names(Some(node));
        self.emit_token(
            Kind::OpenBraceToken,
            self.p.nodes[node].pos(),
            WriteKind::Punctuation,
            node,
        );

        let format = if (!multi_line && self.is_empty_block(node, statements.as_ref()))
            || self.should_emit_on_single_line(Some(node))
        {
            LF_SINGLE_LINE_BLOCK_STATEMENTS
        } else {
            LF_MULTI_LINE_BLOCK_STATEMENTS
        };
        self.emit_list(
            Self::emit_statement,
            Some(node),
            statements.as_ref(),
            format,
        );

        self.emit_token_ex(
            Kind::CloseBraceToken,
            statements.map(|s| s.loc.end()).unwrap_or_default(),
            WriteKind::Punctuation,
            node,
            if format & LF_MULTI_LINE != 0 {
                TEF_INDENT_LEADING_COMMENTS
            } else {
                TEF_NONE
            },
        );
        self.exit_node(node, state);
    }

    /// `p.emitVariableStatement`
    fn emit_variable_statement(&mut self, node: NodeId) {
        let declaration_list = self.p.nodes[node].as_variable_statement().declaration_list;
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        self.emit_variable_declaration_list(declaration_list.expect("variable declaration list"));
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitEmptyStatement`
    fn emit_empty_statement(&mut self, node: NodeId, is_embedded_statement: bool) {
        let state = self.enter_node(node);

        // While most trailing semicolons are possibly insignificant, an embedded "empty"
        // statement is significant and cannot be elided by a trailing-semicolon-omitting writer.
        if is_embedded_statement {
            self.write_punctuation(";");
        } else {
            self.write_trailing_semicolon();
        }
        self.exit_node(node, state);
    }

    /// `p.emitExpressionStatement`
    fn emit_expression_statement(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_expression_statement().expression;
        let state = self.enter_node(node);

        if self
            .p
            .current_source_file
            .is_some_and(|sf| self.p.nodes[sf].as_source_file().script_kind == ScriptKind::Json)
        {
            // !!! In strada, this was handled by an undefined parenthesizerRule, so this is a hack.
            self.emit_expression(expression, OperatorPrecedence::COMMA);
        } else if util::is_immediately_invoked_function_expression_or_arrow_function(
            self.p.nodes,
            expression.expect("expression statement"),
        ) {
            // For IIFEs, parenthesize just the callee (not the whole call), matching TypeScript's
            // parenthesizeExpressionOfExpressionStatement which wraps the function/arrow in parens:
            //   (function() { })()  -- not (function() { }())
            self.emit_iife_with_parenthesized_callee(expression.unwrap());
        } else {
            match self.p.nodes
                [get_leftmost_expression(expression.unwrap_or_default(), false, self.p.nodes)]
            .kind
            {
                Kind::FunctionExpression | Kind::ObjectLiteralExpression => {
                    self.emit_expression(expression, OperatorPrecedence::PARENTHESES)
                }
                _ => self.emit_expression(expression, OperatorPrecedence::COMMA),
            }
        }

        // Emit semicolon in non json files
        // or if json file that created synthesized expression(eg.define expression statement when --out and amd code generation)
        if self.p.current_source_file.is_none()
            || self.p.nodes[self.p.current_source_file.unwrap()]
                .as_source_file()
                .script_kind
                != ScriptKind::Json
            || expression.is_some_and(|e| ast::node_is_synthesized(&self.p.nodes[e]))
        {
            self.write_trailing_semicolon();
        }

        self.exit_node(node, state);
    }

    // emitIIFEWithParenthesizedCallee emits a call expression that is an IIFE,
    // wrapping just the callee in parens rather than the entire call expression.
    // This matches TypeScript's parenthesizeExpressionOfExpressionStatement behavior:
    //
    //	(function() { })()   -- parens around callee only
    //
    // instead of:
    //
    //	(function() { }())   -- parens around entire call
    /// `p.emitIIFEWithParenthesizedCallee`
    fn emit_iife_with_parenthesized_callee(&mut self, node: NodeId) {
        // Walk through PartiallyEmittedExpression wrappers to find the call
        let call = ast::skip_partially_emitted_expressions(node, self.p.nodes);
        let (expression, question_dot_token, type_arguments, arguments) = {
            let d = self.p.nodes[call].as_call_expression();
            (
                d.expression,
                d.question_dot_token,
                d.type_arguments.clone(),
                d.arguments.clone(),
            )
        };
        let state = self.enter_node(call);
        // Emit the callee wrapped in parens
        self.write_punctuation("(");
        self.emit_expression(expression, OperatorPrecedence::LOWEST);
        self.write_punctuation(")");
        self.emit_token_node(question_dot_token);
        self.emit_type_arguments(call, type_arguments);
        self.emit_list(
            Self::emit_argument,
            Some(call),
            arguments.as_ref(),
            LF_CALL_EXPRESSION_ARGUMENTS,
        );
        self.exit_node(call, state);
    }

    /// `p.emitIfStatement`
    fn emit_if_statement(&mut self, node: NodeId) {
        let (expression, then_statement, else_statement) = {
            let d = self.p.nodes[node].as_if_statement();
            (d.expression, d.then_statement, d.else_statement)
        };
        let state = self.enter_node(node);
        let pos = self.emit_token(
            Kind::IfKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_token(Kind::OpenParenToken, pos, WriteKind::Punctuation, node);
        self.emit_expression(expression, OperatorPrecedence::LOWEST);
        self.emit_token(
            Kind::CloseParenToken,
            expression
                .map(|e| self.p.nodes[e].end())
                .unwrap_or_default(),
            WriteKind::Punctuation,
            node,
        );
        self.emit_embedded_statement(node, then_statement.expect("then statement"));
        if let Some(else_statement) = else_statement {
            self.write_line_or_space(Some(node), then_statement, Some(else_statement));
            self.emit_token(
                Kind::ElseKeyword,
                then_statement
                    .map(|t| self.p.nodes[t].end())
                    .unwrap_or_default(),
                WriteKind::Keyword,
                node,
            );
            if self.p.nodes[else_statement].kind == Kind::IfStatement {
                self.write_space();
                self.emit_if_statement(else_statement);
            } else {
                self.emit_embedded_statement(node, else_statement);
            }
        }
        self.exit_node(node, state);
    }

    /// `p.emitWhileClause`
    fn emit_while_clause(&mut self, node: NodeId, expression: Option<NodeId>, start_pos: i32) {
        let pos = self.emit_token(Kind::WhileKeyword, start_pos, WriteKind::Keyword, node);
        self.write_space();
        self.emit_token(Kind::OpenParenToken, pos, WriteKind::Punctuation, node);
        self.emit_expression(expression, OperatorPrecedence::LOWEST);
        self.emit_token(
            Kind::CloseParenToken,
            expression
                .map(|e| self.p.nodes[e].end())
                .unwrap_or_default(),
            WriteKind::Punctuation,
            node,
        );
    }

    /// `p.emitDoStatement`
    fn emit_do_statement(&mut self, node: NodeId) {
        let (statement, expression) = {
            let d = self.p.nodes[node].as_do_statement();
            (d.iteration_statement_base.statement, d.expression)
        };
        let state = self.enter_node(node);
        self.emit_token(
            Kind::DoKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.emit_embedded_statement(node, statement.expect("do statement"));
        if ast::is_block(&self.p.nodes[statement.unwrap()])
            && !self.p.options.preserve_source_newlines
        {
            self.write_space();
        } else {
            self.write_line_or_space(Some(node), statement, expression);
        }

        self.emit_while_clause(
            node,
            expression,
            statement.map(|s| self.p.nodes[s].end()).unwrap_or_default(),
        );
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitWhileStatement`
    fn emit_while_statement(&mut self, node: NodeId) {
        let (expression, statement) = {
            let d = self.p.nodes[node].as_while_statement();
            (d.expression, d.iteration_statement_base.statement)
        };
        let state = self.enter_node(node);
        self.emit_while_clause(node, expression, self.p.nodes[node].pos());
        self.emit_embedded_statement(node, statement.expect("while statement"));
        self.exit_node(node, state);
    }

    /// `p.emitForInitializer`
    fn emit_for_initializer(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        if self.p.nodes[node].kind == Kind::VariableDeclarationList {
            self.emit_variable_declaration_list(node);
        } else {
            self.emit_expression(Some(node), OperatorPrecedence::LOWEST);
        }
    }

    /// `p.emitForStatement`
    fn emit_for_statement(&mut self, node: NodeId) {
        let (initializer, condition, incrementor, statement) = {
            let d = self.p.nodes[node].as_for_statement();
            (
                d.initializer,
                d.condition,
                d.incrementor,
                d.iteration_statement_base.statement,
            )
        };
        let state = self.enter_node(node);
        let mut pos = self.emit_token(
            Kind::ForKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        pos = self.emit_token(Kind::OpenParenToken, pos, WriteKind::Punctuation, node);
        if let Some(initializer) = initializer {
            self.emit_for_initializer(Some(initializer));
            pos = self.p.nodes[initializer].end();
        }
        pos = self.emit_token(Kind::SemicolonToken, pos, WriteKind::Punctuation, node);
        if let Some(condition) = condition {
            self.write_space();
            self.emit_expression(Some(condition), OperatorPrecedence::LOWEST);
            pos = self.p.nodes[condition].end();
        }
        pos = self.emit_token(Kind::SemicolonToken, pos, WriteKind::Punctuation, node);
        if let Some(incrementor) = incrementor {
            self.write_space();
            self.emit_expression(Some(incrementor), OperatorPrecedence::LOWEST);
            pos = self.p.nodes[incrementor].end();
        }
        self.emit_token(Kind::CloseParenToken, pos, WriteKind::Punctuation, node);
        self.emit_embedded_statement(node, statement.expect("for statement"));
        self.exit_node(node, state);
    }

    /// `p.emitForInStatement`
    fn emit_for_in_statement(&mut self, node: NodeId) {
        let (initializer, expression, statement) = {
            let d = self.p.nodes[node].as_for_in_or_of_statement();
            (d.initializer, d.expression, d.statement)
        };
        let state = self.enter_node(node);
        let pos = self.emit_token(
            Kind::ForKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_token(Kind::OpenParenToken, pos, WriteKind::Punctuation, node);
        self.emit_for_initializer(initializer);
        self.write_space();
        self.emit_token(
            Kind::InKeyword,
            initializer
                .map(|i| self.p.nodes[i].end())
                .unwrap_or_default(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_expression(expression, OperatorPrecedence::LOWEST);
        self.emit_token(
            Kind::CloseParenToken,
            expression
                .map(|e| self.p.nodes[e].end())
                .unwrap_or_default(),
            WriteKind::Punctuation,
            node,
        );
        self.emit_embedded_statement(node, statement.expect("for-in statement"));
        self.exit_node(node, state);
    }

    /// `p.emitForOfStatement`
    fn emit_for_of_statement(&mut self, node: NodeId) {
        let (await_modifier, initializer, expression, statement) = {
            let d = self.p.nodes[node].as_for_in_or_of_statement();
            (d.await_modifier, d.initializer, d.expression, d.statement)
        };
        let state = self.enter_node(node);
        let open_paren_pos = self.emit_token(
            Kind::ForKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        if let Some(await_modifier) = await_modifier {
            self.emit_keyword_node(await_modifier);
            self.write_space();
        }
        self.emit_token(
            Kind::OpenParenToken,
            open_paren_pos,
            WriteKind::Punctuation,
            node,
        );
        self.emit_for_initializer(initializer);
        self.write_space();
        self.emit_token(
            Kind::OfKeyword,
            initializer
                .map(|i| self.p.nodes[i].end())
                .unwrap_or_default(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_expression(expression, OperatorPrecedence::LOWEST);
        self.emit_token(
            Kind::CloseParenToken,
            expression
                .map(|e| self.p.nodes[e].end())
                .unwrap_or_default(),
            WriteKind::Punctuation,
            node,
        );
        self.emit_embedded_statement(node, statement.expect("for-of statement"));
        self.exit_node(node, state);
    }

    /// `p.emitContinueStatement`
    fn emit_continue_statement(&mut self, node: NodeId) {
        let label = self.p.nodes[node].as_continue_statement().label;
        let state = self.enter_node(node);
        self.emit_token(
            Kind::ContinueKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        if let Some(label) = label {
            self.write_space();
            self.emit_label_identifier(label);
        }
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitBreakStatement`
    fn emit_break_statement(&mut self, node: NodeId) {
        let label = self.p.nodes[node].as_break_statement().label;
        let state = self.enter_node(node);
        self.emit_token(
            Kind::BreakKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        if let Some(label) = label {
            self.write_space();
            self.emit_label_identifier(label);
        }
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitReturnStatement`
    fn emit_return_statement(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_return_statement().expression;
        let state = self.enter_node(node);
        self.emit_token(
            Kind::ReturnKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        if let Some(expression) = expression {
            self.write_space();
            self.emit_expression_no_asi(expression, OperatorPrecedence::LOWEST);
        }
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitWithStatement`
    fn emit_with_statement(&mut self, node: NodeId) {
        let (expression, statement) = {
            let d = self.p.nodes[node].as_with_statement();
            (d.expression, d.statement)
        };
        let state = self.enter_node(node);
        let pos = self.emit_token(
            Kind::WithKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_token(Kind::OpenParenToken, pos, WriteKind::Punctuation, node);
        self.emit_expression(expression, OperatorPrecedence::LOWEST);
        self.emit_token(
            Kind::CloseParenToken,
            expression
                .map(|e| self.p.nodes[e].end())
                .unwrap_or_default(),
            WriteKind::Punctuation,
            node,
        );
        self.emit_embedded_statement(node, statement.expect("with statement"));
        self.exit_node(node, state);
    }

    /// `p.emitSwitchStatement`
    fn emit_switch_statement(&mut self, node: NodeId) {
        let (expression, case_block) = {
            let d = self.p.nodes[node].as_switch_statement();
            (d.expression, d.case_block)
        };
        let state = self.enter_node(node);
        let pos = self.emit_token(
            Kind::SwitchKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_token(Kind::OpenParenToken, pos, WriteKind::Punctuation, node);
        self.emit_expression(expression, OperatorPrecedence::LOWEST);
        self.emit_token(
            Kind::CloseParenToken,
            expression
                .map(|e| self.p.nodes[e].end())
                .unwrap_or_default(),
            WriteKind::Punctuation,
            node,
        );
        self.write_space();
        self.emit_case_block(case_block.expect("case block"));
        self.exit_node(node, state);
    }

    /// `p.emitLabeledStatement`
    fn emit_labeled_statement(&mut self, node: NodeId) {
        let (label, statement) = {
            let d = self.p.nodes[node].as_labeled_statement();
            (d.label, d.statement)
        };
        let state = self.enter_node(node);
        self.emit_label_identifier(label.expect("labeled statement label"));
        self.emit_token(
            Kind::ColonToken,
            label.map(|l| self.p.nodes[l].end()).unwrap_or_default(),
            WriteKind::Punctuation,
            node,
        );

        // TODO: use emitEmbeddedStatement rather than writeSpace/emitStatement here after Strada migration as it is
        //       more consistent with similar emit elsewhere. writeSpace/emitStatement is used here to reduce spurious
        //       diffs when testing the Strada migration.
        ////p.emitEmbeddedStatement(node.AsNode(), node.Statement)

        self.write_space();
        self.emit_statement(statement.expect("labeled statement"));

        self.exit_node(node, state);
    }

    /// `p.emitThrowStatement`
    fn emit_throw_statement(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_throw_statement().expression;
        let state = self.enter_node(node);
        self.emit_token(
            Kind::ThrowKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_expression_no_asi(
            expression.expect("throw expression"),
            OperatorPrecedence::LOWEST,
        );
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitTryStatement`
    fn emit_try_statement(&mut self, node: NodeId) {
        let (try_block, catch_clause, finally_block) = {
            let d = self.p.nodes[node].as_try_statement();
            (d.try_block, d.catch_clause, d.finally_block)
        };
        let state = self.enter_node(node);
        self.emit_token(
            Kind::TryKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_block(try_block.expect("try block"));
        if let Some(catch_clause) = catch_clause {
            self.write_line_or_space(Some(node), try_block, Some(catch_clause));
            self.emit_catch_clause(catch_clause);
        }
        if let Some(finally_block) = finally_block {
            let prev = catch_clause.or(try_block);
            self.write_line_or_space(Some(node), prev, Some(finally_block));
            self.emit_token(
                Kind::FinallyKeyword,
                prev.map(|b| self.p.nodes[b].end()).unwrap_or_default(),
                WriteKind::Keyword,
                node,
            );
            self.write_space();
            self.emit_block(finally_block);
        }
        self.exit_node(node, state);
    }

    /// `p.emitDebuggerStatement`
    fn emit_debugger_statement(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.emit_token(
            Kind::DebuggerKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitNotEmittedStatement`
    fn emit_not_emitted_statement(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.exit_node(node, state);
    }

    /// `p.emitNotEmittedTypeElement`
    fn emit_not_emitted_type_element(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.exit_node(node, state);
    }

    //
    // Declarations
    //

    /// `p.emitVariableDeclaration`
    fn emit_variable_declaration(&mut self, node: NodeId) {
        let (name, exclamation_token, type_, initializer) = {
            let d = self.p.nodes[node].as_variable_declaration();
            (d.name, d.exclamation_token, d.type_, d.initializer)
        };
        let state = self.enter_node(node);
        self.emit_binding_name(name);
        self.emit_punctuation_node_opt(exclamation_token);
        self.emit_type_annotation(type_);
        let type_node = name.and_then(|n| self.p.emit_context.get_type_node(n));
        self.emit_initializer(
            initializer,
            greatest_end(
                name.map(|n| self.p.nodes[n].end()).unwrap_or_default(),
                [
                    type_.map(|t| self.p.nodes[t].end()),
                    type_node.map(|t| self.p.nodes[t].end()),
                ],
            ),
            node,
        );
        self.exit_node(node, state);
    }

    /// `p.emitVariableDeclarationNode`
    fn emit_variable_declaration_node(&mut self, node: NodeId) {
        self.emit_variable_declaration(node)
    }

    /// `p.emitVariableDeclarationList`
    fn emit_variable_declaration_list(&mut self, node: NodeId) {
        let declarations = self.p.nodes[node]
            .as_variable_declaration_list()
            .declarations
            .clone();
        let state = self.enter_node(node);
        if ast::is_var_let(node, self.p.nodes) {
            self.write_keyword("let");
        } else if ast::is_var_const(node, self.p.nodes) {
            self.write_keyword("const");
        } else if ast::is_var_using(node, self.p.nodes) {
            self.write_keyword("using");
        } else if ast::is_var_await_using(node, self.p.nodes) {
            self.write_keyword("await");
            self.write_space();
            self.write_keyword("using");
        } else {
            self.write_keyword("var");
        }
        self.write_space();
        self.emit_list(
            Self::emit_variable_declaration_node,
            Some(node),
            declarations.as_ref(),
            LF_VARIABLE_DECLARATION_LIST,
        );
        self.exit_node(node, state);
    }

    /// `p.emitFunctionDeclaration`
    fn emit_function_declaration(&mut self, node: NodeId) {
        let (name, asterisk_token, body) = {
            let d = self.p.nodes[node].as_function_declaration();
            (
                d.name,
                d.function_like_with_body_base.body_base.asterisk_token,
                d.function_like_with_body_base.body_base.body,
            )
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.generate_name_if_needed(name);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        self.write_keyword("function");
        self.emit_token_node(asterisk_token);
        self.write_space();
        if let Some(name) = name {
            self.emit_identifier_name(name);
        }
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.emit_function_body_node(body);
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitClassDeclaration`
    fn emit_class_declaration(&mut self, node: NodeId) {
        let (name, type_parameters, heritage_clauses, members) = {
            let d = self.p.nodes[node].as_class_declaration();
            (
                d.class_like_base.name,
                d.class_like_base.type_parameters.clone(),
                d.class_like_base.heritage_clauses.clone(),
                d.class_like_base.members.clone(),
            )
        };
        let state = self.enter_node(node);
        self.generate_name_if_needed(name);
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let pos = self.emit_modifier_list(node, modifiers.as_ref(), true /*allowDecorators*/);
        self.emit_token(Kind::ClassKeyword, pos, WriteKind::Keyword, node);
        if let Some(name) = name {
            self.write_space();
            self.emit_identifier_name(name);
        }
        let indented = self.should_emit_indented(Some(node));
        self.increase_indent_if(indented);
        self.emit_type_parameters(node, type_parameters);
        self.emit_list(
            Self::emit_heritage_clause_node,
            Some(node),
            heritage_clauses.as_ref(),
            LF_CLASS_HERITAGE_CLAUSES,
        );
        self.write_space();
        self.write_punctuation("{");
        self.push_name_generation_scope(node);
        self.generate_all_member_names(members.as_ref());
        self.emit_list(
            Self::emit_class_element,
            Some(node),
            members.as_ref(),
            LF_CLASS_MEMBERS,
        );
        self.pop_name_generation_scope(node);
        self.write_punctuation("}");
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    /// `p.emitInterfaceDeclaration`
    fn emit_interface_declaration(&mut self, node: NodeId) {
        let (name, type_parameters, heritage_clauses, members) = {
            let d = self.p.nodes[node].as_interface_declaration();
            (
                d.name,
                d.type_parameters.clone(),
                d.heritage_clauses.clone(),
                d.members.clone(),
            )
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        self.write_keyword("interface");
        self.write_space();
        self.emit_binding_identifier(name.expect("interface name"));
        self.emit_type_parameters(node, type_parameters);
        self.emit_list(
            Self::emit_heritage_clause_node,
            Some(node),
            heritage_clauses.as_ref(),
            LF_HERITAGE_CLAUSES,
        );
        self.write_space();
        self.write_punctuation("{");
        self.push_name_generation_scope(node);
        self.generate_all_member_names(members.as_ref());
        self.emit_list(
            Self::emit_type_element,
            Some(node),
            members.as_ref(),
            LF_INTERFACE_MEMBERS,
        );
        self.pop_name_generation_scope(node);
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    /// `p.emitTypeAliasDeclaration`
    fn emit_type_alias_declaration(&mut self, node: NodeId) {
        let (name, type_parameters, type_) = {
            let d = self.p.nodes[node].as_type_alias_declaration();
            (d.name, d.type_parameters.clone(), d.type_)
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        self.write_keyword("type");
        self.write_space();
        self.emit_binding_identifier(name.expect("type alias name"));
        self.emit_type_parameters(node, type_parameters);
        self.write_space();
        self.write_punctuation("=");
        self.write_space();
        self.emit_type_node_outside_extends_opt(type_);
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitEnumDeclaration`
    fn emit_enum_declaration(&mut self, node: NodeId) {
        let (name, members) = {
            let d = self.p.nodes[node].as_enum_declaration();
            (d.name, d.members.clone())
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        self.write_keyword("enum");
        self.write_space();
        self.emit_binding_identifier(name.expect("enum name"));
        self.write_space();
        self.write_punctuation("{");
        self.emit_list(
            Self::emit_enum_member_node,
            Some(node),
            members.as_ref(),
            LF_ENUM_MEMBERS,
        );
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    /// `p.emitModuleDeclaration`
    fn emit_module_declaration(&mut self, node: NodeId) {
        let (keyword, name, mut body, attributes) = {
            let d = self.p.nodes[node].as_module_declaration();
            (d.keyword, d.name, d.body_base.body, d.attributes)
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        if keyword != Kind::GlobalKeyword {
            self.write_keyword(if keyword == Kind::NamespaceKeyword {
                "namespace"
            } else {
                "module"
            });
            self.write_space();
        }
        self.emit_module_name(name);
        while let Some(b) = body
            && ast::is_module_declaration(&self.p.nodes[b])
        {
            let (name2, body2) = {
                let d = self.p.nodes[b].as_module_declaration();
                (d.name, d.body_base.body)
            };
            self.write_punctuation(".");
            self.emit_nested_module_name(name2);
            body = body2;
        }
        if let Some(attributes) = attributes {
            self.write_space();
            self.write_keyword("with");
            self.write_space();
            self.emit_type_node(Some(attributes), TypePrecedence::NON_ARRAY);
        }
        if body.is_none() {
            self.write_trailing_semicolon();
        } else {
            self.write_space();
            self.emit_module_block(body.unwrap());
        }
        self.exit_node(node, state);
    }

    /// `p.emitModuleBlock`
    fn emit_module_block(&mut self, node: NodeId) {
        let statements = self.p.nodes[node].as_module_block().statements.clone();
        let state = self.enter_node(node);
        self.generate_names(Some(node));
        self.emit_token(
            Kind::OpenBraceToken,
            self.p.nodes[node].pos(),
            WriteKind::Punctuation,
            node,
        );
        let format = if self.is_empty_block(node, statements.as_ref())
            || self.should_emit_on_single_line(Some(node))
        {
            LF_SINGLE_LINE_BLOCK_STATEMENTS
        } else {
            LF_MULTI_LINE_BLOCK_STATEMENTS
        };
        self.emit_list(
            Self::emit_statement,
            Some(node),
            statements.as_ref(),
            format,
        );
        self.emit_token_ex(
            Kind::CloseBraceToken,
            statements.map(|s| s.loc.end()).unwrap_or_default(),
            WriteKind::Punctuation,
            node,
            if format & LF_MULTI_LINE != 0 {
                TEF_INDENT_LEADING_COMMENTS
            } else {
                TEF_NONE
            },
        );
        self.exit_node(node, state);
    }

    /// `p.emitCaseBlock`
    fn emit_case_block(&mut self, node: NodeId) {
        let clauses = self.p.nodes[node].as_case_block().clauses.clone();
        let state = self.enter_node(node);
        self.emit_token(
            Kind::OpenBraceToken,
            self.p.nodes[node].pos(),
            WriteKind::Punctuation,
            node,
        );
        self.emit_list(
            Self::emit_case_or_default_clause_node,
            Some(node),
            clauses.as_ref(),
            LF_CASE_BLOCK_CLAUSES,
        );
        self.emit_token_ex(
            Kind::CloseBraceToken,
            clauses.map(|c| c.loc.end()).unwrap_or_default(),
            WriteKind::Punctuation,
            node,
            TEF_INDENT_LEADING_COMMENTS,
        );
        self.exit_node(node, state);
    }

    /// `p.emitImportEqualsDeclaration`
    fn emit_import_equals_declaration(&mut self, node: NodeId) {
        let (is_type_only, name, module_reference) = {
            let d = self.p.nodes[node].as_import_equals_declaration();
            (d.is_type_only, d.name, d.module_reference)
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        let pos = self.emit_token(
            Kind::ImportKeyword,
            greatest_end(self.p.nodes[node].pos(), [modifiers.map(|m| m.loc.end())]),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        if is_type_only {
            self.emit_token(Kind::TypeKeyword, pos, WriteKind::Keyword, node);
            self.write_space();
        }
        self.emit_binding_identifier(name.expect("import equals name"));
        self.write_space();
        self.emit_token(
            Kind::EqualsToken,
            name.map(|n| self.p.nodes[n].end()).unwrap_or_default(),
            WriteKind::Punctuation,
            node,
        );
        self.write_space();
        self.emit_module_reference(module_reference.expect("module reference"));
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitModuleReference`
    fn emit_module_reference(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::Identifier => self.emit_identifier_reference(node),
            Kind::QualifiedName => self.emit_qualified_name(node),
            Kind::ExternalModuleReference => self.emit_external_module_reference(node),
            _ => panic!("unhandled ModuleReference: {:?}", self.p.nodes[node].kind),
        }
    }

    /// `p.emitImportDeclaration`
    fn emit_import_declaration(&mut self, node: NodeId) {
        let (import_clause, module_specifier, attributes) = {
            let d = self.p.nodes[node].as_import_declaration();
            (d.import_clause, d.module_specifier, d.attributes)
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        self.emit_token(
            Kind::ImportKeyword,
            greatest_end(self.p.nodes[node].pos(), [modifiers.map(|m| m.loc.end())]),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        if let Some(import_clause) = import_clause {
            self.emit_import_clause(import_clause);
            self.write_space();
            self.emit_token(
                Kind::FromKeyword,
                self.p.nodes[import_clause].end(),
                WriteKind::Keyword,
                node,
            );
            self.write_space();
        }
        self.emit_expression(module_specifier, OperatorPrecedence::LOWEST);
        if let Some(attributes) = attributes {
            self.write_space();
            self.emit_import_attributes(attributes);
        }
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitImportClause`
    fn emit_import_clause(&mut self, node: NodeId) {
        let (phase_modifier, name, named_bindings) = {
            let d = self.p.nodes[node].as_import_clause();
            (d.phase_modifier, d.name, d.named_bindings)
        };
        let state = self.enter_node(node);
        if phase_modifier != Kind::Unknown {
            self.emit_token(
                phase_modifier,
                self.p.nodes[node].pos(),
                WriteKind::Keyword,
                node,
            );
            self.write_space();
        }
        if let Some(name) = name {
            self.emit_binding_identifier(name);
            if named_bindings.is_some() {
                self.emit_token(
                    Kind::CommaToken,
                    self.p.nodes[name].end(),
                    WriteKind::Punctuation,
                    node,
                );
                self.write_space();
            }
        }
        self.emit_named_import_bindings(named_bindings);
        self.exit_node(node, state);
    }

    /// `p.emitNamespaceImport`
    fn emit_namespace_import(&mut self, node: NodeId) {
        let name = self.p.nodes[node].as_namespace_import().name;
        let state = self.enter_node(node);
        let pos = self.emit_token(
            Kind::AsteriskToken,
            self.p.nodes[node].pos(),
            WriteKind::Punctuation,
            node,
        );
        self.write_space();
        self.emit_token(Kind::AsKeyword, pos, WriteKind::Keyword, node);
        self.write_space();
        self.emit_binding_identifier(name.expect("namespace import name"));
        self.exit_node(node, state);
    }

    /// `p.emitNamedImports`
    fn emit_named_imports(&mut self, node: NodeId) {
        let elements = self.p.nodes[node].as_named_imports().elements.clone();
        let state = self.enter_node(node);
        self.write_punctuation("{");
        self.emit_list(
            Self::emit_import_specifier_node,
            Some(node),
            elements.as_ref(),
            LF_NAMED_IMPORTS_OR_EXPORTS_ELEMENTS,
        );
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    /// `p.emitNamedImportBindings`
    fn emit_named_import_bindings(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        match self.p.nodes[node].kind {
            Kind::NamespaceImport => self.emit_namespace_import(node),
            Kind::NamedImports => self.emit_named_imports(node),
            _ => panic!(
                "unhandled NamedImportBindings: {:?}",
                self.p.nodes[node].kind
            ),
        }
    }

    /// `p.emitImportSpecifier`
    fn emit_import_specifier(&mut self, node: NodeId) {
        let (is_type_only, property_name, name) = {
            let d = self.p.nodes[node].as_import_specifier();
            (d.is_type_only, d.property_name, d.name)
        };
        let state = self.enter_node(node);
        if is_type_only {
            self.write_keyword("type");
            self.write_space();
        }
        if let Some(property_name) = property_name {
            self.emit_module_export_name(Some(property_name));
            self.write_space();
            self.emit_token(
                Kind::AsKeyword,
                self.p.nodes[property_name].end(),
                WriteKind::Keyword,
                node,
            );
            self.write_space();
        }
        self.emit_binding_identifier(name.expect("import specifier name"));
        self.exit_node(node, state);
    }

    /// `p.emitImportSpecifierNode`
    fn emit_import_specifier_node(&mut self, node: NodeId) {
        self.emit_import_specifier(node)
    }

    /// `p.emitExportAssignment`
    fn emit_export_assignment(&mut self, node: NodeId) {
        let (is_export_equals, expression) = {
            let d = self.p.nodes[node].as_export_assignment();
            (d.is_export_equals, d.expression)
        };
        let state = self.enter_node(node);
        let next_pos = self.emit_token(
            Kind::ExportKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        if is_export_equals {
            self.emit_token(Kind::EqualsToken, next_pos, WriteKind::Operator, node);
        } else {
            self.emit_token(Kind::DefaultKeyword, next_pos, WriteKind::Keyword, node);
        }
        self.write_space();
        if is_export_equals {
            self.emit_expression(expression, OperatorPrecedence::ASSIGNMENT);
        } else {
            // parenthesize `class` and `function` expressions so as not to conflict with exported `class` and `function` declarations
            let expr = get_leftmost_expression(
                expression.unwrap_or_default(),
                false, /*stopAtCallExpressions*/
                self.p.nodes,
            );
            if ast::is_class_expression(&self.p.nodes[expr])
                || ast::is_function_expression(&self.p.nodes[expr])
            {
                self.emit_expression(expression, OperatorPrecedence::PARENTHESES);
            } else {
                self.emit_expression(expression, OperatorPrecedence::ASSIGNMENT);
            }
        }
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitExportDeclaration`
    fn emit_export_declaration(&mut self, node: NodeId) {
        let (is_type_only, export_clause, module_specifier, attributes) = {
            let d = self.p.nodes[node].as_export_declaration();
            (
                d.is_type_only,
                d.export_clause,
                d.module_specifier,
                d.attributes,
            )
        };
        let modifiers = self.p.nodes[node].modifiers().cloned();
        let state = self.enter_node(node);
        self.emit_modifier_list(node, modifiers.as_ref(), false /*allowDecorators*/);
        let mut pos = self.emit_token(
            Kind::ExportKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        if is_type_only {
            pos = self.emit_token(Kind::TypeKeyword, pos, WriteKind::Keyword, node);
            self.write_space();
        }
        if let Some(export_clause) = export_clause {
            self.emit_named_export_bindings(export_clause);
        } else {
            pos = self.emit_token(Kind::AsteriskToken, pos, WriteKind::Punctuation, node);
        }
        if let Some(module_specifier) = module_specifier {
            self.write_space();
            self.emit_token(
                Kind::FromKeyword,
                greatest_end(pos, [export_clause.map(|c| self.p.nodes[c].end())]),
                WriteKind::Keyword,
                node,
            );
            self.write_space();
            self.emit_expression(Some(module_specifier), OperatorPrecedence::LOWEST);
        }
        if let Some(attributes) = attributes {
            self.write_space();
            self.emit_import_attributes(attributes);
        }
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitImportAttributes`
    fn emit_import_attributes(&mut self, node: NodeId) {
        let (token, attributes) = {
            let d = self.p.nodes[node].as_import_attributes();
            (d.token, d.attributes.clone())
        };
        let state = self.enter_node(node);
        self.emit_token(token, self.p.nodes[node].pos(), WriteKind::Keyword, node);
        self.write_space();
        self.emit_list(
            Self::emit_import_attribute_node,
            Some(node),
            attributes.as_ref(),
            LF_IMPORT_ATTRIBUTES,
        );
        self.exit_node(node, state);
    }

    /// `p.emitImportAttribute`
    fn emit_import_attribute(&mut self, node: NodeId) {
        let (name, value) = {
            let d = self.p.nodes[node].as_import_attribute();
            (d.name, d.value)
        };
        let state = self.enter_node(node);
        self.emit_import_attribute_name(name.expect("import attribute name"));
        self.write_punctuation(":");
        self.write_space();
        let value = value.expect("import attribute value");
        if !self
            .p
            .emit_context
            .emit_flags(value)
            .has(EmitFlags::NO_LEADING_COMMENTS)
        {
            let comment_range = self.p.emit_context.comment_range(self.p.nodes, value);
            self.emit_trailing_comments(comment_range.pos(), CommentSeparator::After);
        }
        self.emit_expression(Some(value), OperatorPrecedence::DISALLOW_COMMA);
        self.exit_node(node, state);
    }

    /// `p.emitImportAttributeNode`
    fn emit_import_attribute_node(&mut self, node: NodeId) {
        self.emit_import_attribute(node)
    }

    /// `p.emitNamespaceExportDeclaration`
    fn emit_namespace_export_declaration(&mut self, node: NodeId) {
        let name = self.p.nodes[node].as_namespace_export_declaration().name;
        let state = self.enter_node(node);
        let mut pos = self.emit_token(
            Kind::ExportKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        pos = self.emit_token(Kind::AsKeyword, pos, WriteKind::Keyword, node);
        self.write_space();
        self.emit_token(Kind::NamespaceKeyword, pos, WriteKind::Keyword, node);
        self.write_space();
        self.emit_binding_identifier(name.expect("namespace export declaration name"));
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    /// `p.emitNamespaceExport`
    fn emit_namespace_export(&mut self, node: NodeId) {
        let name = self.p.nodes[node].as_namespace_export().name;
        let state = self.enter_node(node);
        let pos = self.emit_token(
            Kind::AsteriskToken,
            self.p.nodes[node].pos(),
            WriteKind::Punctuation,
            node,
        );
        self.write_space();
        self.emit_token(Kind::AsKeyword, pos, WriteKind::Keyword, node);
        self.write_space();
        self.emit_module_export_name(name);
        self.exit_node(node, state);
    }

    /// `p.emitNamedExports`
    fn emit_named_exports(&mut self, node: NodeId) {
        let elements = self.p.nodes[node].as_named_exports().elements.clone();
        let state = self.enter_node(node);
        self.write_punctuation("{");
        self.emit_list(
            Self::emit_export_specifier_node,
            Some(node),
            elements.as_ref(),
            LF_NAMED_IMPORTS_OR_EXPORTS_ELEMENTS,
        );
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    /// `p.emitNamedExportBindings`
    fn emit_named_export_bindings(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::NamespaceExport => self.emit_namespace_export(node),
            Kind::NamedExports => self.emit_named_exports(node),
            _ => panic!(
                "unhandled NamedExportBindings: {:?}",
                self.p.nodes[node].kind
            ),
        }
    }

    /// `p.emitExportSpecifier`
    fn emit_export_specifier(&mut self, node: NodeId) {
        let (is_type_only, property_name, name) = {
            let d = self.p.nodes[node].as_export_specifier();
            (d.is_type_only, d.property_name, d.name)
        };
        let state = self.enter_node(node);
        if is_type_only {
            self.write_keyword("type");
            self.write_space();
        }
        if let Some(property_name) = property_name {
            self.emit_module_export_name(Some(property_name));
            self.write_space();
            self.emit_token(
                Kind::AsKeyword,
                self.p.nodes[property_name].end(),
                WriteKind::Keyword,
                node,
            );
            self.write_space();
        }
        self.emit_module_export_name(name);
        self.exit_node(node, state);
    }

    /// `p.emitExportSpecifierNode`
    fn emit_export_specifier_node(&mut self, node: NodeId) {
        self.emit_export_specifier(node)
    }

    /// `p.emitEmbeddedStatement`
    fn emit_embedded_statement(&mut self, parent_node: NodeId, node: NodeId) {
        if ast::is_block(&self.p.nodes[node])
            || self.should_emit_on_single_line(Some(parent_node))
            || (self.p.options.preserve_source_newlines
                && self.get_leading_line_terminator_count(Some(parent_node), Some(node), LF_NONE)
                    == 0)
        {
            self.write_space();
            self.emit_statement(node);
        } else {
            self.write_line();
            self.increase_indent();
            if self.p.nodes[node].kind == Kind::EmptyStatement {
                self.emit_empty_statement(node, true /*isEmbeddedStatement*/);
            } else {
                self.emit_statement(node);
            }
            self.decrease_indent();
        }
    }

    /// `p.emitStatement`
    fn emit_statement(&mut self, node: NodeId) {
        if let Some(snippet_element) = self.p.emit_context.snippet_element(node) {
            self.emit_snippet_node(node, &snippet_element);
            return;
        }

        match self.p.nodes[node].kind {
            // Statements
            Kind::Block => self.emit_block(node),
            Kind::EmptyStatement => {
                self.emit_empty_statement(node, false /*isEmbeddedStatement*/)
            }
            Kind::VariableStatement => self.emit_variable_statement(node),
            Kind::ExpressionStatement => self.emit_expression_statement(node),
            Kind::IfStatement => self.emit_if_statement(node),
            Kind::DoStatement => self.emit_do_statement(node),
            Kind::WhileStatement => self.emit_while_statement(node),
            Kind::ForStatement => self.emit_for_statement(node),
            Kind::ForInStatement => self.emit_for_in_statement(node),
            Kind::ForOfStatement => self.emit_for_of_statement(node),
            Kind::ContinueStatement => self.emit_continue_statement(node),
            Kind::BreakStatement => self.emit_break_statement(node),
            Kind::ReturnStatement => self.emit_return_statement(node),
            Kind::WithStatement => self.emit_with_statement(node),
            Kind::SwitchStatement => self.emit_switch_statement(node),
            Kind::LabeledStatement => self.emit_labeled_statement(node),
            Kind::ThrowStatement => self.emit_throw_statement(node),
            Kind::TryStatement => self.emit_try_statement(node),
            Kind::DebuggerStatement => self.emit_debugger_statement(node),
            Kind::NotEmittedStatement => self.emit_not_emitted_statement(node),

            // Declaration Statements
            Kind::FunctionDeclaration => self.emit_function_declaration(node),
            Kind::ClassDeclaration => self.emit_class_declaration(node),
            Kind::InterfaceDeclaration => self.emit_interface_declaration(node),
            Kind::TypeAliasDeclaration | Kind::JSTypeAliasDeclaration => {
                self.emit_type_alias_declaration(node)
            }
            Kind::EnumDeclaration => self.emit_enum_declaration(node),
            Kind::ModuleDeclaration => self.emit_module_declaration(node),
            Kind::MissingDeclaration => {
                // Missing declarations do not emit a statement.
            }

            // Import/Export Statements
            Kind::NamespaceExportDeclaration => self.emit_namespace_export_declaration(node),
            Kind::ImportEqualsDeclaration => self.emit_import_equals_declaration(node),
            Kind::ImportDeclaration => self.emit_import_declaration(node),
            Kind::ExportAssignment => self.emit_export_assignment(node),
            Kind::ExportDeclaration => self.emit_export_declaration(node),

            _ => panic!("unhandled statement: {:?}", self.p.nodes[node].kind),
        }
    }

    //
    // Module references
    //

    /// `p.emitExternalModuleReference`
    fn emit_external_module_reference(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_external_module_reference().expression;
        let state = self.enter_node(node);
        self.write_keyword("require");
        self.write_punctuation("(");
        self.emit_expression(expression, OperatorPrecedence::DISALLOW_COMMA);
        self.write_punctuation(")");
        self.exit_node(node, state);
    }

    //
    // JSX
    //

    /// `p.emitJsxElement`
    fn emit_jsx_element(&mut self, node: NodeId) {
        let (opening_element, children, closing_element) = {
            let d = self.p.nodes[node].as_jsx_element();
            (d.opening_element, d.children.clone(), d.closing_element)
        };
        let state = self.enter_node(node);
        self.emit_jsx_opening_element(opening_element.expect("jsx opening element"));
        self.emit_list(
            Self::emit_jsx_child,
            Some(node),
            children.as_ref(),
            LF_JSX_ELEMENT_OR_FRAGMENT_CHILDREN,
        );
        self.emit_jsx_closing_element(closing_element.expect("jsx closing element"));
        self.exit_node(node, state);
    }

    /// `p.emitJsxSelfClosingElement`
    fn emit_jsx_self_closing_element(&mut self, node: NodeId) {
        let (tag_name, type_arguments, attributes) = {
            let d = self.p.nodes[node].as_jsx_self_closing_element();
            (d.tag_name, d.type_arguments.clone(), d.attributes)
        };
        let state = self.enter_node(node);
        self.write_punctuation("<");
        self.emit_jsx_tag_name(tag_name.expect("jsx tag name"));
        self.emit_type_arguments(node, type_arguments);
        self.write_space();
        self.emit_jsx_attributes(attributes.expect("jsx attributes"));
        self.write_punctuation("/>");
        self.exit_node(node, state);
    }

    /// `p.emitJsxFragment`
    fn emit_jsx_fragment(&mut self, node: NodeId) {
        let (opening_fragment, children, closing_fragment) = {
            let d = self.p.nodes[node].as_jsx_fragment();
            (d.opening_fragment, d.children.clone(), d.closing_fragment)
        };
        let state = self.enter_node(node);
        self.emit_jsx_opening_fragment(opening_fragment.expect("jsx opening fragment"));
        self.emit_list(
            Self::emit_jsx_child,
            Some(node),
            children.as_ref(),
            LF_JSX_ELEMENT_OR_FRAGMENT_CHILDREN,
        );
        self.emit_jsx_closing_fragment(closing_fragment.expect("jsx closing fragment"));
        self.exit_node(node, state);
    }

    /// `p.emitJsxOpeningElement`
    fn emit_jsx_opening_element(&mut self, node: NodeId) {
        let (tag_name, type_arguments, attributes) = {
            let d = self.p.nodes[node].as_jsx_opening_element();
            (d.tag_name, d.type_arguments.clone(), d.attributes)
        };
        let state = self.enter_node(node);
        self.write_punctuation("<");
        let indented = self.write_line_separators_and_indent_before(tag_name, Some(node));
        self.emit_jsx_tag_name(tag_name.expect("jsx tag name"));
        self.emit_type_arguments(node, type_arguments);
        if attributes.as_ref().is_some_and(|a| {
            self.p.nodes[*a]
                .as_jsx_attributes()
                .properties
                .as_ref()
                .is_some_and(|p| !p.nodes.is_empty())
        }) {
            self.write_space();
        }
        self.emit_jsx_attributes(attributes.expect("jsx attributes"));
        self.write_line_separators_after(attributes, Some(node));
        self.decrease_indent_if(indented);
        self.write_punctuation(">");
        self.exit_node(node, state);
    }

    /// `p.emitJsxClosingElement`
    fn emit_jsx_closing_element(&mut self, node: NodeId) {
        let tag_name = self.p.nodes[node].as_jsx_closing_element().tag_name;
        let state = self.enter_node(node);
        self.write_punctuation("</");
        self.emit_jsx_tag_name(tag_name.expect("jsx tag name"));
        self.write_punctuation(">");
        self.exit_node(node, state);
    }

    /// `p.emitJsxOpeningFragment`
    fn emit_jsx_opening_fragment(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.write_punctuation("<");
        self.write_punctuation(">");
        self.exit_node(node, state);
    }

    /// `p.emitJsxClosingFragment`
    fn emit_jsx_closing_fragment(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        self.write_punctuation("</");
        self.write_punctuation(">");
        self.exit_node(node, state);
    }

    /// `p.emitJsxText`
    fn emit_jsx_text(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        // TODO(rbuckton): Should this be using `getLiteralTextOfNode` instead?
        // PORT: Go accesses the `Text` field on `JsxText` directly; `Node::text` does
        // not handle `Kind::JsxText`.
        let text = self.p.nodes[node]
            .as_jsx_text()
            .literal_like_node_base
            .text
            .clone();
        self.write_literal(&text);
        self.exit_node(node, state);
    }

    /// `p.emitJsxAttributes`
    fn emit_jsx_attributes(&mut self, node: NodeId) {
        let properties = self.p.nodes[node].as_jsx_attributes().properties.clone();
        let state = self.enter_node(node);
        self.emit_list(
            Self::emit_jsx_attribute_like,
            Some(node),
            properties.as_ref(),
            LF_JSX_ELEMENT_ATTRIBUTES,
        );
        self.exit_node(node, state);
    }

    /// `p.emitJsxAttribute`
    fn emit_jsx_attribute(&mut self, node: NodeId) {
        let (name, initializer) = {
            let d = self.p.nodes[node].as_jsx_attribute();
            (d.name, d.initializer)
        };
        let state = self.enter_node(node);
        self.emit_jsx_attribute_name(name.expect("jsx attribute name"));
        if let Some(initializer) = initializer {
            self.write_punctuation("=");
            self.emit_jsx_attribute_value(initializer);
        }
        self.exit_node(node, state);
    }

    /// `p.emitJsxSpreadAttribute`
    fn emit_jsx_spread_attribute(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_jsx_spread_attribute().expression;
        let state = self.enter_node(node);
        self.write_punctuation("{...");
        self.emit_expression(expression, OperatorPrecedence::LOWEST);
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    /// `p.emitJsxAttributeLike`
    fn emit_jsx_attribute_like(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::JsxAttribute => self.emit_jsx_attribute(node),
            Kind::JsxSpreadAttribute => self.emit_jsx_spread_attribute(node),
            _ => panic!("unhandled JsxAttributeLike: {:?}", self.p.nodes[node].kind),
        }
    }

    /// `p.emitJsxExpression`
    fn emit_jsx_expression(&mut self, node: NodeId) {
        let (dot_dot_dot_token, expression) = {
            let d = self.p.nodes[node].as_jsx_expression();
            (d.dot_dot_dot_token, d.expression)
        };
        let state = self.enter_node(node);
        // preserve empty expressions if they contain comments!
        if expression.is_some()
            || (!self.comments_disabled
                && !ast::node_is_synthesized(&self.p.nodes[node])
                && self.has_comments_at_position(self.p.nodes[node].pos()))
        {
            let indented = self.p.current_source_file.is_some()
                && !ast::node_is_synthesized(&self.p.nodes[node])
                && util::get_lines_between_positions(
                    self.p.nodes[self.p.current_source_file.unwrap()].as_source_file(),
                    self.p.nodes[node].pos(),
                    self.p.nodes[node].end(),
                ) != 0;
            self.increase_indent_if(indented);
            let end = self.emit_token(
                Kind::OpenBraceToken,
                self.p.nodes[node].pos(),
                WriteKind::Punctuation,
                node,
            );
            self.emit_token_node(dot_dot_dot_token);
            if let Some(expression) = expression {
                self.emit_expression(Some(expression), OperatorPrecedence::DISALLOW_COMMA);
            }
            self.emit_token(
                Kind::CloseBraceToken,
                greatest_end(
                    end,
                    [
                        expression.map(|e| self.p.nodes[e].end()),
                        dot_dot_dot_token.map(|t| self.p.nodes[t].end()),
                    ],
                ),
                WriteKind::Punctuation,
                node,
            );
            self.decrease_indent_if(indented);
        }
        self.exit_node(node, state);
    }

    /// `p.emitJsxNamespacedName`
    fn emit_jsx_namespaced_name(&mut self, node: NodeId) {
        let (namespace, name) = {
            let d = self.p.nodes[node].as_jsx_namespaced_name();
            (d.namespace, d.name)
        };
        let state = self.enter_node(node);
        self.emit_identifier_name(namespace.expect("jsx namespace"));
        self.write_punctuation(":");
        self.emit_identifier_name(name.expect("jsx namespaced name"));
        self.exit_node(node, state);
    }

    /// `p.emitJsxChild`
    fn emit_jsx_child(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::JsxText => self.emit_jsx_text(node),
            Kind::JsxExpression => self.emit_jsx_expression(node),
            Kind::JsxElement => self.emit_jsx_element(node),
            Kind::JsxSelfClosingElement => self.emit_jsx_self_closing_element(node),
            Kind::JsxFragment => self.emit_jsx_fragment(node),
            _ => panic!("unhandled JsxChild: {:?}", self.p.nodes[node].kind),
        }
    }

    /// `p.emitJsxTagName`
    fn emit_jsx_tag_name(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::Identifier => self.emit_identifier_reference(node),
            Kind::ThisKeyword => self.emit_keyword_expression(node),
            Kind::JsxNamespacedName => self.emit_jsx_namespaced_name(node),
            Kind::PropertyAccessExpression => self.emit_property_access_expression(node),
            _ => panic!("unhandled JsxTagName: {:?}", self.p.nodes[node].kind),
        }
    }

    /// `p.emitJsxAttributeName`
    fn emit_jsx_attribute_name(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::Identifier => self.emit_identifier_name(node),
            Kind::JsxNamespacedName => self.emit_jsx_namespaced_name(node),
            _ => panic!("unhandled JsxAttributeName: {:?}", self.p.nodes[node].kind),
        }
    }

    /// `p.emitJsxAttributeValue`
    fn emit_jsx_attribute_value(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::StringLiteral => self.emit_string_literal(node),
            Kind::JsxExpression => self.emit_jsx_expression(node),
            Kind::JsxElement => self.emit_jsx_element(node),
            Kind::JsxSelfClosingElement => self.emit_jsx_self_closing_element(node),
            Kind::JsxFragment => self.emit_jsx_fragment(node),
            _ => self.emit_expression(Some(node), OperatorPrecedence::LOWEST),
        }
    }

    //
    // Clauses
    //

    /// `p.emitCaseOrDefaultClauseStatements`
    fn emit_case_or_default_clause_statements(&mut self, node: NodeId, colon_pos: i32) {
        let statements = self.p.nodes[node]
            .as_case_or_default_clause()
            .statements
            .clone();
        let emit_as_single_statement = statements.as_ref().is_some_and(|s| {
            s.nodes.len() == 1
                // treat synthesized nodes as located on the same line for emit purposes
                && (self.p.current_source_file.is_none()
                    || ast::node_is_synthesized(&self.p.nodes[node])
                    || ast::node_is_synthesized(&self.p.nodes[s.nodes[0]])
                    || util::range_start_positions_are_on_same_line(
                        self.p.nodes[node].loc,
                        self.p.nodes[s.nodes[0]].loc,
                        self.p.nodes[self.p.current_source_file.unwrap()].as_source_file(),
                    ))
        });

        let mut format = LF_CASE_OR_DEFAULT_CLAUSE_STATEMENTS;
        if emit_as_single_statement {
            // When emitting as a single statement, use writeToken (no comments) for the colon
            // to avoid duplicating trailing comments that will be picked up by the statement list.
            self.write_token_text(Kind::ColonToken, WriteKind::Punctuation, colon_pos);
            self.write_space();
            format &= !(LF_MULTI_LINE | LF_INDENTED);
        } else {
            self.emit_token(Kind::ColonToken, colon_pos, WriteKind::Punctuation, node);
        }

        self.emit_list(
            Self::emit_statement,
            Some(node),
            statements.as_ref(),
            format,
        );
    }

    /// `p.emitCaseClause`
    fn emit_case_clause(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_case_or_default_clause().expression;
        let state = self.enter_node(node);
        self.emit_token(
            Kind::CaseKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();
        self.emit_expression(expression, OperatorPrecedence::LOWEST);
        self.emit_case_or_default_clause_statements(
            node,
            expression
                .map(|e| self.p.nodes[e].end())
                .unwrap_or_default(),
        );
        self.exit_node(node, state);
    }

    /// `p.emitDefaultClause`
    fn emit_default_clause(&mut self, node: NodeId) {
        let state = self.enter_node(node);
        let pos = self.emit_token(
            Kind::DefaultKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.emit_case_or_default_clause_statements(node, pos);
        self.exit_node(node, state);
    }

    /// `p.emitCaseOrDefaultClauseNode`
    fn emit_case_or_default_clause_node(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::CaseClause => self.emit_case_clause(node),
            Kind::DefaultClause => self.emit_default_clause(node),
            _ => panic!(
                "unhandled CaseOrDefaultClause: {:?}",
                self.p.nodes[node].kind
            ),
        }
    }

    /// `p.emitHeritageClause`
    fn emit_heritage_clause(&mut self, node: NodeId) {
        let (token, types) = {
            let d = self.p.nodes[node].as_heritage_clause();
            (d.token, d.types.clone())
        };
        let state = self.enter_node(node);
        self.write_space();
        self.emit_token(token, self.p.nodes[node].pos(), WriteKind::Keyword, node);
        self.write_space();
        self.emit_list(
            Self::emit_heritage_clause_element,
            Some(node),
            types.as_ref(),
            LF_HERITAGE_CLAUSE_TYPES,
        );
        self.exit_node(node, state);
    }

    /// `p.emitHeritageClauseElement`
    fn emit_heritage_clause_element(&mut self, node: NodeId) {
        match self.p.nodes[node].kind {
            Kind::ExpressionWithTypeArguments => self.emit_expression_with_type_arguments(node),
            Kind::TypeReference => self.emit_type_reference(node),
            _ => panic!(
                "unhandled HeritageClauseElement: {:?}",
                self.p.nodes[node].kind
            ),
        }
    }

    /// `p.emitHeritageClauseNode`
    fn emit_heritage_clause_node(&mut self, node: NodeId) {
        self.emit_heritage_clause(node)
    }

    /// `p.emitCatchClause`
    fn emit_catch_clause(&mut self, node: NodeId) {
        let (variable_declaration, block) = {
            let d = self.p.nodes[node].as_catch_clause();
            (d.variable_declaration, d.block)
        };
        let state = self.enter_node(node);
        let open_paren_pos = self.emit_token(
            Kind::CatchKeyword,
            self.p.nodes[node].pos(),
            WriteKind::Keyword,
            node,
        );
        self.write_space();

        if let Some(variable_declaration) = variable_declaration {
            self.emit_token(
                Kind::OpenParenToken,
                open_paren_pos,
                WriteKind::Punctuation,
                node,
            );
            self.emit_variable_declaration(variable_declaration);
            self.emit_token(
                Kind::CloseParenToken,
                self.p.nodes[variable_declaration].end(),
                WriteKind::Punctuation,
                node,
            );
            self.write_space();
        }

        self.emit_block(block.expect("catch block"));
        self.exit_node(node, state);
    }

    //
    // Property assignments
    //

    /// `p.emitPropertyAssignment`
    fn emit_property_assignment(&mut self, node: NodeId) {
        let (name, initializer) = {
            let d = self.p.nodes[node].as_property_assignment();
            (d.named_member_base.name, d.initializer)
        };
        let state = self.enter_node(node);
        self.emit_property_name(name);
        self.write_punctuation(":");
        self.write_space();
        // This is to ensure that we emit comment in the following case:
        //      For example:
        //          obj = {
        //              id: /*comment1*/ ()=>void
        //          }
        // "comment1" is not considered to be leading comment for node.initializer
        // but rather a trailing comment on the previous node.
        let initializer = initializer.expect("property assignment initializer");
        if !self
            .p
            .emit_context
            .emit_flags(initializer)
            .has(EmitFlags::NO_LEADING_COMMENTS)
        {
            let comment_range = self.p.emit_context.comment_range(self.p.nodes, initializer);
            self.emit_trailing_comments(comment_range.pos(), CommentSeparator::After);
        }
        self.emit_expression(Some(initializer), OperatorPrecedence::DISALLOW_COMMA);
        self.exit_node(node, state);
    }

    /// `p.emitShorthandPropertyAssignment`
    fn emit_shorthand_property_assignment(&mut self, node: NodeId) {
        let (name, object_assignment_initializer) = {
            let d = self.p.nodes[node].as_shorthand_property_assignment();
            (d.named_member_base.name, d.object_assignment_initializer)
        };
        let state = self.enter_node(node);
        self.emit_property_name(name);
        if let Some(object_assignment_initializer) = object_assignment_initializer {
            self.write_space();
            self.write_punctuation("=");
            self.write_space();
            self.emit_expression(
                Some(object_assignment_initializer),
                OperatorPrecedence::DISALLOW_COMMA,
            );
        }
        self.exit_node(node, state);
    }

    /// `p.emitSpreadAssignment`
    fn emit_spread_assignment(&mut self, node: NodeId) {
        let expression = self.p.nodes[node].as_spread_assignment().expression;
        let state = self.enter_node(node);
        if expression.is_some() {
            self.emit_token(
                Kind::DotDotDotToken,
                self.p.nodes[node].pos(),
                WriteKind::Punctuation,
                node,
            );
            self.emit_expression(expression, OperatorPrecedence::DISALLOW_COMMA);
        }
        self.exit_node(node, state);
    }

    //
    // Enum
    //

    /// `p.emitEnumMember`
    fn emit_enum_member(&mut self, node: NodeId) {
        let (name, initializer) = {
            let d = self.p.nodes[node].as_enum_member();
            (d.named_member_base.name, d.initializer)
        };
        let state = self.enter_node(node);
        self.emit_property_name(name);
        self.emit_initializer(
            initializer,
            name.map(|n| self.p.nodes[n].end()).unwrap_or_default(),
            node,
        );
        self.exit_node(node, state);
    }

    /// `p.emitEnumMemberNode`
    fn emit_enum_member_node(&mut self, node: NodeId) {
        self.emit_enum_member(node)
    }

    //
    // JSDoc
    //

    /// `p.emitJSDocNode`
    fn emit_js_doc_node(&mut self, _node: NodeId) {
        // !!!
        panic!("not implemented")
    }

    //
    // Top-level nodes
    //

    /// `p.emitShebangIfNeeded`
    fn emit_shebang_if_needed(&mut self, node: NodeId) {
        if ast::node_is_synthesized(&self.p.nodes[node]) {
            return;
        }
        let shebang = scanner::get_shebang(self.p.nodes[node].as_source_file().text()).to_string();
        if !shebang.is_empty() {
            self.write_comment(&shebang);
            self.write_line();
        }
    }

    /// `p.emitPrologueDirectives`
    fn emit_prologue_directives(&mut self, statements: Option<&NodeList>) -> usize {
        if let Some(statements) = statements {
            for (i, &statement) in statements.nodes.iter().enumerate() {
                if ast::is_prologue_directive(&self.p.nodes[statement], self.p.nodes) {
                    self.write_line();
                    self.emit_statement(statement);
                } else {
                    return i;
                }
            }
            return statements.nodes.len();
        }
        0
    }

    /// `p.emitHelpers`
    fn emit_helpers(&mut self, node: NodeId) -> bool {
        let mut helpers_emitted = false;
        let source_file = self.p.current_source_file;
        let should_skip = self.p.options.no_emit_helpers
            || (source_file.is_some_and(|sf| {
                self.p
                    .emit_context
                    .has_recorded_external_helpers(self.p.nodes, sf)
            }));
        let mut helpers = self.p.emit_context.get_emit_helpers(node);
        if !helpers.is_empty() {
            helpers.sort_by(compare_emit_helpers);
            for helper in helpers {
                if !helper.scoped {
                    // Skip the helper if it can be skipped and the noEmitHelpers compiler
                    // option is set, or if it can be imported and the importHelpers compiler
                    // option is set.
                    if should_skip {
                        continue;
                    }
                }
                if let Some(text_callback) = &helper.text_callback {
                    // `p.makeFileLevelOptimisticUniqueName`
                    let mut name_fn = |n: &str| self.p.make_file_level_optimistic_unique_name(n);
                    let name_fn: &mut UniqueNameFn = &mut name_fn;
                    let text = text_callback(name_fn);
                    self.write_lines(&text);
                } else {
                    let text = helper.text;
                    self.write_lines(text);
                }
                helpers_emitted = true;
            }
        }

        helpers_emitted
    }

    /// `p.emitSourceFile`
    fn emit_source_file_node(&mut self, node: NodeId) {
        let saved_current_source_file = self.p.current_source_file;
        let saved_comments_disabled = self.comments_disabled;
        self.p.current_source_file = Some(node);

        self.write_line();

        self.push_name_generation_scope(node);
        let statements = self.p.nodes[node].as_source_file().statements.clone();
        self.generate_all_names(statements.as_ref());

        let mut index = 0usize;
        let state;
        let script_kind = self.p.nodes[node].as_source_file().script_kind;
        let is_declaration_file = self.p.nodes[node].as_source_file().is_declaration_file;
        if script_kind != ScriptKind::Json {
            self.emit_shebang_if_needed(node);
            index = self.emit_prologue_directives(statements.as_ref());
            if !self.w().is_at_start_of_line() {
                self.write_line();
            }
            state = self.emit_detached_comments_before_statement_list(
                node,
                statements.as_ref().map(|s| s.loc).unwrap_or_default(),
            );
            self.emit_helpers(node);
            if is_declaration_file {
                self.emit_triple_slash_directives(node);
            }
        } else {
            state = self.emit_detached_comments_before_statement_list(
                node,
                statements.as_ref().map(|s| s.loc).unwrap_or_default(),
            );
        }

        // !!! Emit triple-slash directives
        self.emit_list_range(
            Self::emit_statement,
            Some(node),
            statements.as_ref(),
            LF_MULTI_LINE,
            index as i32,
            -1, /*count*/
        );
        self.pop_name_generation_scope(node);
        self.emit_detached_comments_after_statement_list(
            node,
            statements.map(|s| s.loc).unwrap_or_default(),
            state,
        );
        self.p.current_source_file = saved_current_source_file;
        self.comments_disabled = saved_comments_disabled;
    }

    /// `p.emitTripleSlashDirectives`
    fn emit_triple_slash_directives(&mut self, node: NodeId) {
        let (referenced_files, type_reference_directives, lib_reference_directives) = {
            let sf = self.p.nodes[node].as_source_file();
            (
                sf.referenced_files.clone(),
                sf.type_reference_directives.clone(),
                sf.lib_reference_directives.clone(),
            )
        };
        self.emit_directive("path", &referenced_files);
        self.emit_directive("types", &type_reference_directives);
        self.emit_directive("lib", &lib_reference_directives);
    }

    /// `p.emitDirective`
    fn emit_directive(&mut self, kind: &str, refs: &[FileReference]) {
        for ref_ in refs {
            let mut resolution_mode = String::new();
            if ref_.resolution_mode != tsc_core::compileroptions::RESOLUTION_MODE_NONE {
                resolution_mode = format!(
                    "resolution-mode=\"{}\" ",
                    if ref_.resolution_mode == tsc_core::compileroptions::RESOLUTION_MODE_ESM {
                        "import"
                    } else {
                        "require"
                    }
                );
            }
            self.write_comment(&format!(
                "/// <reference {}=\"{}\" {}{}/>",
                kind,
                ref_.file_name,
                resolution_mode,
                if ref_.preserve {
                    "preserve=\"true\" "
                } else {
                    ""
                },
            ));
            self.write_line();
        }
    }

    //
    // Lists
    //

    /// `p.emitList`
    fn emit_list(
        &mut self,
        emit: fn(&mut Self, NodeId),
        parent_node: Option<NodeId>,
        children: Option<&NodeList>,
        mut format: ListFormat,
    ) {
        if self.should_emit_on_multiple_lines(parent_node) {
            format |= LF_PREFER_NEW_LINE | LF_INDENTED;
        }

        self.emit_list_range(emit, parent_node, children, format, -1, -1);
    }

    /// `p.emitListRange`
    fn emit_list_range(
        &mut self,
        emit: fn(&mut Self, NodeId),
        parent_node: Option<NodeId>,
        children: Option<&NodeList>,
        format: ListFormat,
        mut start: i32,
        mut count: i32,
    ) {
        let is_nil = children.is_none();

        let mut length = 0usize;
        if !is_nil {
            length = children.unwrap().nodes.len();
        }

        if start < 0 {
            start = 0;
        }
        let start = start as usize;

        if count < 0 {
            count = length.saturating_sub(start) as i32;
        }
        let count = count;

        if is_nil && format & LF_OPTIONAL_IF_NIL != 0 {
            return;
        }

        let is_empty = is_nil || start >= length || count <= 0;
        if is_empty && format & LF_OPTIONAL_IF_EMPTY != 0 {
            if let Some(h) = self.p.handlers.on_before_emit_node_list.as_mut() {
                h(children);
            }
            if let Some(h) = self.p.handlers.on_after_emit_node_list.as_mut() {
                h(children);
            }
            return;
        }

        if format & LF_BRACKETS_MASK != 0 {
            self.write_punctuation(get_opening_bracket(format));
            if is_empty && !is_nil {
                // Emit comments within empty lists
                self.emit_trailing_comments(children.unwrap().loc.pos(), CommentSeparator::Before);
            }
        }

        if let Some(h) = self.p.handlers.on_before_emit_node_list.as_mut() {
            h(children);
        }

        if is_empty {
            // Write a line terminator if the parent node was multi-line
            if format & LF_MULTI_LINE != 0
                && !(self.p.options.preserve_source_newlines
                    && (parent_node.is_none()
                        || (self.p.current_source_file.is_some()
                            && util::range_is_on_single_line(
                                self.p.nodes[parent_node.unwrap()].loc,
                                self.p.nodes[self.p.current_source_file.unwrap()].as_source_file(),
                            ))))
            {
                self.write_line();
            } else if format & LF_SPACE_BETWEEN_BRACES != 0 && format & LF_NO_SPACE_IF_EMPTY == 0 {
                self.write_space();
            }
        } else {
            let end = (start + count as usize).min(length);
            let children_ref = children.unwrap();
            let items: Vec<NodeId> = children_ref.nodes[start..end].to_vec();
            let has_trailing_comma = self.has_trailing_comma(parent_node, children);
            self.emit_list_items(
                emit,
                parent_node,
                &items,
                format,
                has_trailing_comma,
                children_ref.loc,
            );
        }

        if let Some(h) = self.p.handlers.on_after_emit_node_list.as_mut() {
            h(children);
        }

        if format & LF_BRACKETS_MASK != 0 {
            if is_empty && !is_nil {
                // Emit comments within empty lists
                self.emit_leading_comments(children.unwrap().loc.end(), false /*elided*/);
            }
            self.write_punctuation(get_closing_bracket(format));
        }
    }

    /// `p.hasTrailingComma`
    fn has_trailing_comma(
        &mut self,
        parent_node: Option<NodeId>,
        children: Option<&NodeList>,
    ) -> bool {
        let (Some(parent_node), Some(children)) = (parent_node, children) else {
            return false;
        };
        // NodeList.HasTrailingComma() is unreliable on transformed nodes as some nodes may have been removed. In the event
        // we believe we may need to emit a trailing comma, we must first look to the respective node list on the original
        // node first.
        if !children.has_trailing_comma(self.p.nodes) {
            return false;
        }

        let original_parent = self
            .p
            .emit_context
            .most_original(Some(parent_node))
            .unwrap_or(parent_node);
        if original_parent == parent_node {
            // if this node is the original node, we can trust the result
            return true;
        }

        // Go compares `children` to `parentNode`'s list accessors by
        // pointer (`switch children { case parentNode.ElementList(): }`) to
        // find which member list it is. The same comparison works on arena
        // values — `children` is always one of `parent_node`'s own lists —
        // and identifies which list to consult on the original node,
        // whichever arena that original lives in.
        let which = {
            let pn = &self.p.nodes[parent_node];
            let is = |list: Option<&NodeList>| list.is_some_and(|l| l == children);
            match pn.kind {
                Kind::ObjectLiteralExpression => OriginalListKind::PropertyList,
                Kind::ArrayLiteralExpression | Kind::NamedImports | Kind::NamedExports => {
                    OriginalListKind::ElementList
                }
                Kind::ObjectBindingPattern | Kind::ArrayBindingPattern => {
                    if is(pn.element_list()) {
                        OriginalListKind::ElementList
                    } else {
                        OriginalListKind::Children
                    }
                }
                Kind::CallExpression | Kind::NewExpression => {
                    if is(pn.type_argument_list()) {
                        OriginalListKind::TypeArgumentList
                    } else if is(pn.argument_list()) {
                        OriginalListKind::ArgumentList
                    } else {
                        OriginalListKind::Children
                    }
                }
                Kind::Constructor
                | Kind::MethodDeclaration
                | Kind::GetAccessor
                | Kind::SetAccessor
                | Kind::FunctionDeclaration
                | Kind::FunctionExpression
                | Kind::ArrowFunction
                | Kind::FunctionType
                | Kind::ConstructorType
                | Kind::CallSignature
                | Kind::ConstructSignature => {
                    if is(pn.type_parameter_list()) {
                        OriginalListKind::TypeParameterList
                    } else if is(pn.parameter_list()) {
                        OriginalListKind::ParameterList
                    } else {
                        OriginalListKind::Children
                    }
                }
                Kind::ClassDeclaration
                | Kind::ClassExpression
                | Kind::InterfaceDeclaration
                | Kind::TypeAliasDeclaration
                | Kind::JSTypeAliasDeclaration => {
                    if is(pn.type_parameter_list()) {
                        OriginalListKind::TypeParameterList
                    } else {
                        OriginalListKind::Children
                    }
                }
                Kind::ImportAttributes => OriginalListKind::Attributes,
                _ => OriginalListKind::Children,
            }
        };
        // `originalList := children` — when no candidate matched, Go uses
        // `children` itself, whose result we already know is true.
        if which == OriginalListKind::Children {
            return true;
        }

        // `original_parent` may live in a different file arena than
        // `self.p.nodes` (e.g. node-builder clones carrying parse-node
        // `original` links into a scratch buffer). If the id doesn't resolve
        // in this buffer we cannot dereference the list — the host-provided
        // foreign-arena hook resolves `which` there instead.
        if original_parent.local_index() as usize >= self.p.nodes.len()
            || self.p.nodes[original_parent].id != original_parent
        {
            if let Some(f) = self
                .p
                .handlers
                .original_list_has_trailing_comma
                .as_mut()
                && let Some(result) = f(original_parent, which)
            {
                return result;
            }
            return false;
        }

        if self.p.nodes[original_parent].kind != self.p.nodes[parent_node].kind {
            // if the original node is some other kind of node, we cannot correlate the list
            return false;
        }

        // if we have the original list, we can use it's result.
        if let Some(original_list) =
            original_list_for_kind(self.p.nodes, original_parent, which)
        {
            return original_list.has_trailing_comma(self.p.nodes);
        }

        false
    }

    /// `p.writeDelimiter`
    fn write_delimiter(&mut self, format: ListFormat) {
        match format & LF_DELIMITERS_MASK {
            LF_NONE => {
                // no delimiter for this format
            }
            LF_COMMA_DELIMITED => {
                self.write_punctuation(",");
            }
            LF_BAR_DELIMITED => {
                self.write_space();
                self.write_punctuation("|");
            }
            LF_ASTERISK_DELIMITED => {
                self.write_space();
                self.write_punctuation("*");
                self.write_space();
            }
            LF_AMPERSAND_DELIMITED => {
                self.write_space();
                self.write_punctuation("&");
            }
            _ => {}
        }
    }

    // Emits a list without brackets or raising events.
    //
    // NOTE: You probably don't want to call this directly and should be using `emitList` instead.
    /// `p.emitListItems`
    fn emit_list_items(
        &mut self,
        emit: fn(&mut Self, NodeId),
        parent_node: Option<NodeId>,
        children: &[NodeId],
        format: ListFormat,
        has_trailing_comma: bool,
        children_text_range: TextRange,
    ) {
        // Write the opening line terminator or leading whitespace.
        let may_emit_intervening_comments = format & LF_NO_INTERVENING_COMMENTS == 0;
        let mut should_emit_intervening_comments = may_emit_intervening_comments;

        let mut leading_line_terminator_count = 0;
        if !children.is_empty() {
            leading_line_terminator_count =
                self.get_leading_line_terminator_count(parent_node, Some(children[0]), format);
        }
        if leading_line_terminator_count > 0 {
            for _ in 0..leading_line_terminator_count {
                self.write_line();
            }
            should_emit_intervening_comments = false;
        } else if format & LF_SPACE_BETWEEN_BRACES != 0 {
            self.write_space();
        }

        // Increase the indent, if requested.
        if format & LF_INDENTED != 0 {
            self.increase_indent();
        }

        let parent_end = greatest_end(-1, [parent_node.map(|p| self.p.nodes[p].end())]);

        // Emit each child.
        let mut previous_sibling: Option<NodeId> = None;
        let mut should_decrease_indent_after_emit = false;
        for &child in children {
            // Write the delimiter if this is not the first node.
            if format & LF_ASTERISK_DELIMITED != 0 {
                // always write JSDoc in the format "\n *"
                self.write_line();
                self.write_delimiter(format);
            } else if let Some(previous_sibling) = previous_sibling {
                // i.e
                //      function commentedParameters(
                //          /* Parameter a */
                //          a
                //          /* End of parameter a */ -> this comment isn't considered to be trailing comment of parameter "a" due to newline
                //          ,
                if format & LF_DELIMITERS_MASK != 0
                    && self.p.nodes[previous_sibling].end() != parent_end
                {
                    if !self.comments_disabled
                        && self.should_emit_trailing_comments(previous_sibling)
                    {
                        self.emit_leading_comments(
                            self.p.nodes[previous_sibling].end(),
                            false, /*elided*/
                        );
                    }
                }

                self.write_delimiter(format);

                // Write either a line terminator or whitespace to separate the elements.
                let separating_line_terminator_count = self.get_separating_line_terminator_count(
                    Some(previous_sibling),
                    Some(child),
                    format,
                );
                if separating_line_terminator_count > 0 {
                    // If a synthesized node in a single-line list starts on a new
                    // line, we should increase the indent.
                    if format & (LF_LINES_MASK | LF_INDENTED) == LF_SINGLE_LINE {
                        self.increase_indent();
                        should_decrease_indent_after_emit = true;
                    }

                    if should_emit_intervening_comments
                        && format & LF_DELIMITERS_MASK != 0
                        && !ast::position_is_synthesized(self.p.nodes[child].pos())
                        && self.should_emit_leading_comments(child)
                    {
                        let comment_range = self.p.emit_context.comment_range(self.p.nodes, child);
                        self.emit_trailing_comments_of_position(
                            comment_range.pos(),
                            format & LF_SPACE_BETWEEN_SIBLINGS != 0,
                            true, /*forceNoNewline*/
                        );
                    }

                    for _ in 0..separating_line_terminator_count {
                        self.write_line();
                    }

                    should_emit_intervening_comments = false;
                } else if format & LF_SPACE_BETWEEN_SIBLINGS != 0 {
                    self.write_space();
                }
            }

            // Emit this child.
            if should_emit_intervening_comments && self.should_emit_leading_comments(child) {
                let comment_range = self.p.emit_context.comment_range(self.p.nodes, child);
                self.emit_trailing_comments_of_position(
                    comment_range.pos(),
                    false, /*prefixSpace*/
                    false, /*forceNoNewline*/
                );
            } else {
                should_emit_intervening_comments = may_emit_intervening_comments;
            }

            self.next_list_element_pos = self.p.nodes[child].pos();
            emit(self, child);

            if should_decrease_indent_after_emit {
                self.decrease_indent();
                should_decrease_indent_after_emit = false;
            }

            previous_sibling = Some(child);
        }

        // Write a trailing comma, if requested.
        let skip_trailing_comments = self.comments_disabled
            || previous_sibling.is_none_or(|p| !self.should_emit_trailing_comments(p));
        let emit_trailing_comma = has_trailing_comma
            && format & LF_ALLOW_TRAILING_COMMA != 0
            && format & LF_COMMA_DELIMITED != 0;
        if emit_trailing_comma {
            if let Some(previous_sibling) = previous_sibling
                && !skip_trailing_comments
            {
                self.emit_token(
                    Kind::CommaToken,
                    self.p.nodes[previous_sibling].end(),
                    WriteKind::Punctuation,
                    previous_sibling,
                );
            } else {
                self.write_punctuation(",");
            }
        }

        // Emit any trailing comment of the last element in the list
        // i.e
        //       var array = [...
        //          2
        //          /* end of element 2 */
        //       ];
        if let Some(previous_sibling) = previous_sibling
            && parent_end != self.p.nodes[previous_sibling].end()
            && format & LF_DELIMITERS_MASK != 0
            && !skip_trailing_comments
        {
            let comments_pos = if emit_trailing_comma && children_text_range.end() > 0 {
                children_text_range.end()
            } else {
                self.p.nodes[previous_sibling].end()
            };
            self.emit_leading_comments(comments_pos, false /*elided*/);
        }

        // Decrease the indent, if requested.
        if format & LF_INDENTED != 0 {
            self.decrease_indent();
        }

        // Write the closing line terminator or closing whitespace.
        let closing_line_terminator_count = self.get_closing_line_terminator_count(
            parent_node,
            children.last().copied(),
            format,
            children_text_range,
        );
        if closing_line_terminator_count > 0 {
            for _ in 0..closing_line_terminator_count {
                self.write_line();
            }
        } else if format & (LF_SPACE_AFTER_LIST | LF_SPACE_BETWEEN_BRACES) != 0 {
            self.write_space();
        }
    }

    /// `p.Write`'s `switch node.Kind` dispatch.
    fn emit_node_dispatch(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        match self.p.nodes[node].kind {
            // Pseudo-literals
            Kind::TemplateHead => self.emit_template_head(node),
            Kind::TemplateMiddle => self.emit_template_middle(node),
            Kind::TemplateTail => self.emit_template_tail(node),

            // Identifiers
            Kind::Identifier => self.emit_identifier_name(node),

            // PrivateIdentifiers
            Kind::PrivateIdentifier => self.emit_private_identifier(node),

            // Parse tree nodes
            // Names
            Kind::QualifiedName => self.emit_qualified_name(node),
            Kind::ComputedPropertyName => self.emit_computed_property_name(node),

            // Signature elements
            Kind::TypeParameter => self.emit_type_parameter(node),
            Kind::Parameter => self.emit_parameter(node),
            Kind::Decorator => self.emit_decorator(node),

            // Type members
            Kind::PropertySignature => self.emit_property_signature(node),
            Kind::PropertyDeclaration => self.emit_property_declaration(node),
            Kind::MethodSignature => self.emit_method_signature(node),
            Kind::MethodDeclaration => self.emit_method_declaration(node),
            Kind::ClassStaticBlockDeclaration => self.emit_class_static_block_declaration(node),
            Kind::Constructor => self.emit_constructor(node),
            Kind::GetAccessor => self.emit_get_accessor_declaration(node),
            Kind::SetAccessor => self.emit_set_accessor_declaration(node),
            Kind::CallSignature => self.emit_call_signature(node),
            Kind::ConstructSignature => self.emit_construct_signature(node),
            Kind::IndexSignature => self.emit_index_signature(node),

            // Binding patterns
            Kind::ObjectBindingPattern => self.emit_object_binding_pattern(node),
            Kind::ArrayBindingPattern => self.emit_array_binding_pattern(node),
            Kind::BindingElement => self.emit_binding_element(node),

            // Misc
            Kind::TemplateSpan => self.emit_template_span(node),
            Kind::SemicolonClassElement => self.emit_semicolon_class_element(node),

            // Declarations (non-statement)
            Kind::VariableDeclaration => self.emit_variable_declaration(node),
            Kind::VariableDeclarationList => self.emit_variable_declaration_list(node),
            Kind::ModuleBlock => self.emit_module_block(node),
            Kind::CaseBlock => self.emit_case_block(node),
            Kind::ImportClause => self.emit_import_clause(node),
            Kind::NamespaceImport => self.emit_namespace_import(node),
            Kind::NamespaceExport => self.emit_namespace_export(node),
            Kind::NamedImports => self.emit_named_imports(node),
            Kind::ImportSpecifier => self.emit_import_specifier(node),
            Kind::NamedExports => self.emit_named_exports(node),
            Kind::ExportSpecifier => self.emit_export_specifier(node),
            Kind::ImportAttributes => self.emit_import_attributes(node),
            Kind::ImportAttribute => self.emit_import_attribute(node),

            // Module references
            Kind::ExternalModuleReference => self.emit_external_module_reference(node),

            // JSX (non-expression)
            Kind::JsxText => self.emit_jsx_text(node),
            Kind::JsxOpeningElement => self.emit_jsx_opening_element(node),
            Kind::JsxOpeningFragment => self.emit_jsx_opening_fragment(node),
            Kind::JsxClosingElement => self.emit_jsx_closing_element(node),
            Kind::JsxClosingFragment => self.emit_jsx_closing_fragment(node),
            Kind::JsxAttribute => self.emit_jsx_attribute(node),
            Kind::JsxAttributes => self.emit_jsx_attributes(node),
            Kind::JsxSpreadAttribute => self.emit_jsx_spread_attribute(node),
            Kind::JsxExpression => self.emit_jsx_expression(node),
            Kind::JsxNamespacedName => self.emit_jsx_namespaced_name(node),

            // Clauses
            Kind::CaseClause => self.emit_case_clause(node),
            Kind::DefaultClause => self.emit_default_clause(node),
            Kind::HeritageClause => self.emit_heritage_clause(node),
            Kind::CatchClause => self.emit_catch_clause(node),

            // Property assignments
            Kind::PropertyAssignment => self.emit_property_assignment(node),
            Kind::ShorthandPropertyAssignment => self.emit_shorthand_property_assignment(node),
            Kind::SpreadAssignment => self.emit_spread_assignment(node),

            // Enum
            Kind::EnumMember => self.emit_enum_member(node),

            // Top-level nodes
            Kind::SourceFile => self.emit_source_file_node(node),

            // Transformation nodes
            Kind::NotEmittedTypeElement => self.emit_not_emitted_type_element(node),

            _ => {
                if ast::is_type_node(&self.p.nodes[node]) {
                    self.emit_type_node_outside_extends(node);
                } else if ast::is_statement(&self.p.nodes[node], self.p.nodes) {
                    self.emit_statement(node);
                } else if ast::is_expression(&self.p.nodes[node], self.p.nodes) {
                    self.emit_expression(Some(node), OperatorPrecedence::LOWEST);
                } else if self.p.nodes[node].kind.is_keyword_kind() {
                    self.emit_keyword_node(node);
                } else if self.p.nodes[node].kind.is_punctuation_kind() {
                    self.emit_punctuation_node(node);
                } else if ast::is_js_doc_kind(self.p.nodes[node].kind) {
                    self.emit_js_doc_node(node);
                } else {
                    panic!("unhandled Node: {:?}", self.p.nodes[node].kind)
                }
            }
        }
    }

    //
    // Comments
    //

    /// `p.emitCommentsBeforeNode`
    fn emit_comments_before_node(&mut self, node: NodeId) -> Option<CommentState> {
        if !self.should_emit_comments(Some(node)) {
            return None;
        }

        let emit_flags = self.p.emit_context.emit_flags(node);
        let comment_range = self.p.emit_context.comment_range(self.p.nodes, node);
        let container_pos = self.container_pos;
        let container_end = self.container_end;
        let declaration_list_container_end = self.declaration_list_container_end;

        // Emit leading comments
        self.emit_leading_comments_of_node(node, emit_flags, comment_range);
        self.emit_leading_synthetic_comments_of_node(node, emit_flags);
        if emit_flags & EmitFlags::NO_NESTED_COMMENTS != EmitFlags::NONE {
            self.comments_disabled = true;
        }

        Some(CommentState {
            emit_flags,
            comment_range,
            container_pos,
            container_end,
            declaration_list_container_end,
        })
    }

    /// `p.emitCommentsAfterNode`
    fn emit_comments_after_node(&mut self, node: NodeId, state: Option<CommentState>) {
        let Some(state) = state else {
            return;
        };

        let emit_flags = state.emit_flags;
        let comment_range = state.comment_range;
        let container_pos = state.container_pos;
        let container_end = state.container_end;
        let declaration_list_container_end = state.declaration_list_container_end;

        // Emit trailing comments
        if emit_flags & EmitFlags::NO_NESTED_COMMENTS != EmitFlags::NONE {
            self.comments_disabled = false;
        }

        self.emit_trailing_synthetic_comments_of_node(node, emit_flags);
        self.emit_trailing_comments_of_node(
            node,
            emit_flags,
            comment_range,
            container_pos,
            container_end,
            declaration_list_container_end,
        );

        // Preserve comments from erased type annotation
        if let Some(type_node) = self.p.emit_context.get_type_node(node) {
            let loc = self.p.nodes[type_node].loc;
            self.emit_trailing_comments_of_node(
                node,
                emit_flags,
                loc,
                container_pos,
                container_end,
                declaration_list_container_end,
            );
        }
    }

    /// `p.emitCommentsBeforeToken`
    fn emit_comments_before_token(
        &mut self,
        _token: Kind,
        pos: i32,
        context_node: NodeId,
        flags: TokenEmitFlags,
    ) -> (Option<CommentState>, i32) {
        let mut pos = pos;
        if flags & TEF_NO_COMMENTS != 0 || self.comments_disabled {
            // Still skip trivia so that the returned pos correctly identifies the token position.
            // This is needed for trailing source map positions (writeTokenText advances pos by token length).
            if self.p.current_source_file.is_some() && !ast::position_is_synthesized(pos) {
                pos = scanner::skip_trivia(
                    self.p.nodes[self.p.current_source_file.unwrap()]
                        .as_source_file()
                        .text(),
                    pos,
                );
            }
            return (None, pos);
        }

        let start_pos = pos;
        if self.p.current_source_file.is_some() {
            pos = scanner::skip_trivia(
                self.p.nodes[self.p.current_source_file.unwrap()]
                    .as_source_file()
                    .text(),
                start_pos,
            );
        }

        let node = self.p.emit_context.parse_node(self.p.nodes, context_node);
        let is_similar_node =
            node.is_some_and(|n| self.p.nodes[n].kind == self.p.nodes[context_node].kind);
        if !is_similar_node {
            return (None, pos);
        }

        if self.p.nodes[context_node].pos() != start_pos {
            let indent_leading = flags & TEF_INDENT_LEADING_COMMENTS != 0;
            let needs_indent = indent_leading
                && self.p.current_source_file.is_some()
                && !util::positions_are_on_same_line(
                    start_pos,
                    pos,
                    self.p.nodes[self.p.current_source_file.unwrap()].as_source_file(),
                );
            self.increase_indent_if(needs_indent);
            self.emit_leading_comments(start_pos, false /*elided*/);
            self.decrease_indent_if(needs_indent);
        }

        (Some(CommentState::default()), pos)
    }

    /// `p.emitCommentsAfterToken`
    fn emit_comments_after_token(
        &mut self,
        _token: Kind,
        pos: i32,
        context_node: NodeId,
        state: Option<CommentState>,
    ) {
        if state.is_none() {
            return;
        }

        if self.p.nodes[context_node].end() != pos {
            let is_jsx_expr_context = self.p.nodes[context_node].kind == Kind::JsxExpression;
            self.emit_trailing_comments(
                pos,
                if is_jsx_expr_context {
                    CommentSeparator::None
                } else {
                    CommentSeparator::Before
                },
            );
        }
    }

    /// `p.emitDetachedCommentsBeforeStatementList`
    fn emit_detached_comments_before_statement_list(
        &mut self,
        node: NodeId,
        detached_range: TextRange,
    ) -> Option<CommentState> {
        if !self.should_emit_detached_comments(node) {
            return None;
        }

        let emit_flags = self.p.emit_context.emit_flags(node);
        let container_pos = self.container_pos;
        let container_end = self.container_end;
        let declaration_list_container_end = self.declaration_list_container_end;
        let skip_leading_comments = ast::position_is_synthesized(detached_range.pos())
            || emit_flags & EmitFlags::NO_LEADING_COMMENTS != EmitFlags::NONE;

        if !skip_leading_comments {
            self.emit_detached_comments_and_update_comments_info(detached_range);
        }

        if emit_flags & EmitFlags::NO_NESTED_COMMENTS != EmitFlags::NONE {
            self.comments_disabled = true;
        }

        Some(CommentState {
            emit_flags,
            comment_range: detached_range,
            container_pos,
            container_end,
            declaration_list_container_end,
        })
    }

    /// `p.emitDetachedCommentsAfterStatementList`
    fn emit_detached_comments_after_statement_list(
        &mut self,
        _node: NodeId,
        detached_range: TextRange,
        state: Option<CommentState>,
    ) {
        let Some(state) = state else {
            return;
        };

        let emit_flags = state.emit_flags;
        let skip_trailing_comments = self.comments_disabled
            || ast::position_is_synthesized(detached_range.end())
            || emit_flags & EmitFlags::NO_TRAILING_COMMENTS != EmitFlags::NONE;

        if !skip_trailing_comments {
            let has_written_comment =
                self.emit_leading_comments(detached_range.end(), false /*elided*/);
            if has_written_comment && !self.w().is_at_start_of_line() {
                self.write_line();
            }
        }
    }

    /// `p.emitLeadingCommentsOfNode`
    fn emit_leading_comments_of_node(
        &mut self,
        node: NodeId,
        emit_flags: EmitFlags,
        comment_range: TextRange,
    ) {
        let pos = comment_range.pos();
        let end = comment_range.end();

        // Save current container state on the stack.
        if (!ast::position_is_synthesized(pos) || !ast::position_is_synthesized(end)) && pos != end
        {
            // We have to explicitly check that the node is JsxText because if the compilerOptions.jsx is "preserve" we will not do any transformation.
            // It is expensive to walk entire tree just to set one kind of node to have no comments.
            let skip_leading_comments = ast::position_is_synthesized(pos)
                || emit_flags & EmitFlags::NO_LEADING_COMMENTS != EmitFlags::NONE
                || self.p.nodes[node].kind == Kind::JsxText;
            let skip_trailing_comments = ast::position_is_synthesized(end)
                || emit_flags & EmitFlags::NO_TRAILING_COMMENTS != EmitFlags::NONE
                || self.p.nodes[node].kind == Kind::JsxText;

            // Emit leading comments if the position is not synthesized and the node
            // has not opted out from emitting leading comments.
            if !skip_leading_comments {
                self.emit_leading_comments(
                    pos,
                    self.p.nodes[node].kind == Kind::NotEmittedStatement, /*elided*/
                );
            }

            if !skip_leading_comments
                || (pos >= 0 && emit_flags & EmitFlags::NO_LEADING_COMMENTS != EmitFlags::NONE)
            {
                // Advance the container position if comments get emitted or if they've been disabled explicitly using NoLeadingComments.
                self.container_pos = pos;
            }

            if !skip_trailing_comments
                || (end >= 0 && emit_flags & EmitFlags::NO_TRAILING_COMMENTS != EmitFlags::NONE)
            {
                // Advance the container end if comments get emitted or if they've been disabled explicitly using NoTrailingComments.
                self.container_end = end;

                // To avoid invalid comment emit in a down-level binding pattern, we
                // keep track of the last declaration list container's end
                if self.p.nodes[node].kind == Kind::VariableDeclarationList {
                    self.declaration_list_container_end = end;
                }
            }
        }
    }

    /// `p.emitTrailingCommentsOfNode`
    fn emit_trailing_comments_of_node(
        &mut self,
        node: NodeId,
        emit_flags: EmitFlags,
        comment_range: TextRange,
        container_pos: TextPos,
        container_end: TextPos,
        declaration_list_container_end: TextPos,
    ) {
        let pos = comment_range.pos();
        let end = comment_range.end();
        let skip_trailing_comments = end < 0
            || emit_flags & EmitFlags::NO_TRAILING_COMMENTS != EmitFlags::NONE
            || self.p.nodes[node].kind == Kind::JsxText;
        if (!ast::position_is_synthesized(pos) || !ast::position_is_synthesized(end)) && pos != end
        {
            // Restore previous container state.
            self.container_pos = container_pos;
            self.container_end = container_end;
            self.declaration_list_container_end = declaration_list_container_end;

            // Emit trailing comments if the position is not synthesized and the node
            // has not opted out from emitting leading comments and is an emitted node.
            if !skip_trailing_comments && self.p.nodes[node].kind != Kind::NotEmittedStatement {
                self.emit_trailing_comments(end, CommentSeparator::Before);
            }
        }
    }

    /// `p.emitLeadingSyntheticCommentsOfNode`
    fn emit_leading_synthetic_comments_of_node(&mut self, node: NodeId, emit_flags: EmitFlags) {
        if emit_flags & EmitFlags::NO_LEADING_COMMENTS != EmitFlags::NONE {
            return;
        }
        let synth = self.p.emit_context.get_synthetic_leading_comments(node);
        for c in synth {
            self.emit_leading_synthesized_comment(&c);
        }
    }

    /// `p.emitLeadingSynthesizedComment`
    fn emit_leading_synthesized_comment(&mut self, comment: &SynthesizedComment) {
        if comment.has_leading_new_line || comment.kind == Kind::SingleLineCommentTrivia {
            self.w().write_line();
        }
        self.write_synthesized_comment(comment);
        if comment.has_trailing_new_line || comment.kind == Kind::SingleLineCommentTrivia {
            self.w().write_line();
        } else {
            self.w().write_space(" ");
        }
    }

    /// `p.emitTrailingSyntheticCommentsOfNode`
    fn emit_trailing_synthetic_comments_of_node(&mut self, node: NodeId, emit_flags: EmitFlags) {
        if emit_flags & EmitFlags::NO_TRAILING_COMMENTS != EmitFlags::NONE {
            return;
        }
        let synth = self.p.emit_context.get_synthetic_trailing_comments(node);
        for c in synth {
            self.emit_trailing_synthesized_comment(&c);
        }
    }

    /// `p.emitTrailingSynthesizedComment`
    fn emit_trailing_synthesized_comment(&mut self, comment: &SynthesizedComment) {
        if !self.w().is_at_start_of_line() {
            self.w().write_space(" ");
        }
        self.write_synthesized_comment(comment);
        if comment.has_trailing_new_line {
            self.w().write_line();
        }
    }

    /// `p.writeSynthesizedComment`
    fn write_synthesized_comment(&mut self, comment: &SynthesizedComment) {
        let text = format_synthesized_comment(comment);
        let line_map: Vec<TextPos> = if comment.kind == Kind::MultiLineCommentTrivia {
            tsc_core::core::compute_ecma_line_starts(&text)
        } else {
            Vec::new()
        };
        self.write_comment_range_worker(
            &text,
            &line_map,
            comment.kind,
            TextRange::new(0, text.len() as i32),
        );
    }

    /// `p.emitLeadingComments`
    fn emit_leading_comments(&mut self, mut pos: i32, elided: bool) -> bool {
        // Emit the leading comments only if the container's pos doesn't match because the container should take care of emitting these comments
        if self.comments_disabled
            || self.p.current_source_file.is_none()
            || ast::position_is_synthesized(pos)
            || pos == self.container_pos
        {
            return false;
        }

        let mut triple_slash = Tristate::Unknown;
        if !elided {
            if pos == 0
                && self.p.nodes[self.p.current_source_file.unwrap()]
                    .as_source_file()
                    .is_declaration_file
            {
                triple_slash = Tristate::False;
            }
        } else if pos == 0 {
            // If the node will not be emitted in JS, remove all the comments(normal, pinned and ///) associated with the node,
            // unless it is a triple slash comment at the top of the file.
            // For Example:
            //      /// <reference-path ...>
            //      declare var x;
            //      /// <reference-path ...>
            //      interface F {}
            //  The first /// will NOT be removed while the second one will be removed even though both node will not be emitted
            triple_slash = Tristate::True;
        } else {
            return false;
        }

        // skip detached comments
        if let Some(info) = self.detached_comments_info.last()
            && info.node_pos == pos
        {
            pos = self
                .detached_comments_info
                .pop()
                .unwrap()
                .detached_comment_end_pos;
        }

        let source_file = self.p.current_source_file.unwrap();
        let text = self.p.nodes[source_file]
            .as_source_file()
            .text()
            .to_string();
        let mut comments: Vec<CommentRange> = Vec::new();
        for comment in
            scanner::get_leading_comment_ranges(&self.p.emit_context.factory.inner, &text, pos)
        {
            if self.should_write_comment(comment)
                && Self::should_emit_comment_if_triple_slash(
                    self.p.nodes,
                    source_file,
                    &comment,
                    triple_slash,
                )
            {
                comments.push(comment);
            }
        }

        if !comments.is_empty()
            && self.should_emit_new_line_before_leading_comment_of_position(
                pos,
                comments[0].text_range.pos(),
            )
        {
            self.write_line();
        }

        // Leading comments are emitted as /*leading comment1*/space/*leading comment*/space
        self.emit_comments(&comments, CommentSeparator::After)
    }

    /// `p.shouldEmitCommentIfTripleSlash`
    fn should_emit_comment_if_triple_slash(
        nodes: &[Node],
        source_file: NodeId,
        comment: &CommentRange,
        triple_slash: Tristate,
    ) -> bool {
        match triple_slash {
            Tristate::True => Self::is_triple_slash_comment(nodes, source_file, comment),
            Tristate::False => !Self::is_triple_slash_comment(nodes, source_file, comment),
            _ => true,
        }
    }

    /// `p.shouldEmitNewLineBeforeLeadingCommentOfPosition`
    fn should_emit_new_line_before_leading_comment_of_position(
        &mut self,
        pos: i32,
        comment_pos: i32,
    ) -> bool {
        // If the leading comments start on different line than the start of node, write new line
        self.p.current_source_file.is_some() && pos != comment_pos && {
            let line_map = self.p.nodes[self.p.current_source_file.unwrap()]
                .as_source_file()
                .ecma_line_map();
            scanner::compute_line_of_position(line_map, pos)
                != scanner::compute_line_of_position(line_map, comment_pos)
        }
    }

    /// `p.emitLeadingCommentsOfPosition`
    fn emit_leading_comments_of_position(&mut self, pos: i32) {
        if self.comments_disabled || pos == -1 {
            return;
        }

        self.emit_leading_comments(pos, false /*elided*/);
    }

    /// `p.emitTrailingComments`
    fn emit_trailing_comments(&mut self, pos: i32, comment_separator: CommentSeparator) {
        if self.comments_disabled {
            return;
        }
        // Emit the trailing comments only if the container's end doesn't match because the container should take care of emitting these comments
        if self.comments_disabled
            || self.p.current_source_file.is_none()
            || (self.container_end != -1
                && (pos == self.container_end || pos == self.declaration_list_container_end))
        {
            return;
        }

        let source_file = self.p.current_source_file.unwrap();
        let text = self.p.nodes[source_file]
            .as_source_file()
            .text()
            .to_string();
        let mut comments: Vec<CommentRange> = Vec::new();
        for comment in
            scanner::get_trailing_comment_ranges(&self.p.emit_context.factory.inner, &text, pos)
        {
            if self.should_write_comment(comment) {
                comments.push(comment);
            }
        }

        // trailing comments are normally emitted as space/*trailing comment1*/space/*trailing comment2*/
        self.emit_comments(&comments, comment_separator);
    }

    /// `p.emitTrailingCommentsOfPosition`
    fn emit_trailing_comments_of_position(
        &mut self,
        pos: i32,
        prefix_space: bool,
        force_no_newline: bool,
    ) {
        if self.comments_disabled || self.p.current_source_file.is_none() {
            return;
        }
        if self.container_end != -1
            && (pos == self.container_end || pos == self.declaration_list_container_end)
        {
            return;
        }

        let source_file = self.p.current_source_file.unwrap();
        let text = self.p.nodes[source_file]
            .as_source_file()
            .text()
            .to_string();
        let mut comments: Vec<CommentRange> = Vec::new();
        for comment in
            scanner::get_trailing_comment_ranges(&self.p.emit_context.factory.inner, &text, pos)
        {
            comments.push(comment);
        }
        if comments.is_empty() {
            return;
        }

        for comment in comments {
            if prefix_space {
                if !self.should_write_comment(comment) {
                    continue;
                }
                if !self.w().is_at_start_of_line() {
                    self.write_space();
                }
                self.emit_comment(&comment);
                if comment.has_trailing_new_line {
                    self.write_line();
                }
                continue;
            }

            self.emit_comment(&comment);
            if force_no_newline {
                if comment.kind == Kind::SingleLineCommentTrivia {
                    self.write_line();
                }
            } else if comment.has_trailing_new_line {
                self.write_line();
            } else {
                self.write_space();
            }
        }
    }

    /// `p.emitDetachedCommentsAndUpdateCommentsInfo`
    fn emit_detached_comments_and_update_comments_info(&mut self, text_range: TextRange) {
        if self.p.current_source_file.is_none() {
            return;
        }
        if let Some(current_detached_comment_info) = self.emit_detached_comments(text_range) {
            self.detached_comments_info
                .push(current_detached_comment_info);
        }
    }

    /// `p.emitDetachedComments`
    fn emit_detached_comments(&mut self, text_range: TextRange) -> Option<DetachedCommentsInfo> {
        let source_file = self.p.current_source_file?;

        let (text, line_map) = {
            let sf = self.p.nodes[source_file].as_source_file();
            (sf.text().to_string(), sf.ecma_line_map().to_vec())
        };

        let mut leading_comments: Vec<CommentRange> = Vec::new();
        if self.comments_disabled {
            // removeComments is true, only reserve pinned comment at the top of file
            // For example:
            //      /*! Pinned Comment */
            //
            //      var x = 10;
            if text_range.pos() == 0 {
                for comment in scanner::get_leading_comment_ranges(
                    &self.p.emit_context.factory.inner,
                    &text,
                    text_range.pos(),
                ) {
                    if util::is_pinned_comment(&text, comment) {
                        leading_comments.push(comment);
                    }
                }
            }
        } else {
            // removeComments is false, just get detached as normal and bypass the process to filter comment
            leading_comments = scanner::get_leading_comment_ranges(
                &self.p.emit_context.factory.inner,
                &text,
                text_range.pos(),
            );
        }

        if leading_comments.is_empty() {
            return None;
        }

        let mut detached_comments: Vec<CommentRange> = Vec::new();
        let mut last_comment = CommentRange::default();
        for (i, comment) in leading_comments.iter().enumerate() {
            if i > 0 {
                let last_comment_line =
                    scanner::compute_line_of_position(&line_map, last_comment.text_range.end());
                let comment_line =
                    scanner::compute_line_of_position(&line_map, comment.text_range.pos());

                if comment_line >= last_comment_line + 2 {
                    // There was a blank line between the last comment and this comment.  This
                    // comment is not part of the copyright comments.  Return what we have so
                    // far.
                    break;
                }
            }

            detached_comments.push(*comment);
            last_comment = *comment;
        }

        if detached_comments.is_empty() {
            return None;
        }

        // All comments look like they could have been part of the copyright header.  Make
        // sure there is at least one blank line between it and the node.  If not, it's not
        // a copyright header.
        let last_comment_line = scanner::compute_line_of_position(
            &line_map,
            detached_comments.last().unwrap().text_range.end(),
        );
        let node_line = scanner::compute_line_of_position(
            &line_map,
            scanner::skip_trivia(&text, text_range.pos()),
        );
        if node_line < last_comment_line + 2 {
            return None;
        }

        // Valid detachedComments

        // Filter to only comments that should be written (e.g., JSDoc-style in declaration emit)
        let comments_to_emit: Vec<CommentRange> = detached_comments
            .iter()
            .copied()
            .filter(|c| self.should_write_comment(*c))
            .collect();

        if !comments_to_emit.is_empty() {
            if self.should_emit_new_line_before_leading_comment_of_position(
                text_range.pos(),
                comments_to_emit[0].text_range.pos(),
            ) {
                self.write_line();
            }

            self.emit_comments(&comments_to_emit, CommentSeparator::After);
        }
        Some(DetachedCommentsInfo {
            node_pos: text_range.pos(),
            detached_comment_end_pos: detached_comments.last().unwrap().text_range.end(),
        })
    }

    /// `p.emitComments`
    fn emit_comments(
        &mut self,
        comments: &[CommentRange],
        comment_separator: CommentSeparator,
    ) -> bool {
        let mut intervening_separator = false;
        if comments.is_empty() {
            return false;
        }

        if comment_separator == CommentSeparator::Before {
            self.write_space();
        }

        for comment in comments {
            if intervening_separator {
                self.write_space();
                intervening_separator = false;
            }

            self.emit_comment(comment);

            if comment.kind == Kind::SingleLineCommentTrivia
                || (comment.has_trailing_new_line && comment_separator != CommentSeparator::None)
            {
                self.write_line();
            } else {
                intervening_separator = comment_separator != CommentSeparator::None;
            }
        }

        if intervening_separator && comment_separator == CommentSeparator::After {
            self.write_space();
        }

        true
    }

    /// `p.emitComment`
    fn emit_comment(&mut self, comment: &CommentRange) {
        self.emit_pos(comment.text_range.pos());
        self.write_comment_range(*comment);
        self.emit_pos(comment.text_range.end());
    }

    /// `p.isTripleSlashComment`
    fn is_triple_slash_comment(
        nodes: &[Node],
        source_file: NodeId,
        comment: &CommentRange,
    ) -> bool {
        util::is_recognized_triple_slash_comment(
            nodes[source_file].as_source_file().text(),
            *comment,
        )
    }

    //
    // Source Maps
    //

    /// `p.setSourceMapSource`
    fn set_source_map_source(&mut self, source: SourceMapSource) {
        if self.source_maps_disabled {
            return;
        }

        self.source_map_source = Some(source.clone());
        let (line_map, text) = match &source {
            SourceMapSource::Node(id) => {
                let sf = self.p.nodes[*id].as_source_file();
                (sf.ecma_line_map().to_vec(), sf.text().to_string())
            }
            SourceMapSource::Synthetic(s) => (s.line_map.clone(), s.text.clone()),
        };
        self.source_map_line_char_cache = Some(LineCharacterCache {
            line_map,
            text,
            cached_line: 0,
            cached_pos: 0,
            cached_char: 0,
            has_cached: false,
        });
        if self.p.most_recent_source_map_source.as_ref() == Some(&source) {
            self.source_map_source_index = self.p.most_recent_source_map_source_index;
            return;
        }

        self.source_map_source_is_json = source
            .file_name(self.p.nodes)
            .extension_is(tsc_tspath::EXTENSION_JSON);
        if self.source_map_source_is_json {
            return;
        }

        if let Some(generator) = self.source_map_generator.as_mut() {
            self.source_map_source_index =
                generator.add_source(source.file_name(self.p.nodes).clone());
            if self.p.options.inline_sources {
                let text = match &source {
                    SourceMapSource::Node(id) => {
                        self.p.nodes[*id].as_source_file().text().to_string()
                    }
                    SourceMapSource::Synthetic(s) => s.text.clone(),
                };
                generator
                    .set_source_content(self.source_map_source_index, &text)
                    .expect("SetSourceContent failed");
            }
        }

        self.p.most_recent_source_map_source = Some(source);
        self.p.most_recent_source_map_source_index = self.source_map_source_index;
    }

    /// `p.emitPos`
    fn emit_pos(&mut self, pos: i32) {
        if self.source_maps_disabled
            || self.source_map_source.is_none()
            || self.source_map_generator.is_none()
            || self.source_map_source_is_json
            || ast::position_is_synthesized(pos)
        {
            return;
        }

        let mut pos = pos;
        let source = self.source_map_source.clone().unwrap();
        let mut source_index = self.source_map_source_index;
        let mut mapped_line_char_cache: Option<LineCharacterCache> = None;
        if self.p.handlers.map_source_position.is_some() {
            let source_file_name = source.file_name(self.p.nodes).clone();
            let (mapped_source, mapped_pos) = self.p.handlers.map_source_position.as_mut().unwrap()(
                &source_file_name,
                source.clone(),
                pos,
            );
            if mapped_pos.is_none() {
                let line = self.w().get_line();
                let column = self.w().get_column();
                self.source_map_generator
                    .as_mut()
                    .unwrap()
                    .add_generated_mapping(line, column)
                    .expect("AddGeneratedMapping failed");
                return;
            }
            pos = mapped_pos.unwrap();
            if mapped_source.is_some() && mapped_source != Some(source) {
                let saved_source = self.source_map_source.clone();
                let saved_source_index = self.source_map_source_index;
                let saved_source_is_json = self.source_map_source_is_json;
                let saved_line_char_cache = self.source_map_line_char_cache.take();
                self.set_source_map_source(mapped_source.unwrap());
                source_index = self.source_map_source_index;
                // Go's `lineCharCache` local keeps pointing at the mapped
                // source's cache while the printer's state is restored —
                // the lookup below must use the mapped source's text.
                mapped_line_char_cache = self.source_map_line_char_cache.take();
                self.source_map_source = saved_source;
                self.source_map_source_index = saved_source_index;
                self.source_map_source_is_json = saved_source_is_json;
                self.source_map_line_char_cache = saved_line_char_cache;
            }
        }

        let (source_line, source_character) = mapped_line_char_cache
            .as_mut()
            .or(self.source_map_line_char_cache.as_mut())
            .expect("line char cache")
            .get_line_and_character(pos);
        let line = self.w().get_line();
        let column = self.w().get_column();
        self.source_map_generator
            .as_mut()
            .unwrap()
            .add_source_mapping(line, column, source_index, source_line, source_character)
            .expect("AddSourceMapping failed");
    }

    /// `p.emitSourcePos`
    fn emit_source_pos(&mut self, source: Option<SourceMapSource>, pos: i32) {
        if source != self.source_map_source {
            let saved_source_map_source = self.source_map_source.clone();
            let saved_source_map_source_index = self.source_map_source_index;
            let saved_source_map_line_char_cache = self.source_map_line_char_cache.take();
            if let Some(source) = source {
                self.set_source_map_source(source);
            }
            self.emit_pos(pos);
            self.source_map_source = saved_source_map_source;
            self.source_map_source_index = saved_source_map_source_index;
            self.source_map_line_char_cache = saved_source_map_line_char_cache;
        } else {
            self.emit_pos(pos);
        }
    }

    /// `p.emitSourceMapsBeforeNode`
    fn emit_source_maps_before_node(&mut self, node: NodeId) -> Option<SourceMapState> {
        if !self.should_emit_source_maps(node) {
            return None;
        }

        let emit_flags = self.p.emit_context.emit_flags(node);
        let loc = self.p.emit_context.source_map_range(self.p.nodes, node);

        if !ast::is_not_emitted_statement(&self.p.nodes[node])
            && emit_flags & EmitFlags::NO_LEADING_SOURCE_MAP == EmitFlags::NONE
            && self.p.current_source_file.is_some()
            && !ast::position_is_synthesized(loc.pos())
        {
            let pos = scanner::skip_trivia(
                self.p.nodes[self.p.current_source_file.unwrap()]
                    .as_source_file()
                    .text(),
                loc.pos(),
            );
            self.emit_source_pos(self.source_map_source.clone(), pos);
        }

        if emit_flags & EmitFlags::NO_NESTED_SOURCE_MAPS != EmitFlags::NONE {
            self.source_maps_disabled = true;
        }

        Some(SourceMapState {
            emit_flags,
            source_map_range: loc,
            has_token_source_map_range: false,
        })
    }

    /// `p.emitSourceMapsAfterNode`
    fn emit_source_maps_after_node(
        &mut self,
        node: NodeId,
        previous_state: Option<SourceMapState>,
    ) {
        let Some(previous_state) = previous_state else {
            return;
        };

        let emit_flags = previous_state.emit_flags;
        let loc = previous_state.source_map_range;

        if emit_flags & EmitFlags::NO_NESTED_SOURCE_MAPS != EmitFlags::NONE {
            self.source_maps_disabled = false;
        }

        if !ast::is_not_emitted_statement(&self.p.nodes[node])
            && emit_flags & EmitFlags::NO_TRAILING_SOURCE_MAP == EmitFlags::NONE
            && !ast::position_is_synthesized(loc.end())
        {
            self.emit_source_pos(self.source_map_source.clone(), loc.end());
        }
    }

    /// `p.emitSourceMapsBeforeToken`
    fn emit_source_maps_before_token(
        &mut self,
        token: Kind,
        pos: i32,
        context_node: NodeId,
        flags: TokenEmitFlags,
    ) -> Option<SourceMapState> {
        if !self.should_emit_token_source_maps(token, pos, context_node, flags) {
            return None;
        }

        let emit_flags = self.p.emit_context.emit_flags(context_node);
        let mut pos = pos;
        let token_loc = self
            .p
            .emit_context
            .token_source_map_range(context_node, token);
        let has_loc = token_loc.is_some();
        let loc = token_loc.unwrap_or_default();
        if let Some(token_loc) = token_loc {
            pos = token_loc.pos();
        }
        if pos >= 0 && self.p.current_source_file.is_some() {
            pos = scanner::skip_trivia(
                self.p.nodes[self.p.current_source_file.unwrap()]
                    .as_source_file()
                    .text(),
                pos,
            );
        }
        if emit_flags & EmitFlags::NO_TOKEN_LEADING_SOURCE_MAPS == EmitFlags::NONE && pos >= 0 {
            self.emit_source_pos(self.source_map_source.clone(), pos);
        }

        Some(SourceMapState {
            emit_flags,
            source_map_range: loc,
            has_token_source_map_range: has_loc,
        })
    }

    /// `p.emitSourceMapsAfterToken`
    fn emit_source_maps_after_token(
        &mut self,
        _token: Kind,
        pos: i32,
        _context_node: NodeId,
        previous_state: Option<SourceMapState>,
    ) {
        let Some(previous_state) = previous_state else {
            return;
        };

        let emit_flags = previous_state.emit_flags;
        let loc = previous_state.source_map_range;
        let has_loc = previous_state.has_token_source_map_range;
        let mut pos = pos;
        if emit_flags & EmitFlags::NO_TOKEN_TRAILING_SOURCE_MAPS == EmitFlags::NONE {
            if has_loc {
                pos = loc.end();
            }
            if pos >= 0 {
                self.emit_source_pos(self.source_map_source.clone(), pos);
            }
        }
    }

    //
    // Name Generation
    //

    /// `p.shouldReuseTempVariableScope`
    fn should_reuse_temp_variable_scope(&mut self, node: Option<NodeId>) -> bool {
        node.is_some_and(|node| {
            self.p
                .emit_context
                .emit_flags(node)
                .has(EmitFlags::REUSE_TEMP_VARIABLE_SCOPE)
        })
    }

    /// `p.pushNameGenerationScope`
    fn push_name_generation_scope(&mut self, node: NodeId) {
        let reuse = self.should_reuse_temp_variable_scope(Some(node));
        self.p.push_scope(reuse);
    }

    /// `p.popNameGenerationScope`
    fn pop_name_generation_scope(&mut self, node: NodeId) {
        let reuse = self.should_reuse_temp_variable_scope(Some(node));
        self.p.pop_scope(reuse);
    }

    /// `p.generateAllNames`
    fn generate_all_names(&mut self, nodes: Option<&NodeList>) {
        let Some(nodes) = nodes else {
            return;
        };
        for &node in &nodes.nodes {
            self.generate_names(Some(node));
        }
    }

    /// `p.generateNames`
    fn generate_names(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };

        match self.p.nodes[node].kind {
            Kind::Block | Kind::CaseClause | Kind::DefaultClause => {
                let statements = self.p.nodes[node].statement_list().cloned();
                self.generate_all_names(statements.as_ref());
            }
            Kind::LabeledStatement
            | Kind::WithStatement
            | Kind::DoStatement
            | Kind::WhileStatement => {
                let statement = self.p.nodes[node].statement();
                self.generate_names(statement);
            }
            Kind::IfStatement => {
                let (then_statement, else_statement) = {
                    let d = self.p.nodes[node].as_if_statement();
                    (d.then_statement, d.else_statement)
                };
                self.generate_names(then_statement);
                self.generate_names(else_statement);
            }
            Kind::ForStatement | Kind::ForOfStatement | Kind::ForInStatement => {
                let initializer = self.p.nodes[node].initializer();
                let statement = self.p.nodes[node].statement();
                self.generate_names(initializer);
                self.generate_names(statement);
            }
            Kind::SwitchStatement => {
                let case_block = self.p.nodes[node].as_switch_statement().case_block;
                self.generate_names(case_block);
            }
            Kind::CaseBlock => {
                let clauses = self.p.nodes[node].as_case_block().clauses.clone();
                self.generate_all_names(clauses.as_ref());
            }
            Kind::TryStatement => {
                let (try_block, catch_clause, finally_block) = {
                    let d = self.p.nodes[node].as_try_statement();
                    (d.try_block, d.catch_clause, d.finally_block)
                };
                self.generate_names(try_block);
                self.generate_names(catch_clause);
                self.generate_names(finally_block);
            }
            Kind::CatchClause => {
                let (variable_declaration, block) = {
                    let d = self.p.nodes[node].as_catch_clause();
                    (d.variable_declaration, d.block)
                };
                self.generate_names(variable_declaration);
                self.generate_names(block);
            }
            Kind::VariableStatement => {
                let declaration_list = self.p.nodes[node].as_variable_statement().declaration_list;
                self.generate_names(declaration_list);
            }
            Kind::VariableDeclarationList => {
                let declarations = self.p.nodes[node]
                    .as_variable_declaration_list()
                    .declarations
                    .clone();
                self.generate_all_names(declarations.as_ref());
            }
            Kind::VariableDeclaration
            | Kind::Parameter
            | Kind::BindingElement
            | Kind::ClassDeclaration => {
                let name = self.p.nodes[node].name();
                self.generate_name_if_needed(name);
            }
            Kind::FunctionDeclaration => {
                let name = self.p.nodes[node].name();
                self.generate_name_if_needed(name);
                if self.should_reuse_temp_variable_scope(Some(node)) {
                    let (parameters, body) = {
                        let d = self.p.nodes[node].as_function_declaration();
                        (
                            d.function_like_with_body_base
                                .function_like_base
                                .parameters
                                .clone(),
                            d.function_like_with_body_base.body_base.body,
                        )
                    };
                    self.generate_all_names(parameters.as_ref());
                    self.generate_names(body);
                }
            }
            Kind::ObjectBindingPattern | Kind::ArrayBindingPattern => {
                let elements = self.p.nodes[node].element_list().cloned();
                self.generate_all_names(elements.as_ref());
            }
            Kind::ImportDeclaration | Kind::JSImportDeclaration => {
                let import_clause = self.p.nodes[node].as_import_declaration().import_clause;
                self.generate_names(import_clause);
            }
            Kind::ImportClause => {
                let (name, named_bindings) = {
                    let d = self.p.nodes[node].as_import_clause();
                    (d.name, d.named_bindings)
                };
                self.generate_name_if_needed(name);
                self.generate_names(named_bindings);
            }
            Kind::NamespaceImport | Kind::NamespaceExport => {
                let name = self.p.nodes[node].name();
                self.generate_name_if_needed(name);
            }
            Kind::NamedImports => {
                let elements = self.p.nodes[node].element_list().cloned();
                self.generate_all_names(elements.as_ref());
            }
            Kind::ImportSpecifier => {
                let (property_name, name) = {
                    let d = self.p.nodes[node].as_import_specifier();
                    (d.property_name, d.name)
                };
                if property_name.is_some() {
                    self.generate_name_if_needed(property_name);
                } else {
                    self.generate_name_if_needed(name);
                }
            }
            _ => {}
        }
    }

    /// `p.generateAllMemberNames`
    fn generate_all_member_names(&mut self, nodes: Option<&NodeList>) {
        let Some(nodes) = nodes else {
            return;
        };
        for &node in &nodes.nodes {
            self.generate_member_names(Some(node));
        }
    }

    /// `p.generateMemberNames`
    fn generate_member_names(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        match self.p.nodes[node].kind {
            Kind::PropertyAssignment
            | Kind::ShorthandPropertyAssignment
            | Kind::PropertyDeclaration
            | Kind::PropertySignature
            | Kind::MethodDeclaration
            | Kind::MethodSignature
            | Kind::GetAccessor
            | Kind::SetAccessor => {
                let name = self.p.nodes[node].name();
                self.generate_name_if_needed(name);
            }
            _ => {}
        }
    }

    /// `p.generateNameIfNeeded`
    fn generate_name_if_needed(&mut self, name: Option<NodeId>) {
        if let Some(name) = name {
            if ast::is_member_name(&self.p.nodes[name]) {
                self.generate_name(name);
            } else if ast::is_binding_pattern(&self.p.nodes[name]) {
                self.generate_names(Some(name));
            }
        }
    }

    /// `p.generateName` — generate the text for a generated identifier or
    /// private identifier.
    fn generate_name(&mut self, name: NodeId) {
        let _ = self.p.generate_name_text(name);
    }

    //
    // Scoped operations
    //

    /// `p.enterNode`
    fn enter_node(&mut self, node: NodeId) -> PrinterState {
        let mut state = PrinterState::default();

        if let Some(h) = self.p.handlers.on_before_emit_node.as_mut() {
            h(Some(node));
        }

        state.comment_state = self.emit_comments_before_node(node);
        state.source_map_state = self.emit_source_maps_before_node(node);
        state
    }

    /// `p.exitNode`
    fn exit_node(&mut self, node: NodeId, previous_state: PrinterState) {
        self.emit_source_maps_after_node(node, previous_state.source_map_state);
        self.emit_comments_after_node(node, previous_state.comment_state);

        if let Some(h) = self.p.handlers.on_after_emit_node.as_mut() {
            h(Some(node));
        }
    }

    /// `p.enterTokenNode`
    fn enter_token_node(&mut self, node: NodeId, flags: TokenEmitFlags) -> PrinterState {
        let mut state = PrinterState::default();

        if let Some(h) = self.p.handlers.on_before_emit_token.as_mut() {
            h(Some(node));
        }

        if flags & TEF_NO_COMMENTS == 0 {
            state.comment_state = self.emit_comments_before_node(node);
        }
        if flags & TEF_NO_SOURCE_MAPS == 0 {
            state.source_map_state = self.emit_source_maps_before_node(node);
        }
        state
    }

    /// `p.exitTokenNode`
    fn exit_token_node(&mut self, node: NodeId, previous_state: PrinterState) {
        self.emit_source_maps_after_node(node, previous_state.source_map_state);
        self.emit_comments_after_node(node, previous_state.comment_state);

        if let Some(h) = self.p.handlers.on_after_emit_token.as_mut() {
            h(Some(node));
        }
    }

    /// `p.enterToken`
    fn enter_token(
        &mut self,
        token: Kind,
        pos: i32,
        context_node: NodeId,
        flags: TokenEmitFlags,
    ) -> (PrinterState, i32) {
        let mut state = PrinterState::default();
        let (comment_state, pos) = self.emit_comments_before_token(token, pos, context_node, flags);
        state.comment_state = comment_state;
        state.source_map_state =
            self.emit_source_maps_before_token(token, pos, context_node, flags);
        (state, pos)
    }

    /// `p.exitToken`
    fn exit_token(
        &mut self,
        token: Kind,
        pos: i32,
        context_node: NodeId,
        previous_state: PrinterState,
    ) {
        self.emit_source_maps_after_token(
            token,
            pos,
            context_node,
            previous_state.source_map_state,
        );
        self.emit_comments_after_token(token, pos, context_node, previous_state.comment_state);
    }
}

/// `type ListFormat int`
pub(crate) type ListFormat = u32;

// Line separators
/// `LFSingleLine` — prints the list on a single line (default).
pub(crate) const LF_SINGLE_LINE: ListFormat = 0;
/// `LFMultiLine` — prints the list on multiple lines.
pub(crate) const LF_MULTI_LINE: ListFormat = 1 << 0;
/// `LFPreserveLines` — prints the list using line preservation if possible.
pub(crate) const LF_PRESERVE_LINES: ListFormat = 1 << 1;
/// `LFLinesMask`
pub(crate) const LF_LINES_MASK: ListFormat = LF_SINGLE_LINE | LF_MULTI_LINE | LF_PRESERVE_LINES;

// Delimiters
/// `LFNotDelimited` — there is no delimiter between list items (default).
pub(crate) const LF_NOT_DELIMITED: ListFormat = 0;
/// `LFBarDelimited` — each list item is space-and-bar (" |") delimited.
pub(crate) const LF_BAR_DELIMITED: ListFormat = 1 << 2;
/// `LFAmpersandDelimited` — each list item is space-and-ampersand (" &")
/// delimited.
pub(crate) const LF_AMPERSAND_DELIMITED: ListFormat = 1 << 3;
/// `LFCommaDelimited` — each list item is comma (",") delimited.
pub(crate) const LF_COMMA_DELIMITED: ListFormat = 1 << 4;
/// `LFAsteriskDelimited` — each list item is asterisk ("\n *") delimited, used
/// with JSDoc.
pub(crate) const LF_ASTERISK_DELIMITED: ListFormat = 1 << 5;
/// `LFDelimitersMask`
pub(crate) const LF_DELIMITERS_MASK: ListFormat =
    LF_BAR_DELIMITED | LF_AMPERSAND_DELIMITED | LF_COMMA_DELIMITED | LF_ASTERISK_DELIMITED;

/// `LFAllowTrailingComma` — write a trailing comma (",") if present.
pub(crate) const LF_ALLOW_TRAILING_COMMA: ListFormat = 1 << 6;

// Whitespace
/// `LFIndented` — the list should be indented.
pub(crate) const LF_INDENTED: ListFormat = 1 << 7;
/// `LFSpaceBetweenBraces` — inserts a space after the opening brace and before
/// the closing brace.
pub(crate) const LF_SPACE_BETWEEN_BRACES: ListFormat = 1 << 8;
/// `LFSpaceBetweenSiblings` — inserts a space between each sibling node.
pub(crate) const LF_SPACE_BETWEEN_SIBLINGS: ListFormat = 1 << 9;

// Brackets/Braces
/// `LFBraces` — the list is surrounded by "{" and "}".
pub(crate) const LF_BRACES: ListFormat = 1 << 10;
/// `LFParenthesis` — the list is surrounded by "(" and ")".
pub(crate) const LF_PARENTHESIS: ListFormat = 1 << 11;
/// `LFAngleBrackets` — the list is surrounded by "<" and ">".
pub(crate) const LF_ANGLE_BRACKETS: ListFormat = 1 << 12;
/// `LFSquareBrackets` — the list is surrounded by "[" and "]".
pub(crate) const LF_SQUARE_BRACKETS: ListFormat = 1 << 13;
/// `LFBracketsMask`
pub(crate) const LF_BRACKETS_MASK: ListFormat =
    LF_BRACES | LF_PARENTHESIS | LF_ANGLE_BRACKETS | LF_SQUARE_BRACKETS;

/// `LFOptionalIfNil` — do not emit brackets if the list is nil.
pub(crate) const LF_OPTIONAL_IF_NIL: ListFormat = 1 << 14;
/// `LFOptionalIfEmpty` — do not emit brackets if the list is empty.
pub(crate) const LF_OPTIONAL_IF_EMPTY: ListFormat = 1 << 15;
/// `LFOptional`
pub(crate) const LF_OPTIONAL: ListFormat = LF_OPTIONAL_IF_NIL | LF_OPTIONAL_IF_EMPTY;

// Other
/// `LFPreferNewLine` — prefer adding a LineTerminator between synthesized nodes.
pub(crate) const LF_PREFER_NEW_LINE: ListFormat = 1 << 16;
/// `LFNoTrailingNewLine` — do not emit a trailing NewLine for a MultiLine list.
pub(crate) const LF_NO_TRAILING_NEW_LINE: ListFormat = 1 << 17;
/// `LFNoInterveningComments` — do not emit comments between each node.
pub(crate) const LF_NO_INTERVENING_COMMENTS: ListFormat = 1 << 18;
/// `LFNoSpaceIfEmpty` — if the literal is empty, do not add spaces between
/// braces.
pub(crate) const LF_NO_SPACE_IF_EMPTY: ListFormat = 1 << 19;
/// `LFSingleElement`
pub(crate) const LF_SINGLE_ELEMENT: ListFormat = 1 << 20;
/// `LFSpaceAfterList` — add space after list.
pub(crate) const LF_SPACE_AFTER_LIST: ListFormat = 1 << 21;

/// `LFNone`
pub(crate) const LF_NONE: ListFormat = 0;

// Precomputed Formats
/// `LFModifiers`
pub(crate) const LF_MODIFIERS: ListFormat =
    LF_SINGLE_LINE | LF_SPACE_BETWEEN_SIBLINGS | LF_NO_INTERVENING_COMMENTS | LF_SPACE_AFTER_LIST;
/// `LFHeritageClauses`
pub(crate) const LF_HERITAGE_CLAUSES: ListFormat = LF_SINGLE_LINE | LF_SPACE_BETWEEN_SIBLINGS;
/// `LFSingleLineTypeLiteralMembers`
pub(crate) const LF_SINGLE_LINE_TYPE_LITERAL_MEMBERS: ListFormat =
    LF_SINGLE_LINE | LF_SPACE_BETWEEN_BRACES | LF_SPACE_BETWEEN_SIBLINGS;
/// `LFMultiLineTypeLiteralMembers`
pub(crate) const LF_MULTI_LINE_TYPE_LITERAL_MEMBERS: ListFormat =
    LF_MULTI_LINE | LF_INDENTED | LF_OPTIONAL_IF_EMPTY;
/// `LFSingleLineTupleTypeElements`
pub(crate) const LF_SINGLE_LINE_TUPLE_TYPE_ELEMENTS: ListFormat =
    LF_COMMA_DELIMITED | LF_SPACE_BETWEEN_SIBLINGS | LF_SINGLE_LINE;
/// `LFMultiLineTupleTypeElements`
pub(crate) const LF_MULTI_LINE_TUPLE_TYPE_ELEMENTS: ListFormat =
    LF_COMMA_DELIMITED | LF_INDENTED | LF_SPACE_BETWEEN_SIBLINGS | LF_MULTI_LINE;
/// `LFUnionTypeConstituents`
pub(crate) const LF_UNION_TYPE_CONSTITUENTS: ListFormat =
    LF_BAR_DELIMITED | LF_SPACE_BETWEEN_SIBLINGS | LF_SINGLE_LINE;
/// `LFIntersectionTypeConstituents`
pub(crate) const LF_INTERSECTION_TYPE_CONSTITUENTS: ListFormat =
    LF_AMPERSAND_DELIMITED | LF_SPACE_BETWEEN_SIBLINGS | LF_SINGLE_LINE;
/// `LFObjectBindingPatternElements`
pub(crate) const LF_OBJECT_BINDING_PATTERN_ELEMENTS: ListFormat = LF_SINGLE_LINE
    | LF_ALLOW_TRAILING_COMMA
    | LF_SPACE_BETWEEN_BRACES
    | LF_COMMA_DELIMITED
    | LF_SPACE_BETWEEN_SIBLINGS
    | LF_NO_SPACE_IF_EMPTY;
/// `LFArrayBindingPatternElements`
pub(crate) const LF_ARRAY_BINDING_PATTERN_ELEMENTS: ListFormat = LF_SINGLE_LINE
    | LF_ALLOW_TRAILING_COMMA
    | LF_COMMA_DELIMITED
    | LF_SPACE_BETWEEN_SIBLINGS
    | LF_NO_SPACE_IF_EMPTY;
/// `LFObjectLiteralExpressionProperties`
pub(crate) const LF_OBJECT_LITERAL_EXPRESSION_PROPERTIES: ListFormat = LF_PRESERVE_LINES
    | LF_COMMA_DELIMITED
    | LF_SPACE_BETWEEN_SIBLINGS
    | LF_SPACE_BETWEEN_BRACES
    | LF_INDENTED
    | LF_BRACES
    | LF_NO_SPACE_IF_EMPTY;
/// `LFImportAttributes`
pub(crate) const LF_IMPORT_ATTRIBUTES: ListFormat = LF_PRESERVE_LINES
    | LF_COMMA_DELIMITED
    | LF_SPACE_BETWEEN_SIBLINGS
    | LF_SPACE_BETWEEN_BRACES
    | LF_INDENTED
    | LF_BRACES
    | LF_NO_SPACE_IF_EMPTY;
/// `LFArrayLiteralExpressionElements`
pub(crate) const LF_ARRAY_LITERAL_EXPRESSION_ELEMENTS: ListFormat = LF_PRESERVE_LINES
    | LF_COMMA_DELIMITED
    | LF_SPACE_BETWEEN_SIBLINGS
    | LF_ALLOW_TRAILING_COMMA
    | LF_INDENTED
    | LF_SQUARE_BRACKETS;
/// `LFCommaListElements`
pub(crate) const LF_COMMA_LIST_ELEMENTS: ListFormat =
    LF_COMMA_DELIMITED | LF_SPACE_BETWEEN_SIBLINGS | LF_SINGLE_LINE;
/// `LFCallExpressionArguments`
pub(crate) const LF_CALL_EXPRESSION_ARGUMENTS: ListFormat =
    LF_COMMA_DELIMITED | LF_SPACE_BETWEEN_SIBLINGS | LF_SINGLE_LINE | LF_PARENTHESIS;
/// `LFNewExpressionArguments`
pub(crate) const LF_NEW_EXPRESSION_ARGUMENTS: ListFormat = LF_COMMA_DELIMITED
    | LF_SPACE_BETWEEN_SIBLINGS
    | LF_SINGLE_LINE
    | LF_PARENTHESIS
    | LF_OPTIONAL_IF_NIL;
/// `LFTemplateExpressionSpans`
pub(crate) const LF_TEMPLATE_EXPRESSION_SPANS: ListFormat =
    LF_SINGLE_LINE | LF_NO_INTERVENING_COMMENTS;
/// `LFSingleLineBlockStatements`
pub(crate) const LF_SINGLE_LINE_BLOCK_STATEMENTS: ListFormat =
    LF_SPACE_BETWEEN_BRACES | LF_SPACE_BETWEEN_SIBLINGS | LF_SINGLE_LINE;
/// `LFMultiLineBlockStatements`
pub(crate) const LF_MULTI_LINE_BLOCK_STATEMENTS: ListFormat = LF_INDENTED | LF_MULTI_LINE;
/// `LFVariableDeclarationList`
pub(crate) const LF_VARIABLE_DECLARATION_LIST: ListFormat =
    LF_COMMA_DELIMITED | LF_SPACE_BETWEEN_SIBLINGS | LF_SINGLE_LINE;
/// `LFSingleLineFunctionBodyStatements`
pub(crate) const LF_SINGLE_LINE_FUNCTION_BODY_STATEMENTS: ListFormat =
    LF_SINGLE_LINE | LF_SPACE_BETWEEN_SIBLINGS | LF_SPACE_BETWEEN_BRACES;
/// `LFMultiLineFunctionBodyStatements`
pub(crate) const LF_MULTI_LINE_FUNCTION_BODY_STATEMENTS: ListFormat = LF_MULTI_LINE;
/// `LFClassHeritageClauses`
pub(crate) const LF_CLASS_HERITAGE_CLAUSES: ListFormat = LF_SINGLE_LINE;
/// `LFClassMembers`
pub(crate) const LF_CLASS_MEMBERS: ListFormat = LF_INDENTED | LF_MULTI_LINE;
/// `LFInterfaceMembers`
pub(crate) const LF_INTERFACE_MEMBERS: ListFormat = LF_INDENTED | LF_MULTI_LINE;
/// `LFEnumMembers`
pub(crate) const LF_ENUM_MEMBERS: ListFormat = LF_COMMA_DELIMITED | LF_INDENTED | LF_MULTI_LINE;
/// `LFCaseBlockClauses`
pub(crate) const LF_CASE_BLOCK_CLAUSES: ListFormat = LF_INDENTED | LF_MULTI_LINE;
/// `LFNamedImportsOrExportsElements`
pub(crate) const LF_NAMED_IMPORTS_OR_EXPORTS_ELEMENTS: ListFormat = LF_COMMA_DELIMITED
    | LF_SPACE_BETWEEN_SIBLINGS
    | LF_ALLOW_TRAILING_COMMA
    | LF_SINGLE_LINE
    | LF_SPACE_BETWEEN_BRACES
    | LF_NO_SPACE_IF_EMPTY;
/// `LFJsxElementOrFragmentChildren`
pub(crate) const LF_JSX_ELEMENT_OR_FRAGMENT_CHILDREN: ListFormat =
    LF_SINGLE_LINE | LF_NO_INTERVENING_COMMENTS;
/// `LFJsxElementAttributes`
pub(crate) const LF_JSX_ELEMENT_ATTRIBUTES: ListFormat =
    LF_SINGLE_LINE | LF_SPACE_BETWEEN_SIBLINGS | LF_NO_INTERVENING_COMMENTS;
/// `LFCaseOrDefaultClauseStatements`
pub(crate) const LF_CASE_OR_DEFAULT_CLAUSE_STATEMENTS: ListFormat =
    LF_INDENTED | LF_MULTI_LINE | LF_NO_TRAILING_NEW_LINE | LF_OPTIONAL_IF_EMPTY;
/// `LFHeritageClauseTypes`
pub(crate) const LF_HERITAGE_CLAUSE_TYPES: ListFormat =
    LF_COMMA_DELIMITED | LF_SPACE_BETWEEN_SIBLINGS | LF_SINGLE_LINE;
/// `LFSourceFileStatements`
pub(crate) const LF_SOURCE_FILE_STATEMENTS: ListFormat = LF_MULTI_LINE | LF_NO_TRAILING_NEW_LINE;
/// `LFDecorators`
pub(crate) const LF_DECORATORS: ListFormat = LF_MULTI_LINE | LF_OPTIONAL | LF_SPACE_AFTER_LIST;
/// `LFTypeArguments`
pub(crate) const LF_TYPE_ARGUMENTS: ListFormat = LF_COMMA_DELIMITED
    | LF_SPACE_BETWEEN_SIBLINGS
    | LF_SINGLE_LINE
    | LF_ANGLE_BRACKETS
    | LF_OPTIONAL;
/// `LFTypeParameters`
pub(crate) const LF_TYPE_PARAMETERS: ListFormat = LF_COMMA_DELIMITED
    | LF_SPACE_BETWEEN_SIBLINGS
    | LF_SINGLE_LINE
    | LF_ANGLE_BRACKETS
    | LF_OPTIONAL;
/// `LFParameters`
pub(crate) const LF_PARAMETERS: ListFormat =
    LF_COMMA_DELIMITED | LF_SPACE_BETWEEN_SIBLINGS | LF_SINGLE_LINE | LF_PARENTHESIS;
/// `LFSingleArrowParameter`
pub(crate) const LF_SINGLE_ARROW_PARAMETER: ListFormat =
    LF_COMMA_DELIMITED | LF_SPACE_BETWEEN_SIBLINGS | LF_SINGLE_LINE;
/// `LFIndexSignatureParameters`
pub(crate) const LF_INDEX_SIGNATURE_PARAMETERS: ListFormat = LF_COMMA_DELIMITED
    | LF_SPACE_BETWEEN_SIBLINGS
    | LF_SINGLE_LINE
    | LF_INDENTED
    | LF_SQUARE_BRACKETS;
/// `LFJSDocComment`
pub(crate) const LF_JS_DOC_COMMENT: ListFormat = LF_MULTI_LINE | LF_ASTERISK_DELIMITED;
/// `LFImportClauseEntries` — deprecated: use [`LF_IMPORT_ATTRIBUTES`].
#[allow(dead_code)]
pub(crate) const LF_IMPORT_CLAUSE_ENTRIES: ListFormat = LF_IMPORT_ATTRIBUTES;

/// `getOpeningBracket`
fn get_opening_bracket(format: ListFormat) -> &'static str {
    match format & LF_BRACKETS_MASK {
        LF_BRACES => "{",
        LF_PARENTHESIS => "(",
        LF_ANGLE_BRACKETS => "<",
        LF_SQUARE_BRACKETS => "[",
        _ => panic!("Unexpected bracket: {}", format & LF_BRACKETS_MASK),
    }
}

/// `getClosingBracket`
fn get_closing_bracket(format: ListFormat) -> &'static str {
    match format & LF_BRACKETS_MASK {
        LF_BRACES => "}",
        LF_PARENTHESIS => ")",
        LF_ANGLE_BRACKETS => ">",
        LF_SQUARE_BRACKETS => "]",
        _ => panic!("Unexpected bracket: {}", format & LF_BRACKETS_MASK),
    }
}

/// `canEmitSimpleArrowHead`
fn can_emit_simple_arrow_head(
    nodes: &[Node],
    parent_node: NodeId,
    parameters: Option<&NodeList>,
) -> bool {
    // only arrow functions with a single parameter may have simple arrow head
    let Some(parameters) = parameters else {
        return false;
    };
    if !ast::is_arrow_function(&nodes[parent_node]) || parameters.nodes.len() != 1 {
        return false;
    }

    let parent = nodes[parent_node].as_arrow_function();
    let parameter = nodes[parameters.nodes[0]].as_parameter_declaration();

    nodes[parameters.nodes[0]].loc.pos() == nodes[parent_node].loc.pos() && // may not have parsed tokens between start of parent and parameter
        parent.function_like_with_body_base.function_like_base.type_parameters.is_none() && // parent may not have type parameters
        parent.function_like_with_body_base.function_like_base.type_.is_none() && // parent may not have return type annotation
        parent.modifiers_base.modifiers.as_ref().is_none_or(|m| m.nodes.is_empty()) && // parent may not have modifiers
        !parameters.has_trailing_comma(nodes) && // parameters may not have a trailing comma
        parameter.modifiers_base.modifiers.is_none() && // parameter may not have decorators or modifiers
        parameter.dot_dot_dot_token.is_none() && // parameter may not be rest
        parameter.question_token.is_none() && // parameter may not be optional
        parameter.type_.is_none() && // parameter may not have a type annotation
        parameter.initializer.is_none() && // parameter may not have an initializer
        parameter.name.is_some_and(|n| ast::is_identifier(&nodes[n])) // parameter name must be identifier
}

/// `formatSynthesizedComment`
fn format_synthesized_comment(comment: &SynthesizedComment) -> String {
    if comment.kind == Kind::MultiLineCommentTrivia {
        return format!("/*{}*/", comment.text);
    }
    format!("//{}", comment.text)
}
