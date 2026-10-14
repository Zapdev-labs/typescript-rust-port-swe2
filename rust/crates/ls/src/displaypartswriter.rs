// Ported from tsc/internal/ls/displaypartswriter.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `displayPartsWriter` implements the printer `EmitTextWriter` trait so
// a `printer.Printer` can print directly into it. `WriteSymbol` in Go receives
// `*ast.Symbol`; here it receives `SymbolId`, which cannot resolve
// `symbol.Flags`/`symbol.Declarations` on its own, so the writer retains the
// checker's shared symbol arena plus the program (needed to read the first
// declaration's node `Kind`, which may live in a different file arena).

use std::rc::Rc;

use tsc_ast::{Kind, SymbolArena, SymbolFlags, SymbolId};
use tsc_checker::checker_core::Checker;
use tsc_compiler::program::Program;
use tsc_core::core::UTF16Offset;
use tsc_lsproto as lsproto;
use tsc_printer::EmitTextWriter;
use tsc_stringutil::is_white_space_like;

/// `type displayPartsWriter struct`.
///
/// Implements `EmitTextWriter` and captures classified text runs for VS
/// colorized labels, while also building a plain string. When `vs_capability`
/// is false, only the plain string is built; runs are skipped.
pub(crate) struct DisplayPartsWriter {
    /// `builder`.
    builder: String,
    /// `runs`.
    runs: Vec<lsproto::VSClassifiedTextRun>,
    /// `vsCapability`.
    vs_capability: bool,
    /// `lastWritten`.
    last_written: String,
    /// Shared symbol arena used to implement `classificationForSymbol`
    /// (`c.symbol_arena`). PORT: Go's `WriteSymbol` receives a symbol pointer;
    /// the port receives `SymbolId`, so the writer keeps arena access.
    symbols: SymbolArena,
    /// Program used to read `symbol.Declarations[0].Kind` in the owning
    /// file's node arena.
    program: Rc<Program>,
}

/// `newDisplayPartsWriter`.
pub(crate) fn new_display_parts_writer(
    vs_capability: bool,
    c: &Checker,
    program: &Rc<Program>,
) -> DisplayPartsWriter {
    DisplayPartsWriter {
        builder: String::new(),
        runs: Vec::new(),
        vs_capability,
        last_written: String::new(),
        symbols: c.symbol_arena.clone(),
        program: program.clone(),
    }
}

impl DisplayPartsWriter {
    /// `addRun`.
    fn add_run(&mut self, classification: lsproto::ClassificationTypeName, text: &str) {
        if text.is_empty() {
            return;
        }
        if self.vs_capability {
            self.runs.push(lsproto::VSClassifiedTextRun {
                classification_type_name: classification.to_string(),
                text: text.to_string(),
                ..Default::default()
            });
        }
        self.last_written = text.to_string();
        self.builder.push_str(text);
    }

    /// `WriteClassified` — writes text with an explicit classification type.
    pub(crate) fn write_classified(
        &mut self,
        text: &str,
        classification: lsproto::ClassificationTypeName,
    ) {
        self.add_run(classification, text);
    }

    /// `WriteFrom` — copies the accumulated content from another
    /// `DisplayPartsWriter`.
    pub(crate) fn write_from(&mut self, other: &DisplayPartsWriter) {
        self.builder.push_str(&other.builder);
        if self.vs_capability {
            self.runs.extend(other.runs.iter().cloned());
        }
        if !other.last_written.is_empty() {
            self.last_written = other.last_written.clone();
        }
    }

    /// `GetRuns`.
    pub(crate) fn get_runs(&self) -> &[lsproto::VSClassifiedTextRun] {
        &self.runs
    }

    /// `runs` as an `Option` for serialization: `None` mirrors Go's nil slice.
    pub(crate) fn runs_opt(&self) -> Option<Vec<lsproto::VSClassifiedTextRun>> {
        if self.runs.is_empty() {
            None
        } else {
            Some(self.runs.clone())
        }
    }

    /// `String`.
    pub(crate) fn string(&self) -> &str {
        &self.builder
    }

    /// `HasTrailingWhitespace`.
    ///
    /// PORT: `utf8.DecodeLastRuneInString` returns `RuneError` for the empty
    /// string or invalid UTF-8; Rust strings are always valid UTF-8, and
    /// `chars().last()` returns `None` on empty — both map to `false` here
    /// exactly as Go's `ch == utf8.RuneError` check does.
    pub(crate) fn has_trailing_whitespace(&self) -> bool {
        if self.builder.is_empty() {
            return false;
        }
        let Some(ch) = self.last_written.chars().last() else {
            return false;
        };
        is_white_space_like(ch)
    }
}

/// `displayPartsWriter` implements `EmitTextWriter`.
impl EmitTextWriter for DisplayPartsWriter {
    /// `Write`.
    fn write(&mut self, s: &str) {
        self.add_run(lsproto::ClassificationTypeName::Text, s);
    }

    /// `WriteTrailingSemicolon`.
    fn write_trailing_semicolon(&mut self, text: &str) {
        self.add_run(lsproto::ClassificationTypeName::Punctuation, text);
    }

    /// `WriteComment` — Strada's writeComment uses unknownWrite →
    /// `SymbolDisplayPartKind.text` → "text".
    fn write_comment(&mut self, text: &str) {
        self.add_run(lsproto::ClassificationTypeName::Text, text);
    }

    /// `WriteKeyword`.
    fn write_keyword(&mut self, text: &str) {
        self.add_run(lsproto::ClassificationTypeName::Keyword, text);
    }

    /// `WriteOperator`.
    fn write_operator(&mut self, text: &str) {
        self.add_run(lsproto::ClassificationTypeName::Operator, text);
    }

    /// `WritePunctuation`.
    fn write_punctuation(&mut self, text: &str) {
        self.add_run(lsproto::ClassificationTypeName::Punctuation, text);
    }

    /// `WriteSpace`.
    fn write_space(&mut self, text: &str) {
        self.add_run(lsproto::ClassificationTypeName::WhiteSpace, text);
    }

    /// `WriteStringLiteral`.
    fn write_string_literal(&mut self, text: &str) {
        self.add_run(lsproto::ClassificationTypeName::String, text);
    }

    /// `WriteParameter`.
    fn write_parameter(&mut self, text: &str) {
        self.add_run(lsproto::ClassificationTypeName::ParameterName, text);
    }

    /// `WriteProperty`.
    fn write_property(&mut self, text: &str) {
        self.add_run(lsproto::ClassificationTypeName::PropertyName, text);
    }

    /// `WriteSymbol`.
    fn write_symbol(&mut self, text: &str, symbol: SymbolId) {
        let classification = self.classification_for_symbol(Some(symbol));
        self.add_run(classification, text);
    }

    /// `WriteLine`.
    fn write_line(&mut self) {
        self.add_run(lsproto::ClassificationTypeName::WhiteSpace, " ");
    }

    /// `WriteLineForce`.
    fn write_line_force(&mut self, force: bool) {
        // PORT(ignore): `force` is ignored, exactly as in Go.
        let _ = force;
        self.add_run(lsproto::ClassificationTypeName::WhiteSpace, " ");
    }

    /// `IncreaseIndent` — no-op.
    fn increase_indent(&mut self) {}

    /// `DecreaseIndent` — no-op.
    fn decrease_indent(&mut self) {}

    /// `Clear`.
    fn clear(&mut self) {
        self.last_written.clear();
        self.builder.clear();
        self.runs.clear();
    }

    /// `String`.
    fn get_text(&self) -> String {
        self.builder.clone()
    }

    /// `RawWrite`.
    fn raw_write(&mut self, s: &str) {
        self.add_run(lsproto::ClassificationTypeName::Text, s);
    }

    /// `WriteLiteral` — Strada's writeLiteral →
    /// `SymbolDisplayPartKind.stringLiteral` → "string".
    fn write_literal(&mut self, s: &str) {
        self.add_run(lsproto::ClassificationTypeName::String, s);
    }

    /// `GetTextPos`.
    fn get_text_pos(&self) -> i32 {
        self.builder.len() as i32
    }

    /// `GetLine`.
    fn get_line(&self) -> i32 {
        0
    }

    /// `GetColumn`.
    fn get_column(&self) -> UTF16Offset {
        0
    }

    /// `GetIndent`.
    fn get_indent(&self) -> i32 {
        0
    }

    /// `IsAtStartOfLine` — Go returns `false` unconditionally.
    fn is_at_start_of_line(&self) -> bool {
        false
    }

    /// `HasTrailingComment`.
    fn has_trailing_comment(&self) -> bool {
        false
    }

    /// `HasTrailingWhitespace`.
    fn has_trailing_whitespace(&self) -> bool {
        DisplayPartsWriter::has_trailing_whitespace(self)
    }
}

impl DisplayPartsWriter {
    /// `classificationForSymbol` determines the Roslyn classification type
    /// name based on a symbol's flags. Matches the Strada translation chain:
    /// `displayPartKind()` → `GetClassificationName()`.
    pub(crate) fn classification_for_symbol(
        &self,
        symbol: Option<SymbolId>,
    ) -> lsproto::ClassificationTypeName {
        let Some(symbol) = symbol else {
            return lsproto::ClassificationTypeName::Text;
        };
        let flags = {
            let arena = self.symbols.clone();
            arena[symbol.index()].flags
        };
        if flags.intersects(SymbolFlags::VARIABLE) {
            if self.is_first_declaration_of_symbol_parameter(symbol) {
                return lsproto::ClassificationTypeName::ParameterName;
            }
            return lsproto::ClassificationTypeName::LocalName;
        }
        if flags.intersects(SymbolFlags::PROPERTY) {
            return lsproto::ClassificationTypeName::PropertyName;
        }
        if flags.intersects(SymbolFlags::GET_ACCESSOR) {
            return lsproto::ClassificationTypeName::PropertyName;
        }
        if flags.intersects(SymbolFlags::SET_ACCESSOR) {
            return lsproto::ClassificationTypeName::PropertyName;
        }
        if flags.intersects(SymbolFlags::ENUM_MEMBER) {
            return lsproto::ClassificationTypeName::FieldName;
        }
        if flags.intersects(SymbolFlags::FUNCTION) {
            return lsproto::ClassificationTypeName::MethodName;
        }
        if flags.intersects(SymbolFlags::CLASS) {
            return lsproto::ClassificationTypeName::ClassName;
        }
        if flags.intersects(SymbolFlags::INTERFACE) {
            return lsproto::ClassificationTypeName::InterfaceName;
        }
        if flags.intersects(SymbolFlags::ENUM) {
            return lsproto::ClassificationTypeName::EnumName;
        }
        if flags.intersects(SymbolFlags::MODULE) {
            return lsproto::ClassificationTypeName::ModuleName;
        }
        if flags.intersects(SymbolFlags::METHOD) {
            return lsproto::ClassificationTypeName::MethodName;
        }
        if flags.intersects(SymbolFlags::TYPE_PARAMETER) {
            return lsproto::ClassificationTypeName::TypeParameterName;
        }
        if flags.intersects(SymbolFlags::TYPE_ALIAS) {
            return lsproto::ClassificationTypeName::Identifier;
        }
        if flags.intersects(SymbolFlags::ALIAS) {
            return lsproto::ClassificationTypeName::Identifier;
        }
        lsproto::ClassificationTypeName::Text
    }

    /// `isFirstDeclarationOfSymbolParameter` checks if the symbol's first
    /// declaration is a parameter.
    fn is_first_declaration_of_symbol_parameter(&self, symbol: SymbolId) -> bool {
        let declaration = {
            let arena = self.symbols.clone();
            arena[symbol.index()].declarations.first().copied()
        };
        let Some(declaration) = declaration else {
            return false;
        };
        let nodes = self.program.nodes(declaration.file_index());
        nodes[declaration].kind == Kind::Parameter
    }
}
