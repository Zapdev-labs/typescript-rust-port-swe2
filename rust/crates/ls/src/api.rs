// Ported from tsc/internal/ls/api.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(errors): Go's sentinel `error` values (`ErrNoSourceFile`,
// `ErrNoTokenAtPosition`, completions.go's `ErrNeedsAutoImports`) become unit
// variants of [`Error`]; `fmt.Errorf("%w: ...", err)` becomes `Error::Wrapped`.
// Use [`Error::is`] where Go would use `errors.Is`.

use std::fmt;

use tsc_ast::{NodeId, SymbolId, get_source_file_of_node};
use tsc_checker::types::TypeId;
use tsc_core::context::Context;
use tsc_tspath::RootedFilePath;

use crate::languageservice::LanguageService;

/// `ErrNoSourceFile` — "source file not found".
pub const ERR_NO_SOURCE_FILE: Error = Error::NoSourceFile;
/// `ErrNoTokenAtPosition` — "no token found at position".
pub const ERR_NO_TOKEN_AT_POSITION: Error = Error::NoTokenAtPosition;

/// Language-service error. Go's `error` values become variants; leaf variants
/// are the `errors.New` sentinels, `Wrapped` is `fmt.wrapError`.
#[derive(Debug, Clone)]
pub enum Error {
    /// `ErrNoSourceFile`.
    NoSourceFile,
    /// `ErrNoTokenAtPosition`.
    NoTokenAtPosition,
    /// `ErrNeedsAutoImports` (completions.go).
    NeedsAutoImports,
    /// `errors.New` / `fmt.Errorf` without `%w` — a plain message.
    Message(String),
    /// `fmt.Errorf("...: %w", err)` — `msg` is the fully rendered message
    /// (matching Go's `Error()` output); `source` is the wrapped error.
    Wrapped {
        /// The rendered `fmt.Errorf` message.
        msg: String,
        /// The `%w` operand.
        source: Box<Error>,
    },
}

impl Error {
    /// `fmt.Errorf("{msg}: %w", source)` — `msg` must already contain the
    /// rendered source text where `%w` appeared.
    pub(crate) fn wrapped(msg: impl Into<String>, source: Error) -> Error {
        Error::Wrapped {
            msg: msg.into(),
            source: Box::new(source),
        }
    }

    /// `errors.Is(err, target)`. Go compares the error value itself (pointer
    /// identity for sentinels) then walks `Unwrap`; here leaf variants compare
    /// by value and `Wrapped` recurses into its source chain.
    pub fn is(&self, target: &Error) -> bool {
        match self {
            // `fmt.wrapError` — never equal to the target itself; unwrap.
            Error::Wrapped { source, .. } => source.is(target),
            _ => self.leaf_eq(target),
        }
    }

    /// Value equality for non-wrapping variants — the `err == target` half of
    /// `errors.Is`.
    fn leaf_eq(&self, target: &Error) -> bool {
        match (self, target) {
            (Error::NoSourceFile, Error::NoSourceFile)
            | (Error::NoTokenAtPosition, Error::NoTokenAtPosition)
            | (Error::NeedsAutoImports, Error::NeedsAutoImports) => true,
            (Error::Message(a), Error::Message(b)) => a == b,
            _ => false,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::NoSourceFile => f.write_str("source file not found"),
            Error::NoTokenAtPosition => f.write_str("no token found at position"),
            Error::NeedsAutoImports => f.write_str("completion list needs auto imports"),
            Error::Message(m) => f.write_str(m),
            Error::Wrapped { msg, .. } => f.write_str(msg),
        }
    }
}

impl std::error::Error for Error {}

impl LanguageService<'_> {
    /// `GetSymbolAtPosition`.
    pub fn get_symbol_at_position(
        &self,
        ctx: &Context,
        file_name: &RootedFilePath,
        position: i32,
    ) -> Result<Option<SymbolId>, Error> {
        let (program, file) = self.try_get_program_and_file(file_name);
        let Some(file) = file else {
            return Err(Error::wrapped(
                format!("{ERR_NO_SOURCE_FILE}: {}", file_name.as_string()),
                ERR_NO_SOURCE_FILE,
            ));
        };
        let node = {
            let mut nodes = program.nodes_mut(file.file_index());
            tsc_astnav::tokens::get_token_at_position(&mut nodes, file, position)
        };
        let Some(node) = node else {
            return Err(Error::wrapped(
                format!(
                    "{ERR_NO_TOKEN_AT_POSITION}: {}:{position}",
                    file_name.as_string()
                ),
                ERR_NO_TOKEN_AT_POSITION,
            ));
        };
        let (checker, done) = program.get_type_checker_for_file(ctx.clone(), file);
        let symbol = checker.borrow_mut().get_symbol_at_location_api(node);
        drop(checker);
        done();
        Ok(symbol)
    }

    /// `GetSymbolAtLocation`.
    pub fn get_symbol_at_location(&self, ctx: &Context, node: NodeId) -> Option<SymbolId> {
        let program = self.get_program();
        let source_file = {
            let nodes = program.arena_of(node);
            get_source_file_of_node(Some(node), &nodes)
        };
        let (checker, done) =
            program.get_type_checker_for_file(ctx.clone(), source_file.expect("source file"));
        let symbol = checker.borrow_mut().get_symbol_at_location_api(node);
        drop(checker);
        done();
        symbol
    }

    /// `GetTypeOfSymbol`.
    pub fn get_type_of_symbol(&self, ctx: &Context, symbol: SymbolId) -> TypeId {
        let program = self.get_program();
        let (checker, done) = program.get_type_checker(ctx.clone());
        let ty = checker
            .borrow_mut()
            .get_type_of_symbol_at_location(symbol, None);
        drop(checker);
        done();
        ty
    }
}
