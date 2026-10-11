// Ported from tsc/internal/ls/signaturehelp.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// PORT(skeleton): pending full port. The types and entry point below are a
// compat shim consumed by `completions.rs`; the sibling agent's real port
// replaces them.

use tsc_ast::{Node, NodeId, SymbolId};
use tsc_checker::checker_core::Checker;
use tsc_checker::types::SignatureId;
use tsc_core::text::{TextPos, TextRange};

/// `type callInvocation struct`.
pub(crate) struct CallInvocation {
    /// `node`.
    pub(crate) node: NodeId,
}

/// `type typeArgsInvocation struct`.
pub(crate) struct TypeArgsInvocation {
    /// `called` — `*ast.Identifier`.
    pub(crate) called: NodeId,
}

/// `type contextualInvocation struct`.
pub(crate) struct ContextualInvocation {
    /// `signature`.
    pub(crate) signature: SignatureId,
    /// `node` — just for `enclosingDeclaration` for printing types.
    pub(crate) node: NodeId,
    /// `symbol`.
    pub(crate) symbol: SymbolId,
}

/// `type invocation struct` — exactly one field is `Some`.
#[derive(Default)]
pub(crate) struct Invocation {
    /// `callInvocation`.
    pub(crate) call_invocation: Option<CallInvocation>,
    /// `typeArgsInvocation`.
    pub(crate) type_args_invocation: Option<TypeArgsInvocation>,
    /// `contextualInvocation`.
    pub(crate) contextual_invocation: Option<ContextualInvocation>,
}

/// `type argumentListInfo struct`.
pub(crate) struct ArgumentListInfo {
    /// `isTypeParameterList`.
    pub(crate) is_type_parameter_list: bool,
    /// `invocation`.
    pub(crate) invocation: Invocation,
    /// `argumentsSpan`.
    pub(crate) arguments_span: TextRange,
    /// `argumentIndex`.
    pub(crate) argument_index: usize,
    /// `argumentCount` — the *apparent* number of arguments.
    pub(crate) argument_count: usize,
}

/// `getImmediatelyContainingArgumentInfo` — relevant information for the
/// argument list and the current argument when `position` is in the argument
/// of an invocation.
///
/// PORT(sibling): returns `None` until the full port lands.
pub(crate) fn get_immediately_containing_argument_info(
    _nodes: &mut Vec<Node>,
    _node: NodeId,
    _position: TextPos,
    _file: NodeId,
    _checker: &mut Checker,
) -> Option<ArgumentListInfo> {
    None
}
