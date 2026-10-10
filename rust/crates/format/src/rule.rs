// Ported from tsc/internal/format/rule.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::ast::Node;
use tsc_ast::kind_generated::Kind;

use crate::context::FormattingContext;

/// `type contextPredicate = func(ctx *FormattingContext) bool`
///
/// PORT: predicates also receive the node arena (`&mut Vec<Node>`) since the
/// Rust `astnav`/`lsutil` helpers require it.
pub(crate) type ContextPredicate =
    Box<dyn Fn(&mut FormattingContext, &mut Vec<Node>) -> bool + Send + Sync>;

/// `type ruleImpl struct`
pub(crate) struct RuleImpl {
    pub debug_name: &'static str,
    pub context: Vec<ContextPredicate>,
    pub action: RuleAction,
    pub flags: RuleFlags,
}

impl RuleImpl {
    /// `(r ruleImpl) Action`
    pub fn action(&self) -> RuleAction {
        self.action
    }

    /// `(r ruleImpl) Context`
    pub fn context(&self) -> &[ContextPredicate] {
        &self.context
    }

    /// `(r ruleImpl) Flags`
    pub fn flags(&self) -> RuleFlags {
        self.flags
    }
}

impl std::fmt::Debug for RuleImpl {
    /// `(r ruleImpl) String`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.debug_name)
    }
}

/// `type tokenRange struct`
#[derive(Clone)]
pub(crate) struct TokenRange {
    pub tokens: Vec<Kind>,
    pub is_specific: bool,
}

/// `type ruleSpec struct`
pub(crate) struct RuleSpec {
    pub left_token_range: TokenRange,
    pub right_token_range: TokenRange,
    pub rule: &'static RuleImpl,
}

/// `type ruleSpecArg` — Go's `left any`/`right any` parameter to `rule`,
/// accepting `ast.Kind`, `[]ast.Kind`, or `tokenRange`.
pub(crate) enum TokenRangeArg {
    Kind(Kind),
    Kinds(Vec<Kind>),
    Range(TokenRange),
}

impl From<Kind> for TokenRangeArg {
    fn from(k: Kind) -> TokenRangeArg {
        TokenRangeArg::Kind(k)
    }
}

impl From<Vec<Kind>> for TokenRangeArg {
    fn from(v: Vec<Kind>) -> TokenRangeArg {
        TokenRangeArg::Kinds(v)
    }
}

impl<const N: usize> From<[Kind; N]> for TokenRangeArg {
    fn from(v: [Kind; N]) -> TokenRangeArg {
        TokenRangeArg::Kinds(v.to_vec())
    }
}

impl From<TokenRange> for TokenRangeArg {
    fn from(r: TokenRange) -> TokenRangeArg {
        TokenRangeArg::Range(r)
    }
}

/// `rule` — the variadic `flags ...ruleFlags` becomes `flags: RuleFlags`
/// (every Go call site passes at most one).
pub(crate) fn rule(
    debug_name: &'static str,
    left: impl Into<TokenRangeArg>,
    right: impl Into<TokenRangeArg>,
    context: Vec<ContextPredicate>,
    action: RuleAction,
    flags: RuleFlags,
) -> RuleSpec {
    let left_range = to_token_range(left.into());
    let right_range = to_token_range(right.into());
    let rule: &'static RuleImpl = Box::leak(Box::new(RuleImpl {
        debug_name,
        context,
        action,
        flags,
    }));
    RuleSpec {
        left_token_range: left_range,
        right_token_range: right_range,
        rule,
    }
}

/// `toTokenRange`
fn to_token_range(e: TokenRangeArg) -> TokenRange {
    match e {
        TokenRangeArg::Kind(t) => TokenRange {
            is_specific: true,
            tokens: vec![t],
        },
        TokenRangeArg::Kinds(t) => TokenRange {
            is_specific: true,
            tokens: t,
        },
        TokenRangeArg::Range(r) => r,
    }
}

/// `var anyContext = []contextPredicate{}`
pub(crate) fn any_context() -> Vec<ContextPredicate> {
    Vec::new()
}

/// `type ruleAction int`
pub(crate) type RuleAction = u32;

pub(crate) const RULE_ACTION_NONE: RuleAction = 0;
pub(crate) const RULE_ACTION_STOP_PROCESSING_SPACE_ACTIONS: RuleAction = 1 << 0;
pub(crate) const RULE_ACTION_STOP_PROCESSING_TOKEN_ACTIONS: RuleAction = 1 << 1;
pub(crate) const RULE_ACTION_INSERT_SPACE: RuleAction = 1 << 2;
pub(crate) const RULE_ACTION_INSERT_NEW_LINE: RuleAction = 1 << 3;
pub(crate) const RULE_ACTION_DELETE_SPACE: RuleAction = 1 << 4;
pub(crate) const RULE_ACTION_DELETE_TOKEN: RuleAction = 1 << 5;
pub(crate) const RULE_ACTION_INSERT_TRAILING_SEMICOLON: RuleAction = 1 << 6;

pub(crate) const RULE_ACTION_STOP_ACTION: RuleAction =
    RULE_ACTION_STOP_PROCESSING_SPACE_ACTIONS | RULE_ACTION_STOP_PROCESSING_TOKEN_ACTIONS;
pub(crate) const RULE_ACTION_MODIFY_SPACE_ACTION: RuleAction =
    RULE_ACTION_INSERT_SPACE | RULE_ACTION_INSERT_NEW_LINE | RULE_ACTION_DELETE_SPACE;
pub(crate) const RULE_ACTION_MODIFY_TOKEN_ACTION: RuleAction =
    RULE_ACTION_DELETE_TOKEN | RULE_ACTION_INSERT_TRAILING_SEMICOLON;

/// `type ruleFlags int`
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum RuleFlags {
    #[default]
    None,
    CanDeleteNewLines,
}
