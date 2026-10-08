// Ported from tsc/internal/checker/nodebuilder.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — the `NodeBuilder` shell and
// `VerbosityContext` referenced by `Checker::type_to_string_nodebuilder`.
// The `*NodeBuilder` methods (enterContext/exitContext, the
// NodeBuilderInterface wrappers) stay `PORT(deferred)` with the rest of
// nodebuilder.go; `NodeBuilderImpl` itself lives in nodebuilderimpl.rs.

use std::rc::Rc;

use crate::checker_types::Host;
use crate::nodebuilderimpl::{NodeBuilderContext, NodeBuilderImpl};

/// `type NodeBuilder struct` (nodebuilder.go) — PORT(partial): fields are
/// faithful; every method is deferred. `impl_` is the
/// `NodeBuilderImpl<'static>` shell from nodebuilderimpl.rs (its `ch
/// *Checker` back-pointer is already dropped there).
pub struct NodeBuilder {
    /// `ctxStack`.
    pub ctx_stack: Vec<NodeBuilderContext>,
    /// `host`.
    pub host: Option<Rc<dyn Host>>,
    /// `impl`.
    pub impl_: Option<Box<NodeBuilderImpl<'static>>>,
    /// `verbosity` — nil for non-hover callers.
    pub verbosity: Option<Box<VerbosityContext>>,
}

/// `type VerbosityContext struct` (nodebuilder.go) — controls
/// hover-expansion behavior in the node builder. `None` on
/// `NodeBuilder::verbosity` means no expansion (non-hover callers).
/// Level 0 = default hover (`max_expansion_depth` = 0; detects
/// expandability without expanding). Level 1+ = expansion enabled
/// (`max_expansion_depth` = Level).
#[derive(Default)]
pub struct VerbosityContext {
    /// `Level` — 0 = default (no expansion), 1+ = expansion depth.
    pub level: i32,
    /// `MaxTruncationLength` — 0 = use default.
    pub max_truncation_length: i32,
    /// `CanIncreaseVerbosity` — output: whether increasing Level would
    /// reveal more.
    pub can_increase_verbosity: bool,
    /// `Truncated` — output: whether output was truncated.
    pub truncated: bool,
}
