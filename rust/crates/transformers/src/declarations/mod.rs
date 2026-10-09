// Ported from tsc/internal/transformers/declarations @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Module wiring for the declaration emit transformer:
// - `transform` — `DeclarationTransformer`, the top-level transformer.
// - `diagnostics` — symbol-accessibility and isolated-declaration diagnostics.
// - `tracker` — `SymbolTrackerImpl` + `SymbolTrackerSharedState`.
// - `util` — node predicates/helpers shared across the transformer.
// - `supplementalreferences` — `DeclarationEmitSupplementalReferences`.
// - `host` — `DeclarationEmitHost` trait.

pub mod diagnostics;
pub mod host;
pub mod supplementalreferences;
pub mod tracker;
pub mod transform;
pub mod util;
