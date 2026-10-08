// Ported from tsc/internal/testutil/race/{race.go,norace.go} @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Go gates `Enabled` on the `race` build tag (the `-race` flag compiles in
// runtime/race). Stable Rust has no data-race detector build mode;
// ThreadSanitizer requires nightly `-Zsanitizer`, so the race-enabled file
// has no stable-Rust analog. `ENABLED` is the `norace.go` value — always
// false — matching the default Go build.

/// Enabled reports if the data race detector is enabled.
pub const ENABLED: bool = false;
