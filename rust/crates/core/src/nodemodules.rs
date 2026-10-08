// Ported from tsc/internal/core/nodemodules.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use rustc_hash::FxHashSet;
use std::sync::LazyLock;

// require('module').builtinModules.filter(x => !x.match(/^(?:_|node:)/))
// PORT: Go's `map[string]bool` becomes a FxHashSet; membership checks are
// `UNPREFIXED_NODE_CORE_MODULES.contains(x)`.
pub static UNPREFIXED_NODE_CORE_MODULES: LazyLock<FxHashSet<&'static str>> = LazyLock::new(|| {
    FxHashSet::from_iter([
        "assert",
        "assert/strict",
        "async_hooks",
        "buffer",
        "child_process",
        "cluster",
        "console",
        "constants",
        "crypto",
        "dgram",
        "diagnostics_channel",
        "dns",
        "dns/promises",
        "domain",
        "events",
        "fs",
        "fs/promises",
        "http",
        "http2",
        "https",
        "inspector",
        "inspector/promises",
        "module",
        "net",
        "os",
        "path",
        "path/posix",
        "path/win32",
        "perf_hooks",
        "process",
        "punycode",
        "querystring",
        "readline",
        "readline/promises",
        "repl",
        "stream",
        "stream/consumers",
        "stream/promises",
        "stream/web",
        "string_decoder",
        "sys",
        "timers",
        "timers/promises",
        "tls",
        "trace_events",
        "tty",
        "url",
        "util",
        "util/types",
        "v8",
        "vm",
        "wasi",
        "worker_threads",
        "zlib",
    ])
});

// require('module').builtinModules.filter(x => x.startsWith('node:'))
pub static EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES: LazyLock<FxHashSet<&'static str>> =
    LazyLock::new(|| {
        FxHashSet::from_iter([
            "node:quic",
            "node:sea",
            "node:sqlite",
            "node:test",
            "node:test/reporters",
        ])
    });

// PORT: `sync.OnceValue` becomes `LazyLock`; the map holds owned Strings so
// the `node:`-prefixed keys can be constructed. Membership checks are
// `NODE_CORE_MODULES.contains(x)` (String: Borrow<str>).
pub static NODE_CORE_MODULES: LazyLock<FxHashSet<String>> = LazyLock::new(|| {
    let mut node_core_modules = FxHashSet::with_capacity_and_hasher(
        UNPREFIXED_NODE_CORE_MODULES.len() * 2 + EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES.len(),
        Default::default(),
    );
    for unprefixed in UNPREFIXED_NODE_CORE_MODULES.iter() {
        node_core_modules.insert(unprefixed.to_string());
        node_core_modules.insert(format!("node:{unprefixed}"));
    }
    node_core_modules.extend(
        EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES
            .iter()
            .map(|s| s.to_string()),
    );
    node_core_modules
});

pub fn non_relative_module_name_for_typing_cache(module_name: &str) -> &str {
    if NODE_CORE_MODULES.contains(module_name) {
        return "node";
    }
    module_name
}
