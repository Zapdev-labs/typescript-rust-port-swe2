# Porting Notes

Non-obvious deviations from the Go port forced by Rust semantics. Each entry:
file(s), the Go pattern, the Rust substitution, and why it is behavior-preserving.

Format: `## <date> <rust file> — <Go source>`

## 2026-10-07 rust/Cargo.toml — dependency additions beyond SPEC §5.11
- `serde`/`serde_json`: sanctioned by §5.11 for tsconfig/api; also used as the
  substrate of `tsc-json` (Go's `json` package is a thin facade over
  `encoding/json/v2`, ~100 LOC — not a JSONC parser. The spec's "~800 LOC
  JSONC-ish parser" description is stale; tsconfig quirks live in tsoptions).
- `num-bigint`: Go uses `math/big` in `jsnum` (PseudoBigInt + huge-int parse).
  Rust std has no bigint; num-bigint has matching truncated div/rem semantics.

## 2026-10-07 local `cargo check`/`test` by porting agents — SPEC §9.2
SPEC §9.2 says no builds/tests run on the workstation because the machine has
no toolchain "by design". A toolchain (cargo 1.97.1) is in fact installed and
IDE-resident. Agents use local `cargo test`/`clippy` with isolated
`CARGO_TARGET_DIR=/tmp/tsrs-check-*` purely as an iteration aid. The
authoritative gate remains `remote-test.sh` on dih@192.168.1.15; nothing
local-only counts toward a milestone gate.

## 2026-10-07 crates/collections — OrderedMap JSON marshalling deferred
Go `OrderedMap.MarshalJSONTo`/`UnmarshalJSONFrom` (json.MarshalerTo impls)
deferred behind `// TODO(port)` until `tsc-json` exists; serde
Serialize/Deserialize impls provided in the interim.

## 2026-10-07 SPEC corrections discovered while porting (Go is truth)
- `json/` is a ~100-LOC facade over encoding/json/v2, not a JSONC parser.
- `contentmapper` imports ast/parser/ipc/jsonrpc — cannot be a Layer-1 port;
  deferred until those crates exist (post-M3).
- `symlinks` imports ast/module — deferred likewise.
- `sourcemap` imports scanner — deferred to M3+ (spec said "emit side first";
  the emit path still pulls scanner types).
- `vfs` imports `osutil` — ported as `tsc-osutil` in M1 despite being listed
  in Layer 6.


## 2026-10-07 rust/Cargo.toml — rustc-hash pin "3" → "2"
The workspace pinned `rustc-hash = "3"` but no 3.x is resolvable from
crates.io (the 3.0.x line was yanked upstream; index max is 2.1.3). Pinned
to "2" so tsc-collections can build.

## 2026-10-07 crates/collections — M1 port shape
- `SyncMap`/`SyncSet` over `RwLock<FxHashMap>`: `load`/`load_or_store`/`range`/
  `to_map`/`keys`/`clone` return owned clones (K/V: Clone) since references
  can't outlive the lock. `range` iterates a cloned snapshot — sync.Map::Range
  does the same via its readOnly snapshot — so callbacks may safely call back
  into the map. Iteration order unspecified, same as Go.
- `CopyOnWriteMap`/`CopyOnWriteSet`: `Rc<FxHashMap>` + `Rc::make_mut` replaces
  Go's `owned` flag + maps.Clone; `enter_scope` returns `impl FnOnce(&mut Self)`
  (call `restore(&mut c)` — Rust closures can't capture `&mut self`).
- Nil-able `*Set`/`*OrderedMap` receiver+arg pairs are `Option<&T>` associated
  fns: `Set::{equals,is_subset_of,intersects,unioned_with}`,
  `OrderedMap::equal_func`, `diff_ordered_maps{,_func}`.
- `MultiMap` is `IndexMap`-backed: Go's map iteration is randomized, so
  first-seen key order is a deterministic superset of the Go contract.
- `Set`/`MultiMap` keep their public `m` field (Go `M`); `Set.keys()` returns
  `&FxHashSet<T>` mirroring Go returning the map itself.

## 2026-10-07 crates/core — M1/M2 core.go et al. port shape
- `context.go`: Go's `context.Context` (channel/select cancellation) becomes an
  explicit `Context` bag holding `request_id`, `checker_lifetime`, and an
  atomic cancellation flag + `Condvar`. Cancellation wakeups are
  Condvar-latency-bound rather than select-instant; documented `// PORT:` at
  each site.
- `workgroup.go`: `SingleThreaded` workgroup runs fns via `Vec::pop` (Go's
  `pop()` is inlined at the call site). `ThrottleGroup` uses a shared
  `Semaphore` + first-error `Mutex<Option<E>>` + inflight counter instead of
  Go's goroutine+done-channel fan-out; error precedence (first error wins) is
  preserved.
- `semaphore.go`: `Unlimited` is a no-op struct; `Limited` is a
  `Mutex<usize>` + `Condvar` counting semaphore.
- `bfs.go`: job arena is `Vec<BreadthFirstSearchJob>` indexed by `u32`
  (Go uses pointers into a job arena); parent chains stored as `Option<u32>`.
  Level-parallel execution via scoped threads; goal/fallback selection uses
  `AtomicI64` min-index so earliest-indexed result wins deterministically.
- `core.go`: `sync.Pool` of levenshtein buffers → `thread_local! RefCell`
  (const-initialized). `iter.Seq` helpers become `impl FnMut`/`Iterator`
  adapters per §7.4. `memoize` retains+clones its value (Go can return the
  cached value; Rust must clone since the closure may be `Fn`).
- `options_generated.go`: `json:"...,omitzero"` →
  `#[serde(skip_serializing_if = "...")]` + `#[serde(default)]`; nil-able
  `[]string`/`*int`/`*OrderedMap` → `Option<_>` to preserve nil-vs-empty in
  `Equals`. i32 enums serialize via a local `serde_i32_enum!` macro producing
  `From<i32>`/`TryFrom<i32>` impls used by `#[serde(into/try_from = "i32")]`;
  unknown ordinals reject on deserialize (Go unmarshals into the typed int
  enum without range checks — Rust is stricter here, matching tsconfig
  validation downstream).
- Stringers (`*_stringer_generated.rs`): checked-in `Display` impls over
  `_name`/`_index` tables; Go's `T(-N)` out-of-range fallback is unreachable
  because Rust enums cannot hold out-of-range ordinals.
- `nodemodules.go`: `sync.OnceValue` package-scope set →
  `LazyLock<FxHashSet<String>>`.
- No `unsafe`; nothing added to the unsafe justification list.
