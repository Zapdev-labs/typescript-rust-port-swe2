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

## 2026-10-07 crates/collections — OrderedMap JSON marshalling
Go `OrderedMap.MarshalJSONTo`/`UnmarshalJSONFrom` (json.MarshalerTo impls) is
covered by serde `Serialize`/`Deserialize` impls; `tsc-json` is a serde_json
facade, so `json::marshal(&map)` produces the same insertion-ordered JSON
object Go emits. Integer keys serialize as decimal object keys either way.

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

## 2026-10-08 crates/ast + tools/gen-ast — generated AST core
- `tools/gen-ast` parses the Go `ast` package (`goparse`) into a checked-in
  schema (`kinds.toml`, 353 kinds + bases + node shapes), then emits
  `kind_generated.rs`/`ast_generated.rs`. `gen-ast check` verifies the emitted
  files are current; `bootstrap` re-derives the schema from Go.
- Go kind constants are sequential `iota`; Rust `Kind` uses explicit ordinals
  verified against Go (0 mismatches). Go's 34 `KindFirst*`/`KindLast*`
  sentinel aliases become `Kind::FIRST_*`/`LAST_*` associated consts.
- `Node` is a flat arena struct: `id: NodeId` (packed `file:20|local:44`),
  `kind`, `flags`, `loc: TextRange`, `parent: Option<NodeId>`,
  `data: NodeData` enum — replacing Go's pointer graph + embedded base
  structs. Embedding is flattened into named fields (`flow_node_base`,
  `statement_base`). `Vec<Node>` indexes by `NodeId::local_index()`.
- `*ast.Node` parameters/fields → `NodeId`; nil → `Option<NodeId>`.
  `*ast.NodeList` → `NodeList` (inline `Vec<NodeId>` handle).
- `utilities.rs` is partially ported: only helpers the AST core needs. The
  remainder lands with the checker (Go file is 4.7k LOC of checker-facing
  helpers). `deepclone`, `positionmap`, `precedence`, diagnostic types are
  M2 items — Go has no tests for the ported portion.

## 2026-10-08 crates/ast/src/diagnostic.rs — ast/diagnostic.go port shape
- `*Diagnostic` → `DiagnosticRef = Arc<Mutex<Diagnostic>>`. Go's pointer is
  load-bearing: `DiagnosticsCollection.Add` dedups and returns the canonical
  diagnostic which callers keep mutating, and `d1 == d2` checks in
  `EqualDiagnostics`/`CompareDiagnostics` terminate recursion on
  self-referential chains (`Rc` alone can't satisfy `Send + Sync`, which
  Go's `sync.Mutex`-guarded collection implies). `Arc::ptr_eq` is the `==`
  check; a diagnostic's lock is never held while another's is taken — the
  compare/equal helpers snapshot fields into `DiagnosticView` — so no lock
  ordering exists. Both mutexes tolerate poison (`into_inner`), matching
  Go's panic-safe `sync.Mutex`.
- `file *SourceFile` → `Option<DiagnosticFile>`: a cloneable handle with
  `node: Option<NodeId>` (arena address of the `*SourceFile`) plus
  `path_key`, `file_name`, `text`, `original_text`, `span_map`. Rust
  `SourceFile` is `NodeData` in the node arena and does not yet carry
  `parseOptions`/`contentMapperInfo`; the diagnostics all read immutable,
  parse-time-fixed attributes, so the snapshot can't go stale. When
  `SourceFile` gains `content_mapper_info`, `DiagnosticFile::from_node`
  should populate `span_map`/`original_text` from it.
- `display_message_args` compares byte-wise (Go slices strings at byte
  offsets) and lossy-decodes a non-UTF-8 original span — Rust `String`
  cannot hold arbitrary bytes. Unreachable until contentmapper lands
  (deferred), since `span_map` is always `None` today.
- `CompareDiagnostics` returns `i32` like Go's `int`; `strings.Compare`/
  `slices.Compare` map to `Ord::cmp as i32` (-1/0/+1), and the `a - b`
  integer subtractions map to `cmp` (only the sign is ever read; avoids
  i32 wrap Go can't hit but Rust would panic on in debug).
- `Lookup` uses `partition_point(cmp < 0)` + equality check — Go's
  `slices.BinarySearchFunc` returns the *first* equal element; Rust
  `binary_search_by` does not guarantee that.
- `Clone()` clones `Vec<DiagnosticRef>` (new Vec, shared `Arc` elements) —
  Go's `result := *d` shares slice backing, but only element sharing is
  observable (nobody writes `d.messageChain[i] = x` in place).
- New `tsc-ast` → `tsc-spanmap` path dep mirrors Go's `ast` importing
  `spanmap` (`SourceFile.SpanMap()` / `AliasForVirtualSpan`).

## 2026-10-08 crates/ast — positionmap.rs, precedence.rs, parseoptions.rs
- `positionmap.rs`: Go `int` offsets → `usize`; `text string` → `&[u8]`
  (source text can carry the `EncodeJSStringRune` lone-surrogate CESU-8
  sentinel, which is not valid UTF-8, so `&str` cannot model it — the Go
  test exercises exactly that). Go `ComputePositionMap` returns
  `*PositionMap` (always non-nil) → `PositionMap` by value. Go benchmarks
  omitted — no stable-Rust `testing.B` equivalent.
- `precedence.rs`: `OperatorPrecedence` (`int`) and `TypePrecedence`
  (`int32`) are transparent `i32` newtypes with SCREAMING associated consts
  (crate flag-type convention) rather than Rust enums — Go relies on the
  out-of-band `OperatorPrecedenceInvalid = -1` and callers compare with
  `<`/`>`. `OperatorPrecedenceFlags` uses `flag_type!`. Nil `*Node` field
  dereferences (`OperatorToken`, `Operand`, `Condition`, `Tag`,
  `TypeParameter`, `Expression()`) become `.expect(...)` panics — same
  failure mode as Go's nil-pointer panic.
- `parseoptions.rs`: `*SourceFile`/`*Node` params → `NodeId`; `*Node`
  results → `Option<NodeId>`; arenas threaded as `nodes: &[Node]` /
  `&mut [Node]` appended after the Go parameter list. `SourceFile` node
  fields read via `nodes[file].as_source_file()`. `for _, s := range
  file.Statements.Nodes` on a `NodeList` → `if let Some(list) =
  &d.statements { for &s in list.nodes() }` — `None` is unreachable for a
  parsed file (Go would nil-panic), treated as empty. Go closures that
  recurse (`findChildNode`, `walkTreeForJSXTags`) become nested `fn`s with
  the result out-param (`&mut Option<NodeId>`) since Rust closures can't
  self-recurse.
- `utilities.rs` gained the utilities.go helpers the two files need:
  `is_optional_chain`, `is_import_meta`, `is_jsx_opening_like_element`,
  `get_implied_node_format_for_emit_worker`. `ModuleReference` nil →
  `is_some_and(...)` returns `false` where Go would nil-panic (unreachable
  on a well-formed `ImportEqualsDeclaration`; matches the existing
  `is_assignment_expression` `let-else` convention).

## 2026-10-08 crates/bundled — lib embedding
- `libs` is a symlink to `tsc/internal/bundled/libs` (rsync `-a` preserves it
  on remote since the whole repo syncs).
- `//go:embed`/`embed_generated.go` → `build.rs` walks `libs/` and emits
  `libs_generated.rs` (`LIB_NAMES` + `EMBEDDED_CONTENTS` sorted static table
  of `include_str!`). Deterministic: filenames sorted at build time.
- `noembed.go` (build-tag fallback serving libs from disk) is NOT ported —
  `EMBEDDED` is always true; the embed path is the shipping configuration.
- `TestingLibPath`/`bundledSourceDir`: Go uses `runtime.Caller` + `testing.
  Testing()`; Rust uses `env!("CARGO_MANIFEST_DIR")` + `/libs` at compile
  time — equivalent inside a workspace checkout.
- `fileInfo.ModTime`: Go returns `time.Time{}` (year 1, unrepresentable);
  `BundledFileInfo::mod_time` returns `SystemTime::UNIX_EPOCH` as the "unset"
  sentinel.
- Write/remove/chtimes on bundled paths `panic!` exactly as Go panics.

## 2026-10-08 crates/scanner/regexp.rs — tsc/internal/scanner/regexp.go
- Go's `regExpParser` borrows the caller's `*Scanner`. scanner.rs is being
  ported by another agent in parallel, so `RegExpParser` temporarily owns the
  scanner-state subset it needs (text/pos/end, token value+flags, script
  target, error sink) plus private ports of the Scanner helpers it calls
  (`scanIdentifier` group-name variant, `scanEscapeSequence`,
  `scanUnicodeEscape`, `peekUnicodeEscape`, `scanHexDigits`, surrogate
  plumbing). The `ReScanSlashToken` flag-scanning loop is ported as
  `scan_regular_expression_flags`. Reconcile by moving the helper block into
  scanner.rs and handing the parser a scanner reference.
- Strings returned by scan helpers are `Vec<u8>`, not `String`: Go strings
  hold arbitrary bytes, and lone UTF-16 surrogates ride through as
  tsc-stringutil's CESU-8 sentinels (encode/decode_js_string_rune), which is
  not valid UTF-8. Positions stay byte offsets into the UTF-8 source.
- `s.hexDigitCache` memoization is dropped; the per-call cost is one table
  lookup, so the transform is neutral.
- `errorAt(args ...any)` becomes `error_at(&[String])`; every diagnostic call
  site already knows its format args.
- MSRV 1.85: Go's `if a && b {` combined with `let`-bindings is written with
  pre-bound `Option` temporaries instead of Rust let-chains (edition 2024
  let-chains need 1.88+). Go `fallthrough` arms are flattened into sequential
  `if`s with comments noting the fallthrough origin.

## 2026-10-08 crates/scanner/unicodeproperties.rs — tsc/internal/scanner/unicodeproperties.go
- Go `map[string]string`/`collections.Set[string]` tables become sorted
  `&[&str]` arrays + `binary_search`. Set membership semantics are identical;
  the only iteration consumers are spelling suggestions, where
  `get_spelling_suggestion_for_strings` picks the best match so input order
  is not observable (Go's own map order is random anyway).
  `NON_BINARY_UNICODE_PROPERTY_NAMES` keeps Go literal insertion order — it
  is only iterated, never searched.

## 2026-10-08 crates/ipc — tsc/internal/ipc port shape
- Go `error` returns become a crate `Error` enum; `ErrConnClosed`/
  `ErrRequestTimeout` are unit variants, `%w`/`errors.Join` become
  `Wrapped`/`Joined` nodes, and `Error::is` replays `errors.Is` chain
  walking. `Error` is `Clone` (leaves `Arc`-wrapped) because Go stores the
  terminal error and also returns/sends it — interface sharing becomes
  value copying.
- `Protocol` methods take `&self` with per-half `Mutex`es inside
  `JsonRpcProtocol`, so a blocked read never stalls handler writes (Go gets
  this free from a concurrent `io.ReadWriter`). `params any`/`result any`
  become `Option<json::Value>` (raw `Box<RawValue>`) for dyn-safety; callers
  marshal via `marshal_params`. Note for the future `api` port:
  `MessagePackProtocol.WriteResponse`'s `RawBinary` fast-path does not fit
  that shape and will need a dedicated method.
- `NewJSONRPCProtocol(rw)` sharing one stream → `new_json_rpc_protocol`
  takes `Arc<S>` and splits it via `SharedIo` (`&S: Read + Write`; std
  provides that for `&UnixStream`/`&TcpStream`, `StdioConn` does it with
  per-half mutexes). `io.Closer` → `IoClose` (`shutdown` in place of fd
  close).
- `AsyncConn`: `pending` map → `mpsc::SyncSender` values (dropping the
  sender = `close(ch)`); `handlers sync.WaitGroup` → `thread::scope`;
  `ctx.Done()` in `Call` polls via `recv_timeout` (≤10 ms vs
  select-instant); `recover()` → `catch_unwind` + `Backtrace` (the default
  panic hook still prints to stderr — cosmetic).
- `PipeTransport` (unix): nonblocking `UnixListener` + `closed` flag stands
  in for `listener.Close()` unblocking `Accept` (safe std cannot close a
  listener fd). **Windows named pipes deferred**: `winio.ListenPipe` needs
  unsafe FFI or an unapproved crate; `new_pipe_transport` fails with
  `Unsupported` under `cfg(windows)`. `generate_pipe_path` is ported.

## 2026-10-10 crates/fswatch — notify-backed API-surface port
- `tsc/internal/fswatch` is ~11.4k LOC of hand-rolled OS watchers (inotify,
  fanotify, FSEvents-over-CGO-asm, kqueue, ReadDirectoryChangesW). Only the
  consumed API surface is ported (`Watcher` trait, `Watch`, `Event`,
  `EventKind`, `WatchDirectoryRequest`, `WithRecursive`/`WithIgnore`,
  `Default`/`Kqueue`, `ErrOverflow`/`ErrWatchTerminated`, and the
  `debounce.go`/`event.go` coalescing semantics); the syscall backends are
  replaced by the `notify` crate's `RecommendedWatcher` (inotify on Linux).
  `notify = "8"` added to `[workspace.dependencies]` (extends the §5.11
  third-party list like `num-bigint`/`pprof`).
- Backend mapping (`notify_backend.rs`, ports `inotify_linux.go`):
  `Create`/`Modify(Name(To))` → `create`, `Modify(Data)` → `update`,
  `Remove`/`Modify(Name(From))` → `remove`, paired `RenameMode::Both` →
  remove+create, `need_rescan()` (IN_Q_OVERFLOW) → `ERR_OVERFLOW`,
  self-delete/move of a watch root → `remove` + wrapped
  `ERR_WATCH_TERMINATED`. `Access` and `Modify(Metadata)` are dropped — Go's
  inotify mask never subscribed to `IN_ATTRIB`/`IN_OPEN`/`IN_CLOSE_*`.
- `default()`/`kqueue()` return the same shared notify-backed watcher —
  backend selection is a Go artifact; `name()` reports the platform backend
  Go would select ("inotify" on Linux; note Go's `Default()` prefers
  fanotify, which notify lacks). `has_fast_recursive_backend()` keeps Go's
  windows/fsevents predicate.
- Go's channel-latch debouncer (`waitCh`/`triggerCh` close+replace) becomes
  `Mutex`+`Condvar` + `notified`/`trigger_epoch` in `debounce.rs`;
  50ms quiet-period / 500ms-since-last-fire semantics are preserved,
  including the immediate fire on the first-ever trigger (Go's zero
  `lastTime` yields an infinite gap).
- `dirWatch` sharing by `(dir, recursive)` key, per-callback `sinceSeq`
  cutoffs (`drain_for_sequences`), and the `triggerCallbacks` filter order
  are ported. FSEvents-only consolidation (`canShareRecursiveDirWatches`)
  and the volume-aware `pathComparer` are NOT ported — on non-Darwin the Go
  comparer is exact-byte anyway. `physicalDirFor` uses
  `tsc_nativepath::realpath`; display paths are rebased at dispatch.
- `notify` records one `is_recursive` flag per watched path and its
  `unwatch` removes whole subtrees, so the dispatcher explicitly re-arms
  recursive subdirectory watches on create/move-in events and `watch_remove`
  re-arms overlapping surviving watches after an unwatch (Go's per-wd
  subscription multimap makes this unnecessary). `watched_paths` mirrors
  notify's internal watch set for dedup.
- `Event.Path` is `String` — non-UTF-8 paths are lossy-decoded at the notify
  boundary (Go strings carry arbitrary bytes). `Event::new` substitutes for
  Go's cross-package composite literals.
- `Watch` is a concrete struct (`io.Closer` equivalent) with idempotent
  `close()` + `Drop`; `WatchCallback` is `Arc<dyn Fn(Vec<Event>,
  Option<Error>)>`; `WatchDirectoryRequest.callback` is `Option` so nil →
  `Error::NilCallback` is preserved.

## 2026-10-08 crates/apiencoder — tsc/internal/api/encoder port shape
- Go `*ast.Node` references become `NodeId`s into an explicit
  `&mut Vec<Node>` arena threaded through `encode_source_file` /
  `encode_node` / `decode_nodes` / `decode_source_file` (which return
  `(Vec<u8>, NodeIndexTable)` / `(NodeId, Vec<Node>)`). `NodeIndexTable.nodes`
  is `Box<[Option<NodeId>]>` — `None` is Go's nil entry (index 0 sentinel and
  node-list pseudo-node slots); a parallel `FxHashMap<NodeId, u32>` backs
  `get_index` since pointer-identity lookup is impossible.
- Go's `encodeTree` visitor closures mutate shared traversal state
  (`prevSibling`, per-parent last-child patches); the port uses `RefCell`/
  `Cell` state plus `NodeVisitor`/`NodeVisitorHooks`, with the `VisitFn`
  receiving `&NodeVisitor` explicitly (Rust closures cannot capture the
  visitor under construction — the established visitor.rs pattern).
- `stringTable` stores the source-file `NodeId` rather than sharing a Go
  `string`; source-text slices are resolved through the arena at
  `record_string` time — identical string-offset output.
- `AstDecoder::create_children_node` destructures decoder state and uses
  free helper functions instead of methods so factory calls like
  `factory.new_x(&mut arena, helper(children))` satisfy the borrow checker;
  Go's `d.childBuf` scratch slice becomes a caller-owned buffer.
- Go's unchecked `ast.Kind(u32)` cast is a checked `kind_from_u32` — an
  out-of-range kind produces the same "unhandled node kind" error Go
  reports (the truncated ordinal is never a known kind anyway).
- `getString` returns raw bytes with `from_utf8_lossy` applied at the
  boundaries Go's WTF-8-tolerant `string` slicing would touch; the checked
  `language_variant`/`script_kind` mapping replaces Go's unchecked casts
  (unknown ordinals → `ScriptKind::Unknown`, matching the decoder's error
  surface for malformed input).
- `sortedOnce`/`sortedIdx` (lazy sorted index for `GetIndex`) map to
  `Arc<OnceLock>`. `PositionMap::utf8_to_utf16` takes `usize`, so negative
  Go `pos` values are clamped rather than sign-extended.
- Header offsets/protocol constants are exported as `SCREAMING_SNAKE_CASE`
  (`HEADER_OFFSET_NODES`, `PROTOCOL_VERSION`, …). Benchmarks are kept as
  `#[ignore]`d single-iteration tests; `formatEncodedSourceFile` lives in
  `encoder_test.rs` and its output matches the Go `api` reference baselines
  (`encodeSourceFile{,WithUnicodeEscapes}.txt`) byte-for-byte — note the
  baselines cover the formatted dump, not the raw wire bytes.

## 2026-10-08 crates/lsproto — tsc/internal/lsp/lsproto port shape

- `lsp_generated.rs` (~44k lines) is produced by `crates/lsproto/gen.py`
  from `lsp_generated.go`, not handwritten; regenerate with
  `python3 gen.py <lsp_generated.go> src/lsp_generated.rs` then
  `cargo fmt -p tsc-lsproto`. Never edit the generated file — change the
  generator.
- Go's reflection-driven `structcodec` (required-field tracking, `lsp:
  "required"`/`"nullable"` tags, reject-`null` on nilable fields, unknown
  field skipping, discriminator-before-field deferral) cannot ride on
  serde derives, so gen.py compiles the equivalent checks into each
  type's `json::UnmarshalerFrom` + `Deserialize` impl (bitset for required
  fields, `dec.read_value()` for raw member names, `skip_value` for
  unknowns). Shared helpers live in `structcodec.rs`/`lsp.rs`
  (`decode_member`, `err_null`, `err_missing`, `json_object_raw_field`,
  `json_object_has_key`, `norm_kind`).
- `*T`/`[]T`/`map[K]V` fields become `Option<...>` (Go nil vs absent);
  `any` becomes `serde_json::Value`; `struct{}` becomes `EmptyObject`
  (accepts any object, marshals `{}`). Union types keep Go's
  pointer-per-arm shape as `Option<T>` fields; marshaling asserts exactly
  one arm (`assertOnlyOne`/`assertAtMostOne`), nullable unions emit `null`
  when all arms are `None`.
- Unions decode via the Go dispatch forms: JSON leading-kind switch
  (`norm_kind` folds `-`/`1`-`9` into `'0'`), key-presence
  (`json_object_has_key`), discriminator scan (`json_object_raw_field` —
  so `kind` may appear after payload fields), and try-each-arm
  `from_slice` fallthrough.
- `SelectionRange.parent` is `Option<Box<SelectionRange>>` — the only
  direct `*Self` recursion; `Box` breaks the infinite size without
  changing semantics.
- `Registration` decodes `registerOptions` only after `method` is known
  (raw-field scan then per-method arm decode), matching the Go custom
  codec; `registerOptions` is `json:"-"` and encoded by arm.
- `Resolved*` capability types are lenient (serde `default` +
  `null_to_default`) and `resolve(Option<&T>)` collapses them into the
  fully-populated view Go's `Resolve()` builds.
- `RequestMessage.params`/`ResponseMessage.result` are
  `Option<json::Value>` (raw member bytes) so inbound messages keep the
  absent-vs-`null` distinction; `unmarshal_params::<T>()` uses
  `TypeId == TypeId::of::<NoParams>()` for Go's `any(params).(NoParams)`
  and returns `ParamsError{code: ErrorCode::InvalidParams}` (Go's
  `ErrorIs` wrapping). Go's "empty `json.Value`" sub-case has no safe-Rust
  construction (`RawValue::from_string` validates; `unsafe` is forbidden),
  so it is implemented (`len == 0` accepted) but untested.
- `DocumentUri`/`URI`/`Method` are `String`/`Cow<'static, str>` newtypes;
  `DocumentUri::path` ports `net/url`-on-`file://` plus the dynamic-URI
  encoding round-trip. Enum `String()` becomes `Display`; numeric enums
  are newtype structs with `Type`-style associated consts.
- Go benchmarks (`BenchmarkUnmarshalDiscriminatedUnion`) are not ported —
  `#[bench]` requires nightly.
- Workspace blockage encountered during verification (not ours):
  `crates/core/src/options_generated.rs` had gained a duplicate
  `TypeAcquisition::equals` impl (in-flight regen) vs `typeacquisition.rs`;
  removed the generated-side copy.

## 2026-10-08 crates/modulespecifiers — tsc/internal/modulespecifiers port shape

- Ports `compare.go`, `preferences.go`, `specifiers.go`, `util.go`, and the
  testable subset of `specifiers_test.go` at baseline
  `ec47d33c23e464a17cdf2475632cba629bee8763`. Public entry points match Go
  (`get_module_specifiers`, `get_module_specifiers_with_info`,
  `get_module_specifiers_for_file_with_info`, `get_module_specifier`,
  `update_module_specifier`, `get_each_file_name_of_module`,
  `get_node_modules_package_name`, etc.) plus the trait surface Go exposes
  as interfaces.
- Go interfaces become traits: `SourceFileForSpecifierGeneration`
  (implemented for `ast::SourceFile`), `CheckerShape`
  (`get_ambient_module_symbol` → `Option<SymbolId>`), and
  `ModuleSpecifierGenerationHost` (extends
  `outputpaths::OutputPathsHost`). Go nil returns map to `Option` except
  `get_source_of_project_reference_if_output_included`, which returns the
  `RootedFilePath` default ("") Go callers use as the nil signal.
- `IsExcludedByRegex` cannot use a regex crate (forbidden dependency), so
  `util.rs` ships a small RE2-subset engine: a `RegexParser` → `Ast` →
  `Program` (Inst list) → Pike-VM executor supporting alternation,
  grouping, `* + ? {m,n}` (lazy variants as leftmost-longest — RE2/Pike-VM
  semantics), char classes/shorthands, `^ $ \b \B (?i)` inline flags and
  `/pattern/flags` literal syntax. Go's `regexp.Compile` accepts a superset
  (Perl classes, `\p{...}`); those parse as `Err` and — matching Go's
  ignored-error behavior — fail closed (pattern simply doesn't match).
  Octal escapes follow RE2's strict 3-digit `\ooo` ≤ 0o377 rule; `\1`-`\9`
  are rejected as backreferences.
- Go pointer/aliasing quirks documented inline: `ModulePath` keeps
  `is_in_node_modules`/`is_redirect`/`file_name` per-path; the ambient
  module symbol path threads `NodeId`/`SymbolId` into arenas
  (`symbols[id.index()]`, `nodes[d]`); `specPair` abstracts
  `Vec<String>` (VersionPaths) vs `Option<Vec<String>>` (paths).
- `tsc-tsoptions` is deliberately NOT a dependency (crate is in flight):
  `tsoptions.GetSupportedExtensions` is inlined at
  `util.rs::try_get_any_file_from_path` and
  `tsoptions.SourceOutputAndProjectReference` is reduced to the
  `OutputDts` path in the host trait — both marked `PORT(deferred)`.
- `tsc-json` is a dev-dependency only: Go tests build
  `ExportsOrImports` struct literals, but its `object_kind` field is
  private, so test fixtures decode JSON strings via `json::unmarshal`.
- Verification: remote `cargo test -p tsc-modulespecifiers` (192.168.1.15,
  `CARGO_TARGET_DIR=/tmp/tsc-target CARGO_INCREMENTAL=0
  RUSTFLAGS="-C linker-features=-lld"`) — 10 tests, 10 passed, 0 warnings.
  No `tsc-tsoptions` errors surfaced during this crate's build.
- Not ported: Go integration tests that need a full Program/Checker
  (`TestGetModuleSpecifiers`-style end-to-end cases) — they belong to the
  LSP/compiler harness milestone; the ported tests cover node_modules path
  parts, ending processing, parent-relative detection, exports/imports
  matching, ignored paths, and symlink alternatives.

## 2026-10-10 crates/tsoptions — tsc/internal/tsoptions port shape

- Ports the whole `tsc/internal/tsoptions` package at baseline
  `ec47d33c23e464a17cdf2475632cba629bee8763`: `commandlineoption.rs`,
  `commandlineparser.rs`, `contentmappers.rs`, `diagnostics.rs`,
  `enummaps.rs`, `errors.rs`, `namemap.rs`, `parsedbuildcommandline.rs`,
  `parsedcommandline.rs`, `parsedoptions.rs`, `parsinghelpers.rs`,
  `rawcompileroptions.rs`, `showconfig.rs`, `tsconfigparsing.rs`,
  `wildcarddirectories.rs`, plus `value.rs` and generated tables under
  `src/generated/` (`declarations.rs` ← `declarations_generated.go`,
  `options.rs` ← `options_generated.go`).
- `value.rs` — `enum Value` replaces Go `any`: it deliberately keeps the
  type distinctions Go type-assertions rely on — `Map` (decoder's
  `*collections.OrderedMap[string,any]`) vs `GoMap` (`map[string]any`),
  `List` (`[]any`) vs `StringList`/`FilePathList`/`DirPathList` (typed
  slices), `Plugins` (`[]core.PluginImport`), `EmptyStruct` (`struct{}`),
  `Null`. `Value`'s `PartialEq` models Go comparability (map/slice-bearing
  variants are not structurally comparable). A custom `Deserialize` impl
  emits `Value::Map` recursively so `RawCompilerOptions` preserves JSON
  document order (Go `json.Unmarshal` into `*OrderedMap` does too; the
  serde_json default `Map` sorts keys and would lose `"paths"` order).
- `normalize_json_value` converts `GoMap`/`StringList`/typed lists the way
  Go's `normalizeJsonValue` handles arbitrary `map[string]any`/slices before
  `ParseJsonConfigFileContent` processes them (plain maps are sorted by
  key, matching Go's `slices.Sorted(maps.Keys(...))`).
- `commandlineparser.rs` — `commandLineParser` keeps
  `response_file_stack` entries live until recursive `parse_strings`
  returns (Go's `defer p.responseFileStack.Delete(path)`), which makes
  cyclic `@file` response files terminate instead of recursing forever.
  `ParseCommandLineWorkerDiagnostics.option_declarations` is an
  `Arc<dyn Fn>` so `parse_command_line_test_worker` can inject custom
  option tables exactly like Go's test hook. The test worker returns the
  raw `TestCommandLineParser { file_names, options, errors }` mirroring
  `export_test.go`'s `*commandLineParser` result.
- `tsconfigparsing.rs` — `compile_on_save` defaults to `Some(false)` (Go
  `compileOnSave := new(bool)`), not `None`. `TsConfigSourceFile` splits
  `*ast.SourceFile` into `source_file: NodeId` + `nodes: Vec<Node>` (the
  arena owning the ids); `ExtendedSourceFiles`/`configFileSpecs` live
  behind `Mutex` so `Arc<TsConfigSourceFile>` matches Go's shared
  mutation. `SourceFileCtx` bundles the `(NodeId, &[Node])` view passed to
  functions that took `*ast.SourceFile`. `ExtendedConfigCache` is a trait;
  `get_extended_config` returns `Option<ExtendedConfigCacheEntry>` where
  `None` defers to `parse_extended_config` (a Go nil-entry is impossible,
  so `None` means "cache miss").
- `getPropFromRaw` quirk preserved: a present array prop produces
  `wrong_value == ""` (Go's `propOfRaw{sliceValue: ...}` leaves
  `wrongValue` at its zero value), which is what lets non-empty
  `references` suppress the empty-`files` diagnostic.
- `parsedoptions.rs` — `ParsedOptions` keeps Go's nilability where it
  matters for `Equals`: `compiler_options`/`type_acquisition` are
  `Option`, `content_mappers` is `Vec<Arc<Mapper>>` (`Mapper::equals`
  starts with pointer identity like Go's `m == other`), and
  `Option<Vec<_>>` fields carry nil-vs-empty. `file_names`/
  `project_references` cannot distinguish nil from empty (plain `Vec` —
  the distinction is unobservable in `equals`).
- `parsedcommandline.rs` — `errors` is `Mutex<Vec<DiagnosticRef>>` (Go
  mutates the field on a shared pointer); `config_file:
  Option<Arc<TsConfigSourceFile>>` owns the config-file arena so
  diagnostics' `DiagnosticFile.node` ids resolve.
- Tests: all `*_test.go` files are ported — the baseline-driven suites
  (`TestCommandLineParseResult`, `TestParseCommandLineVerifyNull`,
  `TestParseBuildCommandLine`, `TestParseConfigFileTextToJson`,
  `TestParseJsonConfigFileContent`,
  `TestParseJsonSourceFileConfigFileContent`, `TestParseTypeAcquisition`)
  compare byte-for-byte against the checked-in reference baselines under
  `tsc/testdata/baselines/reference/`, so Go-vs-Rust output drift fails
  the test. Test-side quirks:
  - The command-line baseline tests re-decode marshaled options through a
    `unmarshal_options_go_semantics` helper that strips `null` members
    first — Go `json.Unmarshal` treats `null` as a no-op while serde
    rejects it for non-`Option` fields.
  - Error sections render via `errors_of`, which strips
    `DiagnosticFile.node` before `from_ast_diagnostics` — the snapshot's
    `text`/`file_name`/`span_map` are enough, and the node id indexes a
    per-file arena the writer no longer holds (Go's `*SourceFile`
    pointers are self-contained).
  - `rawcompileroptions.rs` gets `RawCompilerOptions` deserialized
    straight into `Option<OrderedMap<String, Value>>` (never through
    `serde_json::Value`) and converts non-`paths` nested objects to
    `GoMap`, matching Go's generic-unmarshal map shape.
  - Enum serialization uses the first matching enum-map key (`"es6"`, not
    `"es2015"`), matching Go's map iteration in showconfig.
- Verification: `cargo check` (workspace) and `cargo test -p
  tsc-tsoptions` — 63 tests, 0 failures. Go-side tests were read as the
  oracle but not run (local Go toolchain < go.work's 1.27).

## 2026-10-10 crates/lsconv — tsc/internal/ls/lsconv port shape

- `linemap.rs` = `linemap.go`, `converters.rs` = `converters.go`,
  `converters_test.rs` = `converters_test.go`, `runes.rs` = local copies of
  the Go `utf8.DecodeRuneInString`/`utf16.RuneLen` shims (same as
  `tsc-scanner`; `tsc-stringutil`'s `unicode` module is crate-private).
- The Go `Script` interface is a `Script` trait plus impls:
  `SourceFileScript { file: NodeId, nodes: &[Node] }` (Go's `*SourceFile`),
  `DiagnosticFileScript { file: &DiagnosticFile, nodes: &[Node] }` (the
  diagnostic file handle — `original_file_name` resolves
  `CanonicalSourceFile` through `file.node`+`nodes`, falling back to
  `file_name` for node-less handles which cannot be supplemental), and
  `OriginalTextScript { file_name, text }` (Go's `originalTextScript`
  value). `Box<dyn Script + 's>` stands in for `Script` interface returns
  in `virtual_range_to_original`/`virtual_position_to_original`/
  `diagnostic_script_and_range`; a blanket `impl Script for &T` lets `&T`
  fill the `T` slot of `MappedSpan<T>`/`MappedPosition<T>` (Go embeds
  `spanmap.MappedSpan`/`MappedPosition` — their fields are flattened to
  `span`/`position`/`fidelity`).
- `Script::text()`/`original_text()` return `&[u8]`, not `&str`: Go strings
  carry invalid UTF-8, and both the converters' `DecodeRuneInString` loops
  and `TestConvertersInvalidUTF8` depend on byte-exact invalid-input
  stepping. `compute_lsp_line_starts` likewise takes `&[u8]`.
- `Converters.get_line_map` is
  `Box<dyn Fn(&RootedFilePath) -> &'a LspLineMap + 'a>` — the returned map
  must outlive the converters (Go returns a cache-held `*LSPLineMap`).
- `locale.FromContext`: `tsc_locale::from_context` needs the `LocaleContext`
  trait, which `tsc_core::context::Context` can't implement (tsc-locale is
  dependency-free; orphan rule). lsconv stores the locale under its own
  `ContextKey` (`with_locale`/`locale_from_context`, mirroring
  `lsproto::with_client_capabilities`); nothing sets it yet, so
  `Locale::default()` = Go's absent-key result.
- `DiagnosticToLSPPull`/`Push` take an extra `nodes: &[Node]` param (the
  arena `DiagnosticFile.node` resolves through) — needed by
  `message_chain_to_string` → `write_flattened_ast_diagnostic_message`.
- `url.PathEscape` is ported in-line (`path_escape`/`should_escape_path_segment`,
  `encodePathSegment` mode) plus `extra_escape_replacer` — the vscode-uri
  escaping recipe; Go's `net/url` isn't a dependency.
- Positions are converted in `i64` where `core.TextPos` (`int`) would
  silently fit u32 wire values that overflow i32.
- `related.File() == nil` → `debug::fail` (Go nil-panics later anyway).
- The JS-reference UTF-16 test still shells out to `node -e` and skips
  (returns early) when node is absent, like Go's `t.Skipf`.
- Verification: `cargo test -p tsc-lsconv` via `scripts/remote-test.sh` on
  the remote builder (dih@192.168.1.15) — 6 tests passed, 0 failed
  (incl. `test_converters_against_js_reference` run against node, which is
  present on the remote).

## 2026-11-14 crates/printer — tsc/internal/printer port (arena/owner deviations)
- Go's `*ast.Node` graph is a `Vec<Node>` arena threaded as `nodes:
  &mut Vec<Node>`; nilable `*Node` results become `Option<NodeId>` and
  `*NodeList` becomes `Option<NodeList>` (cloned where Go would share the
  header). `Printer` owns emission state; the Go `NameGenerator` struct's
  methods live in `impl Printer` (`name_generator.rs`) because scope push/pop
  interleaves with emit.
- `EmitContext` owns a `crate::factory::NodeFactory` (a wrapper around
  `ast::NodeFactory` carrying the `Shared` `Rc<RefCell<EmitContextShared>>`),
  so Go's `emitContext.Factory`/`autoGenerate` maps resolve through
  `emit_context.shared()`.
- `EmitTextWriter` is a trait object; downcasting (`as_any_mut`) is used by
  `get_trailing_semicolon_deferring_writer` in place of Go type assertions.
- `ScriptKind::JSON` maps to `ScriptKind::Json`; resolution-mode and option
  constants come from `tsc_core::compileroptions`/`options_generated`.
- `emit_jsx_text` reads the `JsxText` text field directly because
  `Node::text()` (like Go's `Node.Text()`) does not handle `Kind::JsxText`.
- Source-map emit through `tsc_sourcemap::Generator` is partial
  (`PORT(deferred)` markers in `printer.rs`); `MapSourcePosition` returns a
  source-list index instead of a `Source` trait object.
- Tests: `namegenerator_test.go`'s free-standing `NameGenerator` cases are
  `#[cfg(test)]` unit tests in `name_generator.rs` (15 cases, all passing);
  `utilities_test.go` is ported to `utilities.rs` (4 tests, all passing);
  `printer_test.go`'s `TestEmit` table is `tests/emit_test.rs` (553 cases;
  the 3 trailing-comma entries are `PORT(deferred)` exactly as commented out
  in Go). The `TestParenthesize*` tests, which build ASTs via `NodeFactory`
  rather than the parser, are `PORT(deferred)`.

## Deferred crates

- **pprof**: `tsc/internal/pprof` wraps `runtime/pprof` (Go runtime CPU/heap
  profiles). There is no Rust equivalent of the Go pprof runtime format;
  when the CLI reaches profiling flags, substitute a tracing/perf-based
  capture and note it here.
