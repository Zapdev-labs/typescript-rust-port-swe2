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

## 2026-11-19 crates/checker — tsc/internal/checker FOUNDATION port shape
Foundation-phase port only (types.go, links.go, mapper.go,
nodebuilderscopes.go, symboltracker.go, tracer.go, jsdoc.go,
stringer_generated.go, free fns of services.go). `checker_core.rs` is a
deliberate `PORT(partial)` `Checker` stub — the real `Checker` lands in
checker.rs; checker.go/relater.go/inference.go/flow.go/jsx.go/exports.go/
grammarchecks.go are deferred entirely.
- `*Type` → `TypeId` into `TypeArena` (`Arc<RwLock<Vec<Type>>>`): `Arc` because
  `tracing::TracedType` is `Send + Sync` and the tracer adapter holds an arena
  share post-hoc (Go: `tracedTypeAdapter.t *Type` heap pointer). `get`/`get_mut`
  return mapped `RwLock` guards — never hold one across another arena access
  (same-thread re-entry deadlocks); fields are staged into locals first.
- `Type.checker *Checker` back-pointer → `checker_shard: u16`; readers needing
  checker state take `&mut Checker` explicitly (SPEC §5.4). `TypeData`
  interface → `TypeData` enum; `as_*()` casts panic like Go type assertions.
- `*TypeMapper` → `TypeMapperId`/`TypeMapperArena` (`Arc<RwLock<Vec>>`) so
  `map()` can take `&mut Checker` without a self-borrow; `DeferredTypeMapper`/
  `FunctionTypeMapper` closures become `Fn(&mut Checker, ...) -> TypeId`.
  `*InferenceContext` → `InferenceContextId` into `Checker::inference_contexts`.
- Link stores: `core.LinkStore[*ast.Node, V]` → `LinkStore<NodeId, V>`;
  `symbolArenaLinkStore` keeps `PagedLinkStore<Option<Box<V>>>` slots — a slot
  is `Some` iff `Get` populated it (Go's arena-pointer `Has` semantics).
- Go scope-cleanup `func()` closures in nodebuilderscopes.go → explicit
  `ScopeCleanup`/`ScopeUndo` records with `restore(b, nodes)` (closures can't
  disjointly capture `b.ctx`/`b.links`/`nodes`); the `add` callback is an
  eagerly-collected `Vec<(String, SymbolId)>`.
- `SymbolTrackerImpl` holds `Rc<RefCell<Vec<Symbol>>>` (shared with
  `Checker.symbols`) for the `symbol.Flags` type-parameter skip — Go reads it
  through `*ast.Symbol`. The `tracker.(*SymbolTrackerImpl)` peel loop is a
  `take_symbol_tracker_impl_inner` trait hook on `nodebuilder::SymbolTracker`.
- `Tracer` (`tracer.rs`): Go's `tracedTypeAdapter.checker` is unreachable from
  `Send + Sync` `TracedType`, so `RecursionIdentity` is computed eagerly in
  `Checker::trace_record_type` (its inputs are creation-time fields) and
  `Display` returns "" until `type_to_string` lands — PORT(deferred).
  `push`'s `checkerId` arg mutation on the caller's map is preserved verbatim.
- New deps beyond the handed list: `tsc-astnav` (services.go
  `GetTouchingPropertyName`), `tsc-printer` (utilities.go `ValueToString` →
  `printer.EscapeString`; no cycle — printer does not import checker),
  `rustc-hash`, `serde_json` (tracer args).
- `services.rs::get_possible_symbol_reference_positions` keeps Go's
  container-relative first index verbatim (`strings.Index(text[Pos():], …)`
  quirk); all real call sites pass the whole file where `Pos()==0`.

## 2026-10-08 crates/dirty — tsc/internal/project/dirty port shape
`Cloneable[T]` interface → `Cloneable` trait (`clone_value()` is Go's
`Clone()`; `Clone::clone` plays Go's assignment — shallow for handle types).
Go's zero-value/nil returns → `Option` everywhere (`Value()`/`Original()`/
nil base maps are `None`).
- `*MapEntry`/`*SyncMapEntry` aliasing → `Rc<RefCell<EntryState>>` /
  `Arc<Mutex<SyncEntryState>>` handles; Go's `entry.mu`/`sync.Mutex` →
  `std::sync::Mutex`; `collections.SyncMap` → `tsc_collections::SyncMap`.
- `Value[T]`/`LockedEntry[T]` interfaces → `Value` trait + concrete
  `LockedEntry` guard (Rust has no Go's implicit `mu.Lock()` scoping — the
  guard borrows the entry for the locked region instead of unlock-by-defer).
- `SyncMap`'s concurrent-mutation proxy race is preserved: `Change`/
  `Delete`/`Locked` re-resolve the entry through the `SyncMap` and recurse
  through `proxy_for` links exactly like Go's `entry.proxyFor` chain.
- `Map`/`Box`/`MapBuilder` are `Rc`-based single-threaded (Go's non-sync
  variants assume single-goroutine use too); `Map::finalize` returns the
  base map itself when clean (Go's `if len(dirty)==0 return base`).
- `syncmap_test.go` ported 1:1 (4 tests).

## 2026-10-08 crates/projectlogging — tsc/internal/project/logging port shape
`Logger` interface → `Logger` trait; `io.Writer` → `Box<dyn io::Write +
Send>`; `sync.Mutex` writer serialization → `Mutex`; `atomic.Int32`/`Bool` →
`AtomicI32`/`AtomicBool`.
- Go's nil-receiver no-ops become `Option<&dyn Logger>` return from
  `verbose()` (callers use `if let`/`map`) — `WriterLogger::verbose`
  returns `Some(self)`/`None` like Go's `if l.verbose { return l }`.
- Log prefix `[HH:MM:SS.mmm]` is hand-rolled in `timefmt.rs` from
  `SystemTime` (Go `time.Now().Format("15:04:05.000")`).
- `LogTree`: `Fork`/`Embed` share `Arc<LogTreeInner>` (Go's shared `*LogTree`
  + `root` back-pointer → `Weak` to avoid the child→root Arc cycle);
  sequence numbering stays atomic (`AtomicU64` counter + `AtomicI32`
  per-tree `count`/`stringLength`).
- `NewTestLogger` → `new_test_logger` collecting into `Arc<Mutex<Vec<u8>>>`
  behind a shared `io::Write` impl (Go's `bytes.Buffer`).
- `logtree_test.go` ported (2 tests).

## 2026-10-08 crates/watchmanager — tsc/internal/execute/watchmanager port shape
`WatchBackend` interface → `WatchBackend` trait; `fswatch.Watch`/`io.Closer`
→ `WatchHandle` trait object (`close(&self)`, wrapped in `Option` inside
`WatchedDir` since Go assigns the closer post-`WatchDirectories`).
- `wm.mu`/`wm.changedMu` → `Mutex<Inner>` + `Mutex<ChangedState>`;
  `wm.Lock`/`Unlock` + the locked-only methods → `WatchManager::lock()`
  guard (`WatchManagerLock`) so `reconcile_watches`/`ensure_default_backend`
  can only run under the lock — Go's contract, enforced by the type.
- `doCycleCh chan struct{}` (cap 1, non-blocking send) →
  `mpsc::sync_channel(1)` + `try_send`; `RunLoop`'s `select` on
  `ctx.Done()`/`doCycleCh` → `recv_timeout(RUN_LOOP_POLL_INTERVAL)` poll —
  PORT: cancel latency bounded by 10ms instead of select-instant.
- Watch callbacks capture `Weak<WatchManager>` (Go's strong `*WatchManager`
  capture would Arc-cycle wm → watched dir → callback → wm); dead-manager
  late events are dropped.
- `reconcile_watches` collects removals then deletes keys after
  `diff_maps_func` (Go deletes `watchedDirs` inside the diff callbacks —
  legal under Go's range-during-delete; identical result).
- `mpsc::Receiver` is `!Sync`, so `do_cycle_rx` is `Mutex`-wrapped
  (uncontended — only `run_loop`/`do_cycle_ch` consumers receive).
- `watchmanager_test.go` ported (12 tests) including DirWatchSet coverage/
  case-sensitivity, resolve-desired-dirs ancestor fallback, and the
  case-only-spelling reconcile regression.

## 2026-12-01 crates/transformers — tsc/internal/transformers ROOT port shape
Root files only (`transformer.go`, `chain.go`, `utilities.go`,
`modifiervisitor.go`, `destructuring.go`); the transform subpackages are
ported separately against this API.
- `Transformer` keeps `emit_context` in `Rc<RefCell<EmitContext>>` (Go's
  shared `*EmitContext` — a `Chain` hands one context to every component,
  and `TransformOptions.Context` is `Option<Rc<RefCell<EmitContext>>>`).
  Go's `tx.factory == emitContext.Factory` identity cannot be expressed:
  `VisitorCx.factory` must be `&mut ast::NodeFactory`, and holding a `&mut`
  to `emit_context.factory` for the visit would make the `EmitContext`
  unreachable inside callbacks. `Transformer` therefore owns a second,
  hooks-equivalent `ast::NodeFactory` (`new_transform_factory`) used purely
  as `cx.factory`; its `on_create`/`on_update`/`on_clone` hooks mirror the
  emit context's via `Weak` upgrades. Explicit `tx.Factory().New*` calls in
  transform code should use `emit_context().borrow_mut().factory` (the real
  printer factory) — `Transformer::with_factory` wraps that borrow.
  `tx.Factory()` itself is `with_factory(|f| ...)` because returning a
  `&mut` out of a `RefCell` is impossible.
- `PORT(deferred)`: the stand-in factory's `on_clone` cannot copy the
  `autoGenerate` entry (it lives in `EmitContextShared`, private to
  tsc-printer), so clones of generated identifiers made through
  `cx.factory.clone_node` lose regeneration metadata. Route such clones
  through `emit_context().borrow_mut().factory.clone_node`, whose real
  `on_clone` copies the entry (transformer.rs).
- `flattener`'s four function fields (`emitBindingOrAssignment`,
  `create{Array,Object}BindingOrAssignmentPattern`,
  `createArrayBindingOrAssignmentElement`) become a `FlattenMode` enum —
  Rust has no method values. `f.tx`/visitor/cx access threads
  `&Transformer` + `&mut VisitorCx` through every flattener method.
  `CreateAssignmentCallback` additionally receives `(&NodeVisitor,
  &mut VisitorCx)` since Go callbacks captured `*Transformer` and Rust
  closures cannot capture the not-yet-constructed visitor/transformer
  pair; the `value` arg is `Option<NodeId>` (Go `*ast.Expression`).
- `chainedTransformer.components` is `Rc<Vec<Transformer>>` captured by
  the chained visit closure (the closure cannot borrow the transformer it
  is installed on). Component source-file visits re-enter
  `transform_source_file` with a fresh `VisitorCx` per component, exactly
  like Go's sequential `t.TransformSourceFile(result)` loop.
- `ExtractModifiers`'s `modifierVisitor` struct collapses into the
  `modifier_visit` closure + one-shot `Transformer`; `emitContext` is
  `Option<&Rc<RefCell<EmitContext>>>` (Go nilable).
- `emitBinding`'s `append(f.expressions, value)` may append Go nil; the
  `Option<NodeId>` element is dropped instead since `InlineExpressions`
  takes `&[NodeId]`. `set_original` calls are skipped for `None`
  originals (Go stores a nil `original` pointer — observably identical).
- `is_original_node_single_line` uses the *ast* `SourceFileLike`
  (`ecma_line_map()` cached slice) + `scanner::compute_line_of_position`;
  `ast::SourceFile` does not implement the scanner's `SourceFileLike`.
- Element slices from `GetElementsOfBindingOrAssignmentPattern` are
  cloned before iteration because the arena is borrowed mutably while
  flattening (Go shares the backing array with the AST).
- `SingleOrMany` takes `&mut ast::NodeFactory` (the `NewSyntaxList` half)
  instead of `*printer.NodeFactory`; `list` is `Option<Vec<NodeId>>`
  (`None` ↔ Go nil slice).

## 2026-10-08 crates/checker — `checker.go` Checker state skeleton + `NewChecker`
`checker_core.rs` now carries the full Go `Checker` field list in declaration
order plus a faithful `Checker::new_checker` initialization sequence. New
modules hold the auxiliary state Go defines next to each domain:
`checker_types.rs` (cache keys, `keyBuilder`, `TypeFacts`, `IterationUse`,
`Program`/`Host` traits, thunk aliases), `relater.rs` (`Relation`,
`Relater` shell, `ExpandingFlags`, `RecursionFlags`, `IntersectionState`,
`RelationComparisonResult`, `ErrorChain`), `flow.rs` (`FlowType`,
`SharedFlow`, `FlowState`, `typeof_ne_facts`), `inference.rs`
(`InferenceKey`, `InferenceState`), `emitresolver.rs`, `nodebuilder.rs`,
`symbolaccessibility.rs` (`SymbolTableId`, `ExternalModuleContainerIndex`).
Key mapping decisions:
- Go `func` fields stored on the checker (`compareSymbols`, `evaluate`,
  `resolveName`, `getGlobal*Resolver`, iteration closures) become
  `Rc`/`Box` thunk aliases taking an explicit `&mut Checker` receiver —
  Rust closures cannot capture the checker they are stored inside.
  `core.Memoize` becomes an `Rc<RefCell<Option<..>>>` cell inside the `Rc`
  thunk so the memo is shared across every cloned field/resolver.
- `binder.NameResolver` hooks need `&mut Checker` (`error`, `lookup`,
  `symbolReferenced`, scope-change caches), but `binder::NameResolver`'s
  hook signatures don't take it. `create_name_resolver` returns a thunk
  that defers to `resolve_name_via_binder` at call time; the real wiring
  lands with the binder/caller wave (PORT(deferred)).
- `evaluator::new_evaluator` takes no checker parameter, so `evaluate`
  defers to `evaluate_entity` at call time (PORT(deferred)).
- `c.globalThisSymbol.Exports = c.globals` shares the Go map header; the
  port's `SymbolTable` is a value, so the constructor clones the table —
  later `globals` inserts do not reflect into `exports` (PORT(divergence);
  may need `Rc<RefCell<SymbolTable>>`).
- `jsnum.Number` isn't `Eq + Hash` (NaN): `NumberLiteralKey` hashes
  normalized float bits; `EnumLiteralKey` hashes `evaluator::Value`
  variants with the same float semantics. `map[jsnum.PseudoBigInt]` uses
  `PseudoBigInt` directly (already `Hash`).
- `new_checker` currently panics at `boolean_type`'s `get_union_type`
  (PORT(deferred)); the constructor sequence after that point —
  `initialize_closures`, `initialize_iteration_resolvers`,
  `initialize_checker` — is in place and will run once the deferred
  helpers land. Verified with `cargo check -p tsc-checker`.
- `IndexInfo` gained `Clone` because `set_structured_type_members`
  copies arena'd `*IndexInfo` values into `StructuredType.index_infos`.

## 2026-10-08 crates/checker — `relater.go` + `flow.go` completion
`relater.rs` (10,850 lines, all 189 Go funcs) and `flow.rs` (4,459 lines,
all 130 Go funcs) are fully ported against the authority commit
`ec47d33c`. Go top-level `func` inventory matches 1:1 modulo naming
(`asRecursionId[T]` → `as_recursion_id_{node,symbol,type}` generics split;
`narrowTypeBySwitchOnTypeOf` → `narrow_type_by_switch_on_typeof`).
Key decisions beyond the module-header notes:
- Diagnostics aren't `PartialEq`: message identity uses `std::ptr::eq` on
  the shared `pub static` `Message` values (assignability, excess-property,
  signature-mismatch branches).
- `Ternary` gained `and`/`or` wrappers over its `&`/`|` impls (Go calls
  `t.And(u)`/`t.Or(u)`; `FALSE=0`, `UNKNOWN=1`, `MAYBE=3`, `TRUE=-1`).
- `ConstrainedType` and `TupleElementInfo` gained `Clone` (mirroring
  `IndexInfo`): relation code clones arena'd template-constraint and
  tuple-element slices.
- `Checker::enum_relation` is `FxHashMap<EnumRelationKey,
  RelationComparisonResult>` — corrected from the earlier
  `EnumLiteralKey` field type to match Go's `EnumRelationKey` key.
- `is_object_type_with_inferable_index` lives on `Checker`, not `Relater`
  (Go receiver); `compare_signatures_identical` likewise is a `Checker`
  method called from relater code without an extra relater arg.
- `map_type` takes `Rc<dyn Fn(&mut Checker, TypeId) -> TypeId>`; all flow
  narrowing call sites wrap closures in `Rc::new`.
- `has_parent_with_assignments_marked` requires the *same* ancestor to be
  function-or-source-file AND `ASSIGNMENTS_MARKED` (the callback tests
  both together — a two-step find would diverge).
- AST helpers that read siblings take `nodes: &[ast::Node]` explicitly
  (`Node::text`, `ast::is_expression`, `find_ancestor` is node-inclusive).
Verification: remote-only (`rsync` + `cargo check -p tsc-checker` on the
remote workspace — no local build). Remaining errors are all
cross-module: 110 `E0433` for undeclared sibling modules
(`crate::utilities`, `crate::checker_c`, `crate::checker_d`) and 603
`E0599` "no method named" for ~184 methods owned by concurrent sibling
ports (`checker_{a..d}`, `utilities`, `inference.rs`'s unported
`infer_types`/`new_inference_context`, `sym`/`sym_mut` in checker_c).
Zero errors originate from relater.rs/flow.rs implementation defects.

## 2026-10-08 crates/transformers — `estransforms` crash-recovery completion
Resumed the in-flight `estransforms` port after a mid-flight crash. All 17
files existed but `classfields.rs` (61 errors) and `esdecorator.rs` (35
errors) did not compile. Now `cargo check -p tsc-transformers` is clean
(0 errors; only dead-code warnings).
Key fixes/decisions:
- `get_private_identifier` was truncated (returned `None` for the
  `members` map path): added the `nodes: &[Node]` param all callers
  already had in scope and implemented the real `env.members[name.Text()]`
  lookup plus `get_node_for_generated_name(nodes, name)` (was `&[]`).
- Removed three stub helpers planted around `is_anonymous_class_needing_assigned_name`
  (`nodes_check::emit_ref` — would have panicked; `emit_flags_pred` —
  hardcoded `false`; `node_has_transform_private_static_elements_flag_from_pred`)
  and routed the predicate through `ec.borrow()` (safe: the enclosing
  `is_named_evaluation_and` holds a shared borrow).
- `PrivateIdentifierKind` lives in `tsc_printer`, so the orphan
  `impl Default` was replaced by a manual `impl Default for
  PrivateIdentifierInfo` (kind == Field).
- `visit_modifier` gained an unused `_ec` param so the `install!` macro's
  uniform `s.$method(&ec2, cx, node)` call applies;
  `visit_for_substitution_opt` wraps the `NodeId`-returning
  `visit_for_substitution` for the `VisitFn`-shaped `substitution_visitor`.
- `class_has_class_this_assignment` moved from `esdecorator.rs` to
  `classfields.rs` (its Go home); esdecorator imports it.
- `create_get/set_accessor_descriptor_forwarder` gained `ec: &Ec` params —
  `new_this_expression`/`new_function_call_call` live on the printer
  `EmitFactory`, not `cx.factory` (tsc_ast::NodeFactory).
- Nested `check` fn in `member_contains_constructor_reference` is generic
  over the resolver lifetime (`dyn ReferenceResolver + 'r`) because
  `RefCell` invariance rejected `ReferenceResolver<'_>` (defaults 'static).
- `child_is_decorated(false, node, nil)` in Go became
  `child_is_decorated(false, node, node, nodes)` — the Rust signature
  takes a non-Option `NodeId` parent and the parent is never consulted
  when `useLegacyDecorators` is false.
- `is_non_static_method_or_accessor_with_private_name` re-signalled to
  `(nodes, member: NodeId)` (was an `unsafe { transmute }` hack, now gone).
- `Node.statements_mut()` doesn't exist; the IIFE statement-list loc is
  set via `as_block_mut().statements` (IIAF body is always `Block`).
- `Node.flags`/`Node.parent` are fields on the arena header, not on the
  per-kind payloads; `StringLiteral.text` is at
  `literal_expression_base.literal_like_node_base.text`;
  `PropertyAssignment.name` is at `named_member_base.name`;
  accessor payloads use `as_get/set_accessor_declaration()` +
  `accessor_declaration_base.function_like_with_body_base`.
- Option-valued factory results assigned back to `Option<NodeId>` locals
  (`inject_pending_initializers`, `inline_expressions`,
  `update_computed_property_name`) now drop the extra `Some(..)`/rename
  shadowed bindings; `new_reflect_{get,set}_call` and
  `new_function_bind_call` take plain `NodeId` receivers (no `Some(..)`).
Deferrals: none inside estransforms. `ClassInfo.class` and
`EsDecoratorTransformer.compiler_options` are write-only, matching Go's
dead fields. `ec_visit_variable_environment`/`node_flags` helpers in
mod.rs are unused until their consumers land.

## 2026-10-08 crates/transformers — `tstransforms` completion
Finished the in-flight port of `tsc/internal/transformers/tstransforms`:
`importelision.rs`, `legacydecorators.rs` (new, full 1038-LOC Go file),
`metadata.rs`, `runtimesyntax.rs`, `typeeraser.rs`, `typeserializer.rs`,
`utilities.rs`. `cargo check`/`test -p tsc-transformers` are clean (only
pre-existing dead-code warnings in `estransforms`/`moduletransforms`).
Key decisions beyond the module-header notes in `tstransforms/mod.rs`:
- `Symbol` is not `Clone`, so `RuntimeSyntaxTransformer` cannot lazily clone
  the bound symbol arena for `ReferenceResolver` calls; it threads
  `TransformOptions::symbols` (`Option<&'a RefCell<Vec<Symbol>>>`) through
  instead, matching `legacydecorators.rs`.
- Go `childIsDecorated(false, node, nil)` (nil parent) became
  `child_is_decorated_no_parent` in `legacydecorators.rs` — the Rust
  `ast::child_is_decorated` requires a non-Option parent.
- `MetadataTransformer`'s `serializingConditionalTypeBranch` and the lexical
  scope cells are `Cell`-based snapshots (`get`/`set` around a copied
  context value) since the methods take `&self`.
- `typeserializer.rs` relies on the emit resolver for
  `get_type_reference_serialization_kind`; untouched.
- Tests: `typeeraser_test.rs` ports `TestTypeEraser` (73-case table) 1:1 via
  `tsc_testutil::parsetestutil` + `Printer::emit_source_file`.
  `importelision_test.rs` ports `TestImportElision` (18-case table). Go's
  `checker.NewChecker(&fakeProgram)` + `NewEmitResolver` have no Rust
  counterpart (checker's `EmitResolver` is a `PORT(deferred)` shell and
  `new_checker` panics on deferred state), so the test carries
  `FakeEmitResolver`, a binder-level stand-in implementing only the four
  resolver members the transform calls — `mark_linked_references_recursively`
  (a faithful `markLinkedReferences` port incl. the import-declaration skip
  and identifier exclusion rules), `is_referenced_alias_declaration`,
  `is_value_alias_declaration`, and
  `is_top_level_value_import_equals_with_entity_name`. It resolves names
  with `binder::NameResolver` over a field-wise scratch copy of
  `bind_result.symbols` (its `resolve` needs `&mut Vec<Symbol>` only to
  append transient `arguments`/`require` symbols) and follows alias chains
  into a bound `other.ts` arena keyed by module specifier — the role of
  `fakeProgram.getResolvedModule`/`getSourceFileForResolvedModule`. All
  remaining `EmitResolver`/`ReferenceResolver` methods are
  `unimplemented!()` and unreachable.
- Dev-deps gained `tsc-nodebuilder` (EmitResolver stub signatures) on top of
  `tsc-parser`/`tsc-testutil`; `tsc-jsnum` joined `[dependencies]` for
  `utilities.rs`.
- Test fns are named `tstransforms_*` so `cargo test -p tsc-transformers
  tstransforms` selects them.

## crates/checker — `checker.go` 8205-16294 module/alias resolution → `checker_b.rs`
`checker_b.rs` (~16.6k lines) now carries the module and alias resolution
cluster from Go `checker.go` ~14708-16277 (authority `ec47d33c`), appended
in a new `impl Checker` block starting ~line 13080. `lib.rs` declares
`pub mod checker_b;`. Ported functions (Go name → Rust name, all snake_case
in `checker_b.rs`):
- Alias-target resolution: `get_target_of_alias_declaration`,
  `get_target_of_import_equals_declaration`,
  `get_symbol_of_part_of_right_hand_side_of_import_equals`,
  `get_target_of_import_clause`, `get_target_of_module_default`,
  `get_target_of_namespace_import`, `get_target_of_namespace_export`,
  `get_target_of_import_specifier`, `get_target_of_export_specifier`,
  `get_target_of_export_assignment`, `get_target_of_binary_expression`,
  `get_target_of_alias_like_expression`,
  `get_target_of_namespace_export_declaration`,
  `get_target_of_access_expression`,
  `check_and_report_error_for_resolving_import_alias_to_type_only_symbol`,
  `mark_symbol_of_alias_declaration_if_type_only`,
  `get_type_only_declaration_of_entity_name`.
- Entity/qualified name resolution: `resolve_entity_name`,
  `resolve_qualified_name`, `try_get_qualified_name_as_value`.
- External module resolution: `resolve_external_module_name`,
  `resolve_external_module_name_worker`, `resolve_external_module`,
  `resolve_external_module_symbol`, `resolve_es_module_symbol`,
  `resolve_external_module_type_by_literal`,
  `get_external_module_file_from_declaration`,
  `try_resolve_pattern_ambient_module`, `try_find_ambient_module`,
  `get_ambient_modules`,
  `get_cannot_resolve_module_name_error_for_specific_module`,
  `error_on_implicit_any_module`, `create_module_not_found_chain`,
  `create_mode_mismatch_details`.
- Export/member lookup and interop: `resolve_export_by_name`,
  `get_export_of_module`, `get_external_module_member`,
  `get_property_of_variable`, `combine_value_and_type_symbols`,
  `is_only_importable_as_default`, `can_have_synthetic_default`,
  `get_emit_syntax_for_module_specifier_expression`,
  `error_no_module_member_symbol`, `report_non_default_export`,
  `report_non_exported_member`,
  `report_invalid_import_equals_export_member`,
  `get_module_specifier_for_import_or_export`,
  `get_suggested_import_source`, `get_suggested_import_extension`,
  `has_signatures`, `get_type_with_synthetic_default_only`,
  `get_type_with_synthetic_default_import_type`, `is_common_js_require`,
  `create_default_property_wrapper_for_module`,
  `clone_type_as_module_type`.
- Free helpers at file tail: `create_diagnostic_for_node`,
  `get_adjusted_node_for_error`, `get_first_declaration`,
  `get_excluded_symbol_flags`, plus earlier helpers
  (`is_contained_by_namespace`, `get_external_module_require_argument`,
  `get_module_specifier_from_node`, `is_side_effect_import`,
  `resolution_extension_is_ts_or_json`,
  `is_shorthand_ambient_module_symbol`, `is_syntactic_default`,
  `has_export_assignment_symbol`,
  `is_esm_format_import_importing_commonjs_format_file`,
  `get_alias_declaration_from_name`,
  `get_containing_qualified_name_node`, `find_in_map`).
Already present elsewhere (not duplicated): `get_merged_symbol` and the
constructor/diagnostic helpers (`new_symbol`, `merge_symbol`, `error`,
`error_or_suggestion`, `get_symbol_of_declaration`) in `checker_core.rs`;
`get_exports_of_symbol`, `get_exports_of_module`, `resolve_alias`,
`resolve_indirection_alias` in `checker_c.rs`;
`check_for_disallowed_es_symbol_operand`, `check_nan_equality`,
`is_global_nan` earlier in `checker_b.rs` (~lines 10034-10120).
Signatures adapted to existing partial-port call sites:
`resolve_entity_name`, `resolve_external_module_name`, and
`resolve_external_module_symbol` take `Option<..>` name/module parameters.
API adaptations: `tsc_scanner::utilities::declaration_name_to_string`,
`tsc_scanner::scanner::token_to_string` (no root re-export),
`ast::is_right_side_of_qualified_name_or_property_access(NodeId, &[Node])`,
`OrderedMap::set`/`entries`/`iter_mut` (no `insert`/`iter`),
`TypeReadGuard::as_structured_type`, `ShorthandPropertyAssignment`
`.named_member_base.name`, disambiguated `Program` vs
`ModuleSpecifierGenerationHost` `file_exists`/`common_source_directory`,
diagnostics compared by `std::ptr::eq` (`Message` isn't `PartialEq`).
Sibling fix required to parse: `checker_a.rs` `check_const_enum_access`
(~line 12597) was missing a `)` on its type-query branch — fixed.
Remote `cargo check -p tsc-checker` leaves only expected cross-file
`E0599`/`E0433` errors in the new range: `sym`, `sym_mut`, `resolve_alias`,
`resolve_indirection_alias`, `get_exports_of_symbol`,
`get_property_of_type{,_ex}`, `get_signatures_of_structured_type`,
`resolve_structured_type_members` (checker_c wave); `is_error_type`,
`is_empty_object_type` (checker_d wave); `symbol_to_string`,
`get_fully_qualified_name`,
`get_suggested_symbol_for_nonexistent_module` (printer/other waves); and
three `crate::utilities::new_diagnostic_for_node` references pending a
checker-crate utilities module.

## Declarations transformer (`tsc/internal/transformers/declarations` @ ec47d33)

`crates/transformers/src/declarations/` now contains a complete port of the
declaration emit subsystem (~8.4k LOC across `transform.rs` ~6.3k,
`diagnostics.rs` ~1.1k, `tracker.rs` ~0.5k, `util.rs`, `host.rs`,
`supplementalreferences.rs`, `mod.rs` wiring). All Go functions in
`transform.go` (~3k LOC) have Rust counterparts, including the
late-binding visitor (`transformAndReplaceLatePaintedStatements`),
`visitDeclarationSubtree`, every `transform*`/`ensure*`/`update*` helper,
CommonJS export handling (`transformCommonJSExport`,
`transformCommonJSExportWorker`, `appendCjsExports`), expando hosts and
expando assignments, `transformClassExpressionToDeclaration` with the
namespace-isolation branch for class self-references, import/JSDoc
transforms, and supplemental reference collection.

Rust-specific architecture:

- `DeclarationTransformerState<'a>` holds the Go transformer struct's
  fields; `tx.ec` → `Rc<RefCell<EmitContext>>` (`self.ec`),
  `tx.state` → `Rc<RefCell<SymbolTrackerSharedState>>` (`self.shared`),
  `tx.tracker` → `RefCell<SymbolTrackerImpl>` (`self.tracker`).
  Go `*ast.Node` → `NodeId`, `*ast.Symbol` → `SymbolId`, node lists →
  `Option<NodeList>`; nil source-file/current-file state →
  `Option<NodeId>`.
- `tsc-nodebuilder`'s `SymbolTracker` trait was extended: every method
  that Go would satisfy by dereferencing `*ast.Node` pointers now takes
  `nodes: &[Node]` (`track_symbol`, all `report_*` methods). The
  checker's `SymbolTrackerImpl`/`TrackerRef` forwarding wrappers and
  `nodebuilder` call sites were updated to match; an earlier arena
  snapshot/pointer design was abandoned (`Node: !Clone`, workspace
  `unsafe_code = "forbid"`).
- Factory `update_*` methods return `Option<NodeId>` (`None` = unchanged);
  call sites use `.unwrap_or(input)` / `.or(Some(input))`. Modifier
  tokens are minted with `NodeFactory::new_token(nodes, Kind::...)` —
  there is no `new_modifier`.
- Generated AST payloads are deeply nested: `type_parameters`/
  `parameters`/`type_` on signatures live under `function_like_base`
  (itself under `function_or_constructor_type_node_base` on
  function/constructor type nodes, under `accessor_declaration_base.
  function_like_with_body_base` on accessors); `ImportTypeNode.
  type_arguments` lives under `node_with_type_arguments_base`.
- Borrow-checker accommodations: arguments that call `self.*`/visitor
  methods are hoisted into locals before `self.ec.borrow_mut().factory.*`
  calls that take `&mut cx.nodes`; `OrderedMap::set` (not `insert`) for
  synthesized locals; `data.declaration_data_mut()` /
  `data.locals_container_data_mut()` mutate symbol/locals on
  synthesized namespace nodes.
- `GetDiagnostics`/`getDiagnostics` clone the shared state's diagnostic
  list; diagnostics are `Mutex`-wrapped `Diagnostic` handles shared with
  the checker-facing `create_diagnostic_for_node` helpers.

Checker-facing API notes / deferred gaps:

- `emitresolver.rs` imports `tsc_nodebuilder::SymbolTracker` directly
  now (it was previously unresolved after the trait moved). The checker's
  own `SymbolTrackerImpl` ignores the threaded `nodes` parameter — it
  reads its captured context instead, matching Go.
- `SymbolTrackerImpl` in `declarations/tracker.rs` needs
  `TransformOptions::symbols` (live `&RefCell<Vec<Symbol>>`); without it
  it panics on symbol reads, matching the Go tracker's requirements.
- Deferred checker calls are stubbed through the existing `EmitResolver`
  trait surface (`is_expando_function_declaration_unsafe`,
  `try_js_type_node_to_type_node`, `create_type_of_declaration`,
  `create_return_type_of_signature_declaration`,
  `is_symbol_accessible`, `get_enum_member_value`,
  `get_effective_declaration_flags`, `requires_adding_implicit_undefined`)
  — no new checker methods were invented; missing behavior is confined
  to whatever those traits still lack.
- `cargo check -p tsc-transformers` is clean for the declarations
  module (remaining warnings are pre-existing in `estransforms`/
  `moduletransforms`). `tsc-checker` still has ~450 pre-existing
  mid-port errors unrelated to this work; no `SymbolTracker`-related
  errors remain.
