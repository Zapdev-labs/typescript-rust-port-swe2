# TypeScript → Rust Port — Working Specification

**Status:** active draft · **Owner:** dih · **Last updated:** 2026-10-07

This document is the authoritative spec for porting the TypeScript compiler to Rust.
It lives at `rust/SPEC.md`; the port lives under `rust/`. The reference implementation
is the Go native port in `tsc/internal` (~239k LOC across 53 packages), *not* the
legacy TypeScript ("Strada") sources — the Go port is newer, already data-oriented,
and is what ships as `tsgo`.

When this spec and the Go code disagree, the Go code is correct and the spec should
be updated.

---

## 1. Goals and non-goals

### Goals

- **Byte-for-byte behavioral parity** with the Go port: same diagnostics (same codes,
  same message text, same order), same emit, same baselines. Where the Go port
  deliberately diverges from Strada, follow Go.
- **Performance at parity or better** than the Go port on cold `tsc` runs of large
  projects, with lower peak memory (no GC, tighter AST layout).
- **Full surface eventually**: batch compiler (`tsc`), build mode (`tsc -b`),
  watch mode, transpile API, LSP server, and the IPC/API protocol used by the
  VS Code extension (`packages/vscode-typescript` talks to the native server over
  the msgpack protocol in `tsc/internal/api`).
- **Determinism**: identical inputs produce byte-identical outputs regardless of
  thread count. This is a hard requirement, not a nice-to-have — baselines depend on it.

### Non-goals

- **No reimplementation of Strada.** `src/` (the old TypeScript codebase) does not
  exist in this repo; the Go port is the only reference.
- **No Rust-idiomatic redesign of compiler semantics.** The port is functionally
  faithful — same algorithms, same data flow, same bug-for-bug behavior. Idiomatic
  Rust is applied to *mechanism* (ownership, enums, iterators), never to *semantics*.
- **No public Rust API stability** in early phases. Internal crate boundaries mirror
  Go packages; none of it is semver-stable until milestones M8+.
- **No FFI to the Go code.** This is a clean port. Cross-checking is done through
  outputs (baselines, diagnostics), not linking.

---

## 2. Repository layout

```
rust/
├── SPEC.md                  ← this file
├── Cargo.toml               ← cargo workspace root (members: crates/*)
├── Cargo.lock               ← committed
├── rust-toolchain.toml      ← pinned stable toolchain
├── clippy.toml
├── rustfmt.toml
├── scripts/
│   ├── remote-sync.sh       ← rsync repo → dih@192.168.1.15:~/TypeScript
│   ├── remote-test.sh       ← sync + cargo test on remote
│   └── remote-run.sh        ← sync + cargo run --release -p tsc -- <args>
├── crates/
│   ├── collections/         ← tsc/internal/collections
│   ├── core/                ← tsc/internal/core
│   ├── ...                  ← one crate per Go package, same names
│   └── tsc-cli/             ← tsc/cmd/tsc (the binary)
└── testdata -> ../tsc/testdata   (symlink; baselines and cases are shared)
```

Crate names: `tsc-<pkg>` (e.g. `tsc-ast`, `tsc-checker`). Library crates for every
internal package; one binary crate `tsc-cli` producing the `tsc` binary.
`internal` visibility maps to `pub(crate)`; cross-package access is `pub`.

**Workspace `Cargo.toml`** pins shared deps (`workspace = true`) and sets:

```toml
[workspace.package]
edition = "2024"
rust-version = "1.85"
license = "Apache-2.0"

[workspace.lints.rust]
unsafe_code = "forbid"        # see §7.6 for the escape hatch
missing_docs = "allow"

[workspace.lints.clippy]
all = { level = "warn", priority = -1 }
pedantic = { level = "allow", priority = -2 }   # too noisy for a port
dbg_macro = "warn"
todo = "warn"
unimplemented = "warn"
```

`rust-toolchain.toml`: `channel = "stable"`, components `rustfmt`, `clippy`,
`rust-analyzer`. Pin a specific version (e.g. `"1.90.0"`) once the port is
non-trivial so remote and local builds agree.

---

## 3. Crate graph (Go package → crate → responsibility)

Dependency layers, bottom-up. A crate may only depend on crates in lower layers.
This mirrors Go's `internal` package DAG; keep it acyclic — `cargo` enforces this
naturally. LOC figures are non-test Go LOC, for sizing the port effort.

### Layer 0 — foundations (no compiler knowledge)

| Crate | Go source | LOC | Contents |
|---|---|---|---|
| `tsc-collections` | `collections/` | 853 | `OrderedMap`, `OrderedSet`, `Set`, `MultiMap`, `SyncMap`, `SyncSet`, `CoW`. Port onto `indexmap`-style insertion-ordered tables + `hashbrown` raw tables. |
| `tsc-stringutil` | `stringutil/` | ~300 | dedup/quote/compare helpers, entity-name splitting. |
| `tsc-jsnum` | `jsnum/` | ~500 | **Critical.** JavaScript `number` semantics: `ToString`/`ParseFloat` exact-matching JS (`strconv`-equivalent ported already in Go — port *that*), pseudo-BigInt helpers. JS numeric formatting (`1e21`, `0.1+0.2`) must match byte-for-byte. |
| `tsc-nativepath` | `nativepath/` | ~200 | OS-native path helpers. |
| `tsc-tspath` | `tspath/` | ~1500 | normalized slash-paths, `Path`/`DirectoryPath` newtypes, relative/combine, `comparePaths`, getPathComponents. |
| `tsc-json` | `json/` | ~100 | Thin facade over `encoding/json/v2` (Marshal/Unmarshal/options/streaming Encoder-Decoder tokens). **Correction:** the JSONC-ish tsconfig parsing lives in `tsoptions`, not here. |
| `tsc-locale` | `locale/` | small | diagnostic message localization hook (English only for now; keep the indirection). |
| `tsc-debug` | `debug/` | ~300 | `debug.Assert`, `assertNever`, panic helpers → `debug_assert!` + `unreachable!` + explicit `panic!` for the "asserts are never too strict" cases (repo rule: **never remove assertions**). |
| `tsc-repo` | `repo/` | tiny | testdata path constants (`testdata/baselines/...`). |
| `tsc-core` | `core/` | 3253 | `TextPos`/`TextRange` (UTF-8 **byte** offsets — Go scans bytes, not UTF-16; keep this), `CompilerOptions` structs, `ScriptTarget`/`ModuleKind`/etc. enums (generated, see §6), `Arena`, `LinkStore`, `PagedLinkStore`, `Tristate`, `WorkGroup`/`Semaphore` (→ `std::thread::scope` + `rayon` equivalents), `ScriptKind`, `LanguageVariant`, `ProjectReference`, `TypeAcquisition`. |

### Layer 1 — diagnostics & fs

| Crate | Go source | Contents |
|---|---|---|
| `tsc-diagnostics` | `diagnostics/` | `Message` registry (~6.7k generated LOC from `diagnosticMessages.json`, ~2900 messages incl. `_2` format-arg variants), `Diagnostic`, `DiagnosticCollection`, category, `loc` localization table. Codegen via `build.rs` reading `tsc/internal/diagnostics/diagnosticMessages.json` (single source of truth — do not fork the JSON). |
| `tsc-vfs` | `vfs/` | `VFS` trait + `osvfs` + `vfstest` in-memory FS. Trait-object based (`Arc<dyn Vfs>`) — matches Go interface usage. **Correction:** also imports `osutil` (ported in M1 as `tsc-osutil`). |
| `tsc-contentmapper` | `contentmapper/` | maps synthetic→source positions for mixed content (e.g. `.ts` inside HTML/Svelte — used by content-mapped LS tests). **Correction:** imports `ast`/`parser`/`ipc`/`jsonrpc` — cannot port at Layer 1; deferred to post-M3. |
| `tsc-glob` | `glob/` | Glob matcher for tsconfig `include`/`exclude`/`files` wildcards (hand-rolled segment matcher, not regex — **correction**). |
| `tsc-packagejson` | `packagejson/` | minimal package.json model + validation. |
| `tsc-semver` | `semver/` | semver subset TS needs (`@types` resolution, `typesVersions`). |
| `tsc-sourcemap` | `sourcemap/` | sourcemap emit/parse, VLQ. **Correction:** imports `scanner` — deferred to M3+. |
| `tsc-symlinks` | `symlinks/` | realpath cache + symlink dedup for module resolution. **Correction:** imports `ast`/`module` — deferred to post-M4. |
| `tsc-tracing` | `tracing/` | build/trace event emission (`.trace` JSON) — port late, stub early. |
| `tsc-spanmap` | `spanmap/` | `MultiMap`-of-spans used by LS features (document highlights etc.). |

### Layer 2 — AST & front end

| Crate | Go source | LOC | Contents |
|---|---|---|---|
| `tsc-ast` | `ast/` | 21278 | `Kind` (422 values, generated), `Node`, per-kind node structs (~10k generated LOC: `ast_generated.go`), `NodeList`, `ModifierList`, `Symbol`, `SymbolTable`, `FlowNode` graph, node flags/token flags/symbol flags/check flags, `NodeFactory` + hooks, visitors (`visitor.go`), `deepclone`, position maps, JSDoc lazy-parse hook, `SourceFile`. **The hardest design crate** — see §5. |
| `tsc-scanner` | `scanner/` | 4331 | hand-written scanner, UTF-8 aware, ASCII fast paths, full unicode identifier tables (`unicodeproperties.go` — generated tables, port via codegen), **JS-regexp engine** (`regexp.go` — JS regex semantics ≠ `regex` crate; port it, don't substitute), `StringToNumber`. |
| `tsc-parser` | `parser/` | 9135 | recursive-descent parser, incremental/reparser (`reparser.go` — tree reuse for edits), JSDoc parser, source references. |
| `tsc-astnav` | `astnav/` | ~700 | pure AST navigation helpers (getStartOfNode etc.). |
| `tsc-binder` | `binder/` | 3569 | scope/symbol binding, `flow.go` control-flow-graph construction (flow nodes live on the AST), `nameresolver`, `referenceresolver`. |

### Layer 3 — program & options

| Crate | Go source | LOC | Contents |
|---|---|---|---|
| `tsc-module` | `module/` | 3272 | module resolution (node10/node16/nodenext/bundler/classic), resolution cache, package.json exports/imports/`typesVersions` walking. |
| `tsc-tsoptions` | `tsoptions/` | 7682 | tsconfig parsing, command-line option tables (`options_generated.go` — codegen from the Go table or port `tools` generator), `ParsedCommandLine`, wildcard directories, `rawcompileroptions`→`compileroptions` conversion. |
| `tsc-compiler` | `compiler/` | 6752 | `Program` (file loading pipeline: `filesparser`→`fileloader`→`includeprocessor`), `EmitHost`, project-reference handling, checker pool. |
| `tsc-outputpaths` | `outputpaths/` | ~400 | out paths for js/d.ts/map/tsbuildinfo. |
| `tsc-bundled` | `bundled/` | ~300 | embedded `lib.*.d.ts` assets (Go `embed.FS` → `include_str!`/`include_dir` codegen from `tsc/internal/bundled` or the TS lib sources). |

### Layer 4 — the checker (the 61k-LOC core)

| Crate | Go source | LOC | Contents |
|---|---|---|---|
| `tsc-checker` | `checker/` | 61207 | `Checker` (one per file shard in Go's checker pool), `Type`/`TypeData` (~40 type shapes), `Signature`, `InferenceContext`, relation engine (`relater.go`), flow analysis (`flow.go`), inference (`inference.go`), grammar checks, JSDoc types, JSX, `nodebuilder` (type→syntax for hover/d.ts), `symbolaccessibility`, `stringer` (type display), emit resolver/symbol tracker. Port order inside the crate is prescribed in §8/M6. |
| `tsc-evaluator` | `evaluator/` | ~2k | compile-time constant expression evaluation (enum values, `const` folding for emit). |
| `tsc-pseudochecker` | `pseudochecker/` | ~400 | lightweight checker for non-semantic queries. |
| `tsc-nodebuilder` | `nodebuilder/` | (in checker deps) | shared type→node building used by printer/declarations. |
| `tsc-modulespecifiers` | `modulespecifiers/` | ~2k | "compute an import specifier for X from file Y" — LS auto-import. |

### Layer 5 — back end

| Crate | Go source | LOC | Contents |
|---|---|---|---|
| `tsc-printer` | `printer/` | 11723 | `Printer`/`EmitTextWriter`, factory for synthetic nodes, name generator, `changetrackerwriter` (incremental text edits), single-line string writer. |
| `tsc-transformers` | `transformers/` | 24438 | transformer pipeline: `estransforms` (ES down-leveling per target), `tstransforms` (TS-specific: enums, namespaces, parameter props, `useDefineForClassFields`), `moduletransforms` (CJS/AMD/UMD/System/ESM), `jsxtransforms`, `inliners`, `declarations/` (d.ts emit), `modifiervisitor`, `chain`. |
| `tsc-transpile` | `transpile/` | ~1k | single-file transpile API surface. |
| `tsc-diagnosticwriter` | `diagnosticwriter/` | ~500 | pretty/plain diagnostic formatting for CLI. |

### Layer 6 — drivers, services, infra

| Crate | Go source | Contents |
|---|---|---|
| `tsc-testutil` | `testutil/` | harness utils: `baseline` (golden-file accept/diff), `harnessutil` (VFS fixtures), `tsbaseline` (`.types`, `.errors.txt`, `.symbols` baseline emitters). |
| `tsc-testrunner` | `testrunner/` | compiler/conformance/transpile runners over `testdata/tests/cases`, `@filename`/`@option` directive parser (`test_case_parser.go`). |
| `tsc-execute` | `execute/` | `tsc` CLI driver, watch manager, `build/` (tsbuildinfo, incremental program graph — `tsc -b`), `tsctests`. |
| `tsc-fswatch` | `fswatch/` | fs watching (Go uses `fsnotify`; Rust: `notify` crate behind the `vFS` watch interface). |
| `tsc-format` | `format/` | formatting engine (smart indent, rules). |
| `tsc-ls` | `ls/` | language-service operations (completions, quickinfo, rename, refs, codefixes...). ~79 files. |
| `tsc-project` | `project/` | project/session management on top of `Program` for LS/LSP. |
| `tsc-lsproto` | `lsp/lsproto/` | LSP type definitions (generated from meta-model — port the generator or check in generated Rust). |
| `tsc-lsp` | `lsp/` | LSP server over `ls`+`project`, dynamic request queue, replay tests. |
| `tsc-jsonrpc`, `tsc-ipc` | `jsonrpc/`, `ipc/` | transports: JSON-RPC framing, msgpack IPC (`api/protocol_msgpack.go`). |
| `tsc-api` | `api/` | native-preview API server (the protocol `packages/vscode-typescript` speaks). |
| `tsc-fourslash` | `fourslash/` | fourslash test DSL runner (4.3k test files!) — needs `ls`+`testrunner` infra. |
| `tsc-pprof` | `pprof/` | CPU/heap profile endpoints — port late; `tracing`/`pprof` can be stubs early. |
| `tsc-osutil` | `osutil/` | OS misc (env, temp dirs). |
| `tsc-positionmap`/`tsc-json` misc | — | see respective layers. |

Total: ~52 crates. That granularity is deliberate — it preserves the Go DAG,
keeps incremental build times sane, and lets milestones be claimed crate-by-crate.

---

## 4. The porting contract (per file, per function)

Every ported item follows the same contract — this is what "faithful port" means
operationally:

1. **Same names.** `isExcessPropertyCheckTarget` stays `is_excess_property_check_target`.
   `AsIdentifier` → `as_identifier`. Enum/flag constants keep exact names
   (`SymbolFlags::BlockScopedVariable` → `SYMBOL_FLAGS_BLOCK_SCOPED_VARIABLE` is
   **wrong** — use `SymbolFlags::BlockScopedVariable`). grep-ability against the
   Go source is a feature: a reader should be able to diff `checker/flow.go`
   against `checker/flow.rs` section by section.
2. **Same file layout.** `tsc/internal/checker/relater.go` → `crates/checker/src/relater.rs`.
   One Go file = one Rust file, same order of items top to bottom. Split only
   when a file exceeds ~10k LOC (split at the same seams the Go file's own
   section comments suggest, e.g. `checker.rs`).
3. **Same algorithms, same iteration order.** Any place Go iterates a
   `collections.OrderedMap`, Rust must iterate an insertion-ordered map.
   Any place Go sorts before emitting, Rust must sort the same way with the same
   comparator (including stable-vs-unstable: Go `slices.Sort` is unstable —
   match stability or results may differ on equal keys).
4. **Comments port verbatim**, including references to Strada line numbers and
   `// REVIEW`/`// TODO(port)` markers. Add a `// PORT:` prefix comment only when
   the Rust code *must* deviate (borrow checker, ownership) and record the
   deviation in `rust/PORTING-NOTES.md` if it's non-obvious.
5. **Assertions port one-to-one.** `debug.Assert(x, "msg")` → `debug::assert_(x, "msg")`
   (a shim over `debug_assert!` that *also* runs in release for the first
   milestones — Go asserts run in release too; see §7.6).
6. **Nil semantics**: Go `nil` pointer/map/slice → `Option` where the nil-check is
   semantic; `Vec` empty-vs-nil distinctions that matter (`len(nil)==0` but
   `nil` printed differently in baselines — check each site) → keep an explicit
   marker where needed.

---

## 5. Core architecture decisions (ADRs)

### 5.1 Node representation — arena + packed IDs

The Go port's `Node` is a heap object: `{Kind, Flags, Loc, id, Parent *Node, data nodeData}`
where `nodeData` is an interface implemented by ~350 concrete node structs
(`ast_generated.go`). Parent pointers and mutation (binder sets `flow`/`symbol`
links, transformers clone and re-parent) are pervasive.

**Decision:** arena-per-`SourceFile` of `Node` structs, plus a **global node index**
so a `NodeId` is unique across the program:

```rust
// tsc-ast
pub struct NodeId(u64);            // file_id:20 | local_index:44
pub struct Node {
    pub kind: Kind,                // u16
    pub flags: NodeFlags,          // u32 — bitfield incl. context flags
    pub loc: TextRange,            // pos/end, UTF-8 byte offsets
    pub id: Cell<u64>,             // lazily assigned GetNodeId
    pub parent: Cell<NodeId>,      // assigned in a post-parse pass (Go does it eagerly)
    pub data: NodeData,            // payload, see below
}
pub enum NodeData {                // one variant per concrete node struct
    Identifier(Identifier),
    BinaryExpression(BinaryExpression),
    // ... ~350 variants, generated
}
```

Rationale:

- `NodeId` is `Copy`; `NodeRef`-style accessor `&SourceFile::node(id)` replaces
  `*Node`. No `Rc<RefCell>` graph, no lifetimes in consumers, cheap cloning of
  handles into checker links.
- **Why not `Rc<Node>`**: cycles (parent/child, symbol↔decl, flow graph) leak;
  interior mutability poisons every signature; `deepclone` and transformer
  re-parenting are far simpler against flat ids.
- **Why not a giant `Box`ed tree** (`struct BinaryExpr { left: Box<Node> }`):
  TypeScript needs parent pointers, sibling mutation (binder attaches
  `symbol`/`locals`), and the checker stores per-node results keyed by node —
  all trivial with ids, painful with ownership trees.
- **Why `enum NodeData` and not trait objects**: dispatch in Go is an interface
  call; in Rust it's a `match`. `match` is exhaustive — the ~10k LOC of
  generated Go accessors (`AsX()`) become generated `match` accessors. Variant
  max size is bounded (~120 bytes); pad the arena slot or `Box` the 3–4 largest
  variants if `clippy::large_enum_variant` fires — decide after measuring.
- `Cell` fields on `Node` are used only for data set *after* construction but
  before escape (parent, id). Binder-era mutable links (`flow`, `symbol`)
  live in **side tables**, not on `Node` — see 5.3.

`NodeList`/`ModifierList`: Go wraps `{pos,end, []*Node}` — port as
`NodeList { loc: TextRange, nodes: Box<[NodeId]> }`. Zero-length lists are
`None`-equivalent: `Option<NodeList>` where Go uses `nil`.

`SourceFile` owns: `text: Box<str>` (UTF-8), `Arena<Node>` (`Vec<Node>` —
index *is* the local id, no separate arena type needed; `Vec` is the arena),
`line_map: Vec<TextPos>`, `bind_results: OnceCell<BindResult>`,
`Identifier` intern table, path/lib refs, parse diagnostics.

### 5.2 Symbols — global interned arena

Go: `Symbol` is a heap struct shared across files via the checker. Rust:

```rust
pub struct SymbolId(u32);                    // index into Program::symbols
pub struct Symbol {
    pub flags: SymbolFlags,
    pub check_flags: CheckFlags,
    pub name: Atom,                          // interned string
    pub declarations: Vec<NodeId>,
    pub value_declaration: Option<NodeId>,
    pub members: SymbolTable,                // FxHashMap<Atom, SymbolId> w/ insertion order → IndexMap
    pub exports: SymbolTable,
    pub parent: Option<SymbolId>,
    pub export_symbol: Option<SymbolId>,
    // transient fields (checker-created) stay here; `Transient` flag same as Go
}
```

One `Vec<Symbol>` lives on `Program` (or the merge layer over per-checker
stores, §5.5). `SymbolTable` = `IndexMap<Atom, SymbolId>` — insertion order is
observable in baselines (`.symbols` files, completions ordering), so `HashMap`
iteration is **forbidden** anywhere output order flows to diagnostics/emit.
Rule: `hashbrown`/`FxHashMap` for scratch lookups, `IndexMap` for anything
whose order can reach output. Violating this is the #1 nondeterminism source.

`SymbolFlags`/`CheckFlags`/`NodeFlags`/`TokenFlags`/`ModifierFlags`: port as
`bitflags!` newtypes with identical bit values — the bit values appear in
baselines and `tsbuildinfo` diffs.

### 5.3 Side tables ("links") — `PagedLinkStore` port

Go attaches checker/binder results to nodes via `LinkStore`/`PagedLinkStore`
(maps keyed by `*Node`/node id → lazily-allocated entry). This pattern is
everywhere in `checker/links.go` — `NodeLinks`, `SymbolLinks`, `TypeLinks`,
`SwitchTypeLinks`, `SignatureLinks`, `EnumLinks`, ...

Rust: direct port — `PagedLinkStore<V>` over `NodeId` (the u64 key is already
what Go's paged store wants; `pageShift=8`, `maxPageCount=65536`, same page
table split). This keeps checker code structurally identical and avoids adding
a `links` field to every node.

### 5.4 Types — interned `TypeId` + `TypeData` union

Go: `Type {flags, objectFlags, id TypeId, symbol, alias, checker, data TypeData}`.
`data` is an interface w/ ~40 impls (Intrinsic, Literal, Union, Intersection,
Object(Reference/Anonymous/Mapped/Instantiated/ReverseMapped/EvolvingArray/
Deferred), TypeParameter/IndexedAccess/Conditional/Substitution, StringMapping,
Index, TemplateLiteral, UnionReduction, Signature-bearing, UniqueESSymbol, ...).

Rust: same shape —

```rust
pub struct TypeId(pub u32);                  // Go's numeric type ids ARE the port's ids
pub struct Type {
    pub flags: TypeFlags,
    pub object_flags: ObjectFlags,
    pub id: TypeId,
    pub symbol: Option<SymbolId>,
    pub alias: Option<TypeAliasId>,
    pub data: TypeData,                      // enum, ~40 variants, generated accessors
}
```

stored in a per-checker `TypeArena` (`Vec<Type>` + hash-consing intern map for
literal/intrinsic/union types — Go interns these; the intern table is
load-bearing for `id`-equality fast paths like `t1.id == t2.id → identical`).

**`checker` back-pointer**: Go's `Type.checker` lets types reach checker state
deep in the call graph. Rust cannot put `&Checker` in `Type` (self-referential).
Instead: `Type` stores `checker_shard: u16`, and every code path that read
`t.checker` instead takes the checker as an explicit parameter — this is the
port's biggest mechanical transformation. Alternative if that proves too viral:
a `CheckerPool`-level `TypeStore` where methods live on the pool and types are
pure data. **Prototype this choice first (M5-spike) before porting relater.go.**

### 5.5 Concurrency — same shape as Go, `std::thread::scope` + `rayon`

Go concurrency, and its Rust equivalent:

| Go pattern | Where | Rust port |
|---|---|---|
| `WorkGroup`+goroutines parse files in parallel | `compiler/filesparser.go` | `std::thread::scope` (no rayon dep needed: it's a flat loop) writing into per-file slots of a `Vec<SourceFile>` — parse is embarrassingly parallel, zero shared state. |
| checker pool: N checkers × file shards | `compiler/checkerpool.go` (4 checkers default) | `std::thread::scope` + per-checker `TypeArena`/`SymbolArena`; merge at end (Go already merges — follow its merge order for determinism). |
| `sync.Map`/`SyncSet` | module resolution cache, seen-file sets | `dashmap` or `Mutex<HashMap>` shards — caches must not affect output order; reads are memoization only. |
| `atomic.Uint64` ids | node/symbol ids | `AtomicU64` same semantics (relaxed). |
| `context.Context` cancellation | request-scoped work | explicit `CancelToken` (`AtomicBool`) threaded the same places — do not drop cancellation paths. |

Determinism rule: parallel sections produce into indexed slots; aggregation is
always ordered by source-file index, never by completion order.

### 5.6 Strings, text, positions

- Source text: `Box<str>` (UTF-8). Positions are **byte offsets** (`TextPos(i32)`),
  identical to Go — *not* UTF-16 code units. UTF-16 conversion exists only at
  protocol boundaries (LSP `Position`) — port `core/text.go` + the UTF-16
  conversion helpers where Go has them.
- String interning: `Atom(u32)` in a program-level `Interner` (FxxHash);
  identifier text, symbol names, and `IntrinsicType.name` intern. `Atom`
  replaces Go's `string` in `Symbol.name`, `Identifier.text`, etc.
- JS string literals: scanner produces cooked values — keep Go's exact
  escape/line-continuation semantics (port `scanner.go` `scanString` faithfully;
  it's subtle around `\u{...}` > 0x10FFFF and lone surrogates).

### 5.7 Diagnostics

- `Message` = generated const table keyed by `MessageKey`/`DiagCode`
  (`TS1005` style). `build.rs` of `tsc-diagnostics` parses
  `tsc/internal/diagnostics/diagnosticMessages.json` and emits
  `messages_generated.rs` (~2900 entries: `code: u32`, `category`, `key`,
  `text` with `{0}` format slots, and the `_2`/`_N` arg-shape variants).
- `Diagnostic { file: Option<FileId>, loc: TextRange, message: MessageKey,
  args: Vec<DiagArg>, chain: Vec<MessageChain>, related: Vec<Diagnostic> }`.
- Ordering: diagnostics are emitted in Go's exact order (file order, then
  position, then code) — port `compiler`/`program` diagnostic aggregation last
  of each phase so ordering rules are exercised early via baselines.

### 5.8 Codegen strategy

Go `*_generated.go` files → Rust generated code, produced by small codegen
programs committed under `rust/tools/` (run via `cargo xtask`-style alias or
`build.rs` where input is data like the diagnostics JSON):

| Generated Go | Rust source of truth | Mechanism |
|---|---|---|
| `ast/kind_generated.go` (422 kinds) | parse Go file or `tools/` metadata | `rust/tools/gen-ast` |
| `ast/ast_generated.go` (node structs+accessors, ~10k LOC) | Go file parsed? No — hand-maintained `rust/tools/gen-ast/kinds.toml` listing node kinds + fields, generating `NodeData` variants, `as_*`/`is_*` accessors, `for_each_child`, `visitor` impls | `rust/tools/gen-ast` |
| `diagnostics/diagnostics_generated.go` | `diagnosticMessages.json` | `build.rs` |
| `core/options_generated.go`, `tsoptions/options_generated.go` | port of the Go generator's data tables (copy table → `kinds.toml`-style or rust file) | `rust/tools/gen-options` |
| `scanner/unicodeproperties.go` | same unicode data source Go uses (`@unicode/unicode-15.1.0` — already a devDep) | `rust/tools/gen-unicode` |
| `lsp/lsproto` | LSP meta-model JSON (upstream) | `rust/tools/gen-lsproto` |

Rule: generated Rust is checked in (same as Go) **and** reproducible —
`cargo run -p xtask -- generate` must be idempotent; CI diffs.

### 5.9 Error handling & panics

- Invariants: `debug::assert_!` shim — `debug_assert!` in debug, but also
  `assert!` under feature `asserts = "on-by-default-until-M7"` (Go release
  binaries keep asserts; repo rule: never remove them).
- `debug.AssertNotNil` / nil deref → `Option::expect("msg")`? No — Go panics
  with nil-deref; port as `.unwrap()` on `Option`/`expect` with the Go message
  where one existed. Never silently `unwrap_or` past a Go panic.
- No `thiserror`/error-stack for control flow: the compiler reports via
  diagnostics, panics on bugs. `anyhow` allowed only at the CLI/process edge.

### 5.10 Memory model per phase

- Parse: per-file `Vec<Node>` arena, dead-`NodeId`s allowed (reparser).
- Bind: writes `BindResult` (symbols, flow graph in `Arena<FlowNode>`,
  `NodeLinks` side tables) into `SourceFile::bind_results` — set-once
  (`OnceCell`), matching Go's bind-once + `bindSourceFile` idempotence.
- Check: per-checker `TypeArena` + `LinkStore`s; merged deterministically.
- Emit/transform: transformer allocates fresh nodes into a target-file arena
  (Go has per-transform factory arenas) — keep clone/update semantics
  (`VisitEachChild` returns `Option<NodeId>`; unchanged child → `None`, so
  sharing/subtree-reuse invariants from `subtreefacts.go` still hold).

### 5.11 Dependency policy (third-party crates)

Minimal, pinned (exact versions in `Cargo.lock`; renovate-style updates only
with a green remote test run):

- `rustc-hash` (FxHashMap) — maps everywhere.
- `indexmap` — ordered maps.
- `memchr` — scanner hot loops.
- `rayon` — only if `std::thread::scope` proves insufficient (defer decision).
- `unicode-width`, `unicode-normalization`? — check Go usage before adding;
  the scanner's unicode tables are generated, not crated.
- `serde`+`serde_json` — tsconfig/api only; scanner/parser JSON is hand-ported
  (`tsc-json`) to match Go's parser quirks.
- `notify` — fswatch only.
- `msgpack` impl — vendored tiny encoder/decoder like Go's
  (`api/protocol_msgpack.go` is hand-rolled; port it).
- **No `regex`** — JS regex semantics differ (port `scanner/regexp.go`).
- **No `swc`/`oxc` reuse** — this is a port of *this* codebase.
- `clap` for the CLI? No — `tsc` flag parsing is custom (`tsoptions/commandlineparser`); port it.

### 5.12 Build & profile

```toml
[profile.release]
lto = "fat"
codegen-units = 1
panic = "unwind"     # Go panics unwind; we need catch_unwind for worker threads
debug = "line-tables-only"  # crash diagnostics parity with Go stack traces
[profile.dev.package."*"]
opt-level = 2        # deps (indexmap etc.) optimized even in dev builds
```

`cargo build --release -p tsc-cli` produces `target/release/tsc`. CI compares
`./tsc --version` banner + a smoke compile against Go `tsc` output.

---

## 6. Generated-code and data provenance

Anything in the Go port generated from external data stays generated from the
*same* external data — never from Go's output as input (two-step codegen
compounds drift). Direct sources:

- `diagnosticMessages.json` (in-repo) → diagnostics tables.
- Unicode 15.1 data (npm `@unicode/unicode-15.1.0`, in-repo devDep) →
  identifier-start/part tables + regexp unicode property tables.
- LSP meta-model (upstream URL pinned in Go's generator) → lsproto.
- Node-kind metadata: **exception** — Go's ast/kind metadata is itself the
  source (maintained by hand upstream); the Rust `kinds.toml` is authored once
  from `ast_generated.go` and maintained by hand afterwards, verified by a test
  that every `Kind` exists with correct ordinal.

---

## 7. Coding conventions

1. **Formatting:** `cargo fmt` with `rustfmt.toml` (`use_small_heuristics = "Max"`,
   `imports_granularity` off — default; keep diffs against Go readable).
   `cargo clippy --workspace --all-targets` clean under the workspace lints.
   `unsafe_code = forbid` at workspace level; any `unsafe` needs a per-crate
   `#![allow(unsafe_code)]` + justification comment + entry in `PORTING-NOTES.md`
   (expected candidates: arena slot reuse, interner — try to stay at zero).
2. **Naming:** `snake_case` mirrors of Go names (§4.1). `AsX()` → `as_x()`;
   `IsX()` → `is_x()`; `GetX()` → `get_x()` for stored lookups but `x()` for
   computed accessors — mirror the Go accessor names rather than Rust naming
   dogma; where Go has `X()` keep `x()`.
3. **File header:** every ported file starts with a banner:
   `// Ported from tsc/internal/<pkg>/<file>.go @ <commit-sha>` — the SHA of the
   Go tree it was ported from (record the moving upstream baseline in
   `rust/GO-BASELINE.txt`, updated when re-syncing).
4. **Go-ism shims live in `tsc-core`:** `debug`, `slices` helpers (`maps`,
   `slices.Concat` → `Vec::extend_from_slice`), `tristate`, `iter` adapters
   (`iter.Seq` push-iterators → `for_each_child`-style callbacks or iterators —
   pick per site; Go's yield-return `iter.Seq` maps best to `impl FnMut(&mut ...)
   -> ControlFlow` visitors, matching Go's own comment about escaping closures).
5. **`i32` everywhere Go uses `int` for positions/counts.** `TextPos` is
   `i32`; use `i32` for locs, indexes into text; `usize` only at slice edges
   (`.as_usize()` helpers, not casts sprinkled everywhere — write the helper once).
6. **Int overflow:** Go silently wraps; Rust debug-panics. Where Go relies on
   wraparound (hash mixing), use `wrapping_*`. Where overflow is a bug, keep
   the panic — it surfaces Go-versus-Rust divergence bugs early. Audit sites
   like `pos - 1` on `pos == 0` deliberately.
7. **Platform:** Linux-first (dev+test host are Linux); keep `nativepath`
   boundary so Windows/macOS aren't precluded.

---

## 8. Milestones

Each milestone is a commit-tagged state with a hard exit gate. The phases are
ordered by the Go DAG; *within* the checker there is a prescribed sub-order.
Estimates assume faithful porting at roughly the pace of the Go port effort
(~1:1 LOC, slightly larger for match-heavy accessors).

### M0 — Scaffolding & remote pipeline *(this spec's first commit)*

- `rust/` workspace, `tsc-core` with `TextPos`/`TextRange`/`Arena`/`LinkStore`
  ported + unit tests.
- `remote-sync.sh`/`remote-test.sh` working end-to-end (rsync → `cargo test`).
- Remote toolchain: rustup stable on `dih@192.168.1.15`.
- **Gate:** `remote-test.sh` exits 0 with ≥1 real ported test passing.

### M1 — Foundations

`collections`, `stringutil`, `jsnum`, `nativepath`, `tspath`, `json`,
`core` (all of it: options enums via codegen, `WorkGroup`, `PagedLinkStore`,
`version.go`), `debug`, `repo`, `locale`, `diagnostics` (incl. codegen),
`spanmap`, `glob`, `semver`, `nativepath`, `vfs` (+`osvfs`, `vfstest`),
`packagejson`, `contentmapper`, `symlinks`, `sourcemap` (emit side first).
**Gate:** all Go unit tests in these packages have Rust equivalents passing;
`jsnum` round-trip fuzz vs JS `Number.toString` on 1e6 random doubles matches
byte-for-byte (run on remote).

### M2 — AST

`ast` complete: generated `Kind`, `NodeData` (~350 variants), factory + hooks,
visitors, `deepclone`, `positionmap`, flags, `Symbol` (without binder use yet),
`SourceFile`, `flow` node types. Plus `tsc-ast`'s `IterChildren`/`ForEachChild`
infrastructure — visitor coverage verified by a property test (walk every
parsed test case; every node's parent chain reaches SourceFile).
**Gate:** `deepclone` round-trip tests + `ast_generated` accessor tests pass
on remote; `kind` table test asserts 1:1 with Go ordinals.

### M3 — Scanner & parser (front end red-line)

`scanner` (incl. regexp engine + unicode tables), `parser` (+JSDoc, reparser),
`astnav`.
**Gate:** parse *all* `tsc/testdata/tests/cases/**/*.ts` (12,503 files) +
`testdata/tests/lib` without panic on remote; parse-error diagnostics for a
hand-picked corpus (~200 cases with error baselines) match Go's
`parseTree`-level errors byte-for-byte. Benchmark: parse `vscode` codebase
fixture ≤ Go parser time × 1.3.

### M4 — Binder & module resolution

`binder` (flow graph included), `module`, `packagejson`, `semver` wiring,
`tsoptions` (tsconfig → `ParsedCommandLine`, incl. codegen'd option tables).
**Gate:** `.symbols`-style output for conformance corpus matches Go; module
resolution tests (`tsc/testdata/tests/cases/conformance/moduleResolution`)
produce identical resolved-file sets; `tsc --showConfig` on fixture tsconfigs
matches Go output byte-for-byte.

### M5 — Program & checker spike

`compiler` (file loading, program construction, diagnostics plumbing,
`EmitHost`), `bundled` libs, `outputpaths`; **checker spike**: `checker` crate
skeleton — `Type`/`TypeData` arena + the `t.checker` eradication strategy
(§5.4) proven on `checker/types.go` + `utilities.go` + intrinsic/literal types
only.
**Gate:** `tsc <file>` on a trivial program loads, binds, parses `lib.d.ts`,
and reports *parse-level* diagnostics (checker not required). Spike demo:
`getTypeOfSymbol` on `let x = 1` infers `1`.

### M6 — Checker (the long pole)

Port `checker/` in this order, landing green slices:

1. `types.go`, `links.go`, `mapper.go` (type instantiation), `utilities.go`,
   `jsdoc.go` types, `exports.go`.
2. `relater.go` (subtype/assignability engine), `inference.go` — with
   `tracer.go` ported early: `--generateTrace` output is the debugging
   lifeline and must diff-match Go.
3. `flow.go` (narrowing), `grammarchecks.go`, `services.go` (check entry points).
4. `nodebuilder*` (type→syntax), `printer.go` (type→string), `stringer`,
   `symbolaccessibility`, `symboltracker`.
5. `jsx.go`, `emitresolver.go`, `emitsupport.go`, `pseudotypenodebuilder`.

Parallel checkers come *after* single-checker correctness (run 1 checker,
deterministic merge = trivial).
**Gate:** staged baseline climb tracked in `rust/CONFORMANCE.md` —
compiler+conformance `.errors.txt`/`.types` match % vs `baselines/reference`.
Targets: ≥50% at first green slice, ≥90% to call M6 done, then grind the long
tail (the `.diff` files in `submoduleAccepted.txt`/`submoduleTriaged.txt` are
*known* Go-vs-Strada deltas — Go baselines are truth).

### M7 — Back end: printer, transformers, emit

`printer`, `transformers` (in order: chain/core visitor infra → `tstransforms`
→ `moduletransforms` → `estransforms` (per-target, largest) → `jsxtransforms`
→ `inliners` → `declarations`), `sourcemap` emit, `evaluator`, `transpile`.
**Gate:** `.js` emit baselines match Go for the emit corpus; `transpileModule`
API parity; `--declaration` emit matches; sourcemaps byte-match.

### M8 — CLI & incremental

`execute` (tsc CLI incl. `--watch` via `fswatch`), `tsbuildinfo`+`build/`
(incremental + project references), `diagnosticwriter`, `ipc`/`jsonrpc`.
**Gate:** `tsc -p` compiles the fixture projects identically to Go
(exit codes, stderr text, emitted files, tsbuildinfo round-trip: rebuild with
no changes emits nothing); `tsc -b` on a project-reference fixture graph.

### M9 — Services layer

`format`, `ls`, `project`, `modulespecifiers`, `spanmap` consumers, `fourslash`
runner, `lsp`+`lsproto`+`api` (msgpack protocol, server, replay tests).
**Gate:** fourslash baselines match; LSP replay tests pass; the vscode
extension's smoke path (open file → quickinfo → completions → organize
imports) works against the Rust server — validated via the existing Go-side
session tests' recorded fixtures where possible.

### M10 — Parity & polish

Full `tsc/testdata` suite green (excluding files the Go port itself skips —
honor `promotedTestCollisions.txt` semantics), perf parity-or-better vs Go on
the benchmark corpus (`vscode`/`TypeScript` self-compile fixtures),
`PORTING-NOTES` finalized, `unsafe` audit, fuzzing pass on scanner/parser
(`cargo fuzz` or afl-lite harness) — differential vs Go on random byte streams.

---

## 9. Testing strategy

### 9.1 Test inventory (mirrored from Go)

- **Unit tests** — every `*_test.go` gets a `tests/` or `#[cfg(test)]` mirror
  (`core/pattern_test.go` → `core/tests/pattern.rs`...). Port the *assertions*,
  not just the cases.
- **Compiler/conformance baselines** — `tsc-testrunner` drives
  `testdata/tests/cases/{compiler,conformance,transpile}`: parse `@filename`/
  `@option` directives, run the program, emit baseline files
  (`.errors.txt`, `.types`, `.symbols`, `.js`, `.d.ts`, `.sourcemap.txt`)
  into `tsc/testdata/baselines/rust-local/<suite>/`, then **diff against
  `baselines/reference/`** — the same files Go writes (its local output goes
  to `baselines/local/`; keep ours separate so both ports coexist).
- **tsoptions tests** — config-parsing baselines (`baselines/reference/tsoptions`).
- **tsc/execute tests** — `tsctests` mirror: CLI behavior incl. exit codes.
- **fourslash/LSP** — deferred to M9, same baseline machinery.
- **Differential fuzz** — M3+: random UTF-8 byte strings → Go `tsc` parse vs
  Rust parse, compare diagnostics streams.

### 9.2 Remote-only testing — hard rule

**No builds or tests run on this workstation.** Dev machine edits + commits;
the remote compiles. Local `cargo` is not required (and not assumed present).

**Host:** `dih@192.168.1.15` (omarchy, x86_64, 16 cores, 23 GB RAM, ~275 GB
free). SSH key auth, `BatchMode` — already verified working.
**Checkout:** `~/TypeScript` on remote (rsync mirror, *not* a git clone —
keeps it byte-identical with the working tree incl. uncommitted WIP).
**Toolchain:** rustup stable at `~/.cargo/bin` (installed 2026-10-07,
`--profile minimal`).

**`rust/scripts/remote-sync.sh`** (contract):

```bash
rsync -az --delete \
  --exclude '.git' --exclude 'node_modules' --exclude 'target' \
  --exclude 'tsc/testdata/baselines/local' --exclude 'tsc/testdata/baselines/rust-local' \
  /home/dih/TypeScript/ dih@192.168.1.15:~/TypeScript/
```

**`rust/scripts/remote-test.sh [cargo-test-args...]`**:

```bash
remote-sync.sh && ssh dih@192.168.1.15 \
  'cd ~/TypeScript/rust && $HOME/.cargo/bin/cargo test --workspace "$@"' -- "$@"
```

Baseline-heavy runs set `TS_RUST_BASELINE_DIR=rust-local` and compare
reference-vs-local via a `remote-diff-baselines.sh` (diff -r, exit code =
number of differing suites). `cargo test` concurrency: remote has 16 cores;
checker tests are heavy — default `--jobs=8` for baseline runs to bound RAM
(Go test runs are tuned similarly in Herebyfile).

**Failure protocol:** if remote is unreachable → commit anyway, mark the todo
blocked, report to user; *never* fall back to building locally (machine has
no toolchain by design). If `ssh` flaps mid-run, `remote-test.sh` retries once
then reports.

### 9.3 Conformance tracking

`rust/CONFORMANCE.md` updated each milestone-green commit:

```
| suite        | total | pass | diff | %     |
| compiler     |  ...  |  ..  |  ..  |  ..   |
| conformance  |  ...  |  ..  |  ..  |  ..   |
```

A test "passes" when its full baseline set is byte-identical to
`baselines/reference`. Diffs are investigated case-by-case; *accepted* deltas
get listed in `rust/ACCEPTED-DELTAS.txt` with reason (mirrors Go's
`submoduleAccepted.txt` pattern).

---

## 10. Git & workflow protocol

- **Branch:** work on `rust-port`. `main` is kept as a clean mirror of
  `origin/main` (upstream microsoft/TypeScript — **never push**, never open
  PRs upstream; per CONTRIBUTING.md this repo forbids bulk agent PRs — our
  work stays local). All port commits land on `rust-port`.
- **Checkpoint commits every 15 minutes.** A background loop commits all
  changes every 900 s when the tree is dirty:
  `wip(auto): checkpoint <HH:MM> — <files changed>`. These are safety
  checkpoints; meaningful milestone commits (`M1: tspath + collections
  ported`) land separately with real messages. Auto-checkpoints never rewrite
  history and are squashed only at explicit milestone boundaries if ever
  (prefer keeping them — history is cheap, lost work isn't).
- **Commit format (human/agent commits):** `port(<pkg>): <what>` —
  e.g. `port(scanner): port scanNumber incl. bigint suffix checks`.
  Generated-code refreshes: `gen(<crate>): regenerate <tables>`.
- **Pre-commit hooks:** none (repo uses `tools/hooks` for the Go side; don't
  install npm hook machinery for Rust work — the 15-min cadence must not be
  gated by a slow or absent local toolchain).
- **Sync discipline:** `remote-sync.sh` runs before *every* remote test, and
  is also run after each milestone commit so the remote tree ≈ HEAD.

---

## 11. Risks & mitigations

| Risk | Impact | Mitigation |
|---|---|---|
| `Type.checker` back-pointer eradication is viral across 61k LOC | M6 blows up | M5 spike decides: explicit param threading vs pool-owned type store. If param threading >~15% of signatures change shape, switch strategy *before* relater.go. |
| Interface-dispatch sites (`nodeData`/`TypeData` methods like `AsNode`, `VisitEachChild`, `Clone`) | every node/type access | generated `match`-based accessors + a `NodeKind→vtable` pattern is rejected (too clever); measure enum size, box fat variants. |
| Go `map` iteration-order dependence leaking into output | nondeterminism / baseline diffs | IndexMap-for-output rule (§5.2) + a clippy lint or code-review checklist grep for `HashMap` in emit paths. |
| Reparser/incremental correctness | M3, M9 | port `parser/reparser.go` + its tests only after full parse passes; keep it behind `reparse` module boundary. |
| Baseline diff noise (trailing whitespace, path separators) | false-negative conformance | port `testutil/baseline` normalization rules (CRLF handling, `repo.TestDataPath` substitution) exactly. |
| Remote-only testing slows iteration | everything | sync is incremental rsync; keep `target/` on remote persistent (never `--delete` it — excluded); `cargo check` fast-fail before `cargo test`. |
| Upstream drift (Go port still moving) | port rots | `rust/GO-BASELINE.txt` pins the ported SHA; re-sync monthly by diffing `tsc/internal` at old vs new SHA and cherry-picking semantic changes (a tracked process, not ad hoc). |
| Regexp engine | wrong regex = wrong scanner | port `scanner/regexp.go` line-by-line incl. its test corpus; do not substitute crates. |
| Memory blowup on huge programs | M10 | arena slots sized ≤64B where possible; `PagedLinkStore` for sparse maps; profile vs Go (`pprof` port + `heaptrack`). |

---

## 12. Open questions (resolve at milestone boundary, not before)

1. `NodeData` enum: inline vs `Box` for large variants — decide with M2
   measurements (target: `Node` ≤ 64 B without box, accept ≤ 96 B boxed).
2. `Atom` interning scope: per-program vs `once_cell` global — global matches
   Go's process-wide string dedup better but adds mutex; decide at M2.
3. Checker merge strategy for parallel phase: Go merges type arenas via
   `linkstore`+renumbering? — read `checkerpool.go` merge path in detail at M6;
   spec the port to mirror it rather than inventing a cleaner scheme.
4. `iter.Seq` visitor pattern: `for_each_child(&mut FnMut)` callback vs
   `impl Iterator` — Go comments say iterator-yield was chosen to avoid
   escape-analysis costs; Rust closures don't have that problem, so use
   iterators where borrow checker permits, callbacks where parents must be
   mutable during iteration.
5. tsconfig `extends` chain cycle-detection: Go impl details in
   `tsoptions/tsconfigparsing.go` — port exactly, but verify behavior vs
   Strada known quirk (Go port may have fixed it; follow Go anyway, log in
   ACCEPTED-DELTAS if baselines disagree).

---

## 13. Glossary

- **Strada** — the original TypeScript compiler in TypeScript (not in this
  repo; `packages/typescript` carries only the API surface).
- **Corsa** — the Go native port (`tsc/`), a.k.a. tsgo; our reference impl.
- **Port** — this Rust reimplementation, `rust/`, a.k.a. *tsrs* internally.
- **Baseline** — golden output file under `tsc/testdata/baselines/reference`.
- **`rust-local`** — our baseline output dir, sibling of Go's `local`.
- **NodeId / SymbolId / TypeId / Atom** — interned indices; the port's pointer.
- **Link store** — lazily-allocated side table keyed by id (`PagedLinkStore`).
- **Shard** — the subset of files a single checker instance owns (Go: 4).
- **Green slice** — a milestone-internal state where `remote-test.sh` is fully
  green; every commit between green slices is a checkpoint, not a state.

---

## 14. Immediate next actions (ordered)

1. Land this spec + M0 scaffold (`rust/Cargo.toml`, `crates/core` with
   `text.rs`+`arena.rs`+`linkstore.rs` ported, `scripts/*`, `.gitignore`).
2. `remote-test.sh` green on `dih@192.168.1.15`.
3. Begin M1: `tspath` + `stringutil` + `collections` (they unblock everything).
4. Stand up `xtask` codegen skeleton (`gen-diagnostics` first — it's needed by
   `tsc-diagnostics` which `ast` depends on).
