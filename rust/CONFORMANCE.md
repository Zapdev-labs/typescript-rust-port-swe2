# Conformance Tracker

Updated at each green-slice commit. A test passes when its full baseline set
under `tsc/testdata/baselines/rust-local/` is byte-identical to
`tsc/testdata/baselines/reference/`.

| suite        | total | pass | diff | % |
|--------------|-------|------|------|---|
| compiler     |     — |    — |    — | — |
| conformance  |     — |    — |    — | — |
| transpile    |     — |    — |    — | — |

## M1 — Foundations (green)

`remote-test.sh` exits 0: all ported crates compile clean and all ported Go
unit tests pass on dih@192.168.1.15. Ported: collections, core, debug,
diagnostics (2,222 generated messages), glob, jsnum, json, locale,
nativepath, osutil, packagejson, repo, semver, spanmap, stringutil, tspath,
vfs (+osvfs, vfstest, cachedvfs, iovfs, walkdir, vfsmatch, vfsmock). Ahead of
schedule: `tsc-ast` generated core (353 kinds, NodeData, factories, visitors)
via `tools/gen-ast`.

jsnum fuzz gate: 1,008,208 f64 cases (1e6 seeded-random + edge cases) vs
Node `""+n`/`+str` oracle — 0 mismatches (`scripts/jsnum-fuzz-remote.sh`).

Spec-layered M1 packages deferred (depend on ast/parser, see
PORTING-NOTES): contentmapper, symlinks, sourcemap.

## M2 — AST remainder (green)

`tsc-ast` complete: utilities (~6.6k LOC), visitor/factory codegen,
deepclone, positionmap, precedence, parseoptions, diagnostic ordering
(same-file → pos → code → message), `tsc-bundled` (lib.d.ts embedding).
Kind ordinals verified 1:1 against Go (387 constants, 0 mismatches).
`VisitorCx` uses two lifetimes — Go's visitor closure semantics.

## M3 — Scanner + Parser (green, corpus parity)

scanner.rs (full port incl. regexp validation, unicode escapes, JSDoc
detection) + parser.rs/jsdoc.rs/reparser.rs (~15k LOC). Corpus gate
(`scripts/corpus-gate.sh`) parses **all 13,017 files** under
`tsc/testdata/tests/cases` + `tsc/testdata/fixtures` with the Rust parser
and a Go oracle (`tsc/internal/parsecorpus`), comparing diagnostics
(code, pos, end, category, message key, args):

- **0 panics** on either side
- **0 diagnostic mismatches** (100% parity)

Fidelity bugs found by the gate and fixed: JSX children rescan
(`rescan_jsx_token` resets to fullStartPos — 216 .tsx divergences),
`finish_source_file` must clone (not drain) `self.diagnostics` so
`reparse_top_level_await` can save them, arrow-speculation bail-outs that
swapped `'_0_expected'` for `Expression_expected`,
`rescan_slash_token` regex gating, lossy-UTF-8 corpus reads.

Parse throughput (release, 12,851 files, remote host): Rust ~0.95s vs Go
~1.49s — **~1.55x faster** including JSONL output.

## M4 wave 1 — binder + contentmapper + pseudochecker (green)

`tsc-binder` (binder.go, nameresolver.go, referenceresolver.go — symbol
merge/declaration, flow graph, strict-mode, CommonJS/expando, unreachable
flow), `tsc-contentmapper` (transform identity hashing via xxhash-rust
byte-identical to zeebo/xxh3, JSON-RPC mapper host protocol, 32 tests),
`tsc-pseudochecker` (all 20 pseudo-type kinds, lookup/inference, 10
tests). Full remote workspace: 79 test suites green.


## M5 wave 1 — tsoptions + printer + lsconv (green)

`tsc-tsoptions`: command-line + tsconfig parsing, wildcard directories,
parsed-options model — 63 tests incl. checked-in baseline comparisons.
`tsc-modulespecifiers` reconciled onto the real tsoptions API
(`get_supported_extensions`, `SourceOutputAndProjectReference`).

`tsc-printer` (~18k LOC): full emitter core — printer.rs, emit context,
name generator, emit factory, text/semicolon/single-line writers,
resolver+host traits. **553/553 round-trip emit cases byte-for-byte
identical to Go**, 19 unit tests. This unlocks transformers → checker →
compiler.

`tsc-lsconv`: LSP converters (diagnostic pull/push, URI escaping,
UTF-8/UTF-16 rune mapping, LSP line maps) — 6/6 remote tests including
the Node.js UTF-16 reference comparison.
