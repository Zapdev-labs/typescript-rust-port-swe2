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

