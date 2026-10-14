#!/usr/bin/env bash
# Build a PGO-optimized release `tsc` binary.
#
# Two modes:
#   ./scripts/build-pgo.sh            — use the committed profile
#                                       (pgo/merged.profdata.gz)
#   ./scripts/build-pgo.sh --train    — regenerate the profile first:
#                                       instrumented build, run the training
#                                       fixtures, llvm-profdata merge, then
#                                       the optimized build.
#
# Result lands in target-pgo/release/tsc (separate dir so a regular
# `cargo build` target dir is untouched).
set -euo pipefail
cd "$(dirname "$0")/.."

PGO_TARGET_DIR="${PGO_TARGET_DIR:-target-pgo}"
PGO_DATA_DIR="$(mktemp -d)"
trap 'rm -rf "$PGO_DATA_DIR"' EXIT

if [ "${1:-}" = "--train" ]; then
    echo "==> instrumented build"
    RUSTFLAGS="-Cprofile-generate=$PGO_DATA_DIR" \
        cargo build --release --bin tsc --target-dir "$PGO_TARGET_DIR"

    TSC="$PGO_TARGET_DIR/release/tsc"
    echo "==> training runs"
    # Checker-heavy fixtures; extend as needed. Errors are fine — the run
    # still exercises the code paths.
    "$TSC" --noEmit --strict --ignoreConfig \
        ../tsc/testdata/fixtures/compiler/types.ts >/dev/null 2>&1 || true

    PD="$(find "$HOME/.rustup/toolchains/"*/lib/rustlib/*/bin/llvm-profdata 2>/dev/null | head -1)"
    [ -n "$PD" ] || { echo "llvm-profdata not found: rustup component add llvm-tools"; exit 1; }
    "$PD" merge -o "$PGO_DATA_DIR/merged.profdata" "$PGO_DATA_DIR"/*.profraw
else
    gzip -dc pgo/merged.profdata.gz > "$PGO_DATA_DIR/merged.profdata"
fi

echo "==> optimized build"
RUSTFLAGS="-Cprofile-use=$PGO_DATA_DIR/merged.profdata" \
    cargo build --release --bin tsc --target-dir "$PGO_TARGET_DIR"
echo "==> $PGO_TARGET_DIR/release/tsc"
