#!/usr/bin/env bash
# M3 corpus gate: parse every source file in the repo corpus with tsc-parser,
# report panics + diagnostics, and diff against the Go oracle
# (tsc/internal/parsecorpus). Uses the /tmp remote staging (btrfs ENOSPC
# workaround). Pass extra roots as args; defaults to the main corpus.
set -uo pipefail
REMOTE_HOST=${REMOTE_HOST:-dih@192.168.1.15}
REMOTE_DIR=${REMOTE_DIR:-/tmp/TypeScript}
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

"$SCRIPT_DIR/remote-sync.sh" "$REMOTE_HOST" "$REMOTE_DIR" || exit 1

ROOTS=("$@")
if [ ${#ROOTS[@]} -eq 0 ]; then
  ROOTS=("tsc/testdata/tests/cases" "tsc/testdata/fixtures")
fi

ssh "$REMOTE_HOST" bash -s -- "${ROOTS[@]}" <<'OUTER'
set -uo pipefail
export CARGO_TARGET_DIR=/tmp/tsc-target
export CARGO_INCREMENTAL=0
export RUSTFLAGS='-C linker-features=-lld'
CARGO=$HOME/.cargo/bin/cargo
GO=$(ls -d $HOME/.local/share/mise/installs/go/*/bin/go 2>/dev/null | sort -V | tail -1)
[ -n "$GO" ] || GO=$HOME/.local/share/mise/shims/go
cd /tmp/TypeScript/rust
"$CARGO" build --release -p parsecorpus 2>&1 | tail -5 || exit 1
cd /tmp/TypeScript/tsc
PATH="$(dirname "$GO"):$PATH" "$GO" build -o /tmp/goparsecorpus ./internal/parsecorpus || exit 1
cd /tmp/TypeScript

args=("$@")
total=0; rpanics=0; gpanics=0; diffs=0
for r in "${args[@]}"; do
  [ -e "$r" ] || { echo "missing root: $r"; continue; }
  safe=$(echo "$r" | tr / _)
  rout=/tmp/corpus-rust-$safe.jsonl
  gout=/tmp/corpus-go-$safe.jsonl
  /tmp/tsc-target/release/parsecorpus "$r" > "$rout"
  /tmp/goparsecorpus "$r" > "$gout"
  n=$(wc -l < "$rout"); gn=$(wc -l < "$gout")
  rp=$(grep -c '"panic"' "$rout" || true)
  gp=$(grep -c '"panic"' "$gout" || true)
  total=$((total+n)); rpanics=$((rpanics+rp)); gpanics=$((gpanics+gp))
  echo "$r: rust=$n go=$gn files, rust panics=$rp, go panics=$gp"
  python3 - "$rout" "$gout" <<'PY'
import json, sys
def load(p):
    out = {}
    for line in open(p):
        if line.strip():
            d = json.loads(line)
            out[d["file"]] = d
    return out
r, g = load(sys.argv[1]), load(sys.argv[2])
only_r = set(r) - set(g); only_g = set(g) - set(r)
mis, msgonly = [], 0
for f in sorted(set(r) & set(g)):
    rd, gd = r[f], g[f]
    rd = {k: v for k, v in rd.items() if k != "msg"}
    gd = {k: v for k, v in gd.items() if k != "msg"}
    if rd != gd:
        # separate message-text-only diffs (formatting differences)
        rdd = dict(rd); gdd = dict(gd)
        for side in (rdd, gdd):
            for d in side.get("diags", []): d.pop("msg", None)
        if rdd == gdd: msgonly += 1
        else: mis.append(f)
if only_r: print("  rust-only files:", len(only_r), list(sorted(only_r))[:5])
if only_g: print("  go-only files:", len(only_g), list(sorted(only_g))[:5])
print(f"  mismatched: {len(mis)}  (msg-text only: {msgonly})")
for f in mis[:15]:
    print("   ", f)
    print("      rust:", json.dumps({k: v for k, v in r[f].items()})[:240])
    print("      go  :", json.dumps({k: v for k, v in g[f].items()})[:240])
sys.exit(1 if (mis or only_r or only_g) else 0)
PY
  [ $? -ne 0 ] && diffs=$((diffs+1))
done
echo "TOTAL: $total files, rust panics=$rpanics, go panics=$gpanics, roots-with-diffs=$diffs"
OUTER
