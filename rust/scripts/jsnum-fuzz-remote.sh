#!/usr/bin/env bash
# Run the SPEC M1 jsnum gate on the remote host: generate a Node-oracle corpus
# of random f64 bit patterns and verify Number::string + from_string match JS
# byte-for-byte / IEEE-equal round-trip.
#   jsnum-fuzz-remote.sh [count]        — default 1e6 random doubles + edges
set -euo pipefail

REMOTE_HOST="${TS_REMOTE_HOST:-dih@192.168.1.15}"
COUNT="${1:-1000000}"
CORPUS="/tmp/jsnum-corpus.tsv"

"$(dirname "$0")/remote-sync.sh"

ssh -o BatchMode=yes "$REMOTE_HOST" "
  set -euo pipefail
  cd ~/TypeScript/rust
  node scripts/jsnum-fuzz-gen.mjs '$CORPUS' '$COUNT'
  \"\$HOME/.cargo/bin/cargo\" run --release -p tsc-jsnum --example fuzzcheck -- '$CORPUS'
"
