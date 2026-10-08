#!/usr/bin/env bash
# Sync the tree to the remote test host and run cargo test there.
# Usage: remote-test.sh [extra cargo test args...]
#   remote-test.sh                 # full workspace test
#   remote-test.sh -p tsc-core     # one crate
# See rust/SPEC.md §9.2 — tests run ONLY on dih@192.168.1.15.
set -euo pipefail

REMOTE_HOST="${TS_REMOTE_HOST:-dih@192.168.1.15}"

"$(dirname "$0")/remote-sync.sh"

ssh -o BatchMode=yes "$REMOTE_HOST" \
  "cd ~/TypeScript/rust && \"\$HOME/.cargo/bin/cargo\" test --workspace $*"
