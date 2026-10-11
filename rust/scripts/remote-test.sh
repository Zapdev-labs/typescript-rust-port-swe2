#!/usr/bin/env bash
# Sync the tree to the remote test host and run cargo test there.
# Usage: remote-test.sh [extra cargo test args...]
#   remote-test.sh                 # full workspace test
#   remote-test.sh -p tsc-core     # one crate
# See rust/SPEC.md §9.2 — tests run ONLY on dih@192.168.1.15.
set -euo pipefail

REMOTE_HOST="${TS_REMOTE_HOST:-dih@192.168.1.15}"

"$(dirname "$0")/remote-sync.sh"

# Remote env fixes (see scanner agent report): rust-lld SIGBUS-crashes on
# btrfs → GNU ld via -lld linker-features opt-out; target dir on tmpfs to
# avoid btrfs allocation ENOSPC; incremental off (tmpfs is not persistent).
# NOTE: `--workspace` overrides `-p` selections, so when -p args are given we
# drop it — in-flight crates otherwise fail the run.
if [[ "$*" == *"-p "* || "$*" == *"-p"* ]]; then
  SCOPE="$*"
else
  SCOPE="--workspace $*"
fi
ssh -o BatchMode=yes "$REMOTE_HOST" \
  "cd /tmp/TypeScript/rust && env CARGO_TARGET_DIR=$HOME/tsc-target CARGO_INCREMENTAL=0 RUSTFLAGS='-C linker-features=-lld -C debuginfo=0' \"\$HOME/.cargo/bin/cargo\" test $SCOPE"
