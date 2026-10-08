#!/usr/bin/env bash
# Sync the tree to the remote host and run a release-built binary there.
# Usage: remote-run.sh <cargo-run-args...>
#   remote-run.sh -p tsc-cli -- --version
set -euo pipefail

REMOTE_HOST="${TS_REMOTE_HOST:-dih@192.168.1.15}"

"$(dirname "$0")/remote-sync.sh"

ssh -o BatchMode=yes "$REMOTE_HOST" \
  "cd ~/TypeScript/rust && \"\$HOME/.cargo/bin/cargo\" run --release $*"
