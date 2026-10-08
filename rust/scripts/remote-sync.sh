#!/usr/bin/env bash
# Sync the working tree to the remote test host (dih@192.168.1.15:~/TypeScript).
# Mirrors the contract in rust/SPEC.md §9.2. Never deletes remote target/.
set -euo pipefail

REMOTE_HOST="${TS_REMOTE_HOST:-dih@192.168.1.15}"
REMOTE_DIR="${TS_REMOTE_DIR:-~/TypeScript}"
REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"

rsync -az --delete \
  --exclude '.git' \
  --exclude 'node_modules' \
  --exclude 'target' \
  --exclude 'tsc/testdata/baselines/local' \
  --exclude 'tsc/testdata/baselines/rust-local' \
  --exclude 'tsc/testdata/baselines/tmp' \
  "$REPO_ROOT/" "$REMOTE_HOST:$REMOTE_DIR/"
