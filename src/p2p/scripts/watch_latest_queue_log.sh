#!/usr/bin/env bash
set -euo pipefail

ROOT="/Users/jonathanhill/src/p2p"
LATEST="$(ls -1t "$ROOT"/runtime/rule30_queue/*.log 2>/dev/null | head -n 1 || true)"

echo "Latest Queue Log"
echo "================"
if [[ -z "$LATEST" ]]; then
  echo "No packet log found yet."
  exit 0
fi

echo "$LATEST"
echo
tail -n 120 "$LATEST"
