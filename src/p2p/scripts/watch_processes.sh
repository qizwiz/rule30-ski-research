#!/usr/bin/env bash
set -euo pipefail

ROOT="/Users/jonathanhill/src/p2p"

echo "Rule30 Processes"
echo "================"
ps -Ao pid=,etime=,%cpu=,state=,command= | \
  rg 'CA_Array_m34_residues|run_rule30_queue|gemini |qwen |claude ' || true

echo
echo "Launchd"
echo "======="
launchctl list | rg 'p2p-loop' || true

echo
echo "Locks"
echo "====="
ls -l "$ROOT"/runtime/*.lock "$ROOT"/runtime/rule30_queue.lock 2>/dev/null || true
