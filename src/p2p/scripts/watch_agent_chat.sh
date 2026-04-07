#!/usr/bin/env bash
set -euo pipefail

ROOT="/Users/jonathanhill/src/p2p"
cd "$ROOT"
python3 scripts/agent_chat.py status --limit 16
