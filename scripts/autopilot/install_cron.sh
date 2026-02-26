#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LINE="*/10 * * * * cd $ROOT_DIR && $ROOT_DIR/scripts/autopilot/autopilot_cycle.sh >> $ROOT_DIR/logs/autopilot/cron.log 2>&1"

( crontab -l 2>/dev/null | rg -v "autopilot_cycle.sh" || true; echo "$LINE" ) | crontab -

echo "cron installed: $LINE"
