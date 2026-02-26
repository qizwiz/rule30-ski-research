#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

INTERVAL_SECONDS="${AUTOPILOT_INTERVAL_SECONDS:-600}"
STOPFILE="$ROOT_DIR/.autopilot_stop"
PIDFILE="$ROOT_DIR/logs/autopilot/daemon.pid"
DAEMON_LOG="$ROOT_DIR/logs/autopilot/daemon.log"

mkdir -p "$ROOT_DIR/logs/autopilot"
printf '%s\n' "$$" > "$PIDFILE"
trap 'rm -f "$PIDFILE"' EXIT

printf '[%s] daemon start (interval=%ss)\n' "$(date '+%Y-%m-%d %H:%M:%S %Z')" "$INTERVAL_SECONDS" >> "$DAEMON_LOG"

while true; do
  if [[ -f "$STOPFILE" ]]; then
    printf '[%s] stop flag detected (%s), exiting daemon\n' "$(date '+%Y-%m-%d %H:%M:%S %Z')" "$STOPFILE" >> "$DAEMON_LOG"
    exit 0
  fi

  "$ROOT_DIR/scripts/autopilot/autopilot_cycle.sh" >> "$DAEMON_LOG" 2>&1 || true
  sleep "$INTERVAL_SECONDS"
done
