#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

LOCKFILE="$ROOT_DIR/logs/autopilot/.cycle.lock"
STOPFILE="$ROOT_DIR/.autopilot_stop"
ENABLEFILE="$ROOT_DIR/.autopilot_enabled"
WORKLOG="$ROOT_DIR/research/WORKLOG.md"
PROMPT_FILE="$ROOT_DIR/research/AUTOPILOT_PROMPT.md"
CYCLE_LOG="$ROOT_DIR/logs/autopilot/cycle-$(date +%Y%m%d-%H%M%S).log"
DRY_RUN="${AUTOPILOT_DRY_RUN:-0}"

if [[ ! -f "$ENABLEFILE" ]]; then
  echo "autopilot disabled: create $ENABLEFILE to enable" | tee -a "$CYCLE_LOG"
  exit 0
fi

if [[ -f "$STOPFILE" ]]; then
  echo "autopilot stop flag present: $STOPFILE" | tee -a "$CYCLE_LOG"
  exit 0
fi

mkdir -p "$ROOT_DIR/logs/autopilot"

if [[ -f "$LOCKFILE" ]]; then
  echo "cycle lock exists: $LOCKFILE" | tee -a "$CYCLE_LOG"
  exit 0
fi
trap 'rm -f "$LOCKFILE"' EXIT
printf '%s\n' "$$" > "$LOCKFILE"

if [[ ! -f "$WORKLOG" ]]; then
  printf "# WORKLOG\n\n" > "$WORKLOG"
fi

{
  echo "## $(date '+%Y-%m-%d %H:%M:%S %Z') cycle start"
  echo "- git status summary:"
  git status --short | sed -n '1,80p'
  echo "- quick checks:"
  (lean prize3/lean/Prize3Model.lean >/dev/null 2>&1 && echo "  - lean: pass") || echo "  - lean: fail"
  (python3 true_irreducibility_test.py >/dev/null 2>&1 && echo "  - irreducibility script: pass") || echo "  - irreducibility script: fail"
} >> "$CYCLE_LOG"

printf -- "- %s Autopilot cycle start.\n" "$(date '+%Y-%m-%d %H:%M:%S %Z')" >> "$WORKLOG"

PROMPT_CONTENT="$(cat "$PROMPT_FILE")"

# Non-interactive Codex run for one cycle.
# Uses explicit working directory and permissive execution policy as authorized by user.
if [[ "$DRY_RUN" == "1" ]]; then
  printf -- "- %s Autopilot dry-run cycle completed.\n" "$(date '+%Y-%m-%d %H:%M:%S %Z')" >> "$WORKLOG"
  echo "dry-run mode: skipped codex exec" >> "$CYCLE_LOG"
else
  if codex exec \
    -s danger-full-access \
    -a never \
    -c shell_environment_policy.inherit=all \
    "$PROMPT_CONTENT" \
    >> "$CYCLE_LOG" 2>&1; then
    printf -- "- %s Autopilot cycle completed successfully.\n" "$(date '+%Y-%m-%d %H:%M:%S %Z')" >> "$WORKLOG"
  else
    printf -- "- %s Autopilot cycle ended with non-zero status. See %s\n" "$(date '+%Y-%m-%d %H:%M:%S %Z')" "$CYCLE_LOG" >> "$WORKLOG"
  fi
fi

echo "cycle log: $CYCLE_LOG"
