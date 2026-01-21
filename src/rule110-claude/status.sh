#!/bin/bash
# status.sh - Quick status check for Claude to poll
# Outputs compact JSON-like status

STATUS_FILE="/Users/jonathanhill/src/rule110-claude/status.txt"
LOG_FILE="/Users/jonathanhill/src/rule110-claude/search.log"
RESULTS_DIR="/Users/jonathanhill/src/rule110-claude/results"

{
    echo "=== GENESIS STATUS $(date '+%H:%M:%S') ==="

    # Is search running?
    if pgrep -f "local-runner.lisp" > /dev/null; then
        echo "SEARCH: RUNNING (pid $(pgrep -f local-runner.lisp))"
    else
        echo "SEARCH: IDLE"
    fi

    # Latest progress from log
    if [ -f "$LOG_FILE" ]; then
        echo ""
        echo "LATEST PROGRESS:"
        grep -E "^Gen |SUCCESS|\*\*\*|SEARCHING FOR:" "$LOG_FILE" | tail -8
    fi

    # Results found
    echo ""
    echo "DISCOVERIES:"
    if [ -d "$RESULTS_DIR" ] && [ "$(ls -A $RESULTS_DIR 2>/dev/null)" ]; then
        for f in "$RESULTS_DIR"/*.lisp; do
            if [ -f "$f" ]; then
                name=$(basename "$f" .lisp)
                # Check if verified (position >= 0)
                if grep -q "verified-position [0-9]" "$f"; then
                    echo "  ✓ $name (VERIFIED)"
                else
                    echo "  ? $name (partial)"
                fi
            fi
        done
    else
        echo "  (none yet)"
    fi

    echo ""
    echo "=== END STATUS ==="
} > "$STATUS_FILE"

cat "$STATUS_FILE"
