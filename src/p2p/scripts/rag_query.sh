#!/usr/bin/env bash
# rag_query.sh — query the findings_index.md for relevant sections
#
# Usage: scripts/rag_query.sh "m=22 algebraic"
#        scripts/rag_query.sh "linearity corridor"
#
# Prints matching index lines (section title + line range + summary).
# Use the line ranges to read specific parts of research/findings.md.
#
# Example:
#   scripts/rag_query.sh "m=22" → prints all sections mentioning m=22
#   Then: sed -n '4715,4804p' research/findings.md   (or use Read tool)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
INDEX="$PROJECT_ROOT/research/findings_index.md"

if [[ ! -f "$INDEX" ]]; then
  echo "Index not found. Run: python3 scripts/rag_index.py" >&2
  exit 1
fi

if [[ $# -eq 0 ]]; then
  echo "Usage: $0 \"query terms\"" >&2
  echo "Example: $0 \"m=22 algebraic\"" >&2
  exit 1
fi

QUERY="$1"
# Build grep pattern: each space-separated word becomes a separate grep -i filter
RESULTS="$INDEX"

# Multi-word AND search: pipe through grep for each word
IFS=' ' read -ra WORDS <<< "$QUERY"
CMD="grep -i"
PATTERN="${WORDS[0]}"

# First grep — skip comment lines (single # only, not ## section headers)
MATCHES=$(grep -i "$PATTERN" "$INDEX" | grep -v "^# [A-Z]" || true)

# Filter by remaining words
for word in "${WORDS[@]:1}"; do
  MATCHES=$(echo "$MATCHES" | grep -i "$word" || true)
done

if [[ -z "$MATCHES" ]]; then
  echo "No sections found matching: $QUERY"
  echo ""
  echo "Index has $(grep -c '^## ' "$INDEX") sections. Try broader terms."
else
  COUNT=$(echo "$MATCHES" | wc -l | tr -d ' ')
  echo "Found $COUNT section(s) matching '$QUERY':"
  echo ""
  echo "$MATCHES"
  echo ""
  echo "To read a section: use Read tool on research/findings.md with offset/limit from the line range above"
fi
