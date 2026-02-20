"""
ski_parse.py — single source of truth for SKI soup log parsing.

The epoch line format is:
  E NNNNNNNN | H=x.xxx u=D/D | name=val | name=val | ... | rate/s

This module parses it generically — no hardcoded metric names.
Adding a metric to *metrics* in ski-soup-v10.lisp automatically
appears here with zero changes.
"""

import re
from typing import Optional

# Fixed fields at the start of every epoch line
_EPOCH_HEAD = re.compile(
    r"E\s*(\d+)\s*\|\s*H=([\d.]+)\s+u=(\d+)/(\d+)\s*\|"
)

# Generic metric: name=value pairs  (name may contain / like ops/int)
_METRIC_RE = re.compile(r"\b([\w/]+)=([\d.]+)")

# Rate at end: number/s
_RATE_RE = re.compile(r"([\d.]+)/s")


def parse_epoch_line(line: str) -> Optional[dict]:
    """
    Parse one epoch report line into a dict.

    Always-present keys: epoch, H, unique, total
    Dynamic keys: whatever name=val pairs appear (ops/int, reps, cat, RAF, cyc, ...)
    Optional key: rate  (from trailing N/s)

    Returns None if the line doesn't match.
    """
    m = _EPOCH_HEAD.search(line)
    if not m:
        return None

    result = {
        "epoch":  int(m.group(1)),
        "H":      float(m.group(2)),
        "unique": int(m.group(3)),
        "total":  int(m.group(4)),
    }

    # Parse all name=val pairs after the header
    tail = line[m.end():]
    for km in _METRIC_RE.finditer(tail):
        name, val = km.group(1), km.group(2)
        # Coerce to int if it looks like one, else float
        result[name] = int(val) if "." not in val else float(val)

    # Rate
    rm = _RATE_RE.search(tail)
    if rm:
        result["rate"] = float(rm.group(1))

    return result


def parse_log(log_path: str) -> list[dict]:
    """Parse all epoch lines from a log file. Returns list of readings dicts."""
    try:
        lines = open(log_path).read().splitlines()
    except FileNotFoundError:
        return []
    return [r for r in (parse_epoch_line(l) for l in lines) if r is not None]
