#!/usr/bin/env python3
"""
rag_index.py — Build a section index for research/findings.md.

Outputs research/findings_index.md with one line per ## section:
  ## Section Title (lines X-Y): one-sentence summary

"Summary" is the first non-empty, non-header line of the section (trimmed to 120 chars).
"""

import os
import re

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(SCRIPT_DIR)
FINDINGS = os.path.join(PROJECT_ROOT, "research", "findings.md")
INDEX = os.path.join(PROJECT_ROOT, "research", "findings_index.md")

def build_index():
    with open(FINDINGS, "r") as f:
        lines = f.readlines()

    total = len(lines)
    sections = []  # list of (title, start_line_1indexed, end_line_1indexed)

    for i, line in enumerate(lines):
        if line.startswith("## "):
            title = line.strip()
            start = i + 1  # 1-indexed
            if sections:
                sections[-1] = sections[-1] + (i,)  # close previous
            sections.append((title, start))

    # Close last section
    if sections:
        last = sections[-1]
        if len(last) == 2:
            sections[-1] = last + (total,)

    index_lines = [
        "# findings.md Section Index",
        f"# Total lines: {total}",
        "# Format: TITLE (lines START-END): SUMMARY",
        "",
    ]

    for entry in sections:
        title, start, end = entry
        # Find first non-empty, non-header content line in this section
        summary = ""
        for j in range(start, min(end, start + 20)):  # look at next 20 lines
            raw = lines[j].strip() if j < len(lines) else ""
            if raw and not raw.startswith("#") and not raw.startswith("---") and not raw.startswith("```"):
                # Strip markdown bold/italics, truncate
                summary = re.sub(r"\*\*|__|\*|_", "", raw)[:120]
                break
        if not summary:
            summary = "(no summary available)"
        index_lines.append(f"{title} (lines {start}-{end}): {summary}")

    with open(INDEX, "w") as f:
        f.write("\n".join(index_lines) + "\n")

    print(f"Indexed {len(sections)} sections → {INDEX}")

if __name__ == "__main__":
    build_index()
