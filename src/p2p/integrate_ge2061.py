#!/usr/bin/env python3
"""Integrate ge2061 into LiftingLemma_LeftPermutive.lean."""
import sys, os

LEAN_FILE = "/Users/jonathanhill/src/p2p/P2p/LiftingLemma_LeftPermutive.lean"
GE_FILE = "/tmp/subcaseB_ge2061_fast.lean"
GE_NUM = 2061
NEXT_NUM = 2181

with open(LEAN_FILE, 'r') as f:
    lean_lines = f.readlines()
with open(GE_FILE, 'r') as f:
    ge_lines = f.readlines()

print(f"Lean file: {len(lean_lines)} lines, ge{GE_NUM}: {len(ge_lines)} lines")

# Find ge1941 (the one that will CALL ge2061)
target_lemma = 'private lemma parity_sensitivity_even_subcaseB_ge1941'
ge_line = next(i for i,l in enumerate(lean_lines) if target_lemma in l)
print(f"ge1941 at line {ge_line+1}")

# Find set_option just before it (insertion point)
insert_line = ge_line
for i in range(ge_line-1, max(ge_line-6,-1), -1):
    if 'set_option maxHeartbeats' in lean_lines[i]:
        insert_line = i
        break
print(f"Insert before line {insert_line+1}")

# Find the sorry comment for n'>=2061
sorry_comment = f"n'≥{GE_NUM}: TODO"
sorry_line = next(i for i,l in enumerate(lean_lines) if sorry_comment in l)
print(f"Sorry comment at line {sorry_line+1}")
assert 'sorry' in lean_lines[sorry_line+1], f"No sorry at line {sorry_line+2}"

# Indentation
ind = len(lean_lines[sorry_line]) - len(lean_lines[sorry_line].lstrip())
call = ' ' * (ind + 2)
next_lemma = f'parity_sensitivity_even_subcaseB_ge{GE_NUM}'
new_call_lines = [
    lean_lines[sorry_line],
    f"{call}exact {next_lemma} n' (by omega) m hm_even hm_low hm_ne_r hm_high hcase hts\n",
]

# Build block
block = ["set_option maxHeartbeats 800000000 in\n"] + ge_lines
if not block[-1].endswith('\n'):
    block[-1] += '\n'
block.append('\n')

new_lines = lean_lines[:insert_line] + block + lean_lines[insert_line:sorry_line] + new_call_lines + lean_lines[sorry_line+2:]
print(f"New file: {len(new_lines)} lines (+{len(block)})")

with open(LEAN_FILE + f'.bak_pre_ge{GE_NUM}', 'w') as f:
    f.writelines(lean_lines)
with open(LEAN_FILE, 'w') as f:
    f.writelines(new_lines)

# Verify
with open(LEAN_FILE, 'r') as f:
    vlines = f.readlines()
found_lemma = any(f'parity_sensitivity_even_subcaseB_ge{GE_NUM}' in l for l in vlines)
found_call = any(f'parity_sensitivity_even_subcaseB_ge{GE_NUM} n' in l for l in vlines)
print(f"ge{GE_NUM} present: {found_lemma}, call present: {found_call}")

for i, l in enumerate(vlines):
    if f"n'≥{NEXT_NUM}: TODO" in l:
        print(f"Remaining sorry at line {i+1}: {l.rstrip()}")
        break

sorry_count = sum(1 for l in vlines if l.strip() == 'sorry')
print(f"Total sorry lines: {sorry_count}")
