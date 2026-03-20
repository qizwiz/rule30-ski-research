#!/usr/bin/env python3
"""
Integrate parity_sensitivity_even_subcaseB_ge1581 into LiftingLemma_LeftPermutive.lean.

Finds:
1. The set_option line before ge1341 (insertion point)
2. The "· -- n'≥1581: TODO" sorry inside ge1461
Inserts ge1581 block before ge1341 and replaces the sorry with a call to ge1581.
"""

import sys

LEAN_FILE = "/Users/jonathanhill/src/p2p/P2p/LiftingLemma_LeftPermutive.lean"
GE1581_FILE = "/tmp/subcaseB_ge1581_full.lean"
GE_START = 1581

def main():
    with open(LEAN_FILE, 'r') as f:
        lean_lines = f.readlines()
    with open(GE1581_FILE, 'r') as f:
        ge_lines = f.readlines()

    print(f"Lean file: {len(lean_lines)} lines")
    print(f"ge1581 file: {len(ge_lines)} lines")

    # Find ge1341 lemma declaration
    ge1341_line = None
    for i, line in enumerate(lean_lines):
        if 'private lemma parity_sensitivity_even_subcaseB_ge1341' in line:
            ge1341_line = i
            break
    if ge1341_line is None:
        print("ERROR: Could not find ge1341 lemma")
        sys.exit(1)
    print(f"ge1341 lemma at line {ge1341_line + 1}")

    # Find the set_option line just before ge1341 (within 5 lines above)
    insert_line = None
    for i in range(ge1341_line - 1, max(ge1341_line - 6, -1), -1):
        if 'set_option maxHeartbeats' in lean_lines[i]:
            insert_line = i
            break
    if insert_line is None:
        insert_line = ge1341_line
    print(f"Insertion point: line {insert_line + 1}")

    # Find the sorry inside ge1461 (n'≥1581 TODO)
    sorry_line = None
    for i, line in enumerate(lean_lines):
        if "n'≥1581: TODO" in line:
            sorry_line = i
            break
    if sorry_line is None:
        print("ERROR: Could not find '· -- n'≥1581: TODO'")
        sys.exit(1)
    print(f"Sorry comment location: line {sorry_line + 1}")

    # Verify next line is sorry
    if 'sorry' not in lean_lines[sorry_line + 1]:
        print(f"ERROR: Expected sorry on line {sorry_line + 2}, got: {lean_lines[sorry_line + 1]!r}")
        sys.exit(1)

    # Determine indentation
    sorry_indent = len(lean_lines[sorry_line]) - len(lean_lines[sorry_line].lstrip())
    call_indent = ' ' * (sorry_indent + 2)

    # Build replacement for the sorry branch
    new_call_lines = [
        lean_lines[sorry_line],  # Keep the comment line
        f"{call_indent}exact parity_sensitivity_even_subcaseB_ge{GE_START} n' (by omega) m hm_even hm_low hm_ne_r hm_high hcase hts\n",
    ]

    # Build the ge1581 block to insert
    ge1581_block = [
        "set_option maxHeartbeats 800000000 in\n",
    ] + ge_lines
    if ge1581_block and not ge1581_block[-1].endswith('\n'):
        ge1581_block[-1] += '\n'
    ge1581_block.append('\n')

    # Assemble new file
    new_lines = (
        lean_lines[:insert_line] +
        ge1581_block +
        lean_lines[insert_line:sorry_line] +
        new_call_lines +
        lean_lines[sorry_line + 2:]  # skip old comment + sorry
    )

    print(f"New file will have {len(new_lines)} lines")
    print(f"(added {len(ge1581_block)} lines from ge1581 block)")

    # Backup
    backup = LEAN_FILE + '.bak_pre_ge1581'
    with open(backup, 'w') as f:
        f.writelines(lean_lines)
    print(f"Backup written: {backup}")

    # Write new file
    with open(LEAN_FILE, 'w') as f:
        f.writelines(new_lines)
    print(f"Written: {LEAN_FILE}")

    # Verify
    with open(LEAN_FILE, 'r') as f:
        verify_lines = f.readlines()

    found_ge1581 = any('parity_sensitivity_even_subcaseB_ge1581' in l for l in verify_lines)
    found_call = any(f'parity_sensitivity_even_subcaseB_ge{GE_START} n\'' in l for l in verify_lines)

    print(f"\nVerification:")
    print(f"  ge1581 lemma present: {found_ge1581}")
    print(f"  call site present: {found_call}")

    for i, line in enumerate(verify_lines):
        if f'parity_sensitivity_even_subcaseB_ge{GE_START} n\'' in line:
            print(f"\nCall site at line {i+1}:")
            for j in range(max(0, i-2), min(len(verify_lines), i+3)):
                print(f"  {j+1}: {verify_lines[j]}", end='')
            break

if __name__ == '__main__':
    main()
