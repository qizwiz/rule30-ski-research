#!/usr/bin/env python3
"""
Integrate parity_sensitivity_even_subcaseB_ge1941 into LiftingLemma_LeftPermutive.lean.

Finds:
1. The set_option line before ge1821 (insertion point for ge1941)
2. The "· -- n'≥1941: TODO" sorry inside ge1821
Inserts ge1941 block before ge1821's set_option and replaces the sorry with a call to ge1941.
"""

import sys

LEAN_FILE = "/Users/jonathanhill/src/p2p/P2p/LiftingLemma_LeftPermutive.lean"
GE1941_FILE = "/tmp/subcaseB_ge1941_fast.lean"


def main():
    with open(LEAN_FILE, 'r') as f:
        lean_lines = f.readlines()
    with open(GE1941_FILE, 'r') as f:
        ge_lines = f.readlines()

    print(f"Lean file: {len(lean_lines)} lines")
    print(f"ge1941 file: {len(ge_lines)} lines")

    # Find ge1821 lemma declaration
    ge1821_line = None
    for i, line in enumerate(lean_lines):
        if 'private lemma parity_sensitivity_even_subcaseB_ge1821' in line:
            ge1821_line = i
            break
    if ge1821_line is None:
        print("ERROR: Could not find ge1821 lemma")
        sys.exit(1)
    print(f"ge1821 lemma at line {ge1821_line + 1}")

    # Find the set_option line just before ge1821 (within 5 lines above)
    insert_line = None
    for i in range(ge1821_line - 1, max(ge1821_line - 6, -1), -1):
        if 'set_option maxHeartbeats' in lean_lines[i]:
            insert_line = i
            break
    if insert_line is None:
        insert_line = ge1821_line
    print(f"Insertion point: line {insert_line + 1}")

    # Find the sorry inside ge1821 (n'≥1941 TODO)
    sorry_line = None
    for i, line in enumerate(lean_lines):
        if "n'≥1941: TODO" in line:
            sorry_line = i
            break
    if sorry_line is None:
        print("ERROR: Could not find '· -- n'≥1941: TODO'")
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
        f"{call_indent}exact parity_sensitivity_even_subcaseB_ge1941 n' (by omega) m hm_even hm_low hm_ne_r hm_high hcase hts\n",
    ]

    # Build the ge1941 block to insert
    ge1941_block = ["set_option maxHeartbeats 800000000 in\n"] + ge_lines
    if ge1941_block and not ge1941_block[-1].endswith('\n'):
        ge1941_block[-1] += '\n'
    ge1941_block.append('\n')

    print(f"ge1941 block: {len(ge1941_block)} lines (including set_option + trailing newline)")

    # Assemble new file
    new_lines = (
        lean_lines[:insert_line] +
        ge1941_block +
        lean_lines[insert_line:sorry_line] +
        new_call_lines +
        lean_lines[sorry_line + 2:]  # skip old comment + sorry
    )

    print(f"New file will have {len(new_lines)} lines")
    print(f"(added {len(ge1941_block)} lines from ge1941 block)")

    # Backup
    backup = LEAN_FILE + '.bak_pre_ge1941'
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

    found_ge1941 = any('parity_sensitivity_even_subcaseB_ge1941' in l for l in verify_lines)
    found_call = any("parity_sensitivity_even_subcaseB_ge1941 n'" in l for l in verify_lines)

    print(f"\nVerification:")
    print(f"  ge1941 lemma present: {found_ge1941}")
    print(f"  call site present: {found_call}")

    for i, line in enumerate(verify_lines):
        if "parity_sensitivity_even_subcaseB_ge1941 n'" in line and 'exact' in line:
            print(f"\nCall site at line {i+1}:")
            for j in range(max(0, i-2), min(len(verify_lines), i+3)):
                print(f"  {j+1}: {verify_lines[j]}", end='')
            break

    # Find remaining sorry
    for i, line in enumerate(verify_lines):
        if "n'≥2061: TODO" in line:
            print(f"\nRemaining sorry at line {i+1}: {line.rstrip()}")
            break
    else:
        sorry_count = sum(1 for l in verify_lines if l.strip() == 'sorry')
        print(f"\nNo '≥2061' sorry found. Total 'sorry' lines: {sorry_count}")


if __name__ == '__main__':
    main()
