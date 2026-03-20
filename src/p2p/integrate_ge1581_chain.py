#!/usr/bin/env python3
"""
Integrate ge1821, ge1701, ge1581 into LiftingLemma_LeftPermutive.lean.

Structure:
- ge1821 covers n'=1821..1940, has sorry for n'≥1941
- ge1701 covers n'=1701..1820, calls ge1821 for n'≥1821
- ge1581 covers n'=1581..1700, calls ge1701 for n'≥1701
- ge1461 calls ge1581 for n'≥1581 (replacing existing sorry)

All three new lemmas are inserted BEFORE ge1461 (in reverse order: ge1821 first,
then ge1701, then ge1581, so ge1581 is just before ge1461 in the file).
"""

import sys

LEAN_FILE = "/Users/jonathanhill/src/p2p/P2p/LiftingLemma_LeftPermutive.lean"
GE1581_FILE = "/tmp/subcaseB_ge1581_fast.lean"
GE1701_FILE = "/tmp/subcaseB_ge1701_fast.lean"
GE1821_FILE = "/tmp/subcaseB_ge1821_fast.lean"

def read_ge_file(path):
    with open(path, 'r') as f:
        lines = f.readlines()
    # Fix the sorry chain: replace "· -- n'≥NEXT: TODO\n    sorry\n"
    # with a call to the next lemma
    return lines

def fix_sorry_chain(ge_lines, next_start, next_lemma_name):
    """Replace the final sorry with a call to the next lemma."""
    result = list(ge_lines)
    # Find the last sorry line
    sorry_idx = None
    for i in range(len(result) - 1, -1, -1):
        if result[i].strip() == 'sorry':
            sorry_idx = i
            break
    if sorry_idx is None:
        print(f"ERROR: No sorry found in ge file for {next_lemma_name}")
        return result

    # The comment is the line before sorry
    comment_idx = sorry_idx - 1
    # Get indentation of the comment line
    comment_line = result[comment_idx]
    sorry_indent = len(comment_line) - len(comment_line.lstrip())
    call_indent = ' ' * (sorry_indent + 2)

    # Replace sorry with call
    result[sorry_idx] = (
        f"{call_indent}exact {next_lemma_name} n' (by omega) m hm_even hm_low hm_ne_r hm_high hcase hts\n"
    )
    return result

def main():
    with open(LEAN_FILE, 'r') as f:
        lean_lines = f.readlines()

    print(f"Lean file: {len(lean_lines)} lines")

    # Read the three ge files
    ge1581_lines = read_ge_file(GE1581_FILE)
    ge1701_lines = read_ge_file(GE1701_FILE)
    ge1821_lines = read_ge_file(GE1821_FILE)

    print(f"ge1581 file: {len(ge1581_lines)} lines")
    print(f"ge1701 file: {len(ge1701_lines)} lines")
    print(f"ge1821 file: {len(ge1821_lines)} lines")

    # Fix the sorry chains
    # ge1581's sorry → call ge1701
    ge1581_fixed = fix_sorry_chain(
        ge1581_lines, 1701,
        'parity_sensitivity_even_subcaseB_ge1701'
    )
    # ge1701's sorry → call ge1821
    ge1701_fixed = fix_sorry_chain(
        ge1701_lines, 1821,
        'parity_sensitivity_even_subcaseB_ge1821'
    )
    # ge1821's sorry stays as sorry (no further lemma yet)
    ge1821_fixed = list(ge1821_lines)

    # Find ge1461 lemma (insertion point: before set_option for ge1461)
    ge1461_line = None
    for i, line in enumerate(lean_lines):
        if 'private lemma parity_sensitivity_even_subcaseB_ge1461' in line:
            ge1461_line = i
            break
    if ge1461_line is None:
        print("ERROR: Could not find ge1461 lemma")
        sys.exit(1)
    print(f"ge1461 lemma at line {ge1461_line + 1}")

    # Find the set_option line just before ge1461
    insert_line = None
    for i in range(ge1461_line - 1, max(ge1461_line - 6, -1), -1):
        if 'set_option maxHeartbeats' in lean_lines[i]:
            insert_line = i
            break
    if insert_line is None:
        insert_line = ge1461_line
    print(f"Insertion point for ge1581/ge1701/ge1821: line {insert_line + 1}")

    # Find the sorry inside ge1461 (n'≥1581 TODO)
    sorry_line = None
    for i, line in enumerate(lean_lines):
        if "n'≥1581: TODO" in line:
            sorry_line = i
            break
    if sorry_line is None:
        print("ERROR: Could not find '· -- n'≥1581: TODO'")
        sys.exit(1)
    print(f"Sorry location: line {sorry_line + 1}")

    # Verify next line is sorry
    if 'sorry' not in lean_lines[sorry_line + 1]:
        print(f"ERROR: Expected sorry, got: {lean_lines[sorry_line + 1]!r}")
        sys.exit(1)

    # Determine indentation and build call replacement
    sorry_indent = len(lean_lines[sorry_line]) - len(lean_lines[sorry_line].lstrip())
    call_indent = ' ' * (sorry_indent + 2)

    new_call_lines = [
        lean_lines[sorry_line],  # Keep the comment
        f"{call_indent}exact parity_sensitivity_even_subcaseB_ge1581 n' (by omega) m hm_even hm_low hm_ne_r hm_high hcase hts\n",
    ]

    # Build the block to insert: ge1821, ge1701, ge1581 (each with set_option wrapper)
    def wrap_with_set_option(ge_lines_fixed):
        block = ["set_option maxHeartbeats 800000000 in\n"] + ge_lines_fixed
        if block and not block[-1].endswith('\n'):
            block[-1] += '\n'
        block.append('\n')
        return block

    insert_block = (
        wrap_with_set_option(ge1821_fixed) +
        wrap_with_set_option(ge1701_fixed) +
        wrap_with_set_option(ge1581_fixed)
    )

    # Assemble new file
    new_lines = (
        lean_lines[:insert_line] +
        insert_block +
        lean_lines[insert_line:sorry_line] +
        new_call_lines +
        lean_lines[sorry_line + 2:]
    )

    print(f"New file will have {len(new_lines)} lines")
    print(f"(added {len(insert_block)} lines)")

    # Backup
    backup = LEAN_FILE + '.bak_pre_ge1581_chain'
    with open(backup, 'w') as f:
        f.writelines(lean_lines)
    print(f"Backup written: {backup}")

    # Write
    with open(LEAN_FILE, 'w') as f:
        f.writelines(new_lines)
    print(f"Written: {LEAN_FILE}")

    # Verify
    with open(LEAN_FILE, 'r') as f:
        verify_lines = f.readlines()

    for lemma in ['ge1581', 'ge1701', 'ge1821']:
        name = f'parity_sensitivity_even_subcaseB_{lemma}'
        found = any(name in l for l in verify_lines)
        print(f"  {lemma} lemma present: {found}")

    # Check call from ge1461 to ge1581
    found_call = any('parity_sensitivity_even_subcaseB_ge1581 n\'' in l for l in verify_lines)
    print(f"  ge1461→ge1581 call present: {found_call}")

    # Check call from ge1581 to ge1701
    found_call2 = any('parity_sensitivity_even_subcaseB_ge1701 n\'' in l for l in verify_lines)
    print(f"  ge1581→ge1701 call present: {found_call2}")

    # Check call from ge1701 to ge1821
    found_call3 = any('parity_sensitivity_even_subcaseB_ge1821 n\'' in l for l in verify_lines)
    print(f"  ge1701→ge1821 call present: {found_call3}")

    # Find remaining sorry
    for i, line in enumerate(verify_lines):
        if "n'≥1941: TODO" in line:
            print(f"\nRemaining sorry at line {i+1}: {line.rstrip()}")
            break

if __name__ == '__main__':
    main()
