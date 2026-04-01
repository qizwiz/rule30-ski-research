#!/usr/bin/env python3
"""
STRUCTURAL WITNESS ANALYSIS:

SubcaseB at (n', m): F_m=0, G_{m,last}=1.
We KNOW a sensitive c exists (computationally) but need STRUCTURAL description.

Key questions:
1. Does a sensitive odd-free c ALWAYS exist? (check exhaustively for small cases)
2. What's the MINIMUM SIZE of the sensitive c (smallest even subset)?
3. Is the sensitive c always in a small neighborhood of m?
4. Is there a formula c = f(n', m) that works everywhere?

Approach: for each SubcaseB firing, find the LEXICOGRAPHICALLY SMALLEST odd-free
sensitive c. Look for patterns.
"""
import numpy as np
from itertools import combinations

def rule30_center_config(n_steps, config, tape_size):
    """config is a list of positions that are 1."""
    row = np.zeros(tape_size, dtype=np.uint8)
    for p in config:
        if 0 <= p < tape_size:
            row[p] = 1
    for _ in range(n_steps):
        new = np.zeros(tape_size, dtype=np.uint8)
        new[1:-1] = row[:-2] ^ (row[1:-1] | row[2:])
        row = new
    return bool(row[n_steps])

def find_min_witness(np_val, m_val, max_size=3):
    """Find the lexicographically smallest odd-free sensitive c for (n',m).
    Tries all subsets of even positions up to max_size.
    Returns (c, center_c, center_c_flip) or None if not found."""
    level = np_val + 1
    tape = 2 * level + 1
    # Even positions: 0, 2, 4, ..., tape-1 (all even)
    even_pos = [p for p in range(0, tape, 2) if p != m_val]

    # Check small subsets first
    for size in range(0, max_size + 1):
        for combo in combinations(even_pos, size):
            c = list(combo)
            c_flip = sorted(c + [m_val]) if m_val not in c else [x for x in c if x != m_val]
            v_c = rule30_center_config(level, c, tape)
            v_flip = rule30_center_config(level, c_flip, tape)
            if v_c != v_flip:
                return c, v_c, v_flip
    return None

print("=== STRUCTURAL WITNESS ANALYSIS ===")
print()
print("For each SubcaseB firing, find minimum odd-free sensitive c")
print()

# Test SubcaseB firings for active m values (first few firings only)
test_firings = [
    (3093, 4),  (3101, 4),  (3109, 4),
    (3094, 6),  (3098, 6),  (3110, 6),
    (3115, 8),  (3147, 8),  (3179, 8),
    (3120, 10), (3184, 10), (3248, 10),
    (3085, 12), (3145, 12), (3149, 14),
    (3209, 16), (3341, 20), (3342, 22),
    (3339, 24), (3340, 26), (3341, 28),
]

print(f"{'n':>6} {'m':>4}  {'c (sensitive witness)':40} {'center(c)':9} {'center(c+m)':11}")
print("-" * 80)

for np_val, m_val in test_firings:
    result = find_min_witness(np_val, m_val, max_size=3)
    if result is None:
        print(f"{np_val:>6} {m_val:>4}  NO WITNESS FOUND (up to size 3)")
    else:
        c, v_c, v_flip = result
        print(f"{np_val:>6} {m_val:>4}  {str(c):40} {str(v_c):9} {str(v_flip):11}")

print()
print("=== LOOKING FOR PATTERN IN WITNESSES ===")
print()
print("Key witness positions (subtract n' to normalize):")
for np_val, m_val in test_firings:
    result = find_min_witness(np_val, m_val, max_size=3)
    if result:
        c, v_c, v_flip = result
        normalized = [p - np_val for p in c]
        print(f"  n'={np_val}, m={m_val}: c={c} → normalized={normalized}")

print()
print("=== CHECKING: Is empty c EVER sensitive? (F_m=0 required) ===")
print("If c=[] is sensitive: center({}) ≠ center({m}), i.e., 0 ≠ F_m.")
print("But SubcaseB has F_m=0, so c=[] gives 0=0: NOT sensitive (as expected).")
print()
print("=== CHECKING: Is c=[last] EVER sensitive? ===")
print("c=[last]: center({last}) = F_last = 1.")
print("c+m=[last,m]: center({last,m}) = G_{m,last} = 1 (SubcaseB).")
print("So 1=1: NOT sensitive (as expected from check_direct_witness.py).")
print()

# The real investigation: look at size-1 witnesses (single even spike ≠ m, ≠ last)
print("=== SIZE-1 WITNESSES: which single spike w works? ===")
print()
for np_val, m_val in test_firings[:12]:
    level = np_val + 1
    tape = 2 * level + 1
    last = tape - 1
    small_w = []
    for w in range(0, min(60, tape), 2):
        if w == m_val or w == last:
            continue
        v_w = rule30_center_config(level, [w], tape)
        v_wm = rule30_center_config(level, [w, m_val], tape)
        if v_w != v_wm:
            small_w.append(w)
    print(f"  n'={np_val}, m={m_val}: size-1 witnesses in [0,60]={small_w[:8]}")
