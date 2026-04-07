#!/usr/bin/env python3
"""
Shadow Cartography: Map shadow regions in the Rule 30 AllEssential induction proof.

Shadow region (n, j): positions where dChain(n+1, j) == False AND dChain(n, j) == False.
These are the ONLY positions where the AllEssential induction proof requires the
unproved lifting_lemma axiom (boundaries and dChain-active positions are handled
by other arguments).

dChain recurrence (diagonal sensitivity chain):
  dChain(t, 0) = True       (right boundary always active)
  dChain(0, k) = False       for k >= 1
  dChain(t+1, 1) = rule30Local(dChain(t,1), True, False)
  dChain(t+1, k+2) = rule30Local(dChain(t,k+2), dChain(t,k+1), dChain(t,k))

rule30Local(a, b, c) = a XOR (b OR c)

For each shadow (n, j), we search for a sensitivity witness: a config c of length
2*(n+1)+1 such that rule30_center(n+1, c) != rule30_center(n+1, flip(c, j)).
"""

import random
from collections import defaultdict

# ---------- Rule 30 core ----------

def rule30_local(a, b, c):
    return a ^ (b | c)

def rule30_center(T, config):
    """Evolve config (length 2T+1) for T steps, return the single remaining cell."""
    tape = list(config)
    assert len(tape) == 2 * T + 1, f"Expected length {2*T+1}, got {len(tape)}"
    for _ in range(T):
        new_tape = []
        for i in range(len(tape) - 2):
            new_tape.append(rule30_local(tape[i], tape[i+1], tape[i+2]))
        tape = new_tape
    assert len(tape) == 1, f"After {T} steps, tape has length {len(tape)}, expected 1"
    return tape[0]

def flip_at(config, j):
    c = list(config)
    c[j] ^= 1
    return c

# ---------- dChain computation ----------

def compute_dchain(max_t, max_k):
    """Compute dChain(t, k) for 0 <= t <= max_t, 0 <= k <= max_k."""
    dc = [[False] * (max_k + 1) for _ in range(max_t + 1)]

    # Base: dChain(t, 0) = True for all t
    for t in range(max_t + 1):
        dc[t][0] = True

    # dChain(0, k) = False for k >= 1 (already initialized)

    for t in range(max_t):
        # dChain(t+1, 1) = rule30Local(dChain(t,1), True, False)
        if max_k >= 1:
            dc[t+1][1] = rule30_local(dc[t][1], True, False)

        # dChain(t+1, k+2) = rule30Local(dChain(t,k+2), dChain(t,k+1), dChain(t,k))
        for k in range(max_k - 1):
            dc[t+1][k+2] = rule30_local(dc[t][k+2], dc[t][k+1], dc[t][k])

    return dc

# ---------- Shadow enumeration ----------

def find_shadows(dc, max_n):
    """Find all shadow (n, j) pairs for n in 0..max_n.
    Shadow: dChain(n+1, j) == False AND dChain(n, j) == False.
    j ranges over interior positions 1..2n+1 (boundaries handled separately)."""
    shadows = []
    for n in range(max_n + 1):
        for j in range(1, 2*n + 2):  # interior positions for level n+1
            if not dc[n+1][j] and not dc[n][j]:
                shadows.append((n, j))
    return shadows

# ---------- Witness search ----------

def find_witness(n, j, max_random=200):
    """Find a config c of length 2*(n+1)+1 where flipping bit j changes the center output.
    Returns (witness_type, config) or (None, None)."""
    T = n + 1
    L = 2 * T + 1

    if j >= L:
        return None, None

    # Strategy 1: spike configs (single 1 at position p)
    for p in range(L):
        config = [0] * L
        config[p] = 1
        orig = rule30_center(T, config)
        flipped = rule30_center(T, flip_at(config, j))
        if orig != flipped:
            return ("spike@%d" % p, config)

    # Strategy 2: all-ones, flip at j
    config = [1] * L
    orig = rule30_center(T, config)
    flipped = rule30_center(T, flip_at(config, j))
    if orig != flipped:
        return ("all-ones", config)

    # Strategy 3: random configs
    rng = random.Random(42 + n * 1000 + j)
    for _ in range(max_random):
        config = [rng.randint(0, 1) for _ in range(L)]
        orig = rule30_center(T, config)
        flipped = rule30_center(T, flip_at(config, j))
        if orig != flipped:
            return ("random", config)

    return None, None

# ---------- Main ----------

def main():
    MAX_N = 60
    MAX_T = MAX_N + 2
    MAX_K = 2 * (MAX_N + 1) + 2

    print("=" * 80)
    print("SHADOW CARTOGRAPHY: Rule 30 AllEssential proof shadow regions")
    print("=" * 80)

    # Step 1: Compute dChain
    print(f"\nComputing dChain for t=0..{MAX_T}, k=0..{MAX_K}...")
    dc = compute_dchain(MAX_T, MAX_K)

    # Visualize dChain for small t, k
    print("\ndChain(t, k) for t=0..15, k=0..20:")
    print("t\\k ", end="")
    for k in range(21):
        print(f"{k:2d}", end="")
    print()
    for t in range(16):
        print(f"{t:3d} ", end="")
        for k in range(21):
            print(" #" if dc[t][k] else " .", end="")
        print()

    # Step 2: Find shadows
    print(f"\nEnumerating shadow regions for n=0..{MAX_N}...")
    shadows = find_shadows(dc, MAX_N)
    print(f"Found {len(shadows)} shadow (n,j) pairs.\n")

    # Step 3: Find witnesses
    print(f"{'n':>4} {'j':>4} {'witness':>12}")
    print("-" * 30)

    witness_found = 0
    witness_missing = 0
    shadow_by_n = defaultdict(list)
    witness_types = {}  # cache: (n, j) -> witness_type

    for n, j in shadows:
        shadow_by_n[n].append(j)
        wtype, wconfig = find_witness(n, j)
        witness_types[(n, j)] = wtype
        if wtype:
            witness_found += 1
            print(f"{n:4d} {j:4d} {wtype:>12s}")
        else:
            witness_missing += 1
            print(f"{n:4d} {j:4d} {'NONE':>12s}  *** DANGER ***")

    # Step 4: Summary stats
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"Total shadow pairs:     {len(shadows)}")
    print(f"Witnesses found:        {witness_found}")
    print(f"Witnesses missing:      {witness_missing}")

    # Density by level
    print(f"\n{'n':>4} {'shadows':>8} {'total_interior':>15} {'density':>10} {'j_values':>30}")
    print("-" * 75)
    for n in range(MAX_N + 1):
        total_interior = 2 * n + 1  # positions 1..2n+1
        n_shadows = len(shadow_by_n.get(n, []))
        density = n_shadows / total_interior if total_interior > 0 else 0
        j_vals = shadow_by_n.get(n, [])
        j_str = str(j_vals) if len(j_vals) <= 8 else str(j_vals[:8]) + "..."
        if n_shadows > 0 or n <= 10:
            print(f"{n:4d} {n_shadows:8d} {total_interior:15d} {density:10.4f} {j_str:>30s}")

    # Step 5: Pattern analysis
    print("\n" + "=" * 80)
    print("PATTERN ANALYSIS")
    print("=" * 80)

    # Check j mod small primes
    if shadows:
        print("\nShadow j values by n (first 30 levels with shadows):")
        count = 0
        for n in sorted(shadow_by_n.keys()):
            if count >= 30:
                break
            j_vals = shadow_by_n[n]
            print(f"  n={n:3d}: j in {j_vals}")
            count += 1

        # Check if j follows patterns mod small numbers
        print("\nModular analysis of j values:")
        for mod in [2, 3, 4, 5, 6, 7, 8]:
            residues = defaultdict(int)
            for n, j in shadows:
                residues[j % mod] += 1
            print(f"  j mod {mod}: {dict(sorted(residues.items()))}")

        # Check j - n patterns
        print("\nDifference (j - n) analysis:")
        diffs = defaultdict(int)
        for n, j in shadows:
            diffs[j - n] += 1
        print(f"  j - n values: {dict(sorted(diffs.items()))}")

        # Check j / (n+1) ratios
        print("\nRatio j/(n+1) analysis:")
        ratios = defaultdict(int)
        for n, j in shadows:
            ratio = round(j / (n + 1), 2)
            ratios[ratio] += 1
        sorted_ratios = sorted(ratios.items())
        if len(sorted_ratios) <= 30:
            print(f"  j/(n+1) values: {dict(sorted_ratios)}")
        else:
            print(f"  j/(n+1) has {len(sorted_ratios)} distinct values (showing top 10):")
            for ratio, cnt in sorted(sorted_ratios, key=lambda x: -x[1])[:10]:
                print(f"    {ratio:.2f}: {cnt} times")

        # Check if shadows grow linearly or faster
        print("\nShadow count growth:")
        for n in range(0, MAX_N + 1, 5):
            sc = len(shadow_by_n.get(n, []))
            ti = 2 * n + 1
            print(f"  n={n:3d}: {sc:4d} shadows / {ti:4d} interior = {sc/ti:.4f}" if ti > 0 else f"  n={n:3d}: 0")

    # Step 6: Additional structural analysis
    print("\n" + "=" * 80)
    print("STRUCTURAL ANALYSIS")
    print("=" * 80)

    # j=3 always a shadow when n ≡ 0 mod 4?
    j3_shadows = [n for n, j in shadows if j == 3]
    print(f"\nLevels n where j=3 is a shadow: {j3_shadows}")
    print(f"  n mod 4 values: {[n % 4 for n in j3_shadows]}")
    print(f"  All n ≡ 0 mod 4? {all(n % 4 == 0 for n in j3_shadows)}")

    # Check: for n ≡ 0 mod 4, is j=3 ALWAYS a shadow?
    shadow_set = set(shadows)
    n_mod4_0 = [n for n in range(MAX_N + 1) if n % 4 == 0 and n >= 4]
    j3_missing = [n for n in n_mod4_0 if (n, 3) not in shadow_set]
    print(f"  n ≡ 0 mod 4 (n>=4) where j=3 is NOT shadow: {j3_missing}")

    # Right-edge shadows: j near 2*(n+1)
    print("\nRight-edge shadows (j >= 2*n):")
    right_edge = [(n, j) for n, j in shadows if j >= 2*n]
    for n, j in right_edge[:20]:
        print(f"  n={n}, j={j}, 2*(n+1)={2*(n+1)}, offset from right = {2*(n+1) - j}")

    # Shadow pairs (consecutive j at same n)
    print("\nConsecutive j-pairs at same n:")
    for n in sorted(shadow_by_n.keys()):
        j_vals = sorted(shadow_by_n[n])
        pairs = [(j_vals[i], j_vals[i+1]) for i in range(len(j_vals)-1) if j_vals[i+1] == j_vals[i]+1]
        if pairs:
            print(f"  n={n}: consecutive pairs {pairs}")

    # Levels with NO shadows
    no_shadow = [n for n in range(MAX_N + 1) if n not in shadow_by_n]
    print(f"\nLevels with ZERO shadows: {no_shadow}")
    print(f"  n mod values: {[n % 8 for n in no_shadow if n >= 4]}")

    # Witness type analysis: which spike position is most common?
    print("\nWitness spike position distribution:")
    spike_pos_count = defaultdict(int)
    for (n, j), wtype in witness_types.items():
        if wtype and wtype.startswith("spike@"):
            pos = int(wtype.split("@")[1])
            spike_pos_count[pos] += 1
    for pos in sorted(spike_pos_count.keys()):
        print(f"  spike@{pos}: {spike_pos_count[pos]} times")

    # Step 7: dChain active positions analysis
    print("\n" + "=" * 80)
    print("dChain ACTIVE POSITIONS (first 16 levels)")
    print("=" * 80)
    for t in range(min(MAX_N + 2, 16)):
        active = [k for k in range(MAX_K + 1) if dc[t][k]]
        if active:
            print(f"  t={t:3d}: active at k={active}")

    # Sanity check: n=4, j=3 should be a shadow
    print("\n" + "=" * 80)
    print("SANITY CHECK")
    print("=" * 80)
    is_shadow_4_3 = (4, 3) in shadows
    print(f"  (n=4, j=3) is shadow: {is_shadow_4_3}")
    print(f"  dChain(5, 3) = {dc[5][3]}")
    print(f"  dChain(4, 3) = {dc[4][3]}")

if __name__ == "__main__":
    main()
