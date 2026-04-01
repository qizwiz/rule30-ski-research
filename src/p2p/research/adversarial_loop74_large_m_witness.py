#!/usr/bin/env python3
"""
LARGE-M WITNESS STABILITY TEST

For large m (24,26,28,30,34,36,38): does the witness found at first firing
transfer to ALL subsequent firings (via period)?

If YES for any m: that m can be closed with a single native_decide base cert + period induction.
If NO: need per-residue witnesses.

Key question: what is the JOINT PERIOD of (SubcaseB fires AND witness w works)?
"""
import numpy as np

def rule30_center(n_steps, spike_positions, tape_size):
    row = np.zeros(tape_size, dtype=np.uint8)
    for p in spike_positions:
        if 0 <= p < tape_size:
            row[p] = 1
    for _ in range(n_steps):
        new = np.zeros(tape_size, dtype=np.uint8)
        new[1:-1] = row[:-2] ^ (row[1:-1] | row[2:])
        row = new
    return bool(row[n_steps])

def subcaseB_fires(np_val, m_val):
    level = np_val + 1
    tape = 2 * level + 1
    F = rule30_center(level, [m_val], tape)
    G = rule30_center(level, [m_val, tape-1], tape)
    return (not F) and G

def is_witness(np_val, m_val, w):
    level = np_val + 1
    tape = 2 * level + 1
    F_w = rule30_center(level, [w], tape)
    H_wm = rule30_center(level, [w, m_val], tape)
    return F_w != H_wm

def find_first_witness(np_val, m_val, max_w=100):
    """Find the smallest even w that witnesses sensitivity at (n', m)."""
    level = np_val + 1
    tape = 2 * level + 1
    for w in range(0, min(max_w, tape), 2):
        if w == m_val:
            continue
        if is_witness(np_val, m_val, w):
            return w
    return None

# Large active m values with their known periods
# Format: (m, period, first_fire, second_fire, ...)
large_m_data = [
    (24, 512,  [3339, 3851]),
    (26, 1024, [3340, 4364]),
    (28, 2048, [3341, 3345, 5389, 5393]),
    (30, 4096, [4114]),  # Only one known so far
    (34, 8192, [4112, 4116]),  # First cluster in [3087, 11279)
    (36, 16384, [4113, 4117]),  # First cluster
]

print("=== LARGE-M WITNESS STABILITY TEST ===")
print()

for m_val, period, known_fires in large_m_data:
    print(f"m={m_val} (period={period}):")

    # Find witness at first firing
    first_fire = known_fires[0]
    w_first = find_first_witness(first_fire, m_val)
    print(f"  First firing n'={first_fire}: witness w={w_first}")

    if w_first is None:
        print(f"  ERROR: no witness found up to w=100!")
        continue

    # Find all SubcaseB firings in first 2 periods + check witness
    scan_end = first_fire + min(2 * period, 4200)  # cap at reasonable size
    print(f"  Scanning [3087, {scan_end}) for SubcaseB and witness stability...")

    fires_found = []
    witness_ok = []
    witness_fail = []

    for np_val in range(3087, scan_end):
        if subcaseB_fires(np_val, m_val):
            fires_found.append(np_val)
            w_works = is_witness(np_val, m_val, w_first)
            if w_works:
                witness_ok.append(np_val)
            else:
                witness_fail.append(np_val)
                # Find the actual witness
                alt_w = find_first_witness(np_val, m_val)
                print(f"  WITNESS FAIL at n'={np_val}: w={w_first} fails, actual w={alt_w}")

    status = "STABLE" if not witness_fail else f"UNSTABLE ({len(witness_fail)} fails)"
    print(f"  → Firings: {fires_found}")
    print(f"  → Witness w={w_first}: {status}")
    print(f"    (OK: {len(witness_ok)}, Fail: {len(witness_fail)})")

    # Also check: if witness fails, try a few other candidates
    if witness_fail and len(witness_fail) < 20:
        print(f"  Searching for stable witness across all found firings...")
        all_fires = fires_found
        for w_try in range(0, 100, 2):
            if w_try == m_val:
                continue
            if all(is_witness(np_val, m_val, w_try) for np_val in all_fires):
                print(f"  ✓ STABLE WITNESS w={w_try} works for all {len(all_fires)} firings!")
                break
        else:
            print(f"  ✗ No stable witness in [0,100] for all {len(all_fires)} firings")

    print()

print()
print("=== SUMMARY: JOINT PERIOD ANALYSIS ===")
print()
print("For each m, the joint period of (SubcaseB AND witness) is:")
print("m=8: period 32, witness w=2 (STABLE — verified earlier)")
print("m=10: period 64, witness w=2 (STABLE — verified earlier)")
print("For large m: see results above")
