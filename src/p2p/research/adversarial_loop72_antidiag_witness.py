#!/usr/bin/env python3
"""
ADVERSARIAL TEST: Is c = spike_{2n'-6} a universal SubcaseB witness?

Hypothesis: For each SubcaseB firing (n', m):
  - center({2n'-6}) = 0           [anti-diagonal zero, verified]
  - center({2n'-6, m}) = 1        [NEW CLAIM — test this]

If both hold, then c = spike_{2n'-6} is odd-false (2n'-6 is even) and
rule30n(c) = 0, rule30n(c with m flipped) = 1: sensitivity ∀ SubcaseB!

This would give a STRUCTURAL proof: no per-m case split, no period enumeration.
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

def check_subcaseB_and_witness(np_val, m_val):
    """Returns (is_subcaseB, F_antidiag, H_m_antidiag) for given n', m."""
    level = np_val + 1
    tape = 2 * level + 1
    last = tape - 1
    antidiag_pos = 2 * np_val - 6  # = tape - 9 = 2n'-6

    # SubcaseB condition
    F_m = rule30_center(level, [m_val], tape)
    G_ml = rule30_center(level, [m_val, last], tape)
    is_SB = (not F_m) and G_ml

    if not is_SB:
        return False, None, None

    # Anti-diagonal check: center({2n'-6}) should be 0
    F_antidiag = rule30_center(level, [antidiag_pos], tape)

    # Key hypothesis: center({2n'-6, m}) should be 1
    H_m_antidiag = rule30_center(level, [antidiag_pos, m_val], tape)

    return True, F_antidiag, H_m_antidiag

print("=== ADVERSARIAL TEST: anti-diagonal structural witness ===")
print()
print("Testing: For each SubcaseB (n', m), is center({2n'-6, m}) = 1?")
print("If yes: c = spike_{2n'-6} is a universal witness!")
print()

# Scan all active m values across multiple periods
active_m_with_periods = [
    (4, 8), (6, 16), (8, 32), (10, 64), (12, 64), (14, 64),
    (16, 256), (20, 256), (22, 256), (24, 512), (26, 1024), (28, 2048),
]

fails = []
passes = []
antidiag_nonzero = []

# Check 3 full periods for each active m starting from 3087
for m_val, period in active_m_with_periods:
    scan_end = 3087 + 3 * period
    print(f"m={m_val} (period={period}): scanning n'=[3087, {scan_end})")
    m_fails = 0
    m_passes = 0
    for np_val in range(3087, scan_end):
        is_SB, F_ad, H_m_ad = check_subcaseB_and_witness(np_val, m_val)
        if not is_SB:
            continue
        if F_ad:  # anti-diagonal should always be 0
            antidiag_nonzero.append((np_val, m_val, F_ad))
        if H_m_ad:  # WANT this to be 1
            m_passes += 1
            passes.append((np_val, m_val))
        else:  # center({2n'-6, m}) = 0 → witness FAILS
            m_fails += 1
            fails.append((np_val, m_val))
            if m_fails <= 3:
                print(f"  FAIL: n'={np_val}, m={m_val}: F_antidiag={F_ad}, H_m_antidiag={H_m_ad}")

    status = "PASS" if m_fails == 0 else f"FAIL ({m_fails} failures)"
    print(f"  → {status}: {m_passes} hits, {m_fails} failures")

print()
print("=== SUMMARY ===")
print(f"Total SubcaseB firings tested: {len(passes) + len(fails)}")
print(f"center({{2n'-6, m}}) = 1: {len(passes)}")
print(f"center({{2n'-6, m}}) = 0 (witness fails): {len(fails)}")
if antidiag_nonzero:
    print(f"ALERT: anti-diagonal nonzero at {len(antidiag_nonzero)} points!")
    for np_val, m_val, v in antidiag_nonzero[:5]:
        print(f"  n'={np_val}, m={m_val}: F_antidiag={v}")

if not fails and not antidiag_nonzero:
    print()
    print("✓✓✓ UNIVERSAL WITNESS CONFIRMED ✓✓✓")
    print("c = spike_{2n'-6} is a structural SubcaseB witness for ALL (n', m)!")
    print("PROOF PATH: center({2n'-6}) = 0 (anti-diagonal) AND center({2n'-6, m}) = 1")
    print("This eliminates all period-dependent case analysis!")
elif fails:
    print()
    print("✗ Structural witness does NOT work for all cases.")
    print(f"First 5 failures: {fails[:5]}")
    # Additional analysis: check if failures have a pattern
    fail_ms = sorted(set(m for _, m in fails))
    print(f"Failure m-values: {fail_ms}")
