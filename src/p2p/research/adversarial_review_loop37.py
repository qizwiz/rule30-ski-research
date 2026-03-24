#!/usr/bin/env python3
"""
Adversarial Review Loop 37 — Part C dense coverage extension to n'=15000
Run date: 2026-03-24

Target: Paper line 703-704:
  "verified densely for n'∈[3089,10000] with no exceptions (6912 values:
   loop-26 to n'=7000 in 293s; loop-32 extended to n'=10000 in 392s)"

The mod-4 rule for SubcaseB at m=2n'-6 has been verified to n'=10000.
Loop 32 did [7001,10000] in 392s. Extending to n'=15000 (5000 more values).

Each evaluation at n'~12500 takes ~0.29s (quadratic in n'), so ~1450s ≈ 24 min total.

Also verify: anti-correlation F+G=1 holds throughout (no exceptions to n'=15000).
Also verify: SubcaseB density exactly 1/2 (count hits/total in new range).
"""
import numpy as np
import time
import sys


def compute_F_and_G_shifting(n_prime):
    """
    Compute F(n', 2n'-6) and G(n', 2n'-6).
    m = 2n'-6, L = 2*(n'+1)+1 = 2n'+3.
    """
    m = 2 * n_prime - 6
    L = 2 * (n_prime + 1) + 1

    if m <= 0 or m >= L - 1:
        return None, None

    # F: single spike at m
    a = np.zeros(L, dtype=np.uint8)
    a[m] = 1
    for _ in range(n_prime + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
    F = int(a[0])

    # G: spikes at m and last
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L - 1] = 1
    for _ in range(n_prime + 1):
        g = g[:-2] ^ (g[1:-1] | g[2:])
    G = int(g[0])

    return F, G


print("=== Loop 37: Part C dense coverage extension to n'=15000 ===\n")
print("  Target: paper claims mod-4 rule verified to n'=10000.")
print("  Extending dense verification [10001, 15000] for SubcaseB(n', 2n'-6).\n")
print("  Recall: SubcaseB iff n'≡1,2 mod 4 (for n'≥3089).\n")

N_START = 10001
N_END = 15001  # exclusive

total_t = time.time()
violations = []
anticorr_violations = []
hits = 0
total = 0
mod4_violations = []

print("  Scanning n' = 10001..15000...")
print("  (Reporting every 500 n' values)\n")

report_interval = 500
last_report = N_START

for n_p in range(N_START, N_END):
    F, G = compute_F_and_G_shifting(n_p)
    if F is None:
        continue

    SubcaseB = (F == 0 and G == 1)
    expected_SubcaseB = (n_p % 4 == 1 or n_p % 4 == 2)

    if SubcaseB:
        hits += 1
    total += 1

    # Check mod-4 rule
    if SubcaseB != expected_SubcaseB:
        violations.append((n_p, F, G, SubcaseB, expected_SubcaseB))

    # Check anti-correlation F+G=1
    if F + G != 1:
        anticorr_violations.append((n_p, F, G))

    # Progress report
    if n_p - last_report >= report_interval:
        elapsed = time.time() - total_t
        rate = (n_p - N_START + 1) / elapsed
        remaining = (N_END - n_p - 1) / rate if rate > 0 else 0
        print(f"  n'={n_p}: {n_p-N_START+1}/{N_END-N_START} done, "
              f"{len(violations)} violations so far, "
              f"{elapsed:.0f}s elapsed, ~{remaining:.0f}s remaining")
        sys.stdout.flush()
        last_report = n_p

total_elapsed = time.time() - total_t
density = hits / total if total > 0 else 0

print(f"\n  Done. {total} values checked in {total_elapsed:.0f}s ({total_elapsed/total*1000:.1f}ms/eval)")
print(f"\n  === Results ===")
print(f"  SubcaseB hits: {hits}/{total} = {density:.6f} (expected 0.5)")
print(f"  Mod-4 rule violations: {len(violations)}")
print(f"  Anti-correlation (F+G=1) violations: {len(anticorr_violations)}")

if violations:
    print(f"\n  *** MOD-4 VIOLATIONS FOUND ***")
    for v in violations[:10]:
        print(f"    n'={v[0]}: F={v[1]}, G={v[2]}, SubcaseB={v[3]}, expected={v[4]}")
else:
    print(f"\n  ✓ Mod-4 rule holds for all n' in [10001, 15000]")
    print(f"  ✓ Paper correction: update '[3089,10000]' to '[3089,15000]' for dense coverage")
    print(f"  Total dense coverage: [3089,15000] = 11912 values checked")

if anticorr_violations:
    print(f"\n  *** ANTI-CORRELATION VIOLATIONS ***")
    for v in anticorr_violations[:10]:
        print(f"    n'={v[0]}: F={v[1]}, G={v[2]}, F+G={v[1]+v[2]} ≠ 1")
else:
    print(f"  ✓ Anti-correlation F+G=1 confirmed throughout [10001,15000]")
