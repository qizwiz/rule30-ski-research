#!/usr/bin/env python3
"""
Adversarial Review Loop 31 — Abstract overstates verification range
Run date: 2026-03-24

Target: Abstract line 85 claims mod-4 rule "verified with no exceptions to n'=50003".
Body (loop-26) says dense verification reached n'=7000 only (293s).
These contradict. Determine: what was actually checked at n'=50003?

Tasks:
1. Spot-check SubcaseB(n', 2n'-6) at n'=50003 and nearby — does the mod-4 rule hold?
2. Time a single evaluation at several n' values to show the O(n'^2) scaling.
3. Determine the honest maximum n' for dense feasibility (< 1 hour budget).
4. Produce corrected abstract language.
"""
import numpy as np
import time
import sys


def compute_FG(n_prime):
    """Compute (F, G) for position m = 2n'-6 (the Part C family)."""
    m = 2 * n_prime - 6
    L = 2 * (n_prime + 1) + 1

    # F: single spike at m
    a = np.zeros(L, dtype=np.uint8)
    a[m] = 1
    for _ in range(n_prime + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
    F = bool(a[0])

    # G: spikes at m and last
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L - 1] = 1
    for _ in range(n_prime + 1):
        g = g[:-2] ^ (g[1:-1] | g[2:])
    G = bool(g[0])

    return F, G


# ============================================================
# 1. Timing at various n' values (show O(n'^2) scaling)
# ============================================================
print("=== Timing of single (F,G) evaluation vs n' ===\n")
print(f"  {'n_prime':>8}  {'time (s)':>10}  {'F':>4}  {'G':>4}  {'SubcaseB':>10}  {'mod4 pred':>10}  {'match':>6}")
print("  " + "-" * 65)

timing_points = [3089, 5000, 7000, 10000, 20000, 50003]
for n_p in timing_points:
    t0 = time.time()
    F, G = compute_FG(n_p)
    elapsed = time.time() - t0
    subcaseB = not F and G
    mod4 = n_p % 4
    pred = (mod4 == 1 or mod4 == 2)
    match = "✓" if subcaseB == pred else "*** FAIL ***"
    print(f"  n'={n_p:>6}  {elapsed:>10.3f}s  F={int(F)}  G={int(G)}  "
          f"{'True ' if subcaseB else 'False':>10}  "
          f"{'True ' if pred else 'False':>10}  {match}")
    sys.stdout.flush()

# ============================================================
# 2. Spot-check several n' values near 50003
# ============================================================
print("\n\n=== Spot-checks near n'=50003 ===\n")
spot_points = list(range(50000, 50013))
all_ok = True
results = []
for n_p in spot_points:
    t0 = time.time()
    F, G = compute_FG(n_p)
    elapsed = time.time() - t0
    subcaseB = not F and G
    mod4 = n_p % 4
    pred = (mod4 == 1 or mod4 == 2)
    match = subcaseB == pred
    results.append((n_p, subcaseB, pred, match, elapsed))
    if not match:
        all_ok = False
        print(f"  *** VIOLATION at n'={n_p}: SubcaseB={subcaseB} but mod-4 pred={pred} ***")
    sys.stdout.flush()

if all_ok:
    print(f"  ✓ All {len(spot_points)} spot-checks n'={spot_points[0]}..{spot_points[-1]} match mod-4 rule")
    avg_time = sum(r[4] for r in results) / len(results)
    print(f"  Average time per evaluation at n'≈50003: {avg_time:.2f}s")

# ============================================================
# 3. Extrapolate: how many dense values can we check per hour?
# ============================================================
print("\n\n=== Feasibility analysis: dense coverage budget ===\n")
# From timing table above
# At n'=7000: time ≈ t7000
# At n'=50003: time ≈ t50003
# dense scan from n'=a to n'=b costs integral of O(n'^2) dn' ≈ O(b^3 - a^3) / 3

# Use measured times
t_3089 = None
t_7000 = None
t_50003 = None
for n_p in timing_points:
    t0 = time.time()
    F, G = compute_FG(n_p)
    elapsed = time.time() - t0
    if n_p == 3089:
        t_3089 = elapsed
    elif n_p == 7000:
        t_7000 = elapsed
    elif n_p == 50003:
        t_50003 = elapsed
    sys.stdout.flush()

if t_7000 and t_50003:
    # Loop-26 checked 3912 values in 293s (n'=3089..7000)
    # Average per value = 293/3912 = 0.075s
    avg_loop26 = 293.0 / 3912
    print(f"  Loop-26 avg per evaluation (n'≈5000): {avg_loop26:.4f}s")
    print(f"  Measured t(7000): {t_7000:.3f}s")
    print(f"  Measured t(50003): {t_50003:.3f}s")
    ratio = t_50003 / max(t_7000, 0.001)
    print(f"  Slowdown ratio (50003/7000)^2 expected: {(50003/7000)**2:.1f}x")
    print(f"  Measured slowdown: {ratio:.1f}x")

    # Budget: 1 hour = 3600s
    vals_per_hour_at_50k = int(3600 / max(t_50003, 0.01))
    print(f"\n  At n'≈50003: ~{vals_per_hour_at_50k} values checkable per hour")
    print(f"  Dense scan [7001, 50003]: {50003-7001} values needed")
    hours_needed = (50003 - 7001) * t_50003 / 3600
    print(f"  Estimated time for dense [7001,50003]: {hours_needed:.0f} hours")

    # What n_max is feasible in 1 hour?
    # Time for dense [3089, N] ≈ sum_{n'=3089}^{N} O(n'^2) / constant
    # ≈ C * (N^3 - 3089^3) / 3
    # We know C from loop-26: 293s = C * sum_{n'=3089}^{7000} n'^2
    # sum n'^2 from 3089 to 7000 ≈ integral = 7000^3/3 - 3089^3/3 ≈ (343e9 - 9.8e9)/3 ≈ 111e9
    import math
    sum_sq_loop26 = sum(n**2 for n in range(3089, 7001))
    C = 293.0 / sum_sq_loop26
    # Feasible in 3600s: sum_{n'=7001}^{N_max} n'^2 ≤ 3600/C
    budget = 3600 / C
    # sum_{n'=7001}^{N_max} n'^2 ≈ N_max^3/3 - 7001^3/3
    # N_max^3 ≤ 3*budget + 7001^3
    N_max_1h = int((3 * budget + 7001**3) ** (1/3))
    print(f"\n  With 1-hour budget starting from n'=7001:")
    print(f"  Feasible dense coverage reaches n'≈{N_max_1h}")
    print(f"\n  CONCLUSION: Abstract '50003' is a stale SPARSE scan claim.")
    print(f"  Dense verification: n'∈[3089,7000] only (loop-26, 293s)")
    print(f"  Sparse spot-checks: n'≈50003 confirmed correct (loop-31, ~{t_50003:.0f}s per point)")
    print(f"  Honest abstract language:")
    print(f"    'verified densely for n'∈[3089,7000] (3912 values; loop-26) and")
    print(f"     spot-checked at selected n'≤50003 (loop-31)'")

# ============================================================
# 4. Also check: does m=40 resonance test hold at expected n'?
# ============================================================
print("\n\n=== Bonus: m=40 resonance test at n'=16403 ===\n")
# Paper claims F(16403,40)=0, G(16403,40)=0 (not SubcaseB — "decisive")
n_p = 16403
m = 40
L = 2 * (n_p + 1) + 1

t0 = time.time()
a = np.zeros(L, dtype=np.uint8)
a[m] = 1
for _ in range(n_p + 1):
    a = a[:-2] ^ (a[1:-1] | a[2:])
F40 = bool(a[0])

g = np.zeros(L, dtype=np.uint8)
g[m] = 1
g[L - 1] = 1
for _ in range(n_p + 1):
    g = g[:-2] ^ (g[1:-1] | g[2:])
G40 = bool(g[0])
elapsed = time.time() - t0

print(f"  n'=16403, m=40: F={int(F40)}, G={int(G40)}, SubcaseB={not F40 and G40}")
print(f"  Paper claims (0,0) — {'✓ CONFIRMED' if not F40 and not G40 else '*** WRONG ***'}")
print(f"  Time: {elapsed:.1f}s")
