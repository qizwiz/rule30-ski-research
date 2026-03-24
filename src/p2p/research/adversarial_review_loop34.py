#!/usr/bin/env python3
"""
Adversarial Review Loop 34 — m=82..200 G-check depth undocumented
Run date: 2026-03-24

Target: Paper line 626: "m=82,...,200: 0 SubcaseB in [3087,20001), triangle method"
The G-check depth is NEVER STATED. m=40..80 now has exhaustive coverage in [3087,7000).
m=82..200 (60 values) has unknown G-check depth from loop-24.

If loop-24 only did first-20 G-checks (as suggested by prior descriptions),
then m=82..200 has 37x less coverage than m=40..80.

Fix: run first-100 G-check for all m=82..200, triangle method. Fast (~3s × 60 = 180s).
Also: explicitly document G-check depth in paper.
"""
import numpy as np
import time
import sys


def compute_F_triangle(m, N_max):
    a = np.zeros(2 * N_max + 1, dtype=np.uint8)
    a[m] = 1
    F = np.zeros(N_max, dtype=np.uint8)
    for k in range(1, N_max + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
        F[k - 1] = a[0]
    return F


def compute_G_single(n_prime, m):
    L = 2 * (n_prime + 1) + 1
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L - 1] = 1
    for _ in range(n_prime + 1):
        g = g[:-2] ^ (g[1:-1] | g[2:])
    return bool(g[0])


print("=== Loop 34: m=82..200 first-100 G-check upgrade ===\n")
print("  Paper: 'triangle method (30s, 60 m-values)' — G-check depth unstated")
print("  m=40..80: exhaustive [3087,7000). m=82..200: unknown depth.")
print("  Running first-100 G-check for all even m=82..200\n")

N_MAX = 20001
all_active = []
total_t = time.time()

print(f"  {'m':>4}  {'F=0 cands':>10}  {'G-checked':>10}  {'SubcaseB':>10}  {'time':>6}")
print("  " + "-" * 55)

for m in range(82, 202, 2):
    t0 = time.time()
    F = compute_F_triangle(m, N_MAX)
    candidates = list(np.where(F[3087:N_MAX] == 0)[0] + 3087)

    hits = []
    checked = min(100, len(candidates))
    for n_p in candidates[:100]:
        if compute_G_single(int(n_p), m):
            hits.append(int(n_p))

    elapsed = time.time() - t0
    if hits:
        all_active.append(m)
        print(f"  m={m:>3}  {len(candidates):>10}  {checked:>10}  *** ACTIVE {hits} ***  {elapsed:.1f}s")
    else:
        print(f"  m={m:>3}  {len(candidates):>10}  {checked:>10}  0             {elapsed:.1f}s")
    sys.stdout.flush()

total_elapsed = time.time() - total_t
print(f"\n  Total: {total_elapsed:.0f}s for 60 m-values")
if all_active:
    print(f"  *** ACTIVE POSITIONS FOUND: {all_active} ***")
else:
    print(f"  ✓ 0 SubcaseB for all m=82..200 (first-100 G-check each)")
    print(f"  Coverage upgrade: unknown depth → first-100 G-checks per m")
    print(f"  (exhaustive [3087,7000) upgrade for m=82..200 would take ~67 min total)")
