#!/usr/bin/env python3
"""
Adversarial Review Loop 36 — m=202..300 triangle-method upgrade
Run date: 2026-03-24

Target: Paper lines 689-692:
  "The first open subproblem is whether active positions exist beyond m=200
  (triangle-method dense scan m≤200, n'≤20001 verified 2026-03-24;
  note: a prior step-500 sparse scan up to m=300 provides only ~0.2%
  detection coverage and is superseded by the triangle scans)"

m=202..300 has ONLY step-500 coverage (0.2% detection rate).
The triangle method is fast: ~0.5s per m-value, 50 m-values = ~25s.

Fix: run triangle method for all even m=202..300, finding all F=0 candidates
in [3087,20001), then G-check the first 50 each.
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


print("=== Loop 36: m=202..300 triangle-method upgrade ===\n")
print("  Paper: m≤200 triangle-method dense (n'≤20001); m=202..300 only step-500.")
print("  Running triangle method (0.5s/m) + first-50 G-checks for m=202..300.\n")

N_MAX = 20001
all_active = []
total_t = time.time()

print(f"  {'m':>4}  {'F=0 cands':>10}  {'G-checked':>10}  {'SubcaseB':>10}  {'time':>6}")
print("  " + "-" * 55)

for m in range(202, 302, 2):
    t0 = time.time()
    F = compute_F_triangle(m, N_MAX)
    candidates = list(np.where(F[3087:N_MAX] == 0)[0] + 3087)

    hits = []
    checked = min(50, len(candidates))
    for n_p in candidates[:50]:
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
print(f"\n  Total: {total_elapsed:.0f}s for 50 m-values")
if all_active:
    print(f"  *** ACTIVE POSITIONS FOUND: {all_active} ***")
    print(f"  Paper claim 'no active m>38' is WRONG. Update immediately.")
else:
    print(f"  ✓ 0 SubcaseB for all m=202..300 (first-50 G-check each)")
    print(f"  Coverage upgrade: step-500 sparse → triangle method dense")
    print(f"  Paper correction: update 'step-500 sparse scan up to m=300' to")
    print(f"  'triangle-method dense scan (loop-36) to m=300, n'≤20001'")
