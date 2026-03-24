#!/usr/bin/env python3
"""
Adversarial Review Loop 26 — Verify "no exceptions through n'=50003" and near-boundary positions
Run date: 2026-03-24

Attacks:
1. Dense SubcaseB(n', 2n'-6) check — mod-4 rule — for n'=3089..7000
   Paper says "no exceptions through n'=50003" but dense computation to 50003 is infeasible.
   We establish honest maximum dense-verification range and report it.
2. Near-boundary positions last-16, last-24: extend scan from [3087,5500) to [3087,8000)
3. Also check F+G=1 anti-correlation densely in [3089, 7000)
"""
import numpy as np
import time
import sys


def compute_F_and_G_shifting(n_prime):
    """Compute F(n', 2n'-6) and G(n', 2n'-6) for the shifting large-m position.

    m = 2n'-6, tape size L = 2*(n'+1)+1 = 2n'+3.
    F: single spike at position m.
    G: spikes at position m and at position L-1 = 2n'+2.
    Returns (F, G) as booleans.
    """
    L = 2 * (n_prime + 1) + 1   # = 2n'+3
    m = 2 * n_prime - 6

    # F: spike at m
    a = np.zeros(L, dtype=np.uint8)
    a[m] = 1
    for _ in range(n_prime + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
    F = bool(a[0])

    # G: spikes at m and at L-1
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L - 1] = 1
    for _ in range(n_prime + 1):
        g = g[:-2] ^ (g[1:-1] | g[2:])
    G = bool(g[0])

    return F, G


def compute_F_and_G_near_boundary(n_prime, offset):
    """Compute SubcaseB(n', 2n'+2-offset) — spike at `offset` cells from last.

    m = 2n'+2 - offset, tape size L = 2n'+3.
    """
    L = 2 * (n_prime + 1) + 1
    m = 2 * n_prime + 2 - offset
    if m < 0 or m >= L:
        return False, False

    # F
    a = np.zeros(L, dtype=np.uint8)
    a[m] = 1
    for _ in range(n_prime + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
    F = bool(a[0])

    # G
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L - 1] = 1
    for _ in range(n_prime + 1):
        g = g[:-2] ^ (g[1:-1] | g[2:])
    G = bool(g[0])

    return F, G


# ============================================================
# Attack 1: Dense mod-4 verification for the shifting position
# ============================================================
print("=== Attack 1: Dense SubcaseB(n', 2n'-6) mod-4 rule verification ===\n")

N_DENSE = 7001   # Target: n'=3089..7000 (dense, every value)
t0 = time.time()

exceptions = []
fg_violations = []
n_checked = 0

for n_p in range(3089, N_DENSE):
    F, G = compute_F_and_G_shifting(n_p)
    expected_subcaseB = (n_p % 4 == 1) or (n_p % 4 == 2)
    actual_subcaseB = (not F) and G

    if actual_subcaseB != expected_subcaseB:
        exceptions.append((n_p, F, G, n_p % 4))

    if F == G:   # F+G != 1 if F=G (they must be opposite)
        fg_violations.append((n_p, F, G))

    n_checked += 1
    if n_checked % 1000 == 0:
        elapsed = time.time() - t0
        print(f"  n'={n_p}: {n_checked} checked, {len(exceptions)} exceptions, "
              f"{len(fg_violations)} F+G≠1 violations, {elapsed:.1f}s elapsed")
        sys.stdout.flush()

elapsed = time.time() - t0
print(f"\nDense check n'=3089..{N_DENSE-1} completed in {elapsed:.1f}s")
print(f"  Mod-4 exceptions: {exceptions[:10]}")
print(f"  F+G=1 violations: {fg_violations[:10]}")
if not exceptions and not fg_violations:
    print(f"  ✓ PERFECT: mod-4 rule holds for ALL n'=3089..{N_DENSE-1}, F+G=1 holds too")
print()

# ============================================================
# Attack 2: Near-boundary positions — extend scan to n'=8000
# ============================================================
print("=== Attack 2: Near-boundary positions last-16, last-24 in [3087, 8000) ===\n")

N_BOUNDARY = 8001
for offset_name, offset in [("last-16 (m=2n'-14)", 16), ("last-24 (m=2n'-22)", 24)]:
    t1 = time.time()
    hits = []
    for n_p in range(3087, N_BOUNDARY):
        F, G = compute_F_and_G_near_boundary(n_p, offset)
        if (not F) and G:
            hits.append((n_p, F, G))
    elapsed2 = time.time() - t1
    print(f"  {offset_name}: {len(hits)} SubcaseB events in [3087, {N_BOUNDARY-1}]  ({elapsed2:.1f}s)")
    if hits:
        print(f"    First hits: {hits[:5]}")
    else:
        print(f"    ✓ Zero SubcaseB events — extending paper's [3087,5500) to [3087,{N_BOUNDARY-1}]")
    sys.stdout.flush()

# ============================================================
# Quick extension: what is the HONEST dense-verification limit?
# ============================================================
print("\n=== Honest dense-verification budget ===")
print(f"Dense check n'=3089..{N_DENSE-1}: {elapsed:.1f}s")
print(f"Scaling: each doubling of N_max costs ~8x more compute")
print(f"  n'=3089..7000  ({N_DENSE-3089} values): {elapsed:.1f}s — DONE")
estimated_14000 = elapsed * 8
estimated_28000 = elapsed * 64
print(f"  n'=3089..14000 estimate: {estimated_14000:.0f}s ({estimated_14000/60:.1f}min)")
print(f"  n'=3089..28000 estimate: {estimated_28000:.0f}s ({estimated_28000/60:.1f}min)")
print(f"  n'=3089..50003 (paper claim): {elapsed * (50003/7000)**3:.0f}s — INFEASIBLE for dense check")
