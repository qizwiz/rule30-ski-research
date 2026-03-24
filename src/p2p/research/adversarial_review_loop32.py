#!/usr/bin/env python3
"""
Adversarial Review Loop 32 — m=40 and m=42 exhaustive G-check; Part C dense extension
Run date: 2026-03-24

Targets:
1. m=40: paper claims "first 100 G-checked: 0 SubcaseB". m=46..80 each had ~1960
   exhaustive G-checks in [3087,7000). m=40 (the most critical inactive position,
   immediately above last active m=38) has 37x less coverage. Fix the asymmetry.

2. m=42: only "first 50 G-checked". Same issue — bring to exhaustive in [3087,7000).

3. Part C dense extension: loop-31 showed dense [7001,10000] costs ~360s (6 min).
   Verify mod-4 rule holds densely for n' in [7001, 10000] — new coverage.
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


def compute_FG_partC(n_prime):
    """Compute (F,G) for Part C position m = 2n'-6."""
    m = 2 * n_prime - 6
    L = 2 * (n_prime + 1) + 1
    a = np.zeros(L, dtype=np.uint8)
    a[m] = 1
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L - 1] = 1
    for _ in range(n_prime + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
        g = g[:-2] ^ (g[1:-1] | g[2:])
    return bool(a[0]), bool(g[0])


# ============================================================
# Target 1: m=40 exhaustive G-check in [3087, 7000)
# ============================================================
print("=== Target 1: m=40 exhaustive G-check in [3087, 7000) ===\n")
print("  Paper: 'first 100 G-checked: 0 SubcaseB'")
print("  m=46..80: ~1960 exhaustive G-checks each — m=40 has 37x less coverage\n")

t0 = time.time()
print("  Computing F triangle for m=40 up to n'=6999...", end=" ", flush=True)
F40 = compute_F_triangle(40, 7000)
t_tri = time.time() - t0
print(f"done in {t_tri:.2f}s")

candidates_40 = list(np.where(F40[3087:7000] == 0)[0] + 3087)
print(f"  F=0 candidates in [3087,7000): {len(candidates_40)}")

hits_40 = []
t_g = time.time()
for n_p in candidates_40:
    if compute_G_single(int(n_p), 40):
        hits_40.append(int(n_p))
        print(f"  *** SubcaseB at n'={n_p}, m=40 ***")
elapsed_g = time.time() - t_g

print(f"\n  G-check complete: {elapsed_g:.1f}s for {len(candidates_40)} candidates")
if hits_40:
    print(f"  *** ACTIVE: m=40 has SubcaseB events: {hits_40} ***")
else:
    print(f"  ✓ 0 SubcaseB for m=40 in [3087,7000) — exhaustive ({len(candidates_40)} candidates checked)")
    print(f"  Previous coverage: 100 candidates. New coverage: {len(candidates_40)} candidates ({len(candidates_40)//100}x improvement)")

sys.stdout.flush()

# ============================================================
# Target 2: m=42 exhaustive G-check in [3087, 7000)
# ============================================================
print("\n\n=== Target 2: m=42 exhaustive G-check in [3087, 7000) ===\n")
print("  Paper: 'first 50 G-checked: 0 SubcaseB'")

t0 = time.time()
print("  Computing F triangle for m=42 up to n'=6999...", end=" ", flush=True)
F42 = compute_F_triangle(42, 7000)
t_tri = time.time() - t0
print(f"done in {t_tri:.2f}s")

candidates_42 = list(np.where(F42[3087:7000] == 0)[0] + 3087)
print(f"  F=0 candidates in [3087,7000): {len(candidates_42)}")

hits_42 = []
t_g = time.time()
for n_p in candidates_42:
    if compute_G_single(int(n_p), 42):
        hits_42.append(int(n_p))
        print(f"  *** SubcaseB at n'={n_p}, m=42 ***")
elapsed_g = time.time() - t_g

print(f"\n  G-check complete: {elapsed_g:.1f}s for {len(candidates_42)} candidates")
if hits_42:
    print(f"  *** ACTIVE: m=42 has SubcaseB events: {hits_42} ***")
else:
    print(f"  ✓ 0 SubcaseB for m=42 in [3087,7000) — exhaustive ({len(candidates_42)} candidates checked)")

sys.stdout.flush()

# ============================================================
# Target 3: Part C dense extension [7001, 10000]
# ============================================================
print("\n\n=== Target 3: Part C dense coverage extension [7001, 10000] ===\n")
print("  Current dense coverage: [3089, 7000] (loop-26, 293s)")
print("  Loop-31 estimated [7001,10000] ≈ 360s (6 min)\n")

t0 = time.time()
violations = []
all_ok = True
for n_p in range(7001, 10001):
    F, G = compute_FG_partC(n_p)
    subcaseB = not F and G
    mod4 = n_p % 4
    pred = (mod4 == 1 or mod4 == 2)
    if subcaseB != pred:
        violations.append((n_p, subcaseB, pred, F, G))
        all_ok = False
        print(f"  *** VIOLATION at n'={n_p}: SubcaseB={subcaseB}, F+G={int(F)+int(G)}, pred={pred} ***")
    # Also check anti-correlation F+G=1
    if int(F) + int(G) != 1:
        print(f"  *** ANTI-CORRELATION VIOLATION at n'={n_p}: F={int(F)}, G={int(G)} ***")
        all_ok = False
    if n_p % 500 == 1:
        elapsed = time.time() - t0
        print(f"  Progress: n'={n_p}, {elapsed:.0f}s elapsed...", flush=True)

elapsed_total = time.time() - t0
print(f"\n  Dense check [7001,10000] complete: {elapsed_total:.0f}s")
if all_ok:
    print(f"  ✓ ALL 3000 values match mod-4 rule — 0 violations")
    print(f"  ✓ Anti-correlation F+G=1 holds for all 3000 values")
    print(f"  New dense coverage: [3089, 10000] = 6912 values (was 3912)")
else:
    print(f"  *** {len(violations)} VIOLATIONS FOUND ***")

# ============================================================
# Summary
# ============================================================
print("\n\n=== Summary ===\n")
print(f"  m=40: {len(candidates_40)} candidates exhaustively G-checked in [3087,7000): "
      f"{'ACTIVE' if hits_40 else '0 SubcaseB ✓'}")
print(f"  m=42: {len(candidates_42)} candidates exhaustively G-checked in [3087,7000): "
      f"{'ACTIVE' if hits_42 else '0 SubcaseB ✓'}")
print(f"  Part C dense [7001,10000]: {'0 violations ✓' if all_ok else 'VIOLATIONS FOUND'}")
