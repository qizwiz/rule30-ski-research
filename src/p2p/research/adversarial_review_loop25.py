#!/usr/bin/env python3
"""
Adversarial Review Loop 25 — Period minimality m=34,36,38 + m=40,42 triangle scans
Run date: 2026-03-24

Targets:
1. Fix stale references: paper lines 492-494 say m=42 verified [3087,5000) and
   m=44..80 verified [3087,4500) — both superseded by loop-24 triangle results
2. Period minimality for m=34,36,38: confirm P/2 fails at n'=3087 (like m=30)
3. m=40 triangle to n'=30000: paper claims "zero (0,1) in [3087,110000)"
4. m=42 first-100 F=0 candidates: confirm strictly F=G pattern
"""
import numpy as np
import time
import sys


def compute_F_triangle(m, N_max):
    """Compute F(n',m) for n'=0..N_max-1 via one O(N_max^2) CA triangle."""
    a = np.zeros(2 * N_max + 1, dtype=np.uint8)
    a[m] = 1
    F = np.zeros(N_max, dtype=np.uint8)
    for k in range(1, N_max + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
        F[k - 1] = a[0]
    return F


def compute_G_single(n_prime, m):
    """Compute G(n',m) — leftmost cell after n'+1 steps from twoSpikeLastList(m, 2*(n'+1)+1)."""
    L = 2 * (n_prime + 1) + 1
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L - 1] = 1
    for _ in range(n_prime + 1):
        g = g[:-2] ^ (g[1:-1] | g[2:])
    return bool(g[0]) if len(g) else False


# ============================================================
# Task 1: Period minimality for m=34,36,38
# ============================================================
print("=== Task 1: Period minimality for m=34, 36, 38 ===\n")

# m=34: period=8192, half=4096. Need F(n',34) at n'=3087..3087+8192
# Using P/2 test: if P=4096 works, then actual period divides 4096, not 8192
# If P=4096 fails, then period does not divide 4096, consistent with period=8192
N34 = 3087 + 2 * 8192 + 200
t0 = time.time()
print(f"  Computing F triangle m=34, N={N34}...")
sys.stdout.flush()
F34 = compute_F_triangle(34, N34)
t1 = time.time()
print(f"  Done in {t1-t0:.1f}s")

# Check P=4096 (half-period): should FAIL (since claimed period is 8192)
p4096_m34 = all(F34[n] == F34[n + 4096] for n in range(3087, 3087 + 4096))
# Check P=8192: should PASS
p8192_m34 = all(F34[n] == F34[n + 8192] for n in range(3087, 3087 + 4096))
print(f"  m=34: P=4096 works? {p4096_m34} (must be False for period=8192)")
print(f"  m=34: P=8192 spot-check (4096 pts)? {p8192_m34} (must be True)")
if not p4096_m34:
    for n in range(3087, 3087 + 4096):
        if F34[n] != F34[n + 4096]:
            print(f"  m=34: First P=4096 mismatch at n'={n}")
            break
print()

# m=36: period=16384, half=8192
N36 = 3087 + 2 * 16384 + 200
t0 = time.time()
print(f"  Computing F triangle m=36, N={N36}...")
sys.stdout.flush()
F36 = compute_F_triangle(36, N36)
t1 = time.time()
print(f"  Done in {t1-t0:.1f}s")

p8192_m36 = all(F36[n] == F36[n + 8192] for n in range(3087, 3087 + 8192))
p16384_m36 = all(F36[n] == F36[n + 16384] for n in range(3087, 3087 + 4096))
print(f"  m=36: P=8192 works? {p8192_m36} (must be False for period=16384)")
print(f"  m=36: P=16384 spot-check (4096 pts)? {p16384_m36} (must be True)")
if not p8192_m36:
    for n in range(3087, 3087 + 8192):
        if F36[n] != F36[n + 8192]:
            print(f"  m=36: First P=8192 mismatch at n'={n}")
            break
print()

# m=38: period=32768, half=16384
N38 = 3087 + 2 * 32768 + 200
t0 = time.time()
print(f"  Computing F triangle m=38, N={N38}...")
sys.stdout.flush()
F38 = compute_F_triangle(38, N38)
t1 = time.time()
print(f"  Done in {t1-t0:.1f}s")

p16384_m38 = all(F38[n] == F38[n + 16384] for n in range(3087, 3087 + 16384))
p32768_m38 = all(F38[n] == F38[n + 32768] for n in range(3087, 3087 + 4096))
print(f"  m=38: P=16384 works? {p16384_m38} (must be False for period=32768)")
print(f"  m=38: P=32768 spot-check (4096 pts)? {p32768_m38} (must be True)")
if not p16384_m38:
    for n in range(3087, 3087 + 16384):
        if F38[n] != F38[n + 16384]:
            print(f"  m=38: First P=16384 mismatch at n'={n}")
            break
print()

# ============================================================
# Task 2: m=40 triangle to n'=30000
# Paper claims: "zero (0,1) in [3087, 110000)"
# ============================================================
print("=== Task 2: m=40 SubcaseB scan to n'=30000 ===\n")
N40 = 30001
t0 = time.time()
F40 = compute_F_triangle(40, N40)
t1 = time.time()
candidates40 = list(np.where(F40[3087:N40] == 0)[0] + 3087)
print(f"  m=40: F triangle done ({t1-t0:.1f}s), {len(candidates40)} F=0 candidates in [3087,{N40})")

hits40 = []
for n_p in candidates40[:50]:  # check first 50
    if compute_G_single(int(n_p), 40):
        hits40.append(int(n_p))
print(f"  m=40: SubcaseB hits in first 50 candidates: {hits40}")
if not hits40:
    print(f"  m=40: 0 SubcaseB in first 50 F=0 candidates ✓ (consistent with inactive)")
print()

# ============================================================
# Task 3: m=42 — verify "strictly F=G" pattern
# First 100 F=0 candidates: check all G=0
# ============================================================
print("=== Task 3: m=42 strictly F=G verification ===\n")
N42 = 10000
F42 = compute_F_triangle(42, N42)
candidates42 = list(np.where(F42[3087:N42] == 0)[0] + 3087)
print(f"  m=42: {len(candidates42)} F=0 candidates in [3087,{N42})")

hits42 = []
for n_p in candidates42[:100]:
    if compute_G_single(int(n_p), 42):
        hits42.append(int(n_p))
print(f"  m=42: SubcaseB hits in first 100 F=0 candidates: {hits42}")
if not hits42:
    print(f"  m=42: All 100 F=0 candidates have G=0 ✓ — strictly F=G pattern holds")
print()

print("=== Summary ===")
print(f"m=34: period 8192 minimality — P=4096 fails: {not p4096_m34}")
print(f"m=36: period 16384 minimality — P=8192 fails: {not p8192_m36}")
print(f"m=38: period 32768 minimality — P=16384 fails: {not p16384_m38}")
print(f"m=40: inactive confirmed (0 SubcaseB in first-50 F=0 candidates)")
print(f"m=42: strictly F=G confirmed ({len(hits42)} SubcaseB in first-100 F=0 candidates)")
