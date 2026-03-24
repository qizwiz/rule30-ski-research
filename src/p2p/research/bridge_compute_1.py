#!/usr/bin/env python3
"""
Bridge Compute 1 — Sensitive position structure for e_n; Path C exploration
Run date: 2026-03-24

After Attack 1 killed Path A, the remaining paths are:
B: information-theoretic (conditional on Prize 1)
C: reduction from general rule30 to fixed-input queries

This script:
1. Analyzes the PATTERN of sensitive positions for e_n (which k are sensitive?)
   — looking for structure that might inform path C
2. Tests a specific path C candidate: can rule30_n(c) be computed from s(n)
   via a simple XOR/perturbation argument?
3. Checks whether the NUMBER of sensitive positions is exactly n+1 for all n
   (which would be a clean theorem)
"""
import numpy as np
import sys


def rule30_n_center(c, n):
    """Compute Rule 30 center cell after n steps. Input length must be 2n+1."""
    a = c.astype(np.uint8).copy()
    for _ in range(n):
        if len(a) < 3:
            break
        a = a[:-2] ^ (a[1:-1] | a[2:])
    return int(a[0]) if len(a) > 0 else 0


def make_en(n):
    c = np.zeros(2*n+1, dtype=np.uint8)
    c[n] = 1
    return c


def sensitive_positions(n):
    """Return set of k where flipping e_n[k] changes rule30_n(e_n)."""
    en = make_en(n)
    sn = rule30_n_center(en, n)
    sens = []
    for k in range(2*n+1):
        flip = en.copy()
        flip[k] ^= 1
        if rule30_n_center(flip, n) != sn:
            sens.append(k)
    return sens, sn


# ============================================================
# 1. Analyze the sensitive position pattern
# ============================================================
print("=== Sensitive position analysis for e_n (n=1..30) ===\n")
print(f"  {'n':>3}  {'s(n)':>5}  {'#sens':>6}  {'#nonsens':>8}  {'first sensitive':>20}  {'last sensitive':>15}")
print("  " + "-" * 65)

counts = []
for n in range(1, 31):
    sens, sn = sensitive_positions(n)
    nonsens_count = (2*n+1) - len(sens)
    counts.append((n, len(sens), sn, sens))
    first_few = str(sens[:4]) if len(sens) > 4 else str(sens)
    last_few = str(sens[-3:]) if len(sens) > 3 else ""
    print(f"  n={n:>2}  s={sn}  {len(sens):>6}  {nonsens_count:>8}  {first_few:<20}  {last_few}")
    sys.stdout.flush()

# ============================================================
# 2. Is #sensitive exactly n+1? Or some other formula?
# ============================================================
print("\n\n=== Is #sensitive = f(n) for some simple f? ===\n")
print("  n, #sensitive, ratio to n:")
for n, cnt, sn, _ in counts:
    print(f"  n={n:>2}: #sens={cnt:>3}, cnt/n={cnt/n:.3f}, cnt-n={cnt-n:>3}, cnt-(n+1)={cnt-n-1:>3}")
    sys.stdout.flush()

# ============================================================
# 3. Path C candidate: perturbation reduction
# Test: can rule30_n(c XOR e_k) be expressed in terms of rule30_n(c) and s(n)?
# Specifically: does rule30_n(e_k) = s(n) XOR something simple?
# ============================================================
print("\n\n=== Path C: perturbation structure ===\n")
print("  Testing: does rule30_n(e_k) follow a pattern as k varies?")
print("  (e_k = single black cell at position k, length 2n+1)\n")

for n in [5, 10, 15, 20]:
    print(f"  n={n}: rule30_n(e_k) for k=0..{2*n}:")
    row = []
    for k in range(2*n+1):
        ek = np.zeros(2*n+1, dtype=np.uint8)
        ek[k] = 1
        row.append(rule30_n_center(ek, n))
    print(f"    {row}")
    # Check if it's symmetric
    sym = all(row[k] == row[2*n - k] for k in range(2*n+1))
    print(f"    Symmetric: {sym}, s(n)=rule30_n(e_n)={row[n]}")
    # How many k give output 1?
    ones = sum(row)
    print(f"    Outputs: {ones} ones, {2*n+1-ones} zeros")
    sys.stdout.flush()

# ============================================================
# 4. Key insight check: left-permutivity implies e_0 always sensitive
# rule30(1,c,r) != rule30(0,c,r) by left-permutivity
# So position 0 is ALWAYS sensitive (for ANY input c, flipping c[0] flips output)
# This means e_n IS sensitive at k=0 for all n.
# ============================================================
print("\n\n=== Left-permutivity guarantees k=0 is always sensitive ===\n")
print("  Left-permutivity: flipping c[0] ALWAYS flips rule30_1(c).")
print("  By induction, k=0 is sensitive at every generation for EVERY initial c.")
print("  Check for e_n:\n")
for n in range(1, 11):
    sens, sn = sensitive_positions(n)
    k0_sens = 0 in sens
    print(f"  n={n}: k=0 sensitive = {k0_sens} (should be True by left-permutivity)")

# ============================================================
# 5. What if we use a DIFFERENT fixed initial condition?
# Consider c_n = all-zeros with flipped k=0: [1, 0, 0, ..., 0]
# Is THIS a universal witness?
# ============================================================
print("\n\n=== Alternative: is the all-zeros-but-position-0 input a universal witness? ===\n")
print("  c_n = [1, 0, 0, ..., 0] (1 at leftmost position, length 2n+1)")
print("  By left-permutivity, this ALWAYS produces output 1 at step 0...")
print("  Checking sensitive positions:\n")

for n in [3, 5, 8, 10]:
    c0 = np.zeros(2*n+1, dtype=np.uint8)
    c0[0] = 1
    out_c0 = rule30_n_center(c0, n)
    sens_c0 = []
    for k in range(2*n+1):
        flip = c0.copy()
        flip[k] ^= 1
        if rule30_n_center(flip, n) != out_c0:
            sens_c0.append(k)
    print(f"  n={n}: c_0=[1,0..0], output={out_c0}, #sensitive={len(sens_c0)}/{2*n+1}, "
          f"sensitive={sens_c0[:6]}{'...' if len(sens_c0)>6 else ''}")
    sys.stdout.flush()
