#!/usr/bin/env python3
"""
Bridge Compute 3 — Max sensitivity growth rate for rule30_n
Run date: 2026-03-24

Goal: Determine the growth rate of max_c s(rule30_n, c).

bridge_compute_2 showed max_sensitivity < 2n+1 for n≥2.
This script extends to larger n using random sampling.

The growth rate matters for Prize 3:
- If max_sensitivity = Θ(n), then the "hardest" inputs have ~n sensitive positions
- The sensitivity polynomial certificate uses these hardest inputs
- Any fast algorithm must read ~n bits (block sensitivity lower bound)

Method: for n=1..20, sample 10000 random inputs and track max sensitivity.
For n≤8, do exhaustive (2^(2n+1) ≤ 131072 inputs).
"""
import numpy as np
import random
import sys
import time


def rule30_n_center(c, n):
    a = np.array(c, dtype=np.uint8).copy()
    for _ in range(n):
        if len(a) < 3:
            break
        a = a[:-2] ^ (a[1:-1] | a[2:])
    return int(a[0]) if len(a) > 0 else 0


def sensitivity_at(c, n):
    base = rule30_n_center(c, n)
    count = 0
    for k in range(2*n+1):
        flip = list(c)
        flip[k] ^= 1
        if rule30_n_center(flip, n) != base:
            count += 1
    return count


# ============================================================
# Exhaustive for n≤8, random sampling for n>8
# ============================================================
print("=== Max sensitivity growth rate for rule30_n ===\n")
print("  n  |  max_sens  |  2n+1  |  ratio  |  method   |  time")
print("  " + "-" * 60)

results = []

for n in range(1, 21):
    size = 2*n+1
    t0 = time.time()

    if n <= 7:
        # Exhaustive
        total_inputs = 2**size
        max_s = 0
        max_input = None
        for i in range(total_inputs):
            c = [(i >> k) & 1 for k in range(size)]
            s = sensitivity_at(c, n)
            if s > max_s:
                max_s = s
                max_input = tuple(c)
        method = "exhaustive"
        n_checked = total_inputs
    else:
        # Random sampling + exhaustive over known "hard" families
        n_samples = 5000
        max_s = 0
        max_input = None

        # Sample random inputs
        for _ in range(n_samples):
            c = [random.randint(0, 1) for _ in range(size)]
            s = sensitivity_at(c, n)
            if s > max_s:
                max_s = s
                max_input = tuple(c)

        # Also check known "hard" families: all-ones, alternating, etc.
        for pattern in [
            [1]*size,                          # all ones
            [0]*size,                          # all zeros
            [i%2 for i in range(size)],        # alternating 0,1
            [1-i%2 for i in range(size)],      # alternating 1,0
            [int(i==n) for i in range(size)],  # e_n (single black cell)
            [int(i==0) for i in range(size)],  # e_0
            [int(i==size-1) for i in range(size)],  # e_{2n}
        ]:
            s = sensitivity_at(pattern, n)
            if s > max_s:
                max_s = s
                max_input = tuple(pattern)

        method = f"{n_samples}+special"
        n_checked = n_samples + 7

    elapsed = time.time() - t0
    ratio = max_s / size
    print(f"  n={n:2d} |  {max_s:7d}   |  {size:4d}  |  {ratio:.3f}  |  {method:12s}  |  {elapsed:.1f}s")
    results.append((n, max_s, size))
    sys.stdout.flush()

print("\n")
print("=== Sensitivity at e_n specifically ===\n")
print("  n  |  sens(e_n)  |  max_sens  |  fraction")
for n in range(1, 16):
    size = 2*n+1
    en = [0]*n + [1] + [0]*n
    s_en = sensitivity_at(en, n)
    # find max_sens from results
    max_s = next(r[1] for r in results if r[0] == n)
    print(f"  n={n:2d} |  {s_en:8d}   |  {max_s:8d}  |  {s_en/max_s:.3f}")
    sys.stdout.flush()

print("\n")
print("=== Growth rate fitting ===\n")
print("  Checking if max_sens ≈ alpha * n for some alpha...")
import math
for n, max_s, size in results:
    alpha = max_s / n
    sqrt_ratio = max_s / math.sqrt(n)
    log_ratio = max_s / math.log2(n) if n > 1 else 0
    print(f"  n={n:2d}: max_s={max_s:3d}, max_s/n={alpha:.3f}, max_s/sqrt(n)={sqrt_ratio:.3f}, max_s/log2(n)={log_ratio:.3f}")
