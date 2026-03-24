#!/usr/bin/env python3
"""
Bridge Compute 2 — GF(2) polynomial degree and full-sensitivity analysis
Run date: 2026-03-24

Goal: Understand the algebraic structure of rule30_n as a function of its 2n+1 inputs.

1. For small n (n=1..8), compute the multivariate GF(2) polynomial for rule30_n.
   - Check the degree
   - Check if it's multilinear (all exponents 0 or 1)
   - Count the number of monomials

2. For Prize 3 bridge: check if the QUERY COMPLEXITY on the specific input e_n
   equals the SENSITIVITY of rule30_n at e_n.
   - These are equal by the definition of query complexity on a specific input
   - #sensitive(e_n) = query complexity of computing rule30_n(e_n)

3. Check: is s(n) = rule30_n(e_n) itself a "hard" input in the sense that
   the sensitivity at e_n equals bs(rule30_n) = 2n+1?
   We know it DOESN'T: sensitivity at e_n is ~n, not ~2n+1.

4. KEY QUESTION: Is there any fixed initial condition c_n (that can be specified
   in O(log n) bits) such that sensitivity(rule30_n, c_n) = 2n+1?
   If yes, that c_n could be a "universal witness" for all positions simultaneously.

5. Check the AVERAGE sensitivity: across all 2^(2n+1) inputs, what is the
   average number of sensitive positions? This is the average sensitivity.
   By left-permutivity, it's at least 1 (position 0).
"""
import numpy as np
import sys
from itertools import product


def rule30_n_center(c, n):
    """Compute Rule 30 center cell after n steps. Input length must be 2n+1."""
    a = np.array(c, dtype=np.uint8).copy()
    for _ in range(n):
        if len(a) < 3:
            break
        a = a[:-2] ^ (a[1:-1] | a[2:])
    return int(a[0]) if len(a) > 0 else 0


def sensitivity_at(c, n):
    """Return list of sensitive positions for input c with n steps."""
    base = rule30_n_center(c, n)
    sensitive = []
    for k in range(2*n+1):
        flip = list(c)
        flip[k] ^= 1
        if rule30_n_center(flip, n) != base:
            sensitive.append(k)
    return sensitive


# ============================================================
# 1. GF(2) polynomial structure for small n
# ============================================================
print("=== GF(2) polynomial analysis of rule30_n ===\n")
print("  Using truth table enumeration over all 2^(2n+1) inputs.\n")

for n in range(1, 7):
    size = 2*n+1
    total_inputs = 2**size

    # Build truth table
    ones_inputs = []
    for i in range(total_inputs):
        c = [(i >> k) & 1 for k in range(size)]
        val = rule30_n_center(c, n)
        if val == 1:
            ones_inputs.append(tuple(c))

    # Average sensitivity
    total_sens = 0
    max_sens = 0
    for i in range(total_inputs):
        c = [(i >> k) & 1 for k in range(size)]
        s = sensitivity_at(c, n)
        total_sens += len(s)
        max_sens = max(max_sens, len(s))

    avg_sens = total_sens / total_inputs

    # Sensitivity at e_n (single black cell at position n)
    en = [0]*size
    en[n] = 1
    sens_en = sensitivity_at(en, n)

    # Block sensitivity: max over inputs = max_sens
    # (by definition, bs(f) = max_c sensitivity(f,c))

    print(f"  n={n} ({size} vars, {total_inputs} inputs, {len(ones_inputs)} ones):")
    print(f"    Block sensitivity bs(rule30_n) = {max_sens}")
    print(f"    Average sensitivity = {avg_sens:.3f}")
    print(f"    Sensitivity at e_n = {len(sens_en)} (positions: {sens_en})")
    print(f"    Paper claims bs = 2n+1 = {size}: {'✓' if max_sens == size else '✗ MISMATCH'}")
    sys.stdout.flush()

print()

# ============================================================
# 2. Which input achieves block sensitivity 2n+1?
# ============================================================
print("=== Which input achieves sensitivity = 2n+1? ===\n")

for n in range(1, 7):
    size = 2*n+1
    total_inputs = 2**size

    universal_witnesses = []
    for i in range(total_inputs):
        c = [(i >> k) & 1 for k in range(size)]
        s = sensitivity_at(c, n)
        if len(s) == size:
            universal_witnesses.append(tuple(c))

    en = tuple([0]*n + [1] + [0]*n)
    en_is_witness = en in universal_witnesses if universal_witnesses else False

    if universal_witnesses:
        print(f"  n={n}: {len(universal_witnesses)} universal witnesses (sensitivity={size})")
        print(f"    First 3: {universal_witnesses[:3]}")
        print(f"    e_n is a universal witness: {en_is_witness}")
        # Check if any witness has O(log n) description (Hamming weight 1 or 2)
        hw1 = [w for w in universal_witnesses if sum(w) == 1]
        hw2 = [w for w in universal_witnesses if sum(w) == 2]
        print(f"    Weight-1 witnesses (e_k style): {hw1}")
        print(f"    Weight-2 witnesses: {len(hw2)}")
    else:
        print(f"  n={n}: NO universal witnesses (max sensitivity < {size})")
    sys.stdout.flush()

print()

# ============================================================
# 3. Anti-concentration: distribution of sensitivity values
# ============================================================
print("=== Sensitivity distribution ===\n")

for n in [3, 4, 5]:
    size = 2*n+1
    total_inputs = 2**size
    sens_counts = {}

    for i in range(total_inputs):
        c = [(i >> k) & 1 for k in range(size)]
        s = len(sensitivity_at(c, n))
        sens_counts[s] = sens_counts.get(s, 0) + 1

    print(f"  n={n} ({size} vars, {total_inputs} inputs):")
    for k in sorted(sens_counts.keys()):
        frac = sens_counts[k] / total_inputs
        bar = '#' * int(frac * 50)
        print(f"    sensitivity={k:2d}: {sens_counts[k]:6d} inputs ({frac:.3f}) {bar}")
    sys.stdout.flush()
