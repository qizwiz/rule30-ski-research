#!/usr/bin/env python3
"""
Bridge Attack 1 — Is e_n a universal witness?
Run date: 2026-03-24

The attacker's key question: for the specific single-black-cell input e_n,
does flipping position k change rule30_n(e_n) for EVERY k in {0,...,2n}?

If YES for all k: e_n is a universal witness → path A of the bridge works
  directly. The bridge is: our theorem says all positions are essential, and
  e_n witnesses ALL of them simultaneously → s(n) depends on all 2n+1 input
  cells even for this specific input → no sub-linear algorithm exists.

If NO for some k: path A fails. Some positions are NOT sensitive for e_n,
  meaning flipping them doesn't change the output. The bridge cannot use e_n
  as a universal witness.
"""
import numpy as np
import sys


def rule30_step(a):
    """One step of Rule 30 on a finite array (zero boundary)."""
    L = a[:-2] ^ (a[1:-1] | a[2:])
    return np.pad(L, 1, constant_values=0)


def rule30_n_center(c, n):
    """Compute center cell after n steps from initial config c (length 2n+1)."""
    a = c.copy()
    for _ in range(n):
        a = rule30_step(a)
    return int(a[n])  # center is still at position n after shrinkage...
    # Actually: after each step the array shrinks by 2. After n steps: len = 2n+1 - 2n = 1.
    # Return a[0].


def rule30_n_center_v2(c, n):
    """Correctly compute center cell after n steps. Array shrinks from 2n+1 to 1."""
    a = c.astype(np.uint8).copy()
    for _ in range(n):
        if len(a) < 3:
            break
        a = a[:-2] ^ (a[1:-1] | a[2:])
    return int(a[0]) if len(a) > 0 else 0


def make_en(n):
    """Single-black-cell initial condition: length 2n+1, 1 at position n."""
    c = np.zeros(2*n+1, dtype=np.uint8)
    c[n] = 1
    return c


# Verify base case
e1 = make_en(1)  # [0, 1, 0]
assert rule30_n_center_v2(e1, 1) == 1, "Base: rule30_1(010) should be 1 (center step)"

print("=== Universal Witness Test: Is e_n sensitive at ALL positions k? ===\n")
print("  e_n = single black cell, length 2n+1, 1 at center position n")
print("  Sensitive(n,k) = (rule30_n(e_n) ≠ rule30_n(flip(e_n, k)))\n")

print(f"  {'n':>3}  {'s(n)':>5}  {'sensitive positions':>50}  {'#sensitive':>10}  {'universal?':>10}")
print("  " + "-" * 85)

universal_all = True
first_failure = None

for n in range(1, 26):
    en = make_en(n)
    sn = rule30_n_center_v2(en, n)

    sensitive = []
    non_sensitive = []
    for k in range(2*n+1):
        en_flip = en.copy()
        en_flip[k] ^= 1
        sn_flip = rule30_n_center_v2(en_flip, n)
        if sn != sn_flip:
            sensitive.append(k)
        else:
            non_sensitive.append(k)

    is_universal = (len(sensitive) == 2*n+1)
    if not is_universal:
        universal_all = False
        if first_failure is None:
            first_failure = (n, non_sensitive)

    # Show non-sensitive positions (or "ALL" if universal)
    if is_universal:
        detail = "ALL sensitive"
    else:
        detail = f"NOT sensitive: {non_sensitive}"

    marker = "✓" if is_universal else "*** FAIL ***"
    print(f"  n={n:>2}  s={sn}  {detail:<50}  {len(sensitive):>2}/{2*n+1:<3}  {marker}")
    sys.stdout.flush()

print()
if universal_all:
    print("  ✓ e_n IS a universal witness for all n=1..25")
    print("  PATH A IS ALIVE: the bridge argument via universal witness works.")
    print()
    print("  IMPLICATION: For any algorithm A computing s(n) = rule30_n(e_n),")
    print("  A must read ALL 2n+1 positions of e_n — but e_n has only ONE non-zero")
    print("  position! This means: A must be sensitive to flipping ANY position,")
    print("  even though only position n is initially 1.")
    print()
    print("  The bridge: by our all-cells-essential theorem, there exists c such")
    print("  that flipping c[k] changes the output. Our computation shows e_n ITSELF")
    print("  is a universal witness — it's the c for every k simultaneously.")
    print("  Therefore any algorithm for s(n) must query all 2n+1 positions of e_n.")
    print("  Since e_n has fixed structure (1 at center, 0 elsewhere), the only")
    print("  'positions to query' are the INDEX n itself — but the algorithm must")
    print("  be sensitive to the *value* at each position, not just n.")
    print()
    print("  NOTE: This is about query complexity of rule30_n as a FUNCTION of c.")
    print("  Prize 3 is about computing s(n) given just n — different model.")
    print("  But the universal witness result strengthens the connection significantly.")
else:
    print(f"  *** PATH A FAILS: e_n is NOT a universal witness ***")
    print(f"  First failure at n={first_failure[0]}: positions {first_failure[1]} are not sensitive")
    print()
    print("  The bridge cannot proceed via path A.")
    print("  Must use path B (information-theoretic, conditional on Prize 1)")
    print("  or path C (reduction from general to fixed-input).")
