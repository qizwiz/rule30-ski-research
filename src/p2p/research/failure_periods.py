#!/usr/bin/env python3
"""
Unit 4: Period-Doubling Failure Map for Shadow Coverage.

KEY RESULTS (verified n=0..500):
1. {0, 1, 4, 6, rightmost} covers ALL 134,528 shadows -- ZERO failures
2. {0, rightmost} alone covers 134,277/134,528 (99.81%)
3. x=0 and rightmost split coverage ~50/50 (boundary vs boundary)
4. The 251 gaps of {0, rightmost} are at j=8k+4, j=8k+6 near n~j/2
   with period structure (j=12 has period 128)
5. x=1 covers almost all remaining gaps; x=4/x=6 handle edge cases

IMPLICATION FOR LIFTING LEMMA:
The lifting lemma requires: for each (n,j), exists witness config c s.t.
flipping position j changes rule30n(n+1, c). We need this to lift
Essential(n,j) to Essential(n+1,j+1).

The spike witness set {0, 1, 4, 6, rightmost} provides 5 FIXED spike
positions that witness ALL shadow positions. Since non-shadow positions
are witnessed by their own spike (by definition of D-chain), this means:
  For ALL (n,j) with n<=500, there exists x in {0,1,4,6,2*(n+1)}
  such that spike(x) witnesses Essential(n+1, j).

This is a finite spike set witnessing universal essentiality.

Shadow(n,j): dChain(n+1,j)=False AND dChain(n,j)=False.
"""

import numpy as np
from collections import defaultdict
from math import gcd
from functools import reduce
import sys
import time


def build_dchain(T_MAX, K_MAX):
    D = np.zeros((T_MAX + 2, K_MAX + 1), dtype=np.bool_)
    D[:, 0] = True
    for t in range(1, T_MAX + 2):
        D[t, 1] = not D[t - 1, 1]
        for k in range(2, min(K_MAX + 1, t + 2)):
            D[t, k] = D[t - 1, k] ^ (D[t - 1, k - 1] | D[t - 1, k - 2])
    return D


def rule30_evolve_np(tape):
    return tape[:-2] ^ (tape[1:-1] | tape[2:])


def rule30_center_np(steps, config):
    tape = np.asarray(config, dtype=np.bool_).copy()
    for _ in range(steps):
        tape = rule30_evolve_np(tape)
    return bool(tape[0])


def spike_witnesses_np(N, j, x):
    L = 2 * N + 1
    if x < 0 or x >= L:
        return False
    config = np.zeros(L, dtype=np.bool_)
    config[x] = True
    flipped = config.copy()
    flipped[j] = not flipped[j]
    return rule30_center_np(N, config) != rule30_center_np(N, flipped)


def compute_period(ns):
    """Given sorted list of n values, return (period, residue) or (None, ns[0])."""
    if len(ns) >= 3:
        diffs = [ns[i + 1] - ns[i] for i in range(len(ns) - 1)]
        period = reduce(gcd, diffs)
        return period, ns[0] % period
    elif len(ns) == 2:
        period = ns[1] - ns[0]
        return period, ns[0] % period
    return None, ns[0]


def main():
    N_MAX = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    K_MAX = 2 * (N_MAX + 2)
    t0 = time.time()

    print(f"Building D-chain table T_MAX={N_MAX+1}, K_MAX={K_MAX}...")
    sys.stdout.flush()
    D = build_dchain(N_MAX + 1, K_MAX)
    print(f"  Done in {time.time()-t0:.1f}s")

    # ===================================================================
    # MAIN: {0, 1, 4, 6, rightmost} coverage -- prioritize x=0 first
    # ===================================================================
    print(f"\nScanning n=0..{N_MAX}: {{0, 1, 4, 6, rightmost}} coverage")
    sys.stdout.flush()

    total_shadows = 0
    covered = {"x=0": 0, "rightmost": 0, "x=1": 0, "x=4": 0, "x=6": 0}
    penta_failures = []
    pair_failures = []  # {0, rightmost} failures

    for n in range(N_MAX + 1):
        N = n + 1
        L = 2 * N + 1
        rightmost = 2 * N

        for j in range(L):
            if j >= D.shape[1] or D[n + 1, j] or D[n, j]:
                continue
            total_shadows += 1

            # Test in priority order
            by_right = spike_witnesses_np(N, j, rightmost)
            by_left = spike_witnesses_np(N, j, 0)

            if by_right:
                covered["rightmost"] += 1
            elif by_left:
                covered["x=0"] += 1
            else:
                # Neither boundary covers -- need interior spikes
                pair_failures.append((n, j))
                if spike_witnesses_np(N, j, 1):
                    covered["x=1"] += 1
                elif spike_witnesses_np(N, j, 6):
                    covered["x=6"] += 1
                elif spike_witnesses_np(N, j, 4):
                    covered["x=4"] += 1
                else:
                    penta_failures.append((n, j))

        if (n + 1) % 50 == 0:
            elapsed = time.time() - t0
            print(f"  n={n}: shadows={total_shadows} pair_fails={len(pair_failures)} "
                  f"penta_fails={len(penta_failures)} t={elapsed:.1f}s", flush=True)

    elapsed = time.time() - t0

    # ===================================================================
    # RESULTS
    # ===================================================================
    print(f"\n{'='*80}")
    print(f"RESULTS (n=0..{N_MAX}, {elapsed:.1f}s)")
    print(f"{'='*80}")
    print(f"Total shadows: {total_shadows}")
    print(f"\nCoverage breakdown:")
    print(f"  rightmost (x=2N):  {covered['rightmost']:6d} ({covered['rightmost']/total_shadows*100:.1f}%)")
    print(f"  x=0 (leftmost):   {covered['x=0']:6d} ({covered['x=0']/total_shadows*100:.1f}%)")
    print(f"  x=1:              {covered['x=1']:6d} ({covered['x=1']/total_shadows*100:.1f}%)")
    print(f"  x=6:              {covered['x=6']:6d} ({covered['x=6']/total_shadows*100:.1f}%)")
    print(f"  x=4:              {covered['x=4']:6d} ({covered['x=4']/total_shadows*100:.1f}%)")
    total_covered = sum(covered.values())
    print(f"  TOTAL covered:    {total_covered:6d} ({total_covered/total_shadows*100:.1f}%)")
    print(f"  Penta-failures:   {len(penta_failures):6d}")

    if penta_failures:
        print(f"\nPENTA-FAILURES: {penta_failures[:20]}")
    else:
        print(f"\n*** {{0, 1, 4, 6, rightmost}} covers ALL {total_shadows} shadows ***")

    # {0, rightmost} failure analysis
    print(f"\n{'='*80}")
    print(f"{{0, rightmost}} failure analysis ({len(pair_failures)} failures)")
    print(f"{'='*80}")

    by_j = defaultdict(list)
    for n, j in pair_failures:
        by_j[j].append(n)

    print(f"\n{'j':>4} | {'count':>5} | {'Period':>8} | n values")
    print("-" * 70)
    for j in sorted(by_j.keys())[:25]:
        ns = sorted(by_j[j])
        period, _ = compute_period(ns)
        ns_str = str(ns[:8])
        if len(ns) > 8:
            ns_str = ns_str[:-1] + ",...]"
        p_str = str(period) if period is not None else "?"
        print(f"{j:4d} | {len(ns):5d} | {p_str:>8} | {ns_str}")

    # Pattern: most single-occurrence failures have j = 2*(n+3) or j = 2*(n+4)
    print(f"\nSingle-occurrence pattern check (j vs n):")
    singles = [(n, j) for n, j in pair_failures if len(by_j[j]) == 1]
    for n, j in singles[:15]:
        print(f"  n={n}, j={j}: j=2n+{j-2*n}, j/2={j//2}, n+3={n+3}, n+4={n+4}")

    # Multi-occurrence: period structure
    print(f"\nMulti-occurrence period structure:")
    for j in sorted(by_j.keys()):
        ns = sorted(by_j[j])
        if len(ns) >= 3:
            period, residue = compute_period(ns)
            print(f"  j={j}: P={period}, r={residue}, n={ns}")

    print(f"\nTotal time: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
