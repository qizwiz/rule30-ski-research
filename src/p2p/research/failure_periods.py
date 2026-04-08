#!/usr/bin/env python3
"""
Unit 4: Period-Doubling Failure Map for Shadow Lifting.

For each shadow position (n,j) with n<=500:
1. Check if spikeAt(j) is a liftable witness for Essential(n,j) → Essential(n+1,j+1)
2. If not, try spikes at other positions {rightmost, 1, 6, j-1, j+1}
3. Record ALL failures (where no spike works)
4. Map out the period structure for each j

Key question: does period(j) = 2^floor(j/2)?

Lifting definition:
  spike_is_liftable(n, j, spike_pos):
    - spike_pos is in tape of width 2*(n+1)+1 (the Essential(n+1,j) level)
    - For (n,j) shadow: spikeAt(spike_pos) in width 2*(n+1)+1 tape
    - Embed as c' = [b0] + spikeAt(spike_pos)[1:-1] + [b1]  ... no.
    - Actually: we need a witness for Essential(n+1, j+1).
    - The canonical lifting: take spike at spike_pos in tape of width 2*n+1,
      pad with [b0, b1] to get tape of width 2*n+3 = 2*(n+1)+1.
    - Then test if this pad witnesses Essential(n+1, j+1).

Shadow(n,j): dChain(n+1,j)=False AND dChain(n,j)=False.
"""

import sys
import time
import numpy as np
from collections import defaultdict
from math import gcd
from functools import reduce


# ---------- dChain table ----------

def build_dchain(T_MAX, K_MAX):
    D = np.zeros((T_MAX + 2, K_MAX + 2), dtype=np.bool_)
    D[:, 0] = True
    for t in range(1, T_MAX + 2):
        D[t, 1] = ~D[t - 1, 1]
        for k in range(2, K_MAX + 2):
            D[t, k] = D[t - 1, k] ^ (D[t - 1, k - 1] | D[t - 1, k - 2])
    return D


# ---------- Rule 30 ----------

def rule30_center(steps, config):
    """Evolve config (list/array of bool) for `steps` steps, return center bit."""
    tape = np.asarray(config, dtype=np.bool_).copy()
    for _ in range(steps):
        tape = tape[:-2] ^ (tape[1:-1] | tape[2:])
    return bool(tape[0])


# ---------- Liftability ----------

def spike_is_liftable(n, j, spike_pos):
    """
    Does spikeAt(spike_pos) in tape of width 2*n+1 lift to a witness for Essential(n+1, j+1)?

    Lifting: c' = [b0] + spike + [b1] for some b0, b1 in {0,1}.
    Then test if flipping position j+1 in c' changes rule30_center(n+1, c').
    """
    width_n = 2 * n + 1
    if spike_pos < 0 or spike_pos >= width_n:
        return False
    spike = [0] * width_n
    spike[spike_pos] = 1

    for b0 in (0, 1):
        for b1 in (0, 1):
            c_prime = [b0] + spike + [b1]
            j_plus_1 = j + 1
            c_flipped = list(c_prime)
            c_flipped[j_plus_1] ^= 1
            f_c = rule30_center(n + 1, c_prime)
            f_f = rule30_center(n + 1, c_flipped)
            if f_c != f_f:
                return True
    return False


def find_liftable_spike(n, j, extra_positions=None):
    """
    Try to find a liftable spike for shadow (n,j).

    Priority order: spikeAt(j), rightmost, 1, 6, j-1, j+1, then extra_positions.
    Returns (spike_pos, label) or (None, None) if no spike works.
    """
    width_n = 2 * n + 1
    rightmost_n = width_n - 1  # = 2*n

    candidates = []
    candidates.append((j, f"spikeAt(j={j})"))
    candidates.append((rightmost_n, "rightmost"))
    candidates.append((1, "x=1"))
    candidates.append((6, "x=6"))
    if j > 0:
        candidates.append((j - 1, f"j-1={j-1}"))
    if j < width_n - 1:
        candidates.append((j + 1, f"j+1={j+1}"))
    if extra_positions:
        for xp in extra_positions:
            candidates.append((xp, f"x={xp}"))

    for xp, label in candidates:
        if 0 <= xp < width_n:
            if spike_is_liftable(n, j, xp):
                return xp, label

    return None, None


def min_liftable_weight(n, j):
    """
    For a shadow where no spike lifts, find the minimum weight config that lifts.
    Weight = number of 1s in the config of width 2*n+1.
    Returns (min_weight, config) or (None, None) if width is too large.
    """
    width_n = 2 * n + 1
    if width_n > 20:  # too expensive
        return None, None

    for w in range(1, width_n + 1):
        # try all configs of weight w
        from itertools import combinations
        for ones_pos in combinations(range(width_n), w):
            config = [0] * width_n
            for p in ones_pos:
                config[p] = 1
            # test if this config lifts
            j_plus_1 = j + 1
            for b0 in (0, 1):
                for b1 in (0, 1):
                    c_prime = [b0] + config + [b1]
                    c_flipped = list(c_prime)
                    c_flipped[j_plus_1] ^= 1
                    if rule30_center(n + 1, c_prime) != rule30_center(n + 1, c_flipped):
                        return w, config
    return None, None


def compute_period(ns):
    """Given sorted list of n values, return period (gcd of differences)."""
    if len(ns) >= 2:
        diffs = [ns[i + 1] - ns[i] for i in range(len(ns) - 1)]
        period = reduce(gcd, diffs)
        return period
    return None


def main():
    N_MAX = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    K_MAX = 2 * (N_MAX + 2) + 4
    t0 = time.time()

    print(f"Unit 4: Period-Doubling Failure Map (n=0..{N_MAX})")
    print(f"Building D-chain table T_MAX={N_MAX+1}, K_MAX={K_MAX}...")
    sys.stdout.flush()
    D = build_dchain(N_MAX + 1, K_MAX)
    print(f"  Done in {time.time()-t0:.1f}s")

    # ===================================================================
    # MAIN SCAN: for each shadow (n,j), test liftability of spike candidates
    # ===================================================================
    total_shadows = 0
    total_covered = 0

    # failures_by_j[j] = list of n values where no spike lifts
    failures_by_j = defaultdict(list)
    # For covered: which spike covered it?
    coverage_by_spike = defaultdict(int)  # label -> count

    print(f"\nScanning shadows n=0..{N_MAX}...")
    sys.stdout.flush()

    # Track min weight for small failures
    small_failures_weights = []  # (n, j, min_weight)

    for n in range(N_MAX + 1):
        width_n = 2 * n + 1

        for j in range(width_n):
            # Check shadow condition: dChain(n+1,j)=False AND dChain(n,j)=False
            if j >= D.shape[1]:
                continue
            if D[n + 1, j] or D[n, j]:
                continue  # not a shadow

            total_shadows += 1

            xp, label = find_liftable_spike(n, j)
            if xp is not None:
                total_covered += 1
                coverage_by_spike[label] += 1
            else:
                failures_by_j[j].append(n)
                # For small n, find min liftable weight
                if n <= 9:
                    w, cfg = min_liftable_weight(n, j)
                    small_failures_weights.append((n, j, w))

        if (n + 1) % 50 == 0:
            total_failures = sum(len(v) for v in failures_by_j.values())
            elapsed = time.time() - t0
            print(f"  n={n}: shadows={total_shadows} covered={total_covered} "
                  f"failures={total_failures} t={elapsed:.1f}s", flush=True)

    elapsed = time.time() - t0
    total_failures = sum(len(v) for v in failures_by_j.values())

    # ===================================================================
    # RESULTS
    # ===================================================================
    print(f"\n{'='*80}")
    print(f"RESULTS (n=0..{N_MAX}, {elapsed:.1f}s)")
    print(f"{'='*80}")
    print(f"Total shadows:   {total_shadows}")
    print(f"Total covered:   {total_covered} ({100.*total_covered/total_shadows:.2f}%)")
    print(f"Total failures:  {total_failures} ({100.*total_failures/total_shadows:.2f}%)")

    print(f"\nCoverage breakdown:")
    for label in sorted(coverage_by_spike.keys(), key=lambda l: -coverage_by_spike[l]):
        count = coverage_by_spike[label]
        print(f"  {label:20s}: {count:6d} ({100.*count/total_shadows:.2f}%)")

    # ===================================================================
    # FAILURE PERIOD ANALYSIS
    # ===================================================================
    print(f"\n{'='*80}")
    print(f"FAILURE PERIOD ANALYSIS BY j")
    print(f"{'='*80}")

    import math

    print(f"\n{'j':>4} | {'#fails':>6} | {'Period':>8} | {'2^floor(j/2)':>12} | {'match?':>6} | first few n")
    print("-" * 80)

    period_matches = 0
    period_mismatches = 0

    for j in sorted(failures_by_j.keys()):
        ns = sorted(failures_by_j[j])
        period = compute_period(ns)
        expected = 2 ** (j // 2)

        if period is not None:
            match = "YES" if period == expected else f"NO({period})"
            if period == expected:
                period_matches += 1
            else:
                period_mismatches += 1
        else:
            match = "single"
            expected_str = str(expected)

        ns_str = str(ns[:6])
        if len(ns) > 6:
            ns_str = ns_str[:-1] + ", ...]"
        period_str = str(period) if period is not None else "?"
        expected_str = str(expected)
        print(f"{j:4d} | {len(ns):6d} | {period_str:>8} | {expected_str:>12} | {match:>6} | {ns_str}")

    print(f"\nPeriod = 2^floor(j/2): {period_matches} YES, {period_mismatches} NO (of multi-occurrence j)")

    # ===================================================================
    # RESIDUE ANALYSIS
    # ===================================================================
    print(f"\n{'='*80}")
    print(f"RESIDUE ANALYSIS (n mod period for each j with failures)")
    print(f"{'='*80}")

    for j in sorted(failures_by_j.keys()):
        ns = sorted(failures_by_j[j])
        if len(ns) < 2:
            continue
        period = compute_period(ns)
        if period is None:
            continue
        residues = sorted(set(n % period for n in ns))
        expected_period = 2 ** (j // 2)
        print(f"  j={j}: P={period} (expected {expected_period}), residues={residues}, count={len(ns)}")

    # ===================================================================
    # SMALL FAILURE WEIGHT ANALYSIS
    # ===================================================================
    if small_failures_weights:
        print(f"\n{'='*80}")
        print(f"MIN LIFTABLE WEIGHT at failures (n<=9)")
        print(f"{'='*80}")
        for n, j, w in small_failures_weights:
            print(f"  (n={n}, j={j}): min_weight={w}")

    # ===================================================================
    # SUMMARY
    # ===================================================================
    print(f"\n{'='*80}")
    print(f"SUMMARY")
    print(f"{'='*80}")
    print(f"Total shadows n=0..{N_MAX}: {total_shadows}")
    print(f"Covered by {{spikeAt(j), rightmost, x=1, x=6, j-1, j+1}}: {total_covered} ({100.*total_covered/total_shadows:.2f}%)")
    print(f"Failures (no spike lifts): {total_failures}")

    if total_failures == 0:
        print("\n*** ZERO FAILURES: Every shadow has a liftable spike witness ***")
        print("    Implies lifting_lemma holds for all n <= " + str(N_MAX))
    else:
        all_j = sorted(failures_by_j.keys())
        print(f"\nFailure j-values: {all_j}")

        # Period formula check
        formula_holds = []
        formula_fails = []
        for j in all_j:
            ns = sorted(failures_by_j[j])
            if len(ns) < 2:
                continue
            p = compute_period(ns)
            exp = 2 ** (j // 2)
            if p == exp:
                formula_holds.append(j)
            else:
                formula_fails.append((j, p, exp))

        if formula_holds:
            print(f"\nPeriod formula period(j) = 2^floor(j/2) HOLDS for j: {formula_holds}")
        if formula_fails:
            print(f"Period formula FAILS for: {formula_fails}")
        if not formula_fails and formula_holds:
            print(f"\nKEY FINDING: period(j) = 2^floor(j/2) confirmed for all multi-failure j")

    print(f"\nTotal time: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
