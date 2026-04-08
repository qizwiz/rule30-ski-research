#!/usr/bin/env python3
"""
Boundary Bit Pattern Analysis for Rule 30 lifting_lemma.

lifting_lemma: Essential(n, j) => Essential(n+1, j+1)

Given witness c for (n,j), the embedding c' = [b0] + c + [b1] should witness
(n+1, j+1) for SOME (b0, b1). This script determines which (b0, b1) pairs work
for each (n, j) and searches for an algebraic invariant predicting the answer.

Key quantities:
  F0 = rule30_center(n, witness)              -- center output of witness
  C  = rule30_center(n+1, [0]+witness+[0])    -- center output of zero-padded lift
  dChain(n,j) = spike at j witnesses (n,j)    -- whether spike works
"""

import itertools
from collections import defaultdict


def rule30_local(a, b, c):
    return a ^ (b | c)


def rule30_evolve(config):
    return [rule30_local(config[i-1], config[i], config[i+1])
            for i in range(1, len(config) - 1)]


def rule30_center(steps, config):
    tape = list(config)
    for _ in range(steps):
        tape = rule30_evolve(tape)
    if len(tape) != 1:
        raise ValueError(f"Expected 1 cell, got {len(tape)}")
    return tape[0]


def flip(config, j):
    c2 = list(config)
    c2[j] ^= 1
    return c2


def is_witness(n, j, config):
    return rule30_center(n, config) != rule30_center(n, flip(config, j))


def find_witness_spike(n, j):
    width = 2 * n + 1
    config = [0] * width
    config[j] = 1
    if is_witness(n, j, config):
        return config
    return None


def find_witness_brute(n, j):
    width = 2 * n + 1
    for bits in range(1 << width):
        config = [(bits >> k) & 1 for k in range(width)]
        if is_witness(n, j, config):
            return config
    return None


def find_witness(n, j):
    w = find_witness_spike(n, j)
    if w is not None:
        return w
    return find_witness_brute(n, j)


def working_boundaries(n, j, witness):
    result = []
    for b0 in [0, 1]:
        for b1 in [0, 1]:
            c = [b0] + list(witness) + [b1]
            c2 = flip(c, j + 1)
            if rule30_center(n + 1, c) != rule30_center(n + 1, c2):
                result.append((b0, b1))
    return result


def main():
    MAX_N = 12

    print("=" * 80)
    print("BOUNDARY BIT PATTERN ANALYSIS")
    print("=" * 80)

    # Collect all data
    records = []  # list of dicts

    for n in range(MAX_N + 1):
        width = 2 * n + 1
        for j in range(width):
            spike_w = find_witness_spike(n, j)
            is_spike = spike_w is not None
            w = spike_w if is_spike else find_witness_brute(n, j)
            if w is None:
                print(f"BUG: no witness for (n={n}, j={j})")
                continue

            boundaries = working_boundaries(n, j, w)

            F0 = rule30_center(n, w)
            c_zero = [0] + list(w) + [0]
            C = rule30_center(n + 1, c_zero)

            records.append({
                'n': n, 'j': j, 'w': w, 'boundaries': boundaries,
                'is_spike': is_spike, 'F0': F0, 'C': C,
                'dc_nj': is_spike,
            })

        print(f"  n={n:2d}: collected {width} positions")

    # ====================================================================
    # Q1: Is (0,0) always sufficient?
    # ====================================================================
    print()
    print("=" * 80)
    print("Q1: Is (0,0) always sufficient?")
    print("=" * 80)

    zero_zero_works = sum(1 for r in records if (0, 0) in r['boundaries'])
    zero_zero_fails = [r for r in records if (0, 0) not in r['boundaries']]
    print(f"  (0,0) works: {zero_zero_works}/{len(records)}")
    print(f"  (0,0) fails: {len(zero_zero_fails)}")
    if zero_zero_fails:
        for r in zero_zero_fails[:20]:
            print(f"    FAIL: n={r['n']}, j={r['j']}, F0={r['F0']}, C={r['C']}, "
                  f"dc={r['dc_nj']}, boundaries={r['boundaries']}")

    # ====================================================================
    # Q2: Is there a FIXED (b0,b1) that always works?
    # ====================================================================
    print()
    print("=" * 80)
    print("Q2: Is there a fixed (b0,b1) that always works?")
    print("=" * 80)

    for b0, b1 in itertools.product([0, 1], repeat=2):
        fails = sum(1 for r in records if (b0, b1) not in r['boundaries'])
        print(f"  ({b0},{b1}): fails {fails}/{len(records)}")

    # ====================================================================
    # Q3: How many boundaries work per (n,j)?
    # ====================================================================
    print()
    print("=" * 80)
    print("Q3: How many boundary pairs work per (n,j)?")
    print("=" * 80)

    count_dist = defaultdict(int)
    for r in records:
        count_dist[len(r['boundaries'])] += 1
    for k in sorted(count_dist):
        print(f"  {k} pairs work: {count_dist[k]} cases")

    # ====================================================================
    # Q4: Correlation with F0, C, dChain
    # ====================================================================
    print()
    print("=" * 80)
    print("Q4: Does (0,0) failure correlate with F0, C, dChain?")
    print("=" * 80)

    # Only look at records where n < MAX_N (so lifting makes sense)
    liftable = [r for r in records if r['n'] < MAX_N]

    # Cross-tabulate (0,0) works vs F0
    print("\n  (0,0) works vs F0:")
    for f0_val in [0, 1]:
        subset = [r for r in liftable if r['F0'] == f0_val]
        works = sum(1 for r in subset if (0, 0) in r['boundaries'])
        print(f"    F0={f0_val}: (0,0) works {works}/{len(subset)}")

    # Cross-tabulate (0,0) works vs C
    print("\n  (0,0) works vs C (center of zero-padded lift):")
    for c_val in [0, 1]:
        subset = [r for r in liftable if r['C'] == c_val]
        works = sum(1 for r in subset if (0, 0) in r['boundaries'])
        print(f"    C={c_val}: (0,0) works {works}/{len(subset)}")

    # Cross-tabulate (0,0) works vs dChain(n,j)
    print("\n  (0,0) works vs dChain(n,j) [spike works as witness]:")
    for dc_val in [True, False]:
        subset = [r for r in liftable if r['dc_nj'] == dc_val]
        works = sum(1 for r in subset if (0, 0) in r['boundaries'])
        print(f"    dChain={dc_val}: (0,0) works {works}/{len(subset)}")

    # ====================================================================
    # Q5: Does b0=dChain(n,j), b1=1 always work?
    # ====================================================================
    print()
    print("=" * 80)
    print("Q5: Candidate formulas for boundary bits")
    print("=" * 80)

    # Test: b1=1 always
    print("\n  Test A: b1=1 always (try both b0):")
    fails_b1_1 = sum(1 for r in liftable
                     if (0, 1) not in r['boundaries'] and (1, 1) not in r['boundaries'])
    print(f"    At least one of (0,1),(1,1) works: fails {fails_b1_1}/{len(liftable)}")

    # Test: b0=0 always (try both b1)
    print("\n  Test B: b0=0 always (try both b1):")
    fails_b0_0 = sum(1 for r in liftable
                     if (0, 0) not in r['boundaries'] and (0, 1) not in r['boundaries'])
    print(f"    At least one of (0,0),(0,1) works: fails {fails_b0_0}/{len(liftable)}")

    # Test: b0=F0, b1=F0
    print("\n  Test C: b0=F0, b1=F0:")
    fails_c = sum(1 for r in liftable if (r['F0'], r['F0']) not in r['boundaries'])
    print(f"    fails {fails_c}/{len(liftable)}")

    # Test: b0=1-F0, b1=F0
    print("\n  Test D: b0=1-F0, b1=F0:")
    fails_d = sum(1 for r in liftable if (1 - r['F0'], r['F0']) not in r['boundaries'])
    print(f"    fails {fails_d}/{len(liftable)}")

    # Test: b0=C, b1=C
    print("\n  Test E: b0=C, b1=C:")
    fails_e = sum(1 for r in liftable if (r['C'], r['C']) not in r['boundaries'])
    print(f"    fails {fails_e}/{len(liftable)}")

    # Test: b0=dChain(n,j), b1=1
    print("\n  Test F: b0=int(dChain(n,j)), b1=1:")
    fails_f = sum(1 for r in liftable
                  if (int(r['dc_nj']), 1) not in r['boundaries'])
    print(f"    fails {fails_f}/{len(liftable)}")

    # Test: b0=0, b1=int(dChain(n,j))
    print("\n  Test G: b0=0, b1=int(dChain(n,j)):")
    fails_g = sum(1 for r in liftable
                  if (0, int(r['dc_nj'])) not in r['boundaries'])
    print(f"    fails {fails_g}/{len(liftable)}")

    # ====================================================================
    # Q6: ALL witnesses -- does SOME (b0,b1) always work?
    # ====================================================================
    print()
    print("=" * 80)
    print("Q6: For EVERY (n,j), does at least one witness lift?")
    print("=" * 80)

    MAX_N_EXHAUST = 8  # 2*8+1=17 bits = 131072 configs
    true_failures = []

    for n in range(min(MAX_N, MAX_N_EXHAUST)):
        width = 2 * n + 1
        n_fail = 0
        for j in range(width):
            # Check: is there ANY witness for (n,j) that lifts to (n+1,j+1)?
            found_liftable = False
            if width <= 17:  # brute force feasible
                for bits in range(1 << width):
                    config = [(bits >> k) & 1 for k in range(width)]
                    if is_witness(n, j, config):
                        if working_boundaries(n, j, config):
                            found_liftable = True
                            break
            else:
                # Just test our chosen witness
                w = find_witness(n, j)
                if w and working_boundaries(n, j, w):
                    found_liftable = True

            if not found_liftable:
                n_fail += 1
                true_failures.append((n, j))

        print(f"  n={n}: {n_fail} positions with NO liftable witness")

    if true_failures:
        print(f"\n  TRUE FAILURES (no witness can be lifted):")
        for n, j in true_failures:
            print(f"    (n={n}, j={j})")
    else:
        print(f"\n  EVERY (n,j) with n<{min(MAX_N, MAX_N_EXHAUST)} has a liftable witness.")

    # ====================================================================
    # Q7: Detailed boundary pattern table
    # ====================================================================
    print()
    print("=" * 80)
    print("Q7: Detailed table for n=0..7 (all j)")
    print("=" * 80)

    print(f"  {'n':>2s} {'j':>2s} | {'spike':>5s} {'F0':>2s} {'C':>2s} "
          f"{'dc':>5s} | {'(0,0)':>5s} {'(0,1)':>5s} {'(1,0)':>5s} {'(1,1)':>5s} "
          f"| {'#ok':>3s} | note")
    print("  " + "-" * 75)

    for r in records:
        if r['n'] > 7 or r['n'] >= MAX_N:
            continue
        bset = set(r['boundaries'])
        note = ""
        if len(bset) == 4:
            note = "all work"
        elif len(bset) == 0:
            note = "NONE"
        elif bset == {(0, 0)}:
            note = "only (0,0)"
        elif (0, 0) not in bset:
            note = "(0,0) FAILS"

        print(f"  {r['n']:2d} {r['j']:2d} | "
              f"{'spike' if r['is_spike'] else 'brute':>5s} "
              f"{r['F0']:2d} {r['C']:2d} "
              f"{'T' if r['dc_nj'] else 'F':>5s} | "
              f"{'Y' if (0,0) in bset else '.':>5s} "
              f"{'Y' if (0,1) in bset else '.':>5s} "
              f"{'Y' if (1,0) in bset else '.':>5s} "
              f"{'Y' if (1,1) in bset else '.':>5s} "
              f"| {len(bset):3d} | {note}")

    # ====================================================================
    # Q8: Parity-based formula search
    # ====================================================================
    print()
    print("=" * 80)
    print("Q8: Systematic formula search (b0, b1 as functions of n, j, F0, C, dc)")
    print("=" * 80)

    # For each candidate (b0_formula, b1_formula), test if it always gives a working pair
    # Variables: n%2, j%2, F0, C, dc_nj, j==0, j==2n
    # We try all 2^5 boolean combinations of (F0, C, dc, n%2, j%2) -> (b0, b1)
    # That's way too many. Instead, test a curated list of formulas.

    formulas = {
        "(0, 0)": lambda r: (0, 0),
        "(0, 1)": lambda r: (0, 1),
        "(1, 0)": lambda r: (1, 0),
        "(1, 1)": lambda r: (1, 1),
        "(F0, F0)": lambda r: (r['F0'], r['F0']),
        "(F0, 1-F0)": lambda r: (r['F0'], 1 - r['F0']),
        "(1-F0, F0)": lambda r: (1 - r['F0'], r['F0']),
        "(1-F0, 1-F0)": lambda r: (1 - r['F0'], 1 - r['F0']),
        "(C, C)": lambda r: (r['C'], r['C']),
        "(C, 1-C)": lambda r: (r['C'], 1 - r['C']),
        "(1-C, C)": lambda r: (1 - r['C'], r['C']),
        "(1-C, 1-C)": lambda r: (1 - r['C'], 1 - r['C']),
        "(F0, C)": lambda r: (r['F0'], r['C']),
        "(C, F0)": lambda r: (r['C'], r['F0']),
        "(F0^C, F0)": lambda r: (r['F0'] ^ r['C'], r['F0']),
        "(F0, F0^C)": lambda r: (r['F0'], r['F0'] ^ r['C']),
        "(n%2, 0)": lambda r: (r['n'] % 2, 0),
        "(n%2, 1)": lambda r: (r['n'] % 2, 1),
        "(j%2, 0)": lambda r: (r['j'] % 2, 0),
        "(j%2, 1)": lambda r: (r['j'] % 2, 1),
        "(0, j%2)": lambda r: (0, r['j'] % 2),
        "(1, j%2)": lambda r: (1, r['j'] % 2),
        "(F0^(n%2), C)": lambda r: (r['F0'] ^ (r['n'] % 2), r['C']),
        "(C, F0^(n%2))": lambda r: (r['C'], r['F0'] ^ (r['n'] % 2)),
        # dChain-based
        "(dc, 0)": lambda r: (int(r['dc_nj']), 0),
        "(dc, 1)": lambda r: (int(r['dc_nj']), 1),
        "(0, dc)": lambda r: (0, int(r['dc_nj'])),
        "(1, dc)": lambda r: (1, int(r['dc_nj'])),
        "(dc, dc)": lambda r: (int(r['dc_nj']), int(r['dc_nj'])),
        "(dc, F0)": lambda r: (int(r['dc_nj']), r['F0']),
        "(F0, dc)": lambda r: (r['F0'], int(r['dc_nj'])),
    }

    print(f"\n  {'Formula':<25s} {'Fails':>5s} / {len(liftable)}")
    print("  " + "-" * 40)

    winners = []
    for name, fn in sorted(formulas.items()):
        fails = 0
        for r in liftable:
            pair = fn(r)
            if pair not in r['boundaries']:
                fails += 1
        status = " <<<< PERFECT" if fails == 0 else ""
        print(f"  {name:<25s} {fails:>5d}{status}")
        if fails == 0:
            winners.append(name)

    if winners:
        print(f"\n  PERFECT FORMULAS: {winners}")
    else:
        print(f"\n  No single formula works for all cases.")

    # ====================================================================
    # Q9: "Existential" -- does at least one of a small set always work?
    # ====================================================================
    print()
    print("=" * 80)
    print("Q9: Does {(0,0), (0,1)} always cover? (b0=0, choose b1)")
    print("=" * 80)

    # For each (n,j), check if b0=0 with some b1 works
    fail_b0_fixed_0 = sum(1 for r in liftable
                          if (0, 0) not in r['boundaries'] and (0, 1) not in r['boundaries'])
    fail_b0_fixed_1 = sum(1 for r in liftable
                          if (1, 0) not in r['boundaries'] and (1, 1) not in r['boundaries'])
    fail_b1_fixed_0 = sum(1 for r in liftable
                          if (0, 0) not in r['boundaries'] and (1, 0) not in r['boundaries'])
    fail_b1_fixed_1 = sum(1 for r in liftable
                          if (0, 1) not in r['boundaries'] and (1, 1) not in r['boundaries'])

    print(f"  b0=0, choose b1: fails {fail_b0_fixed_0}")
    print(f"  b0=1, choose b1: fails {fail_b0_fixed_1}")
    print(f"  b1=0, choose b0: fails {fail_b1_fixed_0}")
    print(f"  b1=1, choose b0: fails {fail_b1_fixed_1}")

    # ====================================================================
    # Q10: Best witness selection -- if we pick the RIGHT witness, does (0,0) work?
    # ====================================================================
    print()
    print("=" * 80)
    print("Q10: With optimal witness choice, does (0,0) always work? (n<=7)")
    print("=" * 80)

    for n in range(min(8, MAX_N)):
        width = 2 * n + 1
        all_00 = True
        for j in range(width):
            found_00 = False
            if width <= 17:
                for bits in range(1 << width):
                    config = [(bits >> k) & 1 for k in range(width)]
                    if is_witness(n, j, config):
                        c = [0] + config + [0]
                        if is_witness(n + 1, j + 1, c):
                            found_00 = True
                            break
            if not found_00:
                all_00 = False
                print(f"  n={n}, j={j}: NO witness lifts with (0,0)")
        if all_00:
            print(f"  n={n}: for every j, SOME witness lifts with (0,0)")


    # ====================================================================
    # Q11: THE KEY PATTERN -- b1=1-C determines everything?
    # ====================================================================
    print()
    print("=" * 80)
    print("Q11: Pattern analysis -- when boundaries work, what determines them?")
    print("=" * 80)

    # For records with >0 working boundaries, check:
    # - Are working pairs always {(0,x),(1,x)} for some fixed x? (b0 irrelevant)
    # - Is x = 1-C always?
    has_boundaries = [r for r in liftable if len(r['boundaries']) > 0]
    b0_irrelevant = 0
    b1_is_1_minus_C = 0
    for r in has_boundaries:
        bset = set(r['boundaries'])
        # Check if both b0 values appear with same b1
        b1_vals = set(b1 for _, b1 in bset)
        if len(b1_vals) == 1:
            b0_irrelevant += 1
            b1_val = list(b1_vals)[0]
            if b1_val == 1 - r['C']:
                b1_is_1_minus_C += 1
            else:
                print(f"    EXCEPTION: n={r['n']}, j={r['j']}, C={r['C']}, "
                      f"b1={b1_val}, boundaries={r['boundaries']}")

    print(f"  Records with >0 boundaries: {len(has_boundaries)}")
    print(f"  b0 is irrelevant (both b0 values work): {b0_irrelevant}/{len(has_boundaries)}")
    print(f"  b1 = 1-C when b0 irrelevant: {b1_is_1_minus_C}/{b0_irrelevant}")

    # For the 4-boundary cases
    four_cases = [r for r in liftable if len(r['boundaries']) == 4]
    print(f"\n  Cases with ALL 4 boundaries working: {len(four_cases)}")
    for r in four_cases:
        print(f"    n={r['n']}, j={r['j']}, F0={r['F0']}, C={r['C']}, dc={r['dc_nj']}")

    # For the 0-boundary cases (THIS witness fails completely)
    zero_cases = [r for r in liftable if len(r['boundaries']) == 0]
    print(f"\n  Cases with 0 boundaries (witness choice problem): {len(zero_cases)}")
    for r in zero_cases:
        print(f"    n={r['n']}, j={r['j']}, F0={r['F0']}, C={r['C']}, dc={r['dc_nj']}, "
              f"spike={r['is_spike']}")

    # ====================================================================
    # Q12: For 0-boundary cases, what about ALL witnesses?
    # ====================================================================
    print()
    print("=" * 80)
    print("Q12: 0-boundary cases -- is b1=1-C universal with optimal witness?")
    print("=" * 80)

    for r in zero_cases:
        n, j = r['n'], r['j']
        width = 2 * n + 1
        if width > 17:
            print(f"  n={n}, j={j}: too large for exhaustive search")
            continue
        # Find ALL witnesses and check their C and boundary patterns
        found_any = False
        for bits in range(1 << width):
            config = [(bits >> k) & 1 for k in range(width)]
            if is_witness(n, j, config):
                bds = working_boundaries(n, j, config)
                if bds:
                    c_zero = [0] + config + [0]
                    C_alt = rule30_center(n + 1, c_zero)
                    b1_match = all(b1 == 1 - C_alt for _, b1 in bds) if len(bds) < 4 else True
                    if not found_any:
                        print(f"  n={n}, j={j}: first liftable witness C={C_alt}, "
                              f"boundaries={bds}, b1=1-C: {b1_match}")
                        found_any = True
        if not found_any:
            print(f"  n={n}, j={j}: NO liftable witness exists (TRUE FAILURE)")


if __name__ == "__main__":
    main()
