#!/usr/bin/env python3
"""
Inductive Lifting Search for Rule 30 AllEssential proof.

Tests whether Essential(n,j) witnesses can be "lifted" to Essential(n+1,j+1)
by embedding the witness config into a longer tape with free boundary bits.

lifting_lemma: Essential(n, j) => Essential(n+1, j+1)

If witness c (length 2n+1) works for (n,j), then c' = [b0] + c + [b1] (length 2n+3)
should witness (n+1, j+1) for SOME choice of b0, b1 in {0,1}.

The causal cone argument: rule30n(n+1, c') depends on c'[1..2n+1] for its center
after n+1 steps. But the first step uses c'[0] and c'[2n+2] too. So we try all 4
combinations of the free boundary bits.
"""

import itertools
from collections import defaultdict


def rule30_local(a, b, c):
    return a ^ (b | c)


def rule30_evolve(config):
    """One step: returns interior cells (length shrinks by 2)."""
    return [rule30_local(config[i-1], config[i], config[i+1]) for i in range(1, len(config)-1)]


def rule30_center(steps, config):
    """Evolve config for `steps` steps, return the single remaining cell."""
    tape = list(config)
    for _ in range(steps):
        tape = rule30_evolve(tape)
    if len(tape) != 1:
        raise ValueError(f"Expected 1 cell after {steps} steps, got {len(tape)} (input len {len(config)})")
    return tape[0]


def flip(config, j):
    c2 = list(config)
    c2[j] ^= 1
    return c2


def is_witness(n, j, config):
    """Does flipping position j change the center output after n steps?"""
    return rule30_center(n, config) != rule30_center(n, flip(config, j))


def find_witness_brute(n, j):
    """Brute force: try all 2^(2n+1) configs to find a witness for Essential(n,j)."""
    width = 2 * n + 1
    for bits in range(1 << width):
        config = [(bits >> k) & 1 for k in range(width)]
        if is_witness(n, j, config):
            return config
    return None


def find_witness_spike(n, j):
    """Try spike at j as witness."""
    width = 2 * n + 1
    config = [0] * width
    config[j] = 1
    if is_witness(n, j, config):
        return config
    return None


def find_witness(n, j):
    """Find a witness for Essential(n,j). Spike first, then brute force."""
    w = find_witness_spike(n, j)
    if w is not None:
        return w
    return find_witness_brute(n, j)


def try_lift(n, j, witness):
    """
    Given witness for (n,j), try to construct witness for (n+1, j+1).

    c' = [b0] + witness + [b1], length 2n+3
    Flip position j+1 in c'.
    Try all 4 combos of (b0, b1).

    Returns: list of (b0, b1) that work, or empty list.
    """
    working = []
    for b0, b1 in itertools.product([0, 1], repeat=2):
        c_prime = [b0] + list(witness) + [b1]
        if is_witness(n + 1, j + 1, c_prime):
            working.append((b0, b1))
    return working


def main():
    MAX_N = 15

    # Phase 1: Find all witnesses
    print("=" * 70)
    print("Phase 1: Finding witnesses for Essential(n,j)")
    print("=" * 70)

    witnesses = {}  # (n, j) -> config

    for n in range(MAX_N + 1):
        width = 2 * n + 1
        for j in range(width):
            w = find_witness(n, j)
            if w is None:
                print(f"  BUG: No witness for (n={n}, j={j})! AllEssential fails!")
            else:
                witnesses[(n, j)] = w
        spike_count = sum(1 for j in range(width) if find_witness_spike(n, j) is not None)
        print(f"  n={n:2d}: all {width} positions essential, {spike_count}/{width} via spike")

    # Phase 2: Test lifting
    print()
    print("=" * 70)
    print("Phase 2: Testing causal-cone lifting (4 boundary combos)")
    print("=" * 70)

    lift_success = 0
    lift_fail = 0
    fail_cases = []
    combo_stats = defaultdict(int)  # (b0,b1) -> count of times it works

    for n in range(MAX_N):
        width = 2 * n + 1
        n_success = 0
        n_fail = 0
        for j in range(width):
            if (n, j) not in witnesses:
                continue
            w = witnesses[(n, j)]
            combos = try_lift(n, j, w)
            if combos:
                lift_success += 1
                n_success += 1
                for combo in combos:
                    combo_stats[combo] += 1
            else:
                lift_fail += 1
                n_fail += 1
                fail_cases.append((n, j, w))

        status = "ALL LIFT" if n_fail == 0 else f"{n_fail} FAIL"
        print(f"  n={n:2d} -> n+1={n+1:2d}: {n_success}/{width} lift, {status}")

    print()
    print(f"  TOTAL: {lift_success} success, {lift_fail} fail")

    if lift_fail == 0:
        print("  >>> LIFTING ALWAYS WORKS via causal-cone embedding! <<<")
    else:
        print(f"  >>> LIFTING FAILS for {lift_fail} cases <<<")

    # Phase 2b: boundary combo statistics
    print()
    print("  Boundary combo stats (how often each (b0,b1) works):")
    for combo in sorted(combo_stats.keys()):
        print(f"    (b0={combo[0]}, b1={combo[1]}): works {combo_stats[combo]} times")

    # Phase 3: Analyze failures
    if fail_cases:
        print()
        print("=" * 70)
        print("Phase 3: Analyzing lifting failures")
        print("=" * 70)

        for n, j, w in fail_cases:
            print(f"\n  FAIL: (n={n}, j={j}), witness={w}")

            # Find the actual witness at (n+1, j+1) by brute force
            actual = find_witness(n + 1, j + 1)
            if actual is not None:
                print(f"    Actual witness for (n+1={n+1}, j+1={j+1}): {actual}")
                # Check: is the actual witness an extension of some OTHER witness for (n,j)?
                inner = actual[1:-1]
                if is_witness(n, j, inner):
                    print(f"    Inner portion IS a witness for (n,j) -- different from ours!")
                    # Now check: does lifting THIS inner witness work?
                    combos2 = try_lift(n, j, inner)
                    if combos2:
                        print(f"    And lifting the inner witness WORKS with combos: {combos2}")
                    else:
                        print(f"    But lifting inner witness also FAILS!")
                else:
                    print(f"    Inner portion is NOT a witness for (n,j)")
            else:
                print(f"    BUG: No witness exists for (n+1={n+1}, j+1={j+1})!")

            # Try ALL witnesses for (n,j) and see if any lift
            width = 2 * n + 1
            any_lifts = False
            lift_count = 0
            total_witnesses = 0
            for bits in range(1 << width):
                config = [(bits >> k) & 1 for k in range(width)]
                if is_witness(n, j, config):
                    total_witnesses += 1
                    combos = try_lift(n, j, config)
                    if combos:
                        lift_count += 1
                        if not any_lifts:
                            any_lifts = True
                            print(f"    Found liftable witness: {config} -> combos {combos}")

            print(f"    Of {total_witnesses} total witnesses for (n={n},j={j}): {lift_count} are liftable")
            if not any_lifts:
                print(f"    >>> NO WITNESS FOR (n={n},j={j}) CAN BE LIFTED! <<<")
                print(f"    This would be a TRUE counterexample to lifting_lemma (constructive version)")

    # Phase 4: Does (0,0) always work?
    print()
    print("=" * 70)
    print("Phase 4: Does (b0=0, b1=0) always suffice?")
    print("=" * 70)

    zero_pad_fails = 0
    for n in range(MAX_N):
        width = 2 * n + 1
        for j in range(width):
            if (n, j) not in witnesses:
                continue
            w = witnesses[(n, j)]
            c_prime = [0] + list(w) + [0]
            if not is_witness(n + 1, j + 1, c_prime):
                zero_pad_fails += 1

    if zero_pad_fails == 0:
        print("  YES: (0,0) padding always works!")
    else:
        print(f"  NO: (0,0) padding fails {zero_pad_fails} times")

    # Phase 5: Witness choice independence
    print()
    print("=" * 70)
    print("Phase 5: Is lifting witness-independent? (all witnesses lift?)")
    print("=" * 70)

    # For small n, check if EVERY witness lifts (not just our chosen one)
    MAX_N_EXHAUST = 6  # 2*6+1 = 13 bits -> 8192 configs, each tested with 4 extensions

    witness_dependent_cases = []
    for n in range(MAX_N_EXHAUST):
        width = 2 * n + 1
        for j in range(width):
            total_w = 0
            liftable_w = 0
            for bits in range(1 << width):
                config = [(bits >> k) & 1 for k in range(width)]
                if is_witness(n, j, config):
                    total_w += 1
                    combos = try_lift(n, j, config)
                    if combos:
                        liftable_w += 1
            if total_w > 0 and liftable_w < total_w:
                witness_dependent_cases.append((n, j, liftable_w, total_w))

        dep_count = sum(1 for nn, jj, _, _ in witness_dependent_cases if nn == n)
        print(f"  n={n}: {dep_count} positions have non-liftable witnesses")

    if witness_dependent_cases:
        print(f"\n  {len(witness_dependent_cases)} cases where some witnesses don't lift:")
        for n, j, liftable, total in witness_dependent_cases[:20]:
            print(f"    (n={n}, j={j}): {liftable}/{total} witnesses liftable")
    else:
        print(f"\n  ALL witnesses are liftable for n <= {MAX_N_EXHAUST}!")

    # Phase 6: dChain shadow analysis
    print()
    print("=" * 70)
    print("Phase 6: Shadow region analysis (dChain vs lifting)")
    print("=" * 70)

    # dChain(n, j) = True iff spike at j witnesses Essential(n, j)
    # "Shadow" = dChain is False (spike doesn't work, need non-spike witness)

    for n in range(min(MAX_N + 1, 13)):
        width = 2 * n + 1
        shadow_positions = []
        for j in range(width):
            spike = [0] * width
            spike[j] = 1
            if not is_witness(n, j, spike):
                shadow_positions.append(j)
        if shadow_positions:
            print(f"  n={n:2d}: shadow at j={shadow_positions}")
        else:
            print(f"  n={n:2d}: no shadow (all spikes work)")


if __name__ == "__main__":
    main()
