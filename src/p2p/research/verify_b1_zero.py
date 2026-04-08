#!/usr/bin/env python3
"""
verify_b1_zero.py — Verify boundary formula claims for the lifting_lemma.

This script tests the claim that b1=0 always works for liftable P10-witnesses
(witnesses for Essential(n,j) with c[j]=1). This claim appears in the task
description for Unit 7 but is computationally FALSE.

The script documents:
1. The known counterexample to the OLD formula (b0=!c[0], b1=!c[2n])
2. The falsity of the b1=0 universal claim
3. The CORRECT state: existence of liftable P10-witnesses for each (n,j)
4. The (n=6,j=5) exception: requires weight-3, not weight-2 as previously claimed

Usage:
    python3 research/verify_b1_zero.py
"""

import sys
import itertools

# ── Rule 30 core ──────────────────────────────────────────────────────


def rule30_local(a, b, c):
    return a ^ (b | c)


def rule30_evolve(config):
    return [rule30_local(config[i], config[i+1], config[i+2])
            for i in range(len(config) - 2)]


def rule30_center(n, config):
    tape = list(config)
    for _ in range(n):
        tape = rule30_evolve(tape)
    if len(tape) != 1:
        return None
    return tape[0]


def is_witness(n, j, config):
    w = 2*n + 1
    if len(config) != w:
        return False
    c2 = list(config)
    c2[j] ^= 1
    v1 = rule30_center(n, config)
    v2 = rule30_center(n, c2)
    return v1 is not None and v2 is not None and v1 != v2


def find_any_liftable_b0b1(n, j, config):
    """Find any (b0,b1) that lifts config for Essential(n+1,j+1). Returns (b0,b1) or None."""
    for b0, b1 in itertools.product([0, 1], [0, 1]):
        lifted = [b0] + list(config) + [b1]
        l2 = list(lifted)
        l2[j+1] ^= 1
        v1 = rule30_center(n+1, lifted)
        v2 = rule30_center(n+1, l2)
        if v1 is not None and v2 is not None and v1 != v2:
            return (b0, b1)
    return None


def lifts_with_b1(n, j, config, b1_val=0):
    """Does config lift with fixed b1=b1_val for any b0?"""
    for b0 in [0, 1]:
        lifted = [b0] + list(config) + [b1_val]
        l2 = list(lifted)
        l2[j+1] ^= 1
        v1 = rule30_center(n+1, lifted)
        v2 = rule30_center(n+1, l2)
        if v1 is not None and v2 is not None and v1 != v2:
            return True, b0
    return False, None


# ── Test 1: counterexample to old formula ────────────────────────────


def test_old_formula_counterexample():
    """
    c=spikeAt(0), n=2, j=0: old formula b0=!c[0], b1=!c[2n] gives (0,1).
    This should FAIL as a lift. b1=0 should SUCCEED for b0=0.
    """
    n, j = 2, 0
    w = 2*n + 1  # 5
    c = [0]*w
    c[0] = 1  # spikeAt(0)

    b0_old = 1 - c[0]   # 0
    b1_old = 1 - c[2*n]  # 1 (c[4]=0, so !0=1)

    lifted_old = [b0_old] + c + [b1_old]
    l2 = list(lifted_old)
    l2[j+1] ^= 1
    v1 = rule30_center(n+1, lifted_old)
    v2 = rule30_center(n+1, l2)
    old_works = (v1 != v2)

    ok_b1_zero, b0_used = lifts_with_b1(n, j, c, b1_val=0)

    return {
        'n': n, 'j': j, 'config': c,
        'old_b0': b0_old, 'old_b1': b1_old,
        'old_formula_works': old_works,
        'v1_old': v1, 'v2_old': v2,
        'b1_zero_works': ok_b1_zero,
        'b0_for_b1_zero': b0_used,
    }


# ── Test 2: b1=0 universality claim ──────────────────────────────────


def test_b1_zero_universality(n_max=4):
    """
    For each n in 1..n_max, test if EVERY liftable P10-witness can be lifted with b1=0.
    Returns per-n results: (n, total_liftable, failures_with_b1_zero).
    """
    results = []
    for n in range(1, n_max + 1):
        w = 2*n + 1
        total = 0
        failures = []
        for j in range(w):
            for bits in itertools.product([0, 1], repeat=w):
                c = list(bits)
                if c[j] != 1:
                    continue
                if not is_witness(n, j, c):
                    continue
                best = find_any_liftable_b0b1(n, j, c)
                if best is None:
                    continue  # not liftable at all
                total += 1
                ok, _ = lifts_with_b1(n, j, c, b1_val=0)
                if not ok:
                    failures.append((j, c, best))
        results.append((n, total, failures))
    return results


# ── Test 3: existential — does a liftable P10-witness always exist? ──


def test_existential_liftable_p10(n_max=5):
    """
    For each (n,j) with n in 1..n_max, does there EXIST a liftable P10-witness?
    Exhaustive for n<=5. Reports any (n,j) where none is found.
    """
    results = []
    for n in range(1, n_max + 1):
        w = 2*n + 1
        missing = []
        for j in range(w):
            found = False
            for bits in itertools.product([0, 1], repeat=w):
                c = list(bits)
                if c[j] != 1:
                    continue
                if not is_witness(n, j, c):
                    continue
                if find_any_liftable_b0b1(n, j, c) is not None:
                    found = True
                    break
            if not found:
                missing.append(j)
        results.append((n, missing))
    return results


# ── Test 4: n=6, j=5 exception ───────────────────────────────────────


def test_n6_j5_exception():
    """
    Investigate (n=6, j=5):
    - spike@5: is it even a witness for Essential(6,5)?
    - weight-2 liftable P10-witnesses: do any exist?
    - weight-3 liftable P10-witnesses: do any exist?
    """
    n, j = 6, 5
    w = 2*n + 1  # 13

    # spike@5
    spike5 = [0]*w
    spike5[5] = 1
    spike5_is_witness = is_witness(n, j, spike5)
    spike5_liftable = find_any_liftable_b0b1(n, j, spike5) if spike5_is_witness else None

    # weight-1: any spike@x with x=j=5 is a witness and liftable?
    weight1_liftable = None
    for x in range(w):
        c = [0]*w
        c[x] = 1
        if c[j] != 1:
            continue
        if not is_witness(n, j, c):
            continue
        b = find_any_liftable_b0b1(n, j, c)
        if b is not None:
            weight1_liftable = (c, b)
            break

    # weight-2
    weight2_liftable = None
    for x in range(w):
        if weight2_liftable:
            break
        for y in range(x+1, w):
            c = [0]*w
            c[x] = 1
            c[y] = 1
            if c[j] != 1:
                continue
            if not is_witness(n, j, c):
                continue
            b = find_any_liftable_b0b1(n, j, c)
            if b is not None:
                weight2_liftable = (c, b)
                break

    # weight-3
    weight3_liftable = None
    for x in range(w):
        if weight3_liftable:
            break
        for y in range(x+1, w):
            if weight3_liftable:
                break
            for z in range(y+1, w):
                c = [0]*w
                c[x] = 1
                c[y] = 1
                c[z] = 1
                if c[j] != 1:
                    continue
                if not is_witness(n, j, c):
                    continue
                b = find_any_liftable_b0b1(n, j, c)
                if b is not None:
                    weight3_liftable = (c, b)
                    break

    return {
        'spike5_is_witness': spike5_is_witness,
        'spike5_liftable': spike5_liftable,
        'weight1_liftable': weight1_liftable,
        'weight2_liftable': weight2_liftable,
        'weight3_liftable': weight3_liftable,
    }


# ── Main ──────────────────────────────────────────────────────────────


def main():
    print("=" * 65)
    print("verify_b1_zero.py — Boundary formula verification for lifting_lemma")
    print("=" * 65)
    print()

    # Test 1
    print("TEST 1: Counterexample to old formula b0=!c[0], b1=!c[2n]")
    print("        c=spikeAt(0), n=2, j=0")
    print("-" * 55)
    ce = test_old_formula_counterexample()
    print(f"  config c      = {ce['config']}")
    print(f"  old formula   : b0={ce['old_b0']}, b1={ce['old_b1']}")
    print(f"  old outputs   : v1={ce['v1_old']}, v2={ce['v2_old']}")
    print(f"  old works?    : {ce['old_formula_works']}")
    print(f"  b1=0 works?   : {ce['b1_zero_works']}  (b0={ce['b0_for_b1_zero']})")
    print()
    if not ce['old_formula_works']:
        print("  CONFIRMED: old formula fails here.")
    if ce['b1_zero_works']:
        print("  CONFIRMED: b1=0 works for THIS specific case.")
    print()

    # Test 2
    print("TEST 2: Is b1=0 UNIVERSAL for all liftable P10-witnesses? (n=1..4)")
    print("-" * 55)
    b1_zero_results = test_b1_zero_universality(n_max=4)
    any_pass = True
    for (n, total, failures) in b1_zero_results:
        if failures:
            any_pass = False
            print(f"  n={n}: FAIL — {len(failures)}/{total} liftable P10-witnesses cannot use b1=0")
            for (j, c, best) in failures[:2]:
                print(f"    j={j}, c={c}, best_b1b0={best}")
        else:
            print(f"  n={n}: PASS — all {total} liftable P10-witnesses can use b1=0")
    print()
    if any_pass:
        print("  b1=0 is universal for tested n.")
    else:
        print("  CONCLUSION: b1=0 is NOT a universal boundary choice.")
        print("  The claim 'b1=0 always works' is FALSE.")
    print()

    # Test 3
    print("TEST 3: Existential — for each (n,j), does a liftable P10-witness exist?")
    print("-" * 55)
    exist_results = test_existential_liftable_p10(n_max=5)
    all_exist = True
    for (n, missing) in exist_results:
        if missing:
            all_exist = False
            print(f"  n={n}: FAIL — no liftable P10-witness found for j={missing}")
        else:
            w = 2*n+1
            print(f"  n={n}: PASS — all {w} positions have a liftable P10-witness")
    print()
    if all_exist:
        print("  CONFIRMED: for n=1..5, every (n,j) has a liftable P10-witness.")
        print("  Existence holds (exhaustively verified n<=5).")
    else:
        print("  WARNING: existence fails for some (n,j). Lifting lemma is in trouble.")
    print()

    # Test 4
    print("TEST 4: (n=6, j=5) exception — what minimum weight works?")
    print("-" * 55)
    r = test_n6_j5_exception()
    print(f"  spike@5 is witness for Essential(6,5): {r['spike5_is_witness']}")
    print(f"  spike@5 is liftable:                   {r['spike5_liftable'] is not None}")
    print(f"  Weight-1 liftable P10-witness:         {r['weight1_liftable'] is not None}")
    print(f"  Weight-2 liftable P10-witness:         {r['weight2_liftable'] is not None}")
    print(f"  Weight-3 liftable P10-witness:         {r['weight3_liftable'] is not None}")
    if r['weight3_liftable']:
        c3, (b0, b1) = r['weight3_liftable']
        print(f"    config: {c3}")
        print(f"    lifts with b0={b0}, b1={b1}")
    print()
    min_weight = None
    for w_label, key in [(1, 'weight1_liftable'), (2, 'weight2_liftable'), (3, 'weight3_liftable')]:
        if r[key] is not None:
            min_weight = w_label
            break
    if min_weight:
        print(f"  Minimum weight for (n=6,j=5): {min_weight}")
        if min_weight == 3:
            print("  NOTE: previous claim of 'weight-2' was WRONG — weight-3 is needed.")
    else:
        print("  WARNING: no liftable P10-witness found up to weight-3.")
    print()

    # Summary
    print("=" * 65)
    print("SUMMARY")
    print("=" * 65)
    print()
    print("Verified claims:")
    print("  [OK] Old formula counterexample: b0=0,b1=1 fails for c=spikeAt(0),n=2,j=0")
    print("  [OK] b1=0 works for that specific case (c[2n]=0)")
    if any_pass:
        print("  [OK] b1=0 works universally for n=1..4")
    else:
        print("  [REFUTED] b1=0 is NOT universal — fails for some liftable P10-witnesses")
    if all_exist:
        print("  [OK] Existential: every (n,j) with n<=5 has a liftable P10-witness")
    else:
        print("  [FAIL] Existential fails for some (n,j)")
    if r['weight3_liftable'] and not r['weight2_liftable']:
        print("  [CORRECTED] (n=6,j=5): weight-3 needed (not weight-2 as previously claimed)")
    print()
    print("Open problem: PROVE the existential claim for all n,")
    print("  i.e., for each (n,j), there exists c with c[j]=1, c witnesses")
    print("  Essential(n,j), and (b0,b1) exists so [b0]+c+[b1] witnesses Essential(n+1,j+1).")


if __name__ == '__main__':
    main()
