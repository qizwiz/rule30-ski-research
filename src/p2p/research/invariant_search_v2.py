#!/usr/bin/env python3
"""
Invariant Search v2 for Rule 30 lifting_lemma.

Builds on v1's finding that P10 (c[j]=1) satisfies EXIST-OK and CLOSE-OK.
Now searches for STRONGER invariants that also guarantee liftability.

New candidates:
  P_A: c[j]=1 AND c[2n]=0
  P_B: c[j]=1 AND c[2n]=1
  P_C: c[j]=1 AND (c[0]=0 OR c[2n]=0)
  P_D: c[j]=1 AND liftable with (b0=0, b1=0)
  P_E: spike at x <= j (hw=1, c[j]=1)
  P_F: c[j]=1 AND rule30_local(c[j-1], c[j], c[j+1])=0  (local condition at j)
  P_G: c[j]=1 AND XOR(c[j+1]..c[2n]) = 0

For each we test: Existence, Closure (with specific b0,b1), Liftability guarantee.
Also analyzes shadow positions and weight-2 witnesses.
"""

from functools import lru_cache
import sys

sys.path.insert(0, '/Users/jonathanhill/src/p2p/research')
try:
    from shadow_api import dchain_value, is_shadow
    HAS_SHADOW = True
except ImportError:
    HAS_SHADOW = False
    print("WARNING: shadow_api not found; shadow analysis skipped.")


# ─── Core Rule 30 ─────────────────────────────────────────────────────

def rule30_local(a, b, c):
    return a ^ (b | c)


def rule30_evolve(config):
    n = len(config)
    if n < 3:
        return []
    return [rule30_local(config[i-1], config[i], config[i+1]) for i in range(1, n-1)]


def rule30_center(steps, config):
    tape = list(config)
    for _ in range(steps):
        tape = rule30_evolve(tape)
    if len(tape) != 1:
        return None
    return tape[0]


def flip(config, j):
    c2 = list(config)
    c2[j] ^= 1
    return c2


def is_witness(n, j, config):
    w = 2*n + 1
    if len(config) != w:
        return False
    return rule30_center(n, config) != rule30_center(n, flip(config, j))


def is_liftable(n, j, config):
    """Returns (success, (b0,b1), lifted_config) or (False, None, None)."""
    for b0 in [0, 1]:
        for b1 in [0, 1]:
            c = [b0] + list(config) + [b1]
            c2 = flip(c, j+1)
            v1 = rule30_center(n+1, c)
            v2 = rule30_center(n+1, c2)
            if v1 is not None and v2 is not None and v1 != v2:
                return True, (b0, b1), c
    return False, None, None


def is_liftable_with(n, j, config, b0, b1):
    """Test liftability with a specific (b0,b1) pair."""
    c = [b0] + list(config) + [b1]
    c2 = flip(c, j+1)
    v1 = rule30_center(n+1, c)
    v2 = rule30_center(n+1, c2)
    return (v1 is not None and v2 is not None and v1 != v2), c


# ─── Witness enumeration (cached) ─────────────────────────────────────

_witness_cache = {}
_liftable_cache = {}


def all_witnesses(n, j):
    if (n, j) in _witness_cache:
        return _witness_cache[(n, j)]
    w = 2*n + 1
    witnesses = []
    for bits in range(1 << w):
        config = [(bits >> k) & 1 for k in range(w)]
        if is_witness(n, j, config):
            witnesses.append(config)
    _witness_cache[(n, j)] = witnesses
    return witnesses


def all_liftable_witnesses(n, j):
    if (n, j) in _liftable_cache:
        return _liftable_cache[(n, j)]
    results = []
    for c in all_witnesses(n, j):
        ok, pair, lifted = is_liftable(n, j, c)
        if ok:
            results.append((c, pair, lifted))
    _liftable_cache[(n, j)] = results
    return results


# ─── Candidate invariants ──────────────────────────────────────────────

def P_A(c, n, j):
    """c[j]=1 AND c[2n]=0 (rightmost clear → b1=0 always works)"""
    return c[j] == 1 and c[2*n] == 0


def P_B(c, n, j):
    """c[j]=1 AND c[2n]=1"""
    return c[j] == 1 and c[2*n] == 1


def P_C(c, n, j):
    """c[j]=1 AND (c[0]=0 OR c[2n]=0) — at least one boundary clear"""
    return c[j] == 1 and (c[0] == 0 or c[2*n] == 0)


def P_D(c, n, j):
    """c[j]=1 AND liftable with (b0=0, b1=0) specifically"""
    if c[j] != 1:
        return False
    ok, _ = is_liftable_with(n, j, c, 0, 0)
    return ok


def P_E(c, n, j):
    """spike at exactly j (hw=1, only position j set)"""
    return sum(c) == 1 and c[j] == 1


def P_F(c, n, j):
    """c[j]=1 AND rule30_local(c[j-1], c[j], c[j+1])=0 (local condition at j)
    For j=0: use c[-1]=0 (boundary); for j=2n: use c[2n+1]=0"""
    if c[j] != 1:
        return False
    left = c[j-1] if j > 0 else 0
    right = c[j+1] if j < len(c)-1 else 0
    return rule30_local(left, c[j], right) == 0


def P_G(c, n, j):
    """c[j]=1 AND XOR(c[j+1]..c[2n]) = 0 (right sum rule)"""
    if c[j] != 1:
        return False
    right_xor = 0
    for k in range(j+1, 2*n+1):
        right_xor ^= c[k]
    return right_xor == 0


# Also test P10 (baseline from v1) and two conjunction variants
def P10(c, n, j):
    """Baseline from v1: c[j]=1"""
    return c[j] == 1


def P_AD(c, n, j):
    """P_A AND P_D: c[j]=1 AND c[2n]=0 AND liftable(0,0)"""
    return P_A(c, n, j) and P_D(c, n, j)


def P_EG(c, n, j):
    """spike at j AND XOR condition (P_E AND P_G)"""
    return P_E(c, n, j) and P_G(c, n, j)


CANDIDATES = [
    ("P10 (baseline: c[j]=1)", P10),
    ("P_A: c[j]=1 AND c[2n]=0", P_A),
    ("P_B: c[j]=1 AND c[2n]=1", P_B),
    ("P_C: c[j]=1 AND (c[0]=0 OR c[2n]=0)", P_C),
    ("P_D: c[j]=1 AND liftable(0,0)", P_D),
    ("P_E: spike at j (hw=1, c[j]=1)", P_E),
    ("P_F: c[j]=1 AND local(j)=0", P_F),
    ("P_G: c[j]=1 AND XOR(j+1..2n)=0", P_G),
    ("P_AD: P_A AND P_D", P_AD),
    ("P_EG: spike@j AND XOR=0", P_EG),
]


# ─── Three-condition test machinery ───────────────────────────────────

def test_invariant_v2(name, pred, n_max=6, verbose=False):
    """Test invariant for:
    1. Existence: for every (n,j), exists liftable c with pred(c,n,j)
    2. Closure: pred(c,n,j) => pred(embed(c,b0,b1), n+1, j+1) [for SOME valid (b0,b1)]
    3. Liftability: pred(c,n,j) => c is liftable (no non-liftable witness satisfies pred)
    """
    existence_fails = []
    closure_fails = []
    liftability_fails = []  # witnesses satisfying pred but NOT liftable

    for n in range(1, n_max + 1):
        w = 2*n + 1
        for j in range(w):
            found_liftable_with_pred = False
            liftable = all_liftable_witnesses(n, j)
            witnesses = all_witnesses(n, j)

            # Check liftability: any NON-liftable witness satisfying pred?
            liftable_set = {tuple(c) for c, _, _ in liftable}
            for c in witnesses:
                if pred(c, n, j) and tuple(c) not in liftable_set:
                    liftability_fails.append((n, j, c))
                    break  # one counterexample per (n,j)

            # Check existence: some liftable witness satisfies pred?
            for (c, pair, lifted) in liftable:
                if pred(c, n, j):
                    found_liftable_with_pred = True
                    # Check closure: does lifted satisfy pred at (n+1, j+1)?
                    if not pred(lifted, n+1, j+1):
                        closure_fails.append((n, j, c, pair, lifted))
                        if verbose:
                            print(f"    CLOSE FAIL: n={n}, j={j}, pair={pair}")
                            print(f"      c     = {c}")
                            print(f"      lifted= {lifted}")
                    break  # check only first liftable witness with pred (for closure)

            if not found_liftable_with_pred:
                existence_fails.append((n, j))

    exist_ok = len(existence_fails) == 0
    close_ok = len(closure_fails) == 0
    lift_ok = len(liftability_fails) == 0

    return {
        'name': name,
        'exist_ok': exist_ok,
        'close_ok': close_ok,
        'lift_ok': lift_ok,
        'existence_fails': existence_fails,
        'closure_fails': closure_fails,
        'liftability_fails': liftability_fails,
    }


def test_closure_all_b01(name, pred, n_max=6):
    """For closable invariants, find which (b0,b1) preserves pred."""
    print(f"\n  [{name}] Checking which (b0,b1) preserves pred at closure:")
    b01_stats = {(0,0): 0, (0,1): 0, (1,0): 0, (1,1): 0}
    b01_fails = {(0,0): 0, (0,1): 0, (1,0): 0, (1,1): 0}

    for n in range(1, n_max + 1):
        w = 2*n + 1
        for j in range(w):
            for (c, pair, lifted) in all_liftable_witnesses(n, j):
                if not pred(c, n, j):
                    continue
                # Try all (b0,b1), check which preserve pred
                for b0 in [0, 1]:
                    for b1 in [0, 1]:
                        ok, lifted_cand = is_liftable_with(n, j, c, b0, b1)
                        if ok:
                            b01_stats[(b0, b1)] += 1
                            if not pred(lifted_cand, n+1, j+1):
                                b01_fails[(b0, b1)] += 1

    for pair in [(0,0), (0,1), (1,0), (1,1)]:
        total = b01_stats[pair]
        fails = b01_fails[pair]
        if total > 0:
            rate = 100.0 * (total - fails) / total
            print(f"    b0,b1={pair}: {total} liftable instances, {fails} closure fails ({rate:.0f}% preserved)")
        else:
            print(f"    b0,b1={pair}: never used as liftable pair")


# ─── Shadow analysis ───────────────────────────────────────────────────

def shadow_analysis(n_max=7):
    """For shadow positions, analyze what witnesses look like."""
    if not HAS_SHADOW:
        print("  (shadow_api unavailable)")
        return

    print("\n" + "="*70)
    print("SHADOW POSITION ANALYSIS")
    print("="*70)
    print("Shadow(n,j): dChain(n+1,j)=False AND dChain(n,j)=False")
    print("These are positions where spike@j fails as witness for Essential(n+1,j).")
    print()

    shadow_positions = []
    for n in range(1, n_max + 1):
        w_next = 2*(n+1) + 1
        for j in range(w_next):
            if is_shadow(n, j):
                shadow_positions.append((n, j))

    print(f"Found {len(shadow_positions)} shadow positions for n=1..{n_max}:")
    for (n, j) in shadow_positions:
        print(f"  shadow at (n={n}, j={j})")

    # For each shadow, examine liftable witnesses for Essential(n+1, j)
    print()
    print("Liftable witnesses at shadow positions (for Essential(n+1, j)):")
    for (n, j) in shadow_positions:
        n_eff = n + 1  # the level we need to witness
        w = 2*n_eff + 1
        if w > 15:
            print(f"  (n_eff={n_eff}, j={j}): too large for exhaustive search, skip")
            continue
        liftable = all_liftable_witnesses(n_eff, j)
        total = len(all_witnesses(n_eff, j))
        print(f"  Essential(n={n_eff}, j={j}): {len(liftable)} liftable / {total} total witnesses")

        # Check: do these satisfy P_D (liftable with b0=0,b1=0)?
        # What patterns do they show?
        weight_dist = {}
        cj_vals = {0: 0, 1: 0}
        c2n_vals = {0: 0, 1: 0}
        pd_count = 0

        for (c, pair, lifted) in liftable:
            hw = sum(c)
            weight_dist[hw] = weight_dist.get(hw, 0) + 1
            cj_vals[c[j]] += 1
            c2n_vals[c[2*n_eff]] += 1
            if P_D(c, n_eff, j):
                pd_count += 1

        print(f"    weight dist: {dict(sorted(weight_dist.items()))}")
        print(f"    c[j]=1: {cj_vals[1]}/{len(liftable)}, c[j]=0: {cj_vals[0]}/{len(liftable)}")
        print(f"    c[2n]=1: {c2n_vals[1]}/{len(liftable)}, c[2n]=0: {c2n_vals[0]}/{len(liftable)}")
        print(f"    P_D (liftable(0,0)) satisfied: {pd_count}/{len(liftable)}")

        # Show weight-2 witnesses with c[j]=1
        wt2_cj1 = [(c, pair) for (c, pair, _) in liftable if sum(c) == 2 and c[j] == 1]
        if wt2_cj1:
            print(f"    Weight-2 with c[j]=1: {len(wt2_cj1)} witnesses")
            for (c, pair) in wt2_cj1[:3]:
                other = [k for k, v in enumerate(c) if v == 1 and k != j]
                print(f"      c={c}, other bit at {other}, lift pair={pair}")


# ─── b1=0 hypothesis ──────────────────────────────────────────────────

def test_b1_zero_hypothesis(n_max=7):
    """Test: for EVERY witness (not just liftable), does b1=0 always have SOME b0 that works?
    Hypothesis from algebraic analysis: b1=0 might always work.
    """
    print("\n" + "="*70)
    print("b1=0 HYPOTHESIS TEST")
    print("="*70)
    print("Testing: for every witness c at (n,j), exists b0 such that (b0,0) lifts c.")
    print()

    fails = []
    for n in range(1, n_max + 1):
        w = 2*n + 1
        for j in range(w):
            for c in all_witnesses(n, j):
                # Try b1=0 with any b0
                found = False
                for b0 in [0, 1]:
                    ok, _ = is_liftable_with(n, j, c, b0, 0)
                    if ok:
                        found = True
                        break
                if not found:
                    fails.append((n, j, c))

    if not fails:
        print("  b1=0 ALWAYS WORKS for some b0 — CONFIRMED up to n_max!")
    else:
        print(f"  b1=0 FAILS for {len(fails)} (n,j,c) triples:")
        for (n, j, c) in fails[:5]:
            print(f"    n={n}, j={j}, c={c}")
        if len(fails) > 5:
            print(f"    ... and {len(fails)-5} more")


def test_b0_formulas_given_b1_zero(n_max=6):
    """Given b1=0, what determines b0?
    Check if b0 is determined by a simple formula of c and (n,j)."""
    print("\n" + "="*70)
    print("b0 FORMULA SEARCH (given b1=0)")
    print("="*70)

    formulas = {
        "b0=0": lambda c, n, j: 0,
        "b0=1": lambda c, n, j: 1,
        "b0=c[0]": lambda c, n, j: c[0],
        "b0=c[0]^1": lambda c, n, j: c[0] ^ 1,
        "b0=c[j]": lambda c, n, j: c[j],
        "b0=c[j]^1": lambda c, n, j: c[j] ^ 1,
        "b0=c[2n]": lambda c, n, j: c[2*n],
        "b0=c[0] XOR c[j]": lambda c, n, j: c[0] ^ c[j],
        "b0=rule30_center(n,c)": lambda c, n, j: rule30_center(n, c),
    }

    for fname, f in formulas.items():
        total = 0
        correct = 0
        fails = []
        for n in range(1, n_max + 1):
            w = 2*n + 1
            for j in range(w):
                for c in all_witnesses(n, j):
                    total += 1
                    b0_pred = f(c, n, j)
                    ok, _ = is_liftable_with(n, j, c, b0_pred, 0)
                    if ok:
                        correct += 1
                    else:
                        fails.append((n, j, c, b0_pred))
        pct = 100.0 * correct / total if total > 0 else 0
        status = "WORKS" if not fails else f"FAILS ({len(fails)} counterex)"
        print(f"  {fname:30s}: {status}  ({correct}/{total}, {pct:.1f}%)")


# ─── Closure analysis for P_A and P_D ─────────────────────────────────

def analyze_closure_for_P_A(n_max=6):
    """P_A: c[j]=1 AND c[2n]=0.
    For closure: lifted = [b0]+c+[b1], need lifted[j+1]=1 (from c[j]=1, offset by 1)
    and lifted[2(n+1)] = b1.
    So closure requires b1=0 (to keep rightmost clear).
    Let's verify: if c satisfies P_A and is liftable, is [b0]+c+[0] always a witness at (n+1,j+1)?
    """
    print("\n" + "="*70)
    print("P_A CLOSURE ANALYSIS: c[j]=1, c[2n]=0 => lift with b1=0?")
    print("="*70)

    results = []
    for n in range(1, n_max + 1):
        w = 2*n + 1
        for j in range(w):
            # Find witnesses satisfying P_A
            for c in all_witnesses(n, j):
                if not P_A(c, n, j):
                    continue
                # Try lifting with b1=0
                ok_00, lc00 = is_liftable_with(n, j, c, 0, 0)
                ok_10, lc10 = is_liftable_with(n, j, c, 1, 0)
                results.append({
                    'n': n, 'j': j, 'c': c,
                    'ok_00': ok_00, 'ok_10': ok_10,
                    'liftable_at_all': ok_00 or ok_10,
                    'b1_zero_works': ok_00 or ok_10,
                })

    b1_zero_always = all(r['b1_zero_works'] for r in results)
    liftable_always = all(r['liftable_at_all'] for r in results)
    print(f"  Total P_A witnesses tested: {len(results)}")
    print(f"  b1=0 always lifts P_A witnesses: {b1_zero_always}")
    print(f"  All P_A witnesses are liftable: {liftable_always}")

    # Now check: does the lifted config satisfy P_A at (n+1,j+1)?
    closure_ok = True
    closure_fails = []
    for r in results:
        n, j, c = r['n'], r['j'], r['c']
        for b0 in [0, 1]:
            ok, lc = is_liftable_with(n, j, c, b0, 0)
            if ok:
                # lc = [b0] + c + [0], check P_A at (n+1, j+1)
                if not P_A(lc, n+1, j+1):
                    closure_ok = False
                    closure_fails.append((n, j, c, b0, lc))
                break

    print(f"  Closure under P_A (with b1=0): {'OK' if closure_ok else f'FAILS ({len(closure_fails)} cases)'}")
    if closure_fails:
        for (n, j, c, b0, lc) in closure_fails[:3]:
            print(f"    n={n}, j={j}, b0={b0}")
            print(f"      c    = {c}")
            print(f"      lifted = {lc}")
            print(f"      lifted[j+1]={lc[j+1]}, lifted[2*(n+1)]={lc[2*(n+1)]}")


# ─── Comprehensive table ───────────────────────────────────────────────

def print_results_table(results):
    print("\n" + "="*70)
    print("RESULTS TABLE (n=1..6, exhaustive)")
    print("="*70)
    print(f"  {'Invariant':<40} {'EXIST':6} {'CLOSE':6} {'LIFT':6}")
    print(f"  {'-'*40} {'-'*6} {'-'*6} {'-'*6}")

    winners = []
    for r in results:
        e = "OK" if r['exist_ok'] else f"FAIL({len(r['existence_fails'])})"
        c = "OK" if r['close_ok'] else f"FAIL({len(r['closure_fails'])})"
        l = "OK" if r['lift_ok'] else f"FAIL({len(r['liftability_fails'])})"
        star = " ***" if r['exist_ok'] and r['close_ok'] and r['lift_ok'] else ""
        print(f"  {r['name']:<40} {e:<6} {c:<6} {l:<6}{star}")
        if star:
            winners.append(r['name'])

    print()
    if winners:
        print("WINNERS (all three conditions met):")
        for w in winners:
            print(f"  {w}")
    else:
        print("NO invariant satisfies all three conditions.")

    return winners


def print_failures(results, max_fails=2):
    """Print detailed failure info for each candidate."""
    print("\n" + "="*70)
    print("FAILURE DETAILS")
    print("="*70)
    for r in results:
        has_issues = not (r['exist_ok'] and r['close_ok'] and r['lift_ok'])
        if not has_issues:
            continue
        print(f"\n  [{r['name']}]")
        if r['existence_fails']:
            print(f"    Existence fails ({len(r['existence_fails'])} positions):")
            for (n, j) in r['existence_fails'][:max_fails]:
                print(f"      no liftable+pred witness at (n={n}, j={j})")
        if r['closure_fails']:
            print(f"    Closure fails ({len(r['closure_fails'])} cases):")
            for (n, j, c, pair, lifted) in r['closure_fails'][:max_fails]:
                print(f"      n={n}, j={j}, pair={pair}")
                print(f"        c     = {c}")
                print(f"        lifted= {lifted}")
        if r['liftability_fails']:
            print(f"    Liftability fails ({len(r['liftability_fails'])} witnesses satisfy pred but not liftable):")
            for (n, j, c) in r['liftability_fails'][:max_fails]:
                print(f"      n={n}, j={j}, c={c}")


# ─── Main ─────────────────────────────────────────────────────────────

def main():
    N_MAX = 6  # exhaustive up to n=6

    print("="*70)
    print("INVARIANT SEARCH V2 FOR RULE 30 LIFTING LEMMA")
    print(f"Testing n=1..{N_MAX} (exhaustive over all witnesses)")
    print("="*70)
    print("Three conditions to satisfy:")
    print("  EXIST: for every (n,j), exists liftable c with pred(c,n,j)")
    print("  CLOSE: pred(c,n,j) => pred(embed(c,b0,b1), n+1, j+1) for valid lift")
    print("  LIFT:  pred(c,n,j) => c is liftable (no non-liftable witness satisfies pred)")
    print()

    # Test all candidates
    results = []
    for name, pred in CANDIDATES:
        print(f"  Testing {name}...", flush=True)
        r = test_invariant_v2(name, pred, n_max=N_MAX)
        results.append(r)

    # Summary table
    winners = print_results_table(results)

    # Failure details
    print_failures(results)

    # Detailed analysis
    test_b1_zero_hypothesis(n_max=N_MAX)
    test_b0_formulas_given_b1_zero(n_max=min(N_MAX, 5))

    # Closure analysis for P_A specifically
    analyze_closure_for_P_A(n_max=N_MAX)

    # Which (b0,b1) preserves each promising candidate?
    for name, pred in CANDIDATES:
        # Only analyze candidates that have EXIST-OK and CLOSE-OK
        matching = [r for r in results if r['name'] == name and r['exist_ok'] and r['close_ok']]
        if matching:
            test_closure_all_b01(name, pred, n_max=min(N_MAX, 5))

    # Shadow analysis
    shadow_analysis(n_max=min(N_MAX, 7))

    print("\n" + "="*70)
    print("KEY FINDINGS SUMMARY")
    print("="*70)
    if winners:
        print(f"Invariants satisfying ALL THREE conditions: {winners}")
    else:
        # Find partial winners
        exist_close = [r['name'] for r in results if r['exist_ok'] and r['close_ok']]
        exist_lift = [r['name'] for r in results if r['exist_ok'] and r['lift_ok']]
        print(f"EXIST+CLOSE (but not LIFT): {exist_close}")
        print(f"EXIST+LIFT (but not CLOSE): {exist_lift}")
    print("="*70)
    print("DONE")


if __name__ == "__main__":
    main()
