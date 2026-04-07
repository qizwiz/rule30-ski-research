#!/usr/bin/env python3
"""
Invariant Search for Rule 30 lifting_lemma.

Tests 6 candidate invariants P(c, n, j) for:
  (a) Existence: for all (n,j) with n<=N_MAX, exists liftable witness satisfying P
  (b) Closure: if P(c,n,j) and c lifts via (b0,b1), does P([b0]+c+[b1], n+1, j+1)?

lifting_lemma: Essential(n, j) => Essential(n+1, j+1)

We need P such that:
  - P(c,n,j) => c witnesses Essential(n,j)
  - P(c,n,j) => exists (b0,b1): P([b0]+c+[b1], n+1, j+1)
"""

from functools import lru_cache


# ─── Core Rule 30 ────────────────────────────────────────────────────

def rule30_evolve(config):
    n = len(config)
    if n < 3:
        return []
    return [config[i-1] ^ (config[i] | config[i+1]) for i in range(1, n-1)]


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


# ─── dChain ──────────────────────────────────────────────────────────

@lru_cache(maxsize=None)
def dchain(t, k):
    """D-chain: dchain(t,0)=1, dchain(0,k>0)=0,
       dchain(t+1,k+2) = rule30(dchain(t,k+2), dchain(t,k+1), dchain(t,k))"""
    if k == 0:
        return 1
    if t == 0:
        return 0
    return dchain(t-1, k) ^ (dchain(t-1, k-1) | dchain(t-1, max(0, k-2)))


# ─── Enumerate witnesses (cached to avoid redundant work) ────────────

_witness_cache = {}
_liftable_cache = {}


def all_witnesses(n, j):
    """For small n, enumerate ALL witnesses for Essential(n,j)."""
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
    """All witnesses that are also liftable, with their lift info."""
    if (n, j) in _liftable_cache:
        return _liftable_cache[(n, j)]
    results = []
    for c in all_witnesses(n, j):
        ok, pair, lifted = is_liftable(n, j, c)
        if ok:
            results.append((c, pair, lifted))
    _liftable_cache[(n, j)] = results
    return results


# ─── Candidate invariants ────────────────────────────────────────────

def P1(c, n, j):
    """c[0] = 1 (leftmost bit is 1)."""
    return c[0] == 1


def P2(c, n, j):
    """c is a spike at position x where x <= j."""
    hw = sum(c)
    if hw != 1:
        return False
    pos = c.index(1)
    return pos <= j


def P3(c, n, j):
    """c[j] = 0 (the sensitive position has bit 0)."""
    return c[j] == 0


def P4(c, n, j):
    """rule30_center(1, [c[0], c[1], c[2]]) = dchain(n, j)."""
    if len(c) < 3:
        return False
    left_val = c[0] ^ (c[1] | c[2])
    return left_val == dchain(n, j)


def P5(c, n, j):
    """c is a spike at the mirror position 2n - j."""
    hw = sum(c)
    if hw != 1:
        return False
    pos = c.index(1)
    mirror = 2*n - j
    return pos == mirror


def P6(c, n, j):
    """c[0] XOR c[2n] = dchain(n+1, j)."""
    w = 2*n + 1
    if len(c) != w:
        return False
    return (c[0] ^ c[w-1]) == dchain(n+1, j)


INVARIANTS = {
    "P1: c[0]=1": P1,
    "P2: spike at x<=j": P2,
    "P3: c[j]=0": P3,
    "P4: left-corner = dChain": P4,
    "P5: spike at mirror(j)": P5,
    "P6: boundary parity = dChain": P6,
}


# ─── Test machinery ──────────────────────────────────────────────────

def test_invariant(name, pred, n_max=7):
    """Test invariant pred for existence and closure up to n_max."""
    existence_ok = True
    closure_ok = True
    existence_fails = []
    closure_fails = []

    for n in range(1, n_max + 1):
        w = 2*n + 1
        for j in range(w):
            found_liftable_with_pred = False
            closure_violation = False

            if n <= 6:
                liftable = all_liftable_witnesses(n, j)
                for (c, pair, lifted) in liftable:
                    if pred(c, n, j):
                        found_liftable_with_pred = True
                        if not pred(lifted, n+1, j+1):
                            closure_violation = True
                            closure_fails.append((n, j, c, pair, lifted))
                            break
            else:
                for x in range(w):
                    config = [0]*w
                    config[x] = 1
                    if is_witness(n, j, config) and pred(config, n, j):
                        ok, pair, lifted = is_liftable(n, j, config)
                        if ok:
                            found_liftable_with_pred = True
                            if not pred(lifted, n+1, j+1):
                                closure_violation = True
                                closure_fails.append((n, j, config, pair, lifted))
                            break

            if not found_liftable_with_pred:
                existence_ok = False
                existence_fails.append((n, j))
            if closure_violation:
                closure_ok = False

    return existence_ok, closure_ok, existence_fails, closure_fails


# ─── Composite / emergent invariant discovery ─────────────────────────

def discover_liftable_patterns(n_max=6):
    """For each (n,j), collect properties of ALL liftable witnesses.
    Look for a property that is ALWAYS satisfiable and ALWAYS preserved."""
    print("\n" + "="*70)
    print("EMERGENT PATTERN DISCOVERY")
    print("="*70)

    # Track: for each (n,j), what (b0,b1) pairs appear in liftable witnesses?
    lift_stats = {}

    for n in range(1, n_max + 1):
        w = 2*n + 1
        for j in range(w):
            liftable = all_liftable_witnesses(n, j)
            total_witnesses = len(all_witnesses(n, j))
            lift_pairs = set()
            # Track which boundary bits are used
            for (c, pair, lifted) in liftable:
                lift_pairs.add(pair)

            lift_stats[(n, j)] = {
                'total_witnesses': total_witnesses,
                'liftable_count': len(liftable),
                'lift_pairs': lift_pairs,
            }

            if len(liftable) == 0:
                print(f"  WARNING: (n={n}, j={j}) has 0 liftable witnesses out of {total_witnesses}!")

    # Summary: what fraction of witnesses are liftable?
    print("\nLiftability rates:")
    for n in range(1, n_max + 1):
        w = 2*n + 1
        rates = []
        for j in range(w):
            s = lift_stats[(n, j)]
            if s['total_witnesses'] > 0:
                rate = s['liftable_count'] / s['total_witnesses']
            else:
                rate = 0
            rates.append(rate)
        min_rate = min(rates)
        max_rate = max(rates)
        print(f"  n={n}: liftable rate in [{min_rate:.3f}, {max_rate:.3f}]")

    # Check: is EVERY witness liftable? (Would make invariant search trivial)
    all_liftable = True
    for key, s in lift_stats.items():
        if s['liftable_count'] < s['total_witnesses']:
            all_liftable = False
            break
    if all_liftable:
        print("\n  *** EVERY witness is liftable! No invariant needed. ***")
    else:
        print("\n  Not every witness is liftable; invariant IS needed.")


def discover_boundary_formula(n_max=6):
    """For each liftable witness, record which (b0,b1) works.
    Look for a formula: b0 = f(c, n, j), b1 = g(c, n, j)."""
    print("\n" + "="*70)
    print("BOUNDARY FORMULA DISCOVERY")
    print("="*70)

    # For each liftable witness, which (b0,b1) work?
    # Hypothesis: b0 = c[0], b1 = c[-1] (extend boundary)
    # Hypothesis: b0 = 0, b1 = 0 always works
    # Hypothesis: b0 = rule30_center(n, c), b1 = ...

    formulas = {
        "b0=0,b1=0": lambda c, n, j: (0, 0),
        "b0=1,b1=0": lambda c, n, j: (1, 0),
        "b0=0,b1=1": lambda c, n, j: (0, 1),
        "b0=1,b1=1": lambda c, n, j: (1, 1),
        "b0=c[0],b1=c[-1]": lambda c, n, j: (c[0], c[-1]),
        "b0=c[0]^1,b1=c[-1]^1": lambda c, n, j: (c[0]^1, c[-1]^1),
        "b0=0,b1=c[-1]": lambda c, n, j: (0, c[-1]),
        "b0=c[0],b1=0": lambda c, n, j: (c[0], 0),
    }

    for fname, f in formulas.items():
        works = True
        fail_count = 0
        for n in range(1, min(n_max+1, 7)):
            w = 2*n + 1
            for j in range(w):
                # Find ANY witness where this formula works
                found = False
                witnesses = all_witnesses(n, j)
                for c in witnesses:
                    b0, b1 = f(c, n, j)
                    lifted = [b0] + list(c) + [b1]
                    v1 = rule30_center(n+1, lifted)
                    v2 = rule30_center(n+1, flip(lifted, j+1))
                    if v1 is not None and v2 is not None and v1 != v2:
                        found = True
                        break
                if not found:
                    works = False
                    fail_count += 1
        if works:
            print(f"  {fname}: WORKS for all (n,j) up to n={min(n_max, 6)}")
        else:
            print(f"  {fname}: FAILS ({fail_count} failures)")


def test_combined_invariants(n_max=6):
    """Test conjunctions / disjunctions of invariants."""
    print("\n" + "="*70)
    print("COMBINED INVARIANT SEARCH")
    print("="*70)

    # P7: c[j]=0 AND c[0]=1
    def P7(c, n, j):
        return c[j] == 0 and c[0] == 1

    # P8: spike at j (the trivial witness: config = spike at j)
    def P8(c, n, j):
        return sum(c) == 1 and c[j] == 1

    # P9: hamming weight <= 2
    def P9(c, n, j):
        return sum(c) <= 2

    # P10: c[j]=1 (the sensitive bit is ON — standard spike direction)
    def P10(c, n, j):
        return c[j] == 1

    # P11: rule30_center(n, c) = 0 (the base output is 0)
    def P11(c, n, j):
        return rule30_center(n, c) == 0

    # P12: rule30_center(n, c) = 1
    def P12(c, n, j):
        return rule30_center(n, c) == 1

    extras = {
        "P7: c[j]=0 AND c[0]=1": P7,
        "P8: spike at j": P8,
        "P9: hw<=2": P9,
        "P10: c[j]=1": P10,
        "P11: center output=0": P11,
        "P12: center output=1": P12,
    }

    for name, pred in extras.items():
        eok, cok, efails, cfails = test_invariant(name, pred, n_max=n_max)
        status_e = "EXIST-OK" if eok else f"EXIST-FAIL({len(efails)})"
        status_c = "CLOSE-OK" if cok else f"CLOSE-FAIL({len(cfails)})"
        print(f"  {name}: {status_e}  {status_c}")
        if not eok and len(efails) <= 3:
            for (nn, jj) in efails[:3]:
                print(f"    no liftable witness at (n={nn}, j={jj})")
        if not cok and len(cfails) <= 3:
            for (nn, jj, c, pair, lifted) in cfails[:3]:
                print(f"    closure fail at (n={nn}, j={jj}), pair={pair}")


def test_universal_liftability(n_max=8):
    """THE key question: is every witness liftable?
    If yes, lifting_lemma is trivially true and no invariant is needed."""
    print("\n" + "="*70)
    print("UNIVERSAL LIFTABILITY TEST (is every witness liftable?)")
    print("="*70)

    for n in range(1, n_max + 1):
        w = 2*n + 1
        all_ok = True
        non_liftable = []
        for j in range(w):
            if n <= 7:
                witnesses = all_witnesses(n, j)
            else:
                # Just test spikes for larger n
                witnesses = []
                for x in range(w):
                    config = [0]*w
                    config[x] = 1
                    if is_witness(n, j, config):
                        witnesses.append(config)
            for c in witnesses:
                ok, _, _ = is_liftable(n, j, c)
                if not ok:
                    all_ok = False
                    non_liftable.append((j, c))
                    break  # one counterexample per j suffices
        if all_ok:
            print(f"  n={n}: ALL witnesses liftable")
        else:
            print(f"  n={n}: NOT all liftable — {len(non_liftable)} position(s)")
            for (jj, cc) in non_liftable[:3]:
                print(f"    j={jj}: non-liftable witness = {cc}")


# ─── Main ────────────────────────────────────────────────────────────

def main():
    N_MAX = 7  # exhaustive for n<=6, spike-only for n=7

    print("="*70)
    print("INVARIANT SEARCH FOR RULE 30 LIFTING LEMMA")
    print(f"Testing n=1..{N_MAX}")
    print("="*70)

    # First: the key question
    test_universal_liftability(n_max=min(N_MAX, 8))

    # Test each candidate invariant
    print("\n" + "="*70)
    print("CANDIDATE INVARIANT RESULTS")
    print("="*70)

    for name, pred in INVARIANTS.items():
        eok, cok, efails, cfails = test_invariant(name, pred, n_max=N_MAX)
        tag = ""
        if eok and cok:
            tag = " *** BOTH CONDITIONS MET ***"
        status_e = "EXIST-OK" if eok else f"EXIST-FAIL({len(efails)})"
        status_c = "CLOSE-OK" if cok else f"CLOSE-FAIL({len(cfails)})"
        print(f"\n  {name}: {status_e}  {status_c}{tag}")
        if not eok:
            for (nn, jj) in efails[:5]:
                print(f"    existence fail: (n={nn}, j={jj})")
            if len(efails) > 5:
                print(f"    ... and {len(efails)-5} more")
        if not cok:
            for (nn, jj, c, pair, lifted) in cfails[:5]:
                print(f"    closure fail: (n={nn}, j={jj}), c={c}, lift=({pair}), lifted={lifted}")
            if len(cfails) > 5:
                print(f"    ... and {len(cfails)-5} more")

    # Combined invariants
    test_combined_invariants(n_max=min(N_MAX, 6))

    # Emergent patterns
    discover_liftable_patterns(n_max=min(N_MAX, 5))

    # Boundary formula
    discover_boundary_formula(n_max=min(N_MAX, 5))

    print("\n" + "="*70)
    print("DONE")
    print("="*70)


if __name__ == "__main__":
    main()
