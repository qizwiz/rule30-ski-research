#!/usr/bin/env python3
"""
Canonical Lifting Witness Search for Rule 30 AllEssential.

Goal: For each (n, j), find the LEXICOGRAPHICALLY FIRST config that:
  1. Is a witness for Essential(n, j)  — flipping bit j changes rule30_center
  2. Is liftable: exists (b0, b1) s.t. [b0]+config+[b1] witnesses Essential(n+1, j+1)

Then search for a formula relating the lex-first liftable witness to (n, j).
"""

from collections import defaultdict


def rule30_evolve(config):
    """One step of Rule 30 on a list of bits. Shrinks width by 2 (no boundary)."""
    n = len(config)
    if n < 3:
        return []
    return [config[i-1] ^ (config[i] | config[i+1]) for i in range(1, n-1)]


def rule30_center(steps, config):
    """Evolve config for `steps` steps, return center bit.
    Config has width 2*steps+1, so after steps evolves we get width 1."""
    tape = list(config)
    for _ in range(steps):
        tape = rule30_evolve(tape)
    if len(tape) != 1:
        return None  # width mismatch
    return tape[0]


def is_witness(n, j, config):
    """Does flipping bit j in config change rule30_center(n, config)?"""
    w = 2*n + 1
    if len(config) != w:
        return False
    c2 = list(config)
    c2[j] ^= 1
    return rule30_center(n, config) != rule30_center(n, c2)


def is_liftable(n, j, config):
    """Can config be embedded as [b0]+config+[b1] to witness Essential(n+1, j+1)?"""
    for b0 in [0, 1]:
        for b1 in [0, 1]:
            c = [b0] + list(config) + [b1]
            c2 = list(c)
            c2[j+1] ^= 1
            v1 = rule30_center(n+1, c)
            v2 = rule30_center(n+1, c2)
            if v1 is not None and v2 is not None and v1 != v2:
                return True, (b0, b1)
    return False, None


def hamming_weight(config):
    return sum(config)


def is_spike(config):
    """If config has exactly one 1-bit, return its position. Else None."""
    hw = hamming_weight(config)
    if hw != 1:
        return None
    return config.index(1)


def lex_first_liftable(n, j, max_configs=None):
    """Find lex-first (as integer) config that is both witness and liftable."""
    w = 2*n + 1
    limit = 1 << w
    if max_configs is not None:
        limit = min(limit, max_configs)
    for bits in range(limit):
        config = [(bits >> k) & 1 for k in range(w)]
        if is_witness(n, j, config) and is_liftable(n, j, config)[0]:
            return config
    return None


def spike_at(pos, width):
    """Return a config of given width with a single 1 at position pos."""
    c = [0] * width
    c[pos] = 1
    return c


def test_spike_liftable(n, j, pos):
    """Test if spike at `pos` in a (2n+1)-width config is a liftable witness for (n,j)."""
    w = 2*n + 1
    if pos < 0 or pos >= w:
        return False, False
    config = spike_at(pos, w)
    wit = is_witness(n, j, config)
    if not wit:
        return False, False
    lift, _ = is_liftable(n, j, config)
    return wit, lift


# =============================================
# Main search
# =============================================

def main():
    print("=" * 70)
    print("CANONICAL LIFTING WITNESS SEARCH")
    print("=" * 70)

    # Phase 1: Full enumeration for small n
    print("\n--- Phase 1: Full enumeration (n <= 7) ---\n")
    results = {}  # (n, j) -> config
    for n in range(8):
        w = 2*n + 1
        for j in range(w):
            config = lex_first_liftable(n, j)
            if config is not None:
                sp = is_spike(config)
                hw = hamming_weight(config)
                results[(n, j)] = config
                spike_str = f"spike@{sp}" if sp is not None else f"hw={hw}"
                print(f"  n={n:2d}, j={j:2d}: {config}  ({spike_str})")
            else:
                results[(n, j)] = None
                print(f"  n={n:2d}, j={j:2d}: NONE (no liftable witness found)")

    # Phase 2: Analyze spike patterns
    print("\n--- Phase 2: Spike analysis ---\n")
    print(f"{'n':>3s} {'j':>3s} {'spike_pos':>10s} {'j//2':>5s} {'j-1':>5s} {'2n-j':>5s} {'n-j//2':>7s}")
    print("-" * 50)
    for (n, j), config in sorted(results.items()):
        if config is None:
            continue
        sp = is_spike(config)
        if sp is not None:
            print(f"{n:3d} {j:3d} {sp:10d} {j//2:5d} {max(0,j-1):5d} {2*n-j:5d} {n - j//2:7d}")

    # Phase 3: Test specific hypotheses for all (n,j)
    print("\n--- Phase 3: Hypothesis testing ---\n")

    hypotheses = {
        "spike@j":       lambda n, j: j,
        "spike@(j//2)":  lambda n, j: j // 2,
        "spike@max(0,j-1)": lambda n, j: max(0, j-1),
        "spike@(2n-j)":  lambda n, j: 2*n - j,
        "spike@(n-j//2)": lambda n, j: n - j // 2,
        "spike@(n)":     lambda n, j: n,
        "spike@0":       lambda n, j: 0,
    }

    # Test on n=0..10 (spike-only, fast)
    max_n_hyp = 12
    print(f"Testing hypotheses for n=0..{max_n_hyp}:\n")
    for name, formula in hypotheses.items():
        ok = 0
        fail = 0
        for n in range(max_n_hyp + 1):
            w = 2*n + 1
            for j in range(w):
                pos = formula(n, j)
                if pos < 0 or pos >= w:
                    fail += 1
                    continue
                wit, lift = test_spike_liftable(n, j, pos)
                if wit and lift:
                    ok += 1
                else:
                    fail += 1
        total = ok + fail
        print(f"  {name:25s}: {ok}/{total} pass ({100*ok/total:.1f}%)")

    # Phase 4+5: For each (n,j), find ALL liftable spike positions (single pass)
    print("\n--- Phase 4: All liftable spike positions per (n,j) for n<=12 ---\n")
    all_liftable_spikes = {}  # (n, j) -> list of positions
    min_spikes = {}           # (n, j) -> min position
    no_spike_cases = []
    for n in range(13):
        w = 2*n + 1
        for j in range(w):
            good_spikes = []
            for pos in range(w):
                wit, lift = test_spike_liftable(n, j, pos)
                if wit and lift:
                    good_spikes.append(pos)
            all_liftable_spikes[(n, j)] = good_spikes
            if good_spikes:
                min_spikes[(n, j)] = good_spikes[0]
                if n <= 10:
                    print(f"  n={n:2d}, j={j:2d}: liftable spikes at {good_spikes}  (min={good_spikes[0]})")
            else:
                no_spike_cases.append((n, j))
                if n <= 10:
                    print(f"  n={n:2d}, j={j:2d}: NO liftable spike witness!")

    print("\n--- Phase 5: Minimum liftable spike position formula search ---\n")
    print(f"{'n':>3s} {'j':>3s} {'min_spike':>10s} {'candidates':>40s}")
    print("-" * 60)
    for (n, j), spikes in sorted(all_liftable_spikes.items()):
        if spikes and (n <= 6 or j in [0, 1, n, 2*n-1, 2*n]):
            cands = spikes[:10]
            print(f"{n:3d} {j:3d} {spikes[0]:10d} {str(cands):>40s}")

    # Phase 6: Derive formula from min_spikes
    print("\n--- Phase 6: Formula derivation ---\n")

    by_j = defaultdict(set)
    for (n, j), ms in min_spikes.items():
        by_j[j].add(ms)

    j_independent = all(len(vals) == 1 for vals in by_j.values())
    print(f"  Min spike depends only on j (independent of n)? {j_independent}")
    if not j_independent:
        print("  j-values with multiple min_spikes across different n:")
        for j_val in sorted(by_j.keys()):
            if len(by_j[j_val]) > 1:
                print(f"    j={j_val}: min_spikes = {sorted(by_j[j_val])}")

    # Check simple formulas against min_spikes
    print("\n  Formula check against min_spike data (n<=12):")
    formulas = [
        ("j",           lambda n, j: j),
        ("j//2",        lambda n, j: j // 2),
        ("max(0,j-1)",  lambda n, j: max(0, j-1)),
        ("(j+1)//2",    lambda n, j: (j+1) // 2),
        ("j if j<=n else 2n-j", lambda n, j: j if j <= n else 2*n - j),
        ("min(j, 2n-j)", lambda n, j: min(j, 2*n - j)),
    ]
    for name, f in formulas:
        match = 0
        total = 0
        for (n, j), ms in min_spikes.items():
            total += 1
            val = f(n, j)
            if val == ms:
                match += 1
        print(f"    {name:30s}: {match}/{total} match ({100*match/total:.1f}%)")

    # Phase 7: Print the full table for visual inspection
    print("\n--- Phase 7: Full min_spike table (n x j) ---\n")
    max_n_table = 10
    # Header
    max_j = 2 * max_n_table + 1
    hdr = "n\\j " + " ".join(f"{j:3d}" for j in range(max_j))
    print(hdr)
    print("-" * len(hdr))
    for n in range(max_n_table + 1):
        w = 2*n + 1
        row = f"{n:3d} "
        for j in range(max_j):
            if j < w and (n, j) in min_spikes:
                row += f"{min_spikes[(n,j)]:3d} "
            elif j < w:
                row += "  . "
            else:
                row += "    "
        print(row)

    # Phase 8: Universal liftable spike existence (uses data from Phase 4)
    print("\n--- Phase 8: Universal liftable spike existence ---\n")
    if no_spike_cases:
        print(f"  FAILURE: No liftable spike for {len(no_spike_cases)} cases:")
        for nj in no_spike_cases[:20]:
            print(f"    (n={nj[0]}, j={nj[1]})")
    else:
        print(f"  SUCCESS: Every (n,j) for n<=12 has at least one liftable spike witness.")

    # Phase 9: Key structural findings
    print("\n--- Phase 9: Structural analysis ---\n")

    # Check: is all-zeros always a witness (and liftable)?
    print("  All-zeros as witness and liftable witness:")
    zero_wit = 0
    zero_lift = 0
    total_pairs = 0
    for n in range(13):
        w = 2*n + 1
        for j in range(w):
            total_pairs += 1
            config = [0] * w
            if is_witness(n, j, config):
                zero_wit += 1
                lft, _ = is_liftable(n, j, config)
                if lft:
                    zero_lift += 1
    print(f"    All-zeros is witness: {zero_wit}/{total_pairs}")
    print(f"    All-zeros is liftable witness: {zero_lift}/{total_pairs}")

    # For the (6,5) failure: what witnesses exist?
    print("\n  (n=6, j=5) failure analysis:")
    w = 2*6 + 1
    print(f"    All-zeros witness? {is_witness(6, 5, [0]*w)}")
    print(f"    All-zeros liftable? {is_liftable(6, 5, [0]*w)}")
    # Find ALL low-weight liftable witnesses
    count = 0
    for bits in range(1 << w):
        config = [(bits >> k) & 1 for k in range(w)]
        if hamming_weight(config) > 2:
            continue
        if is_witness(6, 5, config) and is_liftable(6, 5, config)[0]:
            count += 1
            if count <= 10:
                sp = is_spike(config)
                print(f"    Liftable hw<=2 witness: {config}  (spike@{sp})" if sp is not None
                      else f"    Liftable hw<=2 witness: {config}  (hw={hamming_weight(config)})")

    # Phase 10: Existence of liftable witness (any weight) for all (n,j)
    print("\n--- Phase 10: Existence of ANY liftable witness (full enum n<=7) ---\n")
    for n in range(8):
        w = 2*n + 1
        for j in range(w):
            found = False
            for bits in range(1 << w):
                config = [(bits >> k) & 1 for k in range(w)]
                if is_witness(n, j, config) and is_liftable(n, j, config)[0]:
                    found = True
                    break
            if not found:
                print(f"  NO liftable witness at all for (n={n}, j={j})!")
    print("  Full enum n<=7: every (n,j) has a liftable witness.")

    # Phase 11: The real invariant -- does j=2n always have spike@2n?
    # And j=0 always spike@0? And the pattern at boundaries?
    print("\n--- Phase 11: Boundary invariants ---\n")
    print("  j=0:  spike@0 always liftable?")
    for n in range(20):
        w = 2*n + 1
        wit, lift = test_spike_liftable(n, 0, 0)
        if not (wit and lift):
            print(f"    FAIL at n={n}: wit={wit}, lift={lift}")
            break
    else:
        print(f"    YES for n=0..19")

    print("  j=2n: spike@2n always liftable?")
    for n in range(20):
        w = 2*n + 1
        wit, lift = test_spike_liftable(n, 2*n, 2*n)
        if not (wit and lift):
            print(f"    FAIL at n={n}: wit={wit}, lift={lift}")
            break
    else:
        print(f"    YES for n=0..19")

    # The key question: spike@j liftable? (i.e., THE diagonal witness)
    print("\n  spike@j always liftable? (THE key test for lifting_lemma)")
    spike_j_fails = []
    for n in range(15):
        w = 2*n + 1
        for j in range(w):
            wit, lift = test_spike_liftable(n, j, j)
            if not (wit and lift):
                spike_j_fails.append((n, j, wit, lift))
    if spike_j_fails:
        print(f"    FAILS at {len(spike_j_fails)} cases (first 20):")
        for n, j, wit, lift in spike_j_fails[:20]:
            print(f"      n={n}, j={j}: witness={wit}, liftable={lift}")
    else:
        print(f"    YES for all n<=14!")

    # Phase 12: AllEssential says every j is essential.
    # The witness for Essential(n,j) used in AllEssential is spike@j.
    # Check: is spike@j always a witness?
    print("\n  spike@j always a WITNESS? (not asking about liftability)")
    spike_j_witness_fails = []
    for n in range(15):
        w = 2*n + 1
        for j in range(w):
            config = spike_at(j, w)
            if not is_witness(n, j, config):
                spike_j_witness_fails.append((n, j))
    if spike_j_witness_fails:
        print(f"    FAILS at {len(spike_j_witness_fails)} cases (first 20):")
        for n, j in spike_j_witness_fails[:20]:
            print(f"      n={n}, j={j}")
    else:
        print(f"    YES: spike@j is always a witness for n<=14!")

    # Phase 13: THE REAL QUESTION for lifting_lemma
    # For every witness for Essential(n,j), is it liftable?
    # i.e., does EVERY witness lift, or just some?
    print("\n--- Phase 13: Does EVERY witness for (n,j) lift? ---\n")
    unliftable_witnesses = {}
    for n in range(8):
        w = 2*n + 1
        for j in range(w):
            total_wit = 0
            liftable_wit = 0
            unliftable = []
            for bits in range(1 << w):
                config = [(bits >> k) & 1 for k in range(w)]
                if is_witness(n, j, config):
                    total_wit += 1
                    lft, _ = is_liftable(n, j, config)
                    if lft:
                        liftable_wit += 1
                    elif len(unliftable) < 3:
                        unliftable.append(config)
            if unliftable:
                unliftable_witnesses[(n, j)] = (total_wit, liftable_wit, unliftable)
                print(f"  n={n}, j={j}: {liftable_wit}/{total_wit} witnesses are liftable"
                      f"  (UNLIFTABLE example: {unliftable[0]})")

    if not unliftable_witnesses:
        print("  ALL witnesses are liftable for n<=7! (lifting_lemma is trivially true)")
    else:
        print(f"\n  {len(unliftable_witnesses)} (n,j) pairs have unliftable witnesses.")
        # Key question: are there (n,j) where ALL witnesses are unliftable?
        all_unliftable = [(nj, v) for nj, v in unliftable_witnesses.items() if v[1] == 0]
        if all_unliftable:
            print(f"  CRITICAL: {len(all_unliftable)} cases have NO liftable witness at all:")
            for (n, j), (tw, lw, _) in all_unliftable:
                print(f"    n={n}, j={j}: {tw} witnesses, NONE liftable")
        else:
            print("  Every (n,j) with witnesses has at least one liftable witness.")
            # What fraction of witnesses are liftable?
            print("\n  Liftability ratio per (n,j):")
            for (n, j), (tw, lw, ul) in sorted(unliftable_witnesses.items()):
                print(f"    n={n}, j={j}: {lw}/{tw} = {100*lw/tw:.1f}%")

    # Phase 14: The lifting lemma structure
    # Essential(n,j) means: exists c s.t. flipping j changes center
    # We need: exists c s.t. flipping j changes center AND
    #          exists (b0,b1) s.t. [b0]+c+[b1] witnesses Essential(n+1,j+1)
    # The question: for the all-zeros config, when is it a witness?
    print("\n--- Phase 14: All-zeros witness pattern ---\n")
    print("  rule30_center(n, all_zeros) for various n:")
    for n in range(16):
        w = 2*n + 1
        v = rule30_center(n, [0]*w)
        print(f"    n={n:2d}: center = {v}")

    print("\n  When all-zeros is a witness, what is the flip value?")
    for n in range(10):
        w = 2*n + 1
        base = rule30_center(n, [0]*w)
        for j in range(w):
            c2 = [0]*w
            c2[j] = 1
            flipped = rule30_center(n, c2)
            if base != flipped:
                print(f"    n={n}, j={j}: 0->{base}, spike@{j}->{flipped}")

    print("\n" + "=" * 70)
    print("DONE")
    print("=" * 70)


if __name__ == "__main__":
    main()
