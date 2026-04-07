#!/usr/bin/env python3
"""
Lifting Structure Analysis for Rule 30 AllEssential.

For each (n, j) with n=0..7, j=0..2n:
1. Enumerate ALL witnesses for Essential(n, j) (brute force)
2. Check which are liftable: exists (b0, b1) s.t. [b0]+witness+[b1] witnesses Essential(n+1, j+1)
3. Characterize the liftable set:
   - Fraction liftable, min Hamming weight of liftable witness
   - Shadow positions: is there always a weight-1 (spike) liftable witness?
4. GF(2) structure: is the liftable set a coset of a linear code?
"""

import itertools
import math
from collections import defaultdict


def rule30_local(a, b, c):
    return a ^ (b | c)


def rule30_evolve(config):
    return [rule30_local(config[i-1], config[i], config[i+1]) for i in range(1, len(config)-1)]


def rule30_center(steps, config):
    tape = list(config)
    for _ in range(steps):
        tape = rule30_evolve(tape)
    assert len(tape) == 1, f"len={len(tape)} after {steps} steps from len={len(config)}"
    return tape[0]


def hamming_weight(config):
    return sum(config)


def xor_configs(a, b):
    return tuple(x ^ y for x, y in zip(a, b))


def is_witness(n, j, config):
    c2 = list(config)
    c2[j] ^= 1
    return rule30_center(n, config) != rule30_center(n, c2)


def liftable_pairs(n, j, witness):
    """Return all (b0, b1) pairs that make witness for (n,j) lift to (n+1, j+1)."""
    pairs = []
    for b0 in [0, 1]:
        for b1 in [0, 1]:
            c = [b0] + list(witness) + [b1]
            base = rule30_center(n + 1, c)
            c2 = list(c)
            c2[j + 1] ^= 1
            if base != rule30_center(n + 1, c2):
                pairs.append((b0, b1))
    return pairs


def check_linear_subspace(vectors, dim):
    """Check if a set of binary vectors forms a linear subspace of GF(2)^dim."""
    if not vectors:
        return True, 0
    # Check closure under XOR
    vset = set(vectors)
    zero = tuple([0] * dim)
    if zero not in vset:
        return False, len(vectors)
    for v1 in vectors:
        for v2 in vectors:
            if xor_configs(v1, v2) not in vset:
                return False, len(vectors)
    d = round(math.log2(len(vectors))) if len(vectors) > 0 else 0
    return True, d


def analyze_n_j(n, j):
    width = 2 * n + 1
    all_witnesses = []
    liftable_witnesses = []
    non_liftable_witnesses = []
    pair_counts = defaultdict(int)

    for bits in itertools.product([0, 1], repeat=width):
        config = list(bits)
        if is_witness(n, j, config):
            all_witnesses.append(tuple(bits))
            pairs = liftable_pairs(n, j, bits)
            if pairs:
                liftable_witnesses.append(tuple(bits))
                for p in pairs:
                    pair_counts[p] += 1
            else:
                non_liftable_witnesses.append(tuple(bits))

    return all_witnesses, liftable_witnesses, non_liftable_witnesses, pair_counts


def check_gf2_coset(liftable_set, dim):
    """Check if liftable_set is a coset of a linear subspace."""
    if not liftable_set:
        return False, 0, None
    # Pick any element as reference, XOR all others with it
    ref = liftable_set[0]
    translated = [xor_configs(w, ref) for w in liftable_set]
    is_lin, subdim = check_linear_subspace(translated, dim)
    return is_lin, subdim, ref


def main():
    max_n = 7
    print(f"{'n':>3} {'j':>3} {'width':>5} {'#wit':>7} {'#lift':>7} {'frac':>7} "
          f"{'min_w':>5} {'min_lw':>6} {'spk_l':>5} {'coset':>5} {'codim':>6}")
    print("-" * 80)

    summary = defaultdict(list)

    for n in range(max_n + 1):
        width = 2 * n + 1
        if width > 15:  # 2^15 = 32768, feasible
            print(f"  Skipping n={n} (width={width}, 2^{width} too large)")
            continue

        for j in range(width):
            all_w, lift_w, nonlift_w, pair_cts = analyze_n_j(n, j)

            num_wit = len(all_w)
            num_lift = len(lift_w)
            frac = num_lift / num_wit if num_wit > 0 else 0.0

            # Min Hamming weight among all witnesses
            min_w = min(hamming_weight(w) for w in all_w) if all_w else -1
            # Min Hamming weight among liftable witnesses
            min_lw = min(hamming_weight(w) for w in lift_w) if lift_w else -1

            # Check if any spike (weight-1) witness is liftable
            spike_liftable = False
            if lift_w:
                for w in lift_w:
                    if hamming_weight(w) == 1:
                        spike_liftable = True
                        break

            # GF(2) coset check (skip for large sets to keep runtime sane)
            if num_lift <= 4096:
                is_coset, codim, _ = check_gf2_coset(lift_w, width)
            else:
                is_coset, codim = None, None

            coset_str = "Y" if is_coset else ("N" if is_coset is False else "?")
            codim_str = str(codim) if codim is not None else "?"

            print(f"{n:>3} {j:>3} {width:>5} {num_wit:>7} {num_lift:>7} {frac:>7.3f} "
                  f"{min_w:>5} {min_lw:>6} {'Y' if spike_liftable else 'N':>5} "
                  f"{coset_str:>5} {codim_str:>6}")

            summary[n].append({
                'j': j, 'num_wit': num_wit, 'num_lift': num_lift,
                'frac': frac, 'min_w': min_w, 'min_lw': min_lw,
                'spike_liftable': spike_liftable, 'is_coset': is_coset, 'codim': codim,
                'pair_counts': dict(pair_cts)
            })

    # Summary statistics
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)

    all_liftable_nonempty = True
    all_shadow_spike = True
    fracs = []

    for n, entries in sorted(summary.items()):
        for e in entries:
            if e['num_lift'] == 0:
                all_liftable_nonempty = False
                print(f"  WARNING: (n={n}, j={e['j']}) has NO liftable witnesses!")
            fracs.append(e['frac'])
            if not e['spike_liftable']:
                all_shadow_spike = False

    print(f"\nLiftable set always non-empty: {all_liftable_nonempty}")
    print(f"Mean fraction liftable: {sum(fracs)/len(fracs):.4f}")
    print(f"Min fraction liftable:  {min(fracs):.4f}")
    print(f"Max fraction liftable:  {max(fracs):.4f}")
    print(f"All positions have spike liftable witness: {all_shadow_spike}")

    # Detailed: min liftable weight pattern
    print(f"\nMin liftable Hamming weight by (n, j):")
    for n, entries in sorted(summary.items()):
        weights = [e['min_lw'] for e in entries]
        print(f"  n={n}: {weights}")

    # GF(2) coset pattern
    print(f"\nGF(2) coset structure:")
    for n, entries in sorted(summary.items()):
        cosets = [(e['j'], e['is_coset'], e['codim']) for e in entries]
        coset_summary = [f"j={j}:{'Y' if c else 'N'}(dim={d})" for j, c, d in cosets if c is not None]
        print(f"  n={n}: {', '.join(coset_summary)}")

    print(f"\nBoundary pair analysis (which (b0,b1) make witnesses liftable):")
    for n, entries in sorted(summary.items()):
        if n > 3:
            continue
        for e in entries:
            pc = e['pair_counts']
            total = e['num_wit']
            pairs_str = ", ".join(
                f"({b0},{b1}):{pc.get((b0,b1),0)}/{total}"
                for b0 in [0, 1] for b1 in [0, 1]
            )
            print(f"  n={n}, j={e['j']}: {pairs_str}")


if __name__ == "__main__":
    main()
