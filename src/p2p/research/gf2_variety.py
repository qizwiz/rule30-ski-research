"""
gf2_variety.py — GF(2) Partial Derivative Variety for Rule 30 Shadow Regions

For shadow (n,j) pairs (where dChain(n+1,j)=False AND dChain(n,j)=False),
compute the sensitivity set S_j = {c : rule30n(n+1, c) != rule30n(n+1, flip(c,j))}
and analyze its algebraic structure over GF(2).

Key questions:
  1. Is |S_j| always a power of 2?
  2. Is S_j an affine subspace of GF(2)^(2n+3)?
  3. What is the minimum Hamming weight witness in S_j?
  4. Does a weight-1 or weight-2 witness always exist for shadow positions?
"""

import numpy as np


def rule30_local(a, b, c):
    return a ^ (b | c)


def dchain_table(max_t, max_k):
    """Compute dChain(t, k) for 0 <= t <= max_t, 0 <= k <= max_k."""
    d = np.zeros((max_t + 1, max_k + 1), dtype=bool)
    # dChain(t, 0) = True for all t
    d[:, 0] = True
    # dChain(0, k) = False for k >= 1 (already zero)
    for t in range(max_t):
        # dChain(t+1, 1) = rule30Local(dChain(t,1), True, False)
        if max_k >= 1:
            d[t + 1, 1] = rule30_local(int(d[t, 1]), 1, 0)
        # dChain(t+1, k+2) = rule30Local(dChain(t,k+2), dChain(t,k+1), dChain(t,k))
        for k in range(max_k - 1):
            d[t + 1, k + 2] = rule30_local(
                int(d[t, k + 2]), int(d[t, k + 1]), int(d[t, k])
            )
    return d


def find_shadows(max_n):
    """Find all shadow (n, j) pairs: dChain(n+1, j)=False AND dChain(n, j)=False."""
    max_t = max_n + 2
    max_k = 2 * max_n + 2
    d = dchain_table(max_t, max_k)
    shadows = []
    for n in range(1, max_n + 1):
        for j in range(1, 2 * n + 2):  # j in [1, 2n+1] for level n+1
            if not d[n + 1, j] and not d[n, j]:
                shadows.append((n, j))
    return shadows, d


def rule30_center_vectorized(steps, configs_array):
    """Vectorized: evolve all configs (rows of 2D array) for `steps` steps."""
    tape = configs_array.copy()
    for _ in range(steps):
        tape = tape[:, :-2] ^ (tape[:, 1:-1] | tape[:, 2:])
    return tape[:, 0]


def int_to_config(x, nbits):
    """Convert integer to list of bits (MSB first)."""
    return [(x >> (nbits - 1 - i)) & 1 for i in range(nbits)]


def check_affine_subspace(S_configs, nbits):
    """
    Check if a set of configs (as integer array) forms an affine subspace of GF(2)^nbits.
    Translate by first element, then verify the translated set equals the span of
    a basis found by Gaussian elimination. Returns (is_affine, dimension).
    """
    if len(S_configs) == 0:
        return True, 0
    if len(S_configs) == 1:
        return True, 0

    size = len(S_configs)
    if size & (size - 1) != 0:
        return False, None

    base = int(S_configs[0])
    translated = set(int(s) ^ base for s in S_configs)

    # Gaussian elimination to find a basis for the translated set
    basis = []
    for v in sorted(translated):
        r = v
        for b in basis:
            r = min(r, r ^ b)
        if r > 0:
            basis.append(r)

    # The span of basis should have exactly 2^len(basis) elements
    dim = len(basis)
    if (1 << dim) != size:
        return False, None

    # Verify: generate the full span and compare
    span = {0}
    for b in basis:
        span = span | {s ^ b for s in span}
    if span != translated:
        return False, None

    return True, dim


def analyze_shadow(n, j, max_configs=2**20):
    """
    For shadow (n, j), compute sensitivity set S_j and analyze it.
    Level = n+1, tape length = 2*(n+1)+1 = 2n+3, steps = n+1.
    """
    level = n + 1
    tape_len = 2 * level + 1
    steps = level
    num_configs = 2**tape_len

    if num_configs > max_configs:
        return None  # Too large

    # Build all configs as numpy array (vectorized bit unpacking)
    indices = np.arange(num_configs, dtype=np.int32)
    configs = ((indices[:, None] >> np.arange(tape_len - 1, -1, -1)) & 1).astype(np.int8)

    # Compute f(c) for all configs
    f_vals = rule30_center_vectorized(steps, configs)

    # Compute f(flip(c, j)) — flip bit j in every config
    flipped = configs.copy()
    flipped[:, j] = 1 - flipped[:, j]
    f_flipped = rule30_center_vectorized(steps, flipped)

    # Sensitivity set: where f(c) != f(flip(c,j))
    sensitive = f_vals != f_flipped
    S_indices = np.where(sensitive)[0]
    S_size = len(S_indices)

    if S_size == 0:
        return {
            "n": n,
            "j": j,
            "level": level,
            "tape_len": tape_len,
            "S_size": 0,
            "is_power_of_2": True,
            "min_weight": None,
            "min_weight_witness": None,
            "is_affine": True,
            "affine_dim": 0,
        }

    # Power of 2 check
    is_pow2 = (S_size & (S_size - 1)) == 0

    # Compute weights once, reuse for all analyses
    weights = np.sum(configs[S_indices], axis=1)
    min_weight = int(np.min(weights))
    min_mask = weights == min_weight
    min_weight_count = int(np.sum(min_mask))
    first_min_idx = int(S_indices[np.argmin(weights)])
    min_witness = int_to_config(first_min_idx, tape_len)

    # Affine subspace check (only if not too large)
    if S_size <= 2**16:
        is_affine, affine_dim = check_affine_subspace(
            S_indices.astype(np.int64), tape_len
        )
    else:
        is_affine, affine_dim = None, None

    # Weight-1 (spike) witnesses
    spike_mask = weights == 1
    spike_witnesses = []
    for idx in S_indices[spike_mask]:
        spike_witnesses.append(int(np.argmax(configs[idx])))

    # Weight-2 witnesses (up to 20)
    wt2_mask = weights == 2
    wt2_indices = S_indices[wt2_mask][:20]
    weight2_witnesses = [tuple(int(x) for x in np.where(configs[idx])[0]) for idx in wt2_indices]

    return {
        "n": n,
        "j": j,
        "level": level,
        "tape_len": tape_len,
        "S_size": S_size,
        "is_power_of_2": is_pow2,
        "min_weight": min_weight,
        "min_weight_count": min_weight_count,
        "min_weight_witness": min_witness,
        "is_affine": is_affine,
        "affine_dim": affine_dim,
        "spike_witnesses": spike_witnesses,
        "weight2_count": len(weight2_witnesses),
        "weight2_samples": weight2_witnesses[:5],
    }


def main():
    max_n = 12
    print("=" * 80)
    print("GF(2) Partial Derivative Variety — Rule 30 Shadow Regions")
    print("=" * 80)

    # Step 1: Find shadows
    shadows, d = find_shadows(max_n)
    print(f"\nShadow (n,j) pairs for n <= {max_n}:")
    print(f"  Total: {len(shadows)}")
    for n, j in shadows:
        print(f"  (n={n}, j={j})  dChain({n+1},{j})={d[n+1,j]}  dChain({n},{j})={d[n,j]}")

    # Print dChain table for reference
    print(f"\ndChain table (rows=t, cols=k):")
    show_t = min(max_n + 2, 16)
    show_k = min(2 * max_n + 2, 30)
    print("    k:", " ".join(f"{k:2d}" for k in range(show_k + 1)))
    for t in range(show_t + 1):
        row = " ".join(f" {'T' if d[t,k] else '.'}" for k in range(show_k + 1))
        print(f"  t={t:2d}: {row}")

    # Step 2: Analyze each feasible shadow
    print("\n" + "=" * 80)
    print("Sensitivity Set Analysis")
    print("=" * 80)

    results = []
    # Feasibility: tape_len = 2n+3. For n=4: 11 bits (2048). n=8: 19 bits (512K). n=9: 21 bits (2M).
    # Cap at n=9 for performance (2M configs * 10 steps is manageable with numpy).
    feasible_limit = 9

    for n, j in shadows:
        if n > feasible_limit:
            print(f"\n(n={n}, j={j}): SKIPPED — 2^{2*n+3} = {2**(2*n+3)} configs too large")
            continue

        print(f"\n--- Shadow (n={n}, j={j}) ---")
        result = analyze_shadow(n, j, max_configs=2**22)
        if result is None:
            print("  SKIPPED (too many configs)")
            continue

        results.append(result)
        print(f"  Level: {result['level']}, Tape length: {result['tape_len']}")
        print(f"  |S_j| = {result['S_size']}")
        print(f"  Power of 2: {result['is_power_of_2']}")
        if result["is_power_of_2"] and result["S_size"] > 0:
            print(f"    dim = {result['S_size'].bit_length() - 1}")
        print(f"  Affine subspace: {result['is_affine']}", end="")
        if result["is_affine"] and result["affine_dim"] is not None:
            print(f" (dim={result['affine_dim']})")
        else:
            print()
        print(f"  Min Hamming weight: {result['min_weight']}")
        print(f"    Count at min weight: {result['min_weight_count']}")
        print(f"    Witness: {result['min_weight_witness']}")
        if result["spike_witnesses"]:
            print(f"  Spike (weight-1) witnesses at positions: {result['spike_witnesses']}")
        else:
            print(f"  No weight-1 witnesses")
        if result["weight2_count"] > 0:
            print(f"  Weight-2 witnesses ({result['weight2_count']}): {result['weight2_samples']}")

    # Summary table
    print("\n" + "=" * 80)
    print("SUMMARY TABLE")
    print("=" * 80)
    print(f"{'(n,j)':<10} {'Level':<6} {'|S_j|':<10} {'Pow2?':<6} {'Affine?':<8} "
          f"{'Dim':<5} {'MinWt':<6} {'Spike?':<7} {'Wt2?':<5}")
    print("-" * 75)
    for r in results:
        pow2 = "Y" if r["is_power_of_2"] else "N"
        affine = "Y" if r["is_affine"] else ("N" if r["is_affine"] is not None else "?")
        dim_str = str(r["affine_dim"]) if r["affine_dim"] is not None else "?"
        spike = "Y" if r["spike_witnesses"] else "N"
        wt2 = "Y" if r["weight2_count"] > 0 else "N"
        print(f"({r['n']},{r['j']}){'':<5} {r['level']:<6} {r['S_size']:<10} {pow2:<6} "
              f"{affine:<8} {dim_str:<5} {r['min_weight']:<6} {spike:<7} {wt2:<5}")

    # Key finding
    print("\n" + "=" * 80)
    print("KEY FINDINGS")
    print("=" * 80)
    all_pow2 = all(r["is_power_of_2"] for r in results)
    all_affine = all(r["is_affine"] for r in results if r["is_affine"] is not None)
    all_have_spike = all(bool(r["spike_witnesses"]) for r in results)
    all_have_wt2 = all(r["weight2_count"] > 0 for r in results)
    min_weights = [r["min_weight"] for r in results if r["min_weight"] is not None]

    print(f"  All |S_j| powers of 2: {all_pow2}")
    print(f"  All S_j affine subspaces: {all_affine}")
    print(f"  All have weight-1 (spike) witness: {all_have_spike}")
    print(f"  All have weight-2 witness: {all_have_wt2}")
    if min_weights:
        print(f"  Min weights seen: {sorted(set(min_weights))}")
        print(f"  Max of min weights: {max(min_weights)}")

    # Detailed spike analysis
    print("\n  Spike witness positions for each shadow:")
    for r in results:
        if r["spike_witnesses"]:
            print(f"    (n={r['n']}, j={r['j']}): spike positions {r['spike_witnesses']}")
        else:
            print(f"    (n={r['n']}, j={r['j']}): NO spike witness, min_weight={r['min_weight']}")


if __name__ == "__main__":
    main()
