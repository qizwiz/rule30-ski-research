#!/usr/bin/env python3
"""
GF(2) Lifting Map — characterize liftability algebraically.

For each (n,j), computes:
  W(n,j)  = sensitivity set (all configs c where flipping bit j changes rule30 center)
  L(n,j)  = liftable witnesses (can be embedded into (n+1,j+1) witness)
  Tests whether liftability is a GF(2) linear function on W.

Author: Jonathan Hill + Claude
Date: 2026-04-07
"""

import itertools
import numpy as np
from collections import defaultdict


# ============================================================
# Rule 30 primitives (list-based, matching Lean semantics)
# ============================================================

def ca_step(cells):
    """Single Rule 30 step: rule30Local(p,q,r) = p XOR (q OR r).
    Output length = len(cells) - 2."""
    n = len(cells)
    if n < 3:
        return []
    return [cells[i] ^ (cells[i+1] | cells[i+2]) for i in range(n - 2)]


def ca_evolve(steps, cells):
    """Evolve cells for `steps` steps."""
    tape = list(cells)
    for _ in range(steps):
        tape = ca_step(tape)
    return tape


def rule30n(n, config):
    """rule30n(n, config): evolve n steps, return center cell (index 0).
    config is a list/tuple of length 2n+1."""
    result = ca_evolve(n, list(config))
    # After n steps on a tape of length 2n+1, we get length 1
    if len(result) == 0:
        return 0
    return result[0]


def flip_cell(config, k):
    """Flip bit at position k."""
    c = list(config)
    c[k] ^= 1
    return tuple(c)


# ============================================================
# Sensitivity and liftability
# ============================================================

def compute_W(n, j):
    """W(n,j) = set of configs c (as tuples) where flipping bit j changes output."""
    width = 2 * n + 1
    witnesses = []
    for bits in itertools.product([0, 1], repeat=width):
        c = tuple(bits)
        if rule30n(n, c) != rule30n(n, flip_cell(c, j)):
            witnesses.append(c)
    return witnesses


def is_liftable(n, j, c):
    """Check if witness c for (n,j) can be embedded into a witness for (n+1, j+1).
    Embedding: prepend b0, append b1 to get config of size 2(n+1)+1 = 2n+3."""
    for b0 in [0, 1]:
        for b1 in [0, 1]:
            cp = tuple([b0] + list(c) + [b1])
            cp_flip = flip_cell(cp, j + 1)  # flip at position j+1 in larger config
            if rule30n(n + 1, cp) != rule30n(n + 1, cp_flip):
                return True
    return False


def compute_L(n, j, W):
    """L(n,j) = liftable witnesses subset of W."""
    return [c for c in W if is_liftable(n, j, c)]


# ============================================================
# GF(2) linear algebra
# ============================================================

def xor_vec(a, b):
    return tuple(ai ^ bi for ai, bi in zip(a, b))


def is_linear_subspace(vectors, width):
    """Check if a set of vectors (tuples) forms a GF(2) linear subspace.
    Must contain zero vector and be closed under XOR."""
    vset = set(vectors)
    zero = tuple([0] * width)
    if zero not in vset:
        return False, "no zero vector"
    for a in vectors:
        for b in vectors:
            if xor_vec(a, b) not in vset:
                return False, f"not closed: {a} XOR {b} = {xor_vec(a,b)} not in set"
    return True, "closed"


def check_coset(vectors, width):
    """Check if vectors form a coset of a linear subspace.
    Pick any element, translate, check if result is subspace."""
    if not vectors:
        return False, "empty", None, None
    v0 = vectors[0]
    translated = [xor_vec(v, v0) for v in vectors]
    is_sub, msg = is_linear_subspace(translated, width)
    return is_sub, msg, v0, translated


def _gf2_eliminate(vectors, width):
    """GF(2) Gaussian elimination. Returns (rank, reduced_matrix)."""
    if not vectors:
        return 0, []
    mat = [list(v) for v in vectors]
    rows = len(mat)
    rank = 0
    for col in range(width):
        pivot = None
        for row in range(rank, rows):
            if mat[row][col] == 1:
                pivot = row
                break
        if pivot is None:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        for row in range(rows):
            if row != rank and mat[row][col] == 1:
                mat[row] = [mat[row][i] ^ mat[rank][i] for i in range(width)]
        rank += 1
    return rank, mat


def gf2_rank(vectors, width):
    """Compute GF(2) rank (dimension of span) of a set of vectors."""
    rank, _ = _gf2_eliminate(vectors, width)
    return rank


def find_basis(vectors, width):
    """Find a GF(2) basis for the span of vectors."""
    rank, mat = _gf2_eliminate(vectors, width)
    return [tuple(mat[i]) for i in range(rank)]


def check_liftability_linear(W, L, width):
    """Check if the liftability function f: W -> {0,1} is GF(2)-affine on W.

    W is a coset: W = w0 + V for some subspace V.
    Translate everything to V by subtracting w0.
    Then f is affine on the coset iff f(a XOR b XOR c) = f(a) XOR f(b) XOR f(c)
    for all a,b,c in W (3-wise affine condition).

    If W is a subspace (w0=0), then f affine means f(a XOR b) = f(a) XOR f(b) XOR f(0),
    i.e., f - f(0) is linear.
    """
    L_set = set(L)
    W_list = list(W)

    def f(c):
        return 1 if c in L_set else 0

    # Check 3-wise affine condition on a sample (or all if small enough)
    n_W = len(W_list)
    violations = 0
    checks = 0

    W_set = set(W)

    if n_W <= 200:
        for i in range(n_W):
            for j in range(i+1, n_W):
                for k in range(j+1, n_W):
                    a, b, c = W_list[i], W_list[j], W_list[k]
                    abc = xor_vec(xor_vec(a, b), c)
                    if abc in W_set:
                        checks += 1
                        if f(abc) != (f(a) ^ f(b) ^ f(c)):
                            violations += 1
    else:
        rng = np.random.RandomState(42)
        for _ in range(100000):
            idx = rng.choice(n_W, 3, replace=False)
            a, b, c = W_list[idx[0]], W_list[idx[1]], W_list[idx[2]]
            abc = xor_vec(xor_vec(a, b), c)
            if abc in W_set:
                checks += 1
                if f(abc) != (f(a) ^ f(b) ^ f(c)):
                    violations += 1

    return violations, checks


def find_linear_functional(W, L, width):
    """If f is linear on translated W (subspace), find the functional vector v
    such that f(x) = <v, x> for x in the translated subspace.

    Returns (v, success) where v is the functional vector or None.
    """
    if not W:
        return None, False

    W_list = list(W)
    L_set = set(L)
    w0 = W_list[0]
    f0 = 1 if w0 in L_set else 0

    # Translate: W' = {w XOR w0 : w in W} is a subspace
    # f'(w XOR w0) = f(w) XOR f0

    # Find basis of W'
    translated = [xor_vec(w, w0) for w in W_list]
    basis = find_basis(translated, width)
    dim = len(basis)

    if dim == 0:
        return None, False

    # f' values on basis vectors
    # For each basis vector b, find the original w such that w XOR w0 = b
    # i.e., w = b XOR w0
    f_on_basis = []
    for b in basis:
        w = xor_vec(b, w0)
        fw = 1 if w in L_set else 0
        f_on_basis.append(fw ^ f0)

    # v must satisfy <v, b_i> = f'(b_i) for each basis vector b_i
    # This is a system of linear equations over GF(2)
    # v is a vector in GF(2)^width

    # Build system: for each basis vector b_i, sum_{j where b_i[j]=1} v[j] = f'(b_i)
    # This gives dim equations in width unknowns
    # We want ANY solution (there are many if dim < width)

    # Augmented matrix [basis | f_values]
    aug = [list(b) + [fv] for b, fv in zip(basis, f_on_basis)]
    # Gaussian elimination
    n_rows = len(aug)
    n_cols = width + 1
    pivot_cols = []
    row_idx = 0
    for col in range(width):
        pivot = None
        for r in range(row_idx, n_rows):
            if aug[r][col] == 1:
                pivot = r
                break
        if pivot is None:
            continue
        aug[row_idx], aug[pivot] = aug[pivot], aug[row_idx]
        for r in range(n_rows):
            if r != row_idx and aug[r][col] == 1:
                aug[r] = [aug[r][i] ^ aug[row_idx][i] for i in range(n_cols)]
        pivot_cols.append(col)
        row_idx += 1

    # Read off solution (set free variables to 0)
    v = [0] * width
    for i, col in enumerate(pivot_cols):
        v[col] = aug[i][width]

    # Verify on all of W
    errors = 0
    for w in W_list:
        t = xor_vec(w, w0)
        dot = sum(v[i] * t[i] for i in range(width)) % 2
        expected = (1 if w in L_set else 0) ^ f0
        if dot != expected:
            errors += 1

    return tuple(v), errors == 0


# ============================================================
# Main analysis
# ============================================================

def analyze(n, j, cache=None):
    width = 2 * n + 1
    print(f"\n{'='*70}")
    print(f"  (n={n}, j={j})  width={width}  configs=2^{width}={2**width}")
    print(f"{'='*70}")

    W = compute_W(n, j)
    L = compute_L(n, j, W)
    if cache is not None:
        cache[(n, j)] = (W, L)
    L_set = set(L)
    NL = [c for c in W if c not in L_set]

    print(f"  |W| = {len(W)}  |L| = {len(L)}  |W\\L| = {len(NL)}")
    print(f"  liftable fraction = {len(L)}/{len(W)} = {len(L)/len(W):.4f}" if W else "  W empty")

    # Check if W is a coset
    is_coset_W, msg_W, w0_W, trans_W = check_coset(W, width)
    rank_W = gf2_rank([xor_vec(w, W[0]) for w in W], width) if W else 0
    print(f"  W coset? {is_coset_W} (rank={rank_W}, expected |W|=2^{rank_W}={2**rank_W})")

    # Check if L is a coset
    if L:
        is_coset_L, msg_L, w0_L, trans_L = check_coset(L, width)
        rank_L = gf2_rank([xor_vec(w, L[0]) for w in L], width) if L else 0
        print(f"  L coset? {is_coset_L} (rank={rank_L}, expected |L|=2^{rank_L}={2**rank_L})")
    else:
        print(f"  L empty — nothing liftable!")
        return None

    # Check if NL is a coset
    if NL:
        is_coset_NL, msg_NL, w0_NL, trans_NL = check_coset(NL, width)
        rank_NL = gf2_rank([xor_vec(w, NL[0]) for w in NL], width) if NL else 0
        print(f"  W\\L coset? {is_coset_NL} (rank={rank_NL})")
    else:
        print(f"  W\\L empty — ALL witnesses liftable!")
        return {"n": n, "j": j, "all_liftable": True, "W_size": len(W), "L_size": len(L)}

    # Check 3-wise affine condition
    violations, checks = check_liftability_linear(W, L, width)
    print(f"  Affine check: {violations} violations in {checks} valid triples")
    is_affine = (violations == 0 and checks > 0)
    print(f"  Liftability is {'AFFINE' if is_affine else 'NOT AFFINE'} on W")

    # If affine, find the linear functional
    v = None
    if is_affine:
        v, success = find_linear_functional(W, L, width)
        if success:
            nonzero_pos = [i for i in range(width) if v[i] == 1]
            print(f"  Linear functional v: nonzero at positions {nonzero_pos}")
            print(f"  v = {v}")
            # Interpret: is v related to j?
            center = n  # center position in 0-indexed width=2n+1
            print(f"  j={j}, center={center}, j-center={j-center}")
        else:
            print(f"  WARNING: affine but could not find consistent functional")
            v = None

    return {
        "n": n, "j": j, "width": width,
        "W_size": len(W), "L_size": len(L), "NL_size": len(NL),
        "W_coset": is_coset_W, "L_coset": is_coset_L if L else None,
        "W_rank": rank_W, "L_rank": rank_L if L else None,
        "is_affine": is_affine, "violations": violations, "checks": checks,
        "v": v,
        "all_liftable": len(NL) == 0,
    }


def boundary_analysis(n, j, W, L):
    """For each witness, determine which boundary bit combinations (b0,b1) work."""
    # For each witness, compute the set of working (b0,b1) pairs
    boundary_signatures = defaultdict(list)
    for c in W:
        working = []
        for b0 in [0, 1]:
            for b1 in [0, 1]:
                cp = tuple([b0] + list(c) + [b1])
                cp_flip = flip_cell(cp, j + 1)
                if rule30n(n + 1, cp) != rule30n(n + 1, cp_flip):
                    working.append((b0, b1))
        sig = tuple(sorted(working))
        boundary_signatures[sig].append(c)

    return boundary_signatures


def lifting_by_boundary(n, j, W):
    """Check if the output value rule30n(n,c) predicts liftability."""
    output_vs_lift = defaultdict(lambda: [0, 0])

    for c in W:
        out = rule30n(n, c)
        liftable = is_liftable(n, j, c)
        if liftable:
            output_vs_lift[out][0] += 1
        else:
            output_vs_lift[out][1] += 1

    return output_vs_lift


def causal_cone_analysis(n, j, W, L):
    """Check if liftability depends on bits OUTSIDE the causal cone of cell j.
    The causal cone of cell j at step n has width 2n+1 centered at j,
    but clipped to [0, 2n]. Bits outside this cone cannot affect the output
    difference from flipping j.

    Key insight: the causal cone of j at step n is [j-n, j+n] clipped to [0, 2n].
    But for lifting, we need (n+1, j+1) which has cone [j+1-(n+1), j+1+(n+1)] = [j-n, j+n+2].
    The NEW bits in the lifted cone are at positions 0 (=b0) and 2n+2 (=b1) in the
    n+1 config. In the original config, position j-n-1 and j+n+1 (if they exist)
    are the "fringe" that matters.
    """
    width = 2 * n + 1
    L_set = set(L)

    # Check: do non-liftable witnesses differ from liftable witnesses only
    # at specific bit positions?
    NL = [c for c in W if c not in L_set]
    if not NL or not L:
        return None

    # For each bit position, compute the correlation with liftability
    correlations = []
    for pos in range(width):
        # Count: among W, how does bit[pos] correlate with liftability?
        n00 = n01 = n10 = n11 = 0
        for c in W:
            b = c[pos]
            l = 1 if c in L_set else 0
            if b == 0 and l == 0: n00 += 1
            elif b == 0 and l == 1: n01 += 1
            elif b == 1 and l == 0: n10 += 1
            else: n11 += 1
        # Phi coefficient (correlation)
        num = n11 * n00 - n10 * n01
        den_sq = (n11+n10)*(n01+n00)*(n11+n01)*(n10+n00)
        phi = num / (den_sq**0.5) if den_sq > 0 else 0
        correlations.append((pos, phi, (n00, n01, n10, n11)))

    return correlations


def main():
    print("GF(2) Lifting Map Analysis")
    print("="*70)
    print("lifting_lemma: Essential(n,j) -> Essential(n+1, j+1)")
    print("W(n,j) = sensitivity set, L(n,j) = liftable witnesses")
    print("Question: is liftability a GF(2)-affine function on W?")

    results = []
    cache = {}  # (n, j) -> (W, L)

    for n in range(1, 7):  # n=1..6 (n=7 would be 2^15, too slow for triples)
        width = 2 * n + 1
        for j in range(width):
            r = analyze(n, j, cache)
            if r:
                results.append(r)

    # Summary
    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)

    all_liftable_cases = [r for r in results if r.get("all_liftable")]
    affine_cases = [r for r in results if r.get("is_affine") and not r.get("all_liftable")]
    non_affine_cases = [r for r in results if not r.get("is_affine") and not r.get("all_liftable")]

    print(f"\nAll witnesses liftable (L=W): {len(all_liftable_cases)} cases")
    for r in all_liftable_cases:
        print(f"  (n={r['n']}, j={r['j']}): |W|={r['W_size']}")

    print(f"\nLiftability is AFFINE (but L != W): {len(affine_cases)} cases")
    for r in affine_cases:
        v_str = ""
        if r.get("v"):
            nonzero = [i for i in range(r["width"]) if r["v"][i] == 1]
            v_str = f"  v nonzero at {nonzero}"
        print(f"  (n={r['n']}, j={r['j']}): |W|={r['W_size']}, |L|={r['L_size']}, "
              f"W_rank={r['W_rank']}, L_rank={r.get('L_rank', '?')}{v_str}")

    print(f"\nLiftability is NOT AFFINE: {len(non_affine_cases)} cases")
    for r in non_affine_cases:
        print(f"  (n={r['n']}, j={r['j']}): |W|={r['W_size']}, |L|={r['L_size']}, "
              f"violations={r['violations']}/{r['checks']}")

    # Deeper structural analysis
    print(f"\n{'='*70}")
    print("DEEPER STRUCTURAL ANALYSIS")
    print("="*70)

    print("\n--- Boundary bit signature analysis ---")
    print("For each (n,j), which (b0,b1) pairs make witnesses liftable?")
    for n in range(1, 6):  # n=1..5 for speed
        width = 2 * n + 1
        for j in range(width):
            if (n, j) not in cache:
                continue
            W, L = cache[(n, j)]
            if not W or len(L) == len(W):
                continue
            sigs = boundary_analysis(n, j, W, L)
            print(f"\n  (n={n}, j={j}): |W|={len(W)}")
            for sig, configs in sorted(sigs.items(), key=lambda x: -len(x[1])):
                pct = 100 * len(configs) / len(W)
                label = "NON-LIFTABLE" if not sig else ""
                print(f"    {sig}: {len(configs)} witnesses ({pct:.1f}%) {label}")

    print(f"\n--- Output-value vs liftability ---")
    print("Does output rule30n(n,c) predict liftability?")
    for n in range(1, 6):
        width = 2 * n + 1
        for j in range(width):
            if (n, j) not in cache:
                continue
            W, L = cache[(n, j)]
            if not W or len(L) == len(W):
                continue
            ovl = lifting_by_boundary(n, j, W)
            print(f"  (n={n}, j={j}): output=0: {ovl[0][0]}L/{ovl[0][1]}NL, "
                  f"output=1: {ovl[1][0]}L/{ovl[1][1]}NL")

    print(f"\n--- Bit-position correlation with liftability ---")
    print("Which bit positions most predict liftability?")
    for n in range(2, 6):
        width = 2 * n + 1
        for j in [0, n, width-1]:  # leftmost, center, rightmost
            if (n, j) not in cache:
                continue
            W, L = cache[(n, j)]
            if not W or len(L) == len(W) or not L:
                continue
            corrs = causal_cone_analysis(n, j, W, L)
            if corrs:
                # Sort by absolute correlation
                top = sorted(corrs, key=lambda x: -abs(x[1]))[:5]
                print(f"  (n={n}, j={j}): top correlated positions:")
                for pos, phi, counts in top:
                    rel = pos - n  # relative to center
                    print(f"    pos={pos} (rel={rel:+d}): phi={phi:+.3f}  "
                          f"(0,NL)={counts[0]} (0,L)={counts[1]} (1,NL)={counts[2]} (1,L)={counts[3]}")

    # CRITICAL: minimum liftable fraction across all (n,j)
    print(f"\n--- Minimum liftable fraction by n ---")
    for n_val in sorted(set(r["n"] for r in results)):
        n_results = [r for r in results if r["n"] == n_val and not r.get("all_liftable")]
        if n_results:
            min_frac = min(r["L_size"] / r["W_size"] for r in n_results)
            max_frac = max(r["L_size"] / r["W_size"] for r in n_results)
            min_case = min(n_results, key=lambda r: r["L_size"] / r["W_size"])
            print(f"  n={n_val}: min |L|/|W| = {min_frac:.4f} at j={min_case['j']}, "
                  f"max = {max_frac:.4f}")
        else:
            print(f"  n={n_val}: all witnesses liftable in all cases")

    # Key question
    print(f"\n{'='*70}")
    total = len(results)
    n_all_lift = len(all_liftable_cases)
    n_affine = len(affine_cases)
    n_non_affine = len(non_affine_cases)
    print(f"VERDICT: {total} (n,j) pairs analyzed")
    print(f"  {n_all_lift} all-liftable, {n_affine} affine, {n_non_affine} non-affine")
    if n_non_affine == 0:
        print("  LIFTABILITY IS ALWAYS AFFINE (or trivial) on the sensitivity coset.")
    else:
        print("  LIFTABILITY IS NOT ALWAYS AFFINE.")
        print("  The GF(2) linear invariant hypothesis is REFUTED.")
        print("  Liftability is a NONLINEAR function of the witness configuration.")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
