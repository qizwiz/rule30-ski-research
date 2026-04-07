#!/usr/bin/env python3
"""
Linearity Corridor Analysis for Rule 30 AllEssential shadow regions.

Investigates whether the caEvolve_flip0 lemma (and its right-boundary mirror)
can close shadow positions in the AllEssential induction proof.

caEvolve_flip0 says: if two tapes of length 2T+1 differ ONLY at position 0,
then after T steps of Rule 30 evolution their center outputs differ.
Algebraic reason: rule30Local(!a, b, c) = !rule30Local(a, b, c) since
rule30Local(a,b,c) = a XOR (b OR c), so the flip propagates up the left edge.

Questions answered:
1. Computational verification of caEvolve_flip0
2. Does a right-boundary mirror (caEvolve_flip_last) hold?
3. For each shadow (n,j): can a 1-step reduction to a boundary flip close it?
4. More generally: for each shadow, does ANY config witness essentiality via
   boundary propagation after some number of steps?
"""

import random
from collections import defaultdict

# ---------- Rule 30 core ----------

def rule30_local(a, b, c):
    return a ^ (b | c)

def rule30_step(tape):
    """One step: tape of length L -> tape of length L-2."""
    return [rule30_local(tape[i], tape[i+1], tape[i+2]) for i in range(len(tape) - 2)]

def rule30_center(T, config):
    """Evolve config (length 2T+1) for T steps, return the single remaining cell."""
    tape = list(config)
    for _ in range(T):
        tape = rule30_step(tape)
    assert len(tape) == 1
    return tape[0]

def flip_at(config, j):
    c = list(config)
    c[j] ^= 1
    return c

# ---------- dChain computation ----------

def compute_dchain(max_t, max_k):
    dc = [[False] * (max_k + 1) for _ in range(max_t + 1)]
    for t in range(max_t + 1):
        dc[t][0] = True
    for t in range(max_t):
        if max_k >= 1:
            dc[t+1][1] = rule30_local(dc[t][1], True, False)
        for k in range(max_k - 1):
            dc[t+1][k+2] = rule30_local(dc[t][k+2], dc[t][k+1], dc[t][k])
    return dc

def find_shadows(dc, max_n):
    shadows = []
    for n in range(max_n + 1):
        for j in range(1, 2*n + 2):
            if j < len(dc[0]) and n+1 < len(dc) and n < len(dc):
                if not dc[n+1][j] and not dc[n][j]:
                    shadows.append((n, j))
    return shadows

# ---------- Part 1: Verify caEvolve_flip0 ----------

def verify_flip0(max_T=14):
    """Verify: flipping position 0 always flips the center output.
    For T in 1..max_T, exhaustively check all 2^(2T) agreement patterns."""
    print("=" * 80)
    print("PART 1: Verify caEvolve_flip0")
    print("=" * 80)

    for T in range(1, max_T + 1):
        L = 2 * T + 1
        # positions 1..2T are shared (2T bits), position 0 differs
        n_shared = 2 * T
        violations = 0
        total = 0

        if n_shared > 20:
            print(f"  T={T:2d}: SKIPPED (2^{n_shared} configs too large)")
            continue

        for bits in range(1 << n_shared):
            shared = [(bits >> i) & 1 for i in range(n_shared)]
            l1 = [0] + shared
            l2 = [1] + shared

            c1 = rule30_center(T, l1)
            c2 = rule30_center(T, l2)
            if c1 == c2:
                violations += 1
            total += 1

        status = "PASS" if violations == 0 else f"FAIL ({violations}/{total})"
        print(f"  T={T:2d}: checked {total:8d} pairs -> {status}")

    print()

# ---------- Part 2: Verify caEvolve_flip_last (right boundary mirror) ----------

def verify_flip_last(max_T=14):
    """Verify: flipping the LAST position (2T) always flips the center output.
    rule30_local(a, b, !c) vs rule30_local(a, b, c):
    = a XOR (b OR !c) vs a XOR (b OR c)
    These are NOT generally equal, so this should FAIL."""
    print("=" * 80)
    print("PART 2: Verify caEvolve_flip_last (right boundary mirror)")
    print("=" * 80)

    for T in range(1, max_T + 1):
        L = 2 * T + 1
        n_shared = 2 * T  # positions 0..2T-1
        violations = 0
        total = 0

        if n_shared > 20:
            print(f"  T={T:2d}: SKIPPED (2^{n_shared} configs too large)")
            continue

        for bits in range(1 << n_shared):
            shared = [(bits >> i) & 1 for i in range(n_shared)]
            l1 = shared + [0]
            l2 = shared + [1]

            c1 = rule30_center(T, l1)
            c2 = rule30_center(T, l2)
            if c1 == c2:
                violations += 1
            total += 1

        pct = 100.0 * violations / total if total > 0 else 0
        status = "PASS (always flips)" if violations == 0 else f"FAIL ({violations}/{total} = {pct:.1f}% same)"
        print(f"  T={T:2d}: checked {total:8d} pairs -> {status}")

    print()

# ---------- Part 3: 1-step boundary reduction for shadows ----------

def check_1step_boundary_reduction(shadows, max_n_for_exhaustive=12):
    """For each shadow (n,j): can flipping position j in a tape cause the
    1-step evolution to differ ONLY at position 0 (or only at position 2n)?

    If so, caEvolve_flip0 (or its mirror) closes the remaining n steps.

    After 1 step of Rule 30, a tape of length 2(n+1)+1 becomes length 2(n+1)-1 = 2n+1.
    For the flip at position j in the original to produce a flip ONLY at position 0
    of the evolved tape: we need caStep(A)[0] != caStep(B)[0] and
    caStep(A)[i] == caStep(B)[i] for all i in 1..2n.

    Position 0 of evolved tape = rule30(A[0], A[1], A[2]).
    Position i of evolved tape = rule30(A[i], A[i+1], A[i+2]).

    Flipping A[j] affects positions max(0,j-2)..min(2n, j) of the evolved tape.
    So for the difference to be confined to position 0, we need j <= 2.
    For position 2n (last), we need j >= 2n.
    """
    print("=" * 80)
    print("PART 3: 1-step boundary reduction for shadows")
    print("=" * 80)

    # Geometric analysis first
    print("\nGeometric analysis:")
    print("  Flipping position j in original tape affects evolved positions max(0,j-2)..min(2n, j).")
    print("  For left-boundary-only effect (pos 0): need j <= 2 AND no effect at pos 1,2")
    print("  For right-boundary-only effect (pos 2n): need j >= 2n AND no effect at pos 2n-1, 2n-2")
    print()

    left_viable = 0
    right_viable = 0
    neither = 0

    for n, j in shadows:
        T = n + 1
        L = 2 * T + 1  # = 2n+3
        evolved_len = L - 2  # = 2n+1

        # Positions affected in evolved tape by flipping position j
        affected_lo = max(0, j - 2)
        affected_hi = min(evolved_len - 1, j)

        can_left = (affected_lo == 0 and affected_hi == 0)  # only pos 0
        can_right = (affected_lo == evolved_len - 1 and affected_hi == evolved_len - 1)  # only last

        if can_left:
            left_viable += 1
        elif can_right:
            right_viable += 1
        else:
            neither += 1

    print(f"  Shadows reducible to LEFT boundary only (j=0): {left_viable}")
    print(f"  Shadows reducible to RIGHT boundary only (j=2n+2): {right_viable}")
    print(f"  Neither (j affects interior after 1 step): {neither}")
    print(f"  Total shadows: {len(shadows)}")
    print()

    # Now do exhaustive computational check for small n
    print("Exhaustive check: for each shadow (n,j), does ANY config A cause")
    print("  caStep(A) and caStep(flip(A,j)) to differ ONLY at boundary?")
    print()

    boundary_works = 0
    boundary_fails = 0

    for n, j in shadows:
        if n > max_n_for_exhaustive:
            continue

        T = n + 1
        L = 2 * T + 1
        evolved_len = L - 2

        found = False
        # Exhaustive over all configs (feasible for small n)
        if L <= 21:
            for bits in range(1 << L):
                A = [(bits >> i) & 1 for i in range(L)]
                B = flip_at(A, j)

                eA = rule30_step(A)
                eB = rule30_step(B)

                # Check: differ ONLY at position 0?
                if eA[0] != eB[0] and all(eA[i] == eB[i] for i in range(1, evolved_len)):
                    found = True
                    break

                # Check: differ ONLY at last position?
                if eA[-1] != eB[-1] and all(eA[i] == eB[i] for i in range(evolved_len - 1)):
                    found = True
                    break

        if found:
            boundary_works += 1
            tag = "YES-boundary"
        else:
            boundary_fails += 1
            tag = "NO-boundary"

        print(f"  (n={n:2d}, j={j:2d}): {tag}")

    print(f"\n  Boundary reduction works: {boundary_works}")
    print(f"  Boundary reduction fails: {boundary_fails}")
    print()

# ---------- Part 4: Multi-step boundary reduction ----------

def check_multistep_boundary(shadows, max_n=8):
    """For each shadow (n,j): after s steps (s=1,2,...), does the diff
    concentrate to position 0 (or last)?

    Uses sampling (not exhaustive) to find configs where the diff concentrates.
    """
    print("=" * 80)
    print("PART 4: Multi-step boundary concentration (sampled)")
    print("=" * 80)
    print()

    rng = random.Random(999)

    for n, j in shadows:
        if n > max_n:
            continue

        T = n + 1
        L = 2 * T + 1
        N_SAMPLES = min(5000, 1 << L)  # cap at 5000 samples

        results = []
        for s in range(1, T + 1):
            evolved_len = L - 2 * s
            if evolved_len < 1:
                break

            found_left = False
            found_right = False

            for trial in range(N_SAMPLES):
                if N_SAMPLES == (1 << L):
                    # Exhaustive
                    A = [(trial >> bi) & 1 for bi in range(L)]
                else:
                    A = [rng.randint(0, 1) for _ in range(L)]
                B = flip_at(A, j)

                tA, tB = list(A), list(B)
                for _ in range(s):
                    tA = rule30_step(tA)
                    tB = rule30_step(tB)

                if len(tA) < 1:
                    break

                # Differ only at position 0?
                if tA[0] != tB[0] and all(tA[i] == tB[i] for i in range(1, len(tA))):
                    found_left = True

                # Differ only at last?
                if tA[-1] != tB[-1] and all(tA[i] == tB[i] for i in range(len(tA) - 1)):
                    found_right = True

                if found_left and found_right:
                    break

            tag = ""
            if found_left:
                tag += "L"
            if found_right:
                tag += "R"
            if not tag:
                tag = "-"
            results.append(tag)

        print(f"  (n={n:2d}, j={j:2d}): steps 1..{len(results)}: {' '.join(results)}")

    print()

# ---------- Part 5: Direct essentiality check (ground truth) ----------

def check_essentiality_direct(shadows, max_n=30):
    """For each shadow (n,j), verify Essential(n+1, j) holds by finding ANY witness.
    This is ground truth: does position j matter at level n+1?"""
    print("=" * 80)
    print("PART 5: Direct essentiality ground truth")
    print("=" * 80)
    print()

    rng = random.Random(12345)

    essential_count = 0
    not_found = 0

    for n, j in shadows:
        if n > max_n:
            continue

        T = n + 1
        L = 2 * T + 1

        found = False
        # Try spike configs
        for p in range(L):
            config = [0] * L
            config[p] = 1
            if rule30_center(T, config) != rule30_center(T, flip_at(config, j)):
                found = True
                break

        if not found:
            # Try all-ones
            config = [1] * L
            if rule30_center(T, config) != rule30_center(T, flip_at(config, j)):
                found = True

        if not found:
            # Try random
            for _ in range(500):
                config = [rng.randint(0, 1) for _ in range(L)]
                if rule30_center(T, config) != rule30_center(T, flip_at(config, j)):
                    found = True
                    break

        if found:
            essential_count += 1
        else:
            not_found += 1
            print(f"  WARNING: Essential(n+1={T}, j={j}) NOT found!")

    checked = essential_count + not_found
    print(f"  Checked {checked} shadow pairs (n <= {max_n})")
    print(f"  Essential witness found: {essential_count}")
    print(f"  No witness found: {not_found}")
    print()

# ---------- Part 6: Diff propagation analysis ----------

def analyze_diff_propagation(shadows, max_n=12):
    """For each shadow, track how the diff from flipping position j spreads
    through Rule 30 evolution steps. Key question: does it ever concentrate
    to a single boundary position?"""
    print("=" * 80)
    print("PART 6: Diff propagation analysis")
    print("=" * 80)
    print()

    for n, j in shadows:
        if n > max_n:
            continue

        T = n + 1
        L = 2 * T + 1

        # Use all-zeros as base config (simplest case)
        A = [0] * L
        B = flip_at(A, j)

        tA, tB = list(A), list(B)
        diff_positions_by_step = []

        for s in range(T):
            diffs = [i for i in range(len(tA)) if tA[i] != tB[i]]
            diff_positions_by_step.append(diffs)
            tA = rule30_step(tA)
            tB = rule30_step(tB)

        # Final: single cell
        diffs_final = [i for i in range(len(tA)) if tA[i] != tB[i]]
        diff_positions_by_step.append(diffs_final)

        # Summarize: width of diff region at each step (exclude final single-cell)
        widths = [len(d) for d in diff_positions_by_step]
        intermediate_widths = widths[1:-1] if len(widths) > 2 else widths
        min_width = min(intermediate_widths) if intermediate_widths else 0

        # Does it ever hit width 1 at a boundary (excluding final cell)?
        boundary_hit = False
        for s, diffs in enumerate(diff_positions_by_step[:-1]):
            current_len = L - 2 * s
            if len(diffs) == 1 and (diffs[0] == 0 or diffs[0] == current_len - 1):
                boundary_hit = True
                break

        tag = "BOUNDARY-HIT" if boundary_hit else f"min_width={min_width}"
        print(f"  (n={n:2d}, j={j:2d}): widths={widths[:-1]}  {tag}")

    print()

# ---------- Main ----------

def main():
    MAX_N = 40
    MAX_T = MAX_N + 2
    MAX_K = 2 * (MAX_N + 1) + 2

    print("=" * 80)
    print("LINEARITY CORRIDOR ANALYSIS")
    print("Rule 30 AllEssential shadow regions vs caEvolve_flip0")
    print("=" * 80)
    print()

    # Compute dChain and shadows
    dc = compute_dchain(MAX_T, MAX_K)
    shadows = find_shadows(dc, MAX_N)
    print(f"Shadow (n,j) pairs for n=0..{MAX_N}: {len(shadows)} total")

    shadow_by_n = defaultdict(list)
    for n, j in shadows:
        shadow_by_n[n].append(j)
    print(f"Levels with shadows: {sorted(shadow_by_n.keys())[:20]}...")
    print()

    # Part 1: Verify caEvolve_flip0
    verify_flip0(max_T=10)

    # Part 2: Verify right-boundary mirror
    verify_flip_last(max_T=10)

    # Part 3: 1-step boundary reduction
    check_1step_boundary_reduction(shadows, max_n_for_exhaustive=8)

    # Part 4: Multi-step boundary concentration
    check_multistep_boundary(shadows, max_n=8)

    # Part 5: Ground truth essentiality
    check_essentiality_direct(shadows, max_n=MAX_N)

    # Part 6: Diff propagation
    analyze_diff_propagation(shadows, max_n=12)

    # ---------- CONCLUSIONS ----------
    print("=" * 80)
    print("CONCLUSIONS")
    print("=" * 80)
    print()
    print("caEvolve_flip0: flipping position 0 ALWAYS flips center (algebraic identity).")
    print("caEvolve_flip_last: flipping last position does NOT always flip center")
    print("  (rule30_local(a,b,!c) != !rule30_local(a,b,c) in general).")
    print()
    print("For shadow positions j > 0: a single flip at j affects evolved positions")
    print("  max(0,j-2)..min(2n,j), which spans up to 3 cells. This CANNOT reduce")
    print("  to a boundary-only flip in 1 step unless j <= 0 (left) or j >= 2n+2 (right).")
    print("  But shadow positions have 1 <= j <= 2n+1, so 1-step reduction NEVER works.")
    print()
    print("The linearity corridor (caEvolve_flip0) is a PROOF of Essential(n, 0) for all n,")
    print("  but it does NOT help with interior shadow positions j >= 1.")

if __name__ == "__main__":
    main()
