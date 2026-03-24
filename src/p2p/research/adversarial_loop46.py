"""
adversarial_loop46.py — Try to build a fast algorithm (REAL adversarial attack)

This is the most adversarial thing possible: try to DISPROVE the Omega(n) lower
bound by finding a fast algorithm to predict the Rule 30 center cell sequence.

Rule 30: rule30(l,c,r) = l XOR (c OR r)
s(n) = center cell at step n of Rule 30 starting from single spike at center.

Tests:
  1. Periodicity: is s(n) periodic with period P <= 10000?
  2. Bit-prediction: can s(n) be predicted from last K bits of n (K=1..20)?
  3. Modular: can s(n) be predicted from n mod P for small P in {2,4,...,1024}?
  4. Linear recurrence over GF(2): Berlekamp-Massey on the sequence.
  5. Summary: what is the shortest description found?
"""

import numpy as np
import sys
import time

N_TOTAL = 10000  # compute first N_TOTAL values of s(n)

# ---------------------------------------------------------------------------
# Generate the center cell sequence
# ---------------------------------------------------------------------------

def generate_center_sequence(n_total):
    """
    Compute s(0), s(1), ..., s(n_total-1) using a single tape simulation.
    Tape size: 2*n_total + 3 (large enough for all steps).
    """
    T = 2 * n_total + 3
    center = T // 2
    tape = np.zeros(T, dtype=np.uint8)
    tape[center] = 1  # single spike at center

    s = np.zeros(n_total, dtype=np.uint8)
    s[0] = tape[center]  # step 0

    l = np.empty(T, dtype=np.uint8)
    r = np.empty(T, dtype=np.uint8)

    for i in range(1, n_total):
        # Rule 30 step
        l[1:] = tape[:-1]; l[0] = 0
        r[:-1] = tape[1:]; r[-1] = 0
        np.bitwise_or(tape, r, out=r)
        np.bitwise_xor(l, r, out=tape)
        s[i] = tape[center]

    return s


# ---------------------------------------------------------------------------
# Test 1: Periodicity
# ---------------------------------------------------------------------------

def test_periodicity(s, max_period=None):
    """
    Check if s is periodic with period P for P in [1, min(len(s)//2, max_period)].
    Returns (is_periodic, period) or (False, None).
    """
    n = len(s)
    if max_period is None:
        max_period = n // 2

    print(f"\n[Test 1] Periodicity check (P up to {max_period})...")
    t0 = time.time()

    for P in range(1, max_period + 1):
        # Check if s[P:] == s[:n-P] (all elements match with period P)
        # More precisely: s[i] == s[i+P] for all valid i
        if np.all(s[:n - P] == s[P:]):
            elapsed = time.time() - t0
            print(f"  PERIODIC! Period P = {P} (found in {elapsed:.2f}s)")
            print(f"  => This would give O(1) prediction after O(n) precomputation.")
            return True, P

        # Fast early exit for obviously non-periodic: check a sample
        if P <= 100 or P % 1000 == 0:
            pass  # keep going

    elapsed = time.time() - t0
    print(f"  Not periodic for P in [1, {max_period}]. ({elapsed:.2f}s)")
    return False, None


# ---------------------------------------------------------------------------
# Test 2: Bit-prediction from last K bits of n
# ---------------------------------------------------------------------------

def test_bit_prediction(s, k_max=20):
    """
    For each K in [1..k_max], test if s(n) is determined by the last K bits of n.
    i.e., for all n, n': (n mod 2^K == n' mod 2^K) => s(n) == s(n').

    If true for some K, that's an O(1) lookup table of size 2^K.
    """
    n = len(s)
    print(f"\n[Test 2] Bit-prediction from last K bits (K=1..{k_max})...")
    t0 = time.time()

    best_K = None
    for K in range(1, k_max + 1):
        mod = 1 << K  # 2^K
        # For each residue r in [0, 2^K), collect s values
        consistent = True
        table = np.full(mod, 255, dtype=np.uint8)  # 255 = unset
        for idx in range(min(n, 8 * mod)):  # check at least 8 full cycles
            r = idx % mod
            if table[r] == 255:
                table[r] = s[idx]
            elif table[r] != s[idx]:
                consistent = False
                break
        if consistent and 255 not in table:
            elapsed = time.time() - t0
            print(f"  K={K}: CONSISTENT! s(n) depends only on n mod 2^{K} = n mod {mod}.")
            print(f"  => Lookup table of size {mod} suffices for all n.")
            best_K = K
            break
        else:
            pass  # not consistent

    elapsed = time.time() - t0
    if best_K is None:
        print(f"  No bit-prediction found for K in [1,{k_max}]. ({elapsed:.2f}s)")
        # Report: for each K, how many collisions?
        for K in [1, 4, 8, 12, 16, 20]:
            if K > k_max:
                break
            mod = 1 << K
            # Fraction of residue classes with consistent value
            table_0 = {}
            consistent_count = 0
            total_residues = min(mod, n)
            for idx in range(n):
                r = idx % mod
                if r not in table_0:
                    table_0[r] = s[idx]
                elif table_0[r] != s[idx]:
                    table_0[r] = -1  # inconsistent
            consistent_count = sum(1 for v in table_0.values() if v != -1)
            frac = consistent_count / len(table_0) if table_0 else 0
            print(f"  K={K} (mod {mod}): {consistent_count}/{len(table_0)} residues consistent ({frac:.1%})")
    return best_K


# ---------------------------------------------------------------------------
# Test 3: Modular prediction (n mod P for small P)
# ---------------------------------------------------------------------------

def test_modular_prediction(s, p_values=None):
    """
    For each P, test if s(n) is a function of n mod P alone.
    """
    if p_values is None:
        p_values = [2, 3, 4, 5, 6, 7, 8, 16, 32, 64, 128, 256, 512, 1024]

    n = len(s)
    print(f"\n[Test 3] Modular prediction (n mod P for P in {p_values})...")
    t0 = time.time()

    found = []
    for P in p_values:
        table = {}
        consistent = True
        for idx in range(n):
            r = idx % P
            if r not in table:
                table[r] = s[idx]
            elif table[r] != s[idx]:
                consistent = False
                break
        if consistent and len(table) == P:
            print(f"  P={P}: CONSISTENT! s(n) = f(n mod {P}).")
            found.append(P)
        else:
            # Report consistency fraction
            total = P
            consistent_r = sum(1 for r in range(P) if table.get(r, -1) != -1)
            # Actually count inconsistent ones
            incons = []
            table2 = {}
            for idx in range(n):
                r = idx % P
                if r not in table2:
                    table2[r] = s[idx]
                elif table2[r] != s[idx] and r not in incons:
                    incons.append(r)
            if P <= 8:
                print(f"  P={P}: {len(incons)}/{P} residues have inconsistency")

    elapsed = time.time() - t0
    if not found:
        print(f"  No modular period found in tested P values. ({elapsed:.2f}s)")
    return found


# ---------------------------------------------------------------------------
# Test 4: Linear recurrence over GF(2) (Berlekamp-Massey)
# ---------------------------------------------------------------------------

def berlekamp_massey_gf2(s):
    """
    Berlekamp-Massey algorithm over GF(2).
    Returns the shortest LFSR (length L, connection polynomial as list of 0/1).
    s: list or array of 0/1 values.
    """
    n = len(s)
    C = [1]  # connection polynomial (C[0]=1 always)
    B = [1]  # previous C
    L = 0    # current LFSR length
    m = 1    # number of steps since last length change
    b = 1    # discrepancy of B when last changed

    for i in range(n):
        # Compute discrepancy d
        d = s[i]
        for j in range(1, L + 1):
            if j < len(C):
                d ^= (C[j] * s[i - j]) & 1
        d &= 1

        if d == 0:
            m += 1
        elif 2 * L <= i:
            T = C[:]
            # C = C XOR (d/b) * x^m * B; in GF(2), d/b = d*b^{-1} = d (since b=1 always in GF(2))
            factor = d  # always 1 in GF(2)
            # Extend C if needed
            while len(C) < len(B) + m:
                C.append(0)
            for j in range(len(B)):
                C[j + m] ^= factor * B[j]
            L = i + 1 - L
            B = T
            b = d
            m = 1
        else:
            # Adjust C without changing L
            while len(C) < len(B) + m:
                C.append(0)
            factor = d  # in GF(2)
            for j in range(len(B)):
                C[j + m] ^= factor * B[j]
            m += 1

    return L, C


def test_linear_recurrence(s, max_len=None):
    """
    Apply Berlekamp-Massey to find the shortest LFSR over GF(2).
    If LFSR length L << len(s)/2, that's a compression.
    """
    n = len(s)
    print(f"\n[Test 4] Linear recurrence over GF(2) (Berlekamp-Massey)...")
    print(f"  Sequence length: {n}")
    t0 = time.time()

    s_list = s.tolist()
    L, C = berlekamp_massey_gf2(s_list)
    elapsed = time.time() - t0

    print(f"  LFSR length: L = {L} (elapsed: {elapsed:.2f}s)")
    print(f"  Connection polynomial degree: {len(C)-1}")

    if L < n // 2:
        print(f"  => Potential compression: L={L} << n/2={n//2}")
        print(f"  => If valid, s(n) is determined by initial L values + recurrence.")
        print(f"  => Prediction cost: O(L) per step, O(L^2) total for n steps.")
        # Verify the recurrence on the remaining data
        if L > 0:
            s_pred = list(s_list[:L])
            correct = 0
            for i in range(L, n):
                pred = 0
                for j in range(1, len(C)):
                    if j <= i and j < len(C):
                        pred ^= C[j] * s_pred[i - j]
                pred &= 1
                s_pred.append(pred)
                if pred == s_list[i]:
                    correct += 1
            accuracy = correct / (n - L)
            print(f"  Verification: {correct}/{n-L} correct ({accuracy:.4%})")
            if accuracy == 1.0:
                print(f"  PERFECT RECURRENCE VERIFIED!")
            else:
                print(f"  Recurrence does NOT hold — sequence is not L-linear in GF(2).")
                print(f"  (BM gives LFSR that fits first n/2, but not necessarily all of s)")
    else:
        # L >= n/2 means the sequence is essentially random (BM can't compress)
        compression_ratio = L / n
        print(f"  LFSR length L={L} >= n/2={n//2}. No useful compression.")
        print(f"  Compression ratio: {compression_ratio:.3f} (1.0 = no compression, 0.5 = random)")
        print(f"  => Consistent with sequence having high linear complexity (pseudo-random).")

    return L, C


# ---------------------------------------------------------------------------
# Test 5: Entropy and run-length statistics
# ---------------------------------------------------------------------------

def test_statistics(s):
    """Basic statistics to characterize the sequence."""
    n = len(s)
    ones = int(s.sum())
    zeros = n - ones
    print(f"\n[Test 5] Sequence statistics (n={n})...")
    print(f"  1s: {ones} ({ones/n:.4%}), 0s: {zeros} ({zeros/n:.4%})")

    # Run-length distribution
    runs = []
    cur_val = s[0]
    cur_len = 1
    for i in range(1, n):
        if s[i] == cur_val:
            cur_len += 1
        else:
            runs.append(cur_len)
            cur_val = s[i]
            cur_len = 1
    runs.append(cur_len)
    runs = np.array(runs)
    print(f"  Number of runs: {len(runs)}")
    print(f"  Run lengths: min={runs.min()}, max={runs.max()}, mean={runs.mean():.2f}, median={np.median(runs):.1f}")

    # Bit entropy estimate (pair frequencies)
    pairs = [(int(s[i]), int(s[i+1])) for i in range(n-1)]
    from collections import Counter
    pair_counts = Counter(pairs)
    print(f"  Pair counts: {dict(sorted(pair_counts.items()))}")

    # Check if sequence has obvious bias
    if abs(ones/n - 0.5) > 0.05:
        print(f"  NOTE: significant bias from 0.5 ({ones/n:.4f})")
    else:
        print(f"  Density close to 0.5 — consistent with pseudo-random behavior.")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("=" * 70)
    print("adversarial_loop46.py — Adversarial attack on Rule 30 center sequence")
    print("=" * 70)
    print(f"Rule 30: rule30(l,c,r) = l XOR (c OR r)")
    print(f"Generating s(0)..s({N_TOTAL-1}) (center cell sequence)...")
    t0 = time.time()
    s = generate_center_sequence(N_TOTAL)
    elapsed = time.time() - t0
    print(f"Generated {N_TOTAL} values in {elapsed:.2f}s")
    print(f"First 50 values: {s[:50].tolist()}")
    print(f"s(0)={s[0]}, s(1)={s[1]}, s(10)={s[10]}, s(100)={s[100]}, s(1000)={s[1000]}, s(9999)={s[9999]}")

    # --- Test 1: Periodicity ---
    is_periodic, period = test_periodicity(s, max_period=N_TOTAL // 2)

    # --- Test 2: Bit prediction ---
    best_K = test_bit_prediction(s, k_max=20)

    # --- Test 3: Modular prediction ---
    found_mods = test_modular_prediction(s)

    # --- Test 4: Berlekamp-Massey ---
    L, C = test_linear_recurrence(s)

    # --- Test 5: Statistics ---
    test_statistics(s)

    # --- Summary ---
    print()
    print("=" * 70)
    print("SUMMARY — Adversarial attack results")
    print("=" * 70)

    findings = []

    if is_periodic:
        findings.append(f"PERIODIC with period {period} — O(1) lookup after O(period) precomputation!")
    else:
        findings.append(f"NOT periodic for P <= {N_TOTAL//2}.")

    if best_K is not None:
        findings.append(f"BIT-PREDICTABLE from last {best_K} bits — O(1) lookup table of size {1<<best_K}!")
    else:
        findings.append("NOT bit-predictable from last K bits (K=1..20).")

    if found_mods:
        findings.append(f"MODULAR-PREDICTABLE for P in {found_mods}!")
    else:
        findings.append("NOT modular-predictable for tested P values.")

    compression_ratio = L / N_TOTAL
    if L < N_TOTAL // 4:
        findings.append(f"LINEAR RECURRENCE FOUND: LFSR length {L} << {N_TOTAL} — potential O(L) algorithm!")
    elif L < N_TOTAL // 2:
        findings.append(f"LFSR length {L} (ratio {compression_ratio:.3f}) — moderate compression, possibly random-like.")
    else:
        findings.append(f"LFSR length {L} ({compression_ratio:.3f} of N) — consistent with pseudo-random (no GF(2) compression).")

    print()
    for f in findings:
        print(f"  {f}")

    print()
    # Overall verdict
    any_shortcut = is_periodic or (best_K is not None) or bool(found_mods) or (L < N_TOTAL // 4)
    if any_shortcut:
        print("VERDICT: Potential shortcut(s) found — Omega(n) lower bound may be at risk!")
        print("Further investigation required.")
    else:
        print("VERDICT: No fast algorithm found. All tests consistent with Omega(n) complexity.")
        print("The sequence appears pseudo-random: no period, no bit-structure, no linear recurrence.")
        print("This SUPPORTS the paper's Omega(n) lower bound claim.")

    return {
        "is_periodic": is_periodic,
        "period": period,
        "best_K": best_K,
        "found_mods": found_mods,
        "lfsr_length": L,
        "n_total": N_TOTAL,
    }


if __name__ == "__main__":
    result = main()
    sys.exit(0)
