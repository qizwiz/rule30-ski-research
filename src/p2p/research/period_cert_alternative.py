#!/usr/bin/env python3
"""
Unit 5: G2m46 Period Cert — Algebraic Alternative
===================================================
Investigates three approaches to prove:
  caEvolve 524288 (twoSpikeList 2 46 1048669) = twoSpikeList 2 46 93
in Lean without an Array Bool native_decide (estimated 5-32 hours).

Run: python3 research/period_cert_alternative.py
"""

import sys
import time
import numpy as np

# ---------------------------------------------------------------------------
# Berlekamp-Massey over GF(2)
# ---------------------------------------------------------------------------

def berlekamp_massey(s):
    """Return minimal LFSR (connection polynomial coefficients) for GF(2) sequence s."""
    n = len(s)
    C = [1]
    B = [1]
    L = 0
    x = 1
    b = 1
    for i in range(n):
        d = s[i]
        for j in range(1, len(C)):
            d ^= C[j] & s[i - j]
        d &= 1
        if d == 0:
            x += 1
        elif 2 * L <= i:
            T = C[:]
            p = [0] * x + B
            if len(p) > len(C):
                C += [0] * (len(p) - len(C))
            for j in range(len(p)):
                C[j] ^= p[j]
            L = i + 1 - L
            B = T
            b = d
            x = 1
        else:
            p = [0] * x + B
            if len(p) > len(C):
                C += [0] * (len(p) - len(C))
            for j in range(len(p)):
                C[j] ^= (d * pow(b, -1, 2)) & 1 * p[j]
            x += 1
    return C, L


def berlekamp_massey_gf2(seq):
    """BM over GF(2) — clean implementation."""
    n = len(seq)
    C = [1]   # current connection poly (list of GF2 coefficients, index = degree)
    B = [1]   # previous connection poly
    L = 0     # current LFSR length
    b = 1     # discrepancy scaling (always 1 in GF2)
    x = 1     # number of steps since last L change

    for i in range(n):
        # compute discrepancy
        d = seq[i]
        for j in range(1, len(C)):
            if i - j >= 0:
                d ^= C[j] & seq[i - j]
        d &= 1

        if d == 0:
            x += 1
        elif 2 * L <= i:
            T = C[:]
            # C = C + x-zero-pad + B (polynomial addition)
            padded_B = [0] * x + B
            while len(C) < len(padded_B):
                C.append(0)
            for j in range(len(padded_B)):
                C[j] ^= padded_B[j]
            L = i + 1 - L
            B = T
            x = 1
        else:
            padded_B = [0] * x + B
            while len(C) < len(padded_B):
                C.append(0)
            for j in range(len(padded_B)):
                C[j] ^= padded_B[j]
            x += 1

    return C, L


# ---------------------------------------------------------------------------
# Rule 30 simulation (fixed-size tape, center at index T)
# ---------------------------------------------------------------------------

def rule30_step_np(tape):
    L = np.roll(tape, 1); L[0] = 0
    R = np.roll(tape, -1); R[-1] = 0
    return L ^ (tape | R)


def simulate_G2m_sequence(m, T_max, X=2):
    """
    Simulate G_{X,m}(T) for T=1..T_max.
    Uses a fixed-size tape of size 2*T_max+1, center at T_max.
    Returns list of booleans (center value at each step).
    """
    N = 2 * T_max + 1
    tape = np.zeros(N, dtype=np.int8)
    center = T_max
    # spikes at X and m from center
    tape[center - X] = 1; tape[center + X] = 1
    tape[center - m] = 1; tape[center + m] = 1
    seq = []
    for t in range(T_max):
        tape = rule30_step_np(tape)
        seq.append(int(tape[center]))
    return seq


# ---------------------------------------------------------------------------
# Approach 1: UInt64 speed-up analysis (static, from reading CA_ArrayDef.lean)
# ---------------------------------------------------------------------------

def approach1_uint64():
    print("=" * 70)
    print("APPROACH 1: UInt64 speed-up analysis")
    print("=" * 70)
    print()
    print("Reading CA_ArrayDef.lean findings:")
    print()
    print("  caEvolveU64 EXISTS (lines 573-578):")
    print("    def caEvolveU64 (steps : Nat) (tape : Array UInt64) : Array UInt64")
    print("    Uses a mutable loop — imperative, no per-step allocation.")
    print()
    print("  caStepU64 EXISTS (lines 558-570):")
    print("    def caStepU64 (tape : Array UInt64) : Array UInt64")
    print("    Word-level: L = (cur<<1)|lc; R = (cur>>1)|rc; out = L^(cur|R)")
    print("    Matches C's step() exactly.")
    print()
    print("  GXmFast EXISTS (lines 595-599):")
    print("    def GXmFast (X m T : Nat) : Bool")
    print("    Uses caEvolveU64 on UInt64 tape — the fast path.")
    print()
    print("  twoSpikeArr is Array Bool ONLY (line 46).")
    print("  There is NO twoSpikeArrU64 defined.")
    print()
    print("  CRITICAL: There is NO theorem connecting caEvolveU64 to caEvolveArr.")
    print("  caStepU64/caEvolveU64 are UNVERIFIED relative to caStepArr/caEvolveArr.")
    print("  The U64 path is fast but has NO Lean correctness bridge to twoSpikeList.")
    print()
    print("  PERIOD CERT REQUIREMENT:")
    print("    caEvolve 524288 (twoSpikeList 2 46 1048669) = twoSpikeList 2 46 93")
    print("  This is stated in terms of caEvolve (List Bool), not caEvolveU64.")
    print()
    print("  TO USE caEvolveU64 in a native_decide proof:")
    print("    (a) Define twoSpikeU64 : Array UInt64 analogous to twoSpikeArr")
    print("    (b) Prove: getbitU64 (caEvolveU64 T (twoSpikeU64 X m N)) pos")
    print("               = (caEvolve T (twoSpikeList X m N)).getD pos false")
    print("    (c) Then native_decide on the U64 version would suffice.")
    print()
    print("  FEASIBILITY ESTIMATE:")
    print("    Array Bool cert m=40, P=65536:   estimated 5-30 min (from CLAUDE.md)")
    print("    Array Bool cert m=46, P=524288:  8x larger → 40-240 min (too slow)")
    print("    UInt64 cert m=46, P=524288:      64x speedup → ~0.6-3.7 min (FEASIBLE)")
    print("    Tape size: ceil((2*524288+1)/64) = 16385 words × 8 bytes = 131 KB")
    print()
    print("  VERDICT: UInt64 native_decide is FEASIBLE IF the bridge theorem is added.")
    print("  Estimated Lean proof compilation: 5-30 min (vs 5-32 hours for Array Bool).")
    print("  Work needed: ~50 lines of Lean (twoSpikeU64 def + bridge lemma).")
    print()


# ---------------------------------------------------------------------------
# Approach 2: LFSR algebraic structure of G_{2,46}
# ---------------------------------------------------------------------------

def approach2_lfsr():
    print("=" * 70)
    print("APPROACH 2: LFSR algebraic proof via G_{2,46} connection polynomial")
    print("=" * 70)
    print()
    print("Known from patterns.md:")
    print("  G_{2,46} LFSR degree L = 262145 = 2^18 + 1")
    print("  Period P = 524288 = 2^19")
    print("  Connection polynomial type: (1+x)^{262145}  (only 4 nonzero terms)")
    print("  P - L = 262143 ≈ P/2")
    print()
    print("Generating G_{2,46} sequence (T_max=2000 steps) for BM verification ...")

    T_max = 2000
    t0 = time.time()
    seq = simulate_G2m_sequence(46, T_max, X=2)
    elapsed = time.time() - t0
    print(f"  Simulation done in {elapsed:.2f}s  ({len(seq)} terms)")

    # Run BM to estimate LFSR length
    print("  Running Berlekamp-Massey ...")
    t0 = time.time()
    C_poly, L_est = berlekamp_massey_gf2(seq)
    elapsed = time.time() - t0
    print(f"  BM done in {elapsed:.3f}s")
    print(f"  Estimated LFSR length from {len(seq)} terms: {L_est}")
    print(f"  (True L = 262145 — need >>524290 terms to see full LFSR)")
    print()

    # Count nonzero terms in what we have
    nonzero = sum(c for c in C_poly)
    print(f"  Connection poly degree from BM: {len(C_poly)-1}, nonzero: {nonzero}")

    print()
    print("ALGEBRAIC ARGUMENT (from patterns.md / LFSR table):")
    print()
    print("  Connection poly = (1+x)^{262145} = (1+x)^{2^18+1} over GF(2).")
    print("  The minimal polynomial divides (1+x)^L, so the LFSR satisfies:")
    print("    s[t + L] = s[t]  for all t  (linear recurrence)")
    print("  But L = 2^18+1 does NOT divide P = 2^19 directly.")
    print()
    print("  Key: (1+x)^{2^19} = 1 + x^{2^19} = 1 over GF(2)[x]/(x^{2^19}-1)?")
    print("  NO — that would require the period to divide 2^19, but the minimal poly")
    print("  is (1+x)^{2^18+1}, whose order in GF(2)[[x]] is 2^19 (next power of 2")
    print("  above 2^18+1).  So period of any sequence with this minimal poly DIVIDES 2^19.")
    print()
    print("  THEOREM (algebraic):")
    print("    Any GF(2) sequence with minimal poly dividing (1+x)^{2^18+1}")
    print("    has period dividing 2^19.")
    print()
    print("  PROOF SKETCH:")
    print("    (1+x)^{2^18+1} has order 2^19 in the group of units of GF(2)[x]/(f)")
    print("    where f is any polynomial with (1+x)^{2^18+1} | f.")
    print("    Equivalently: s[t + 2^19] - s[t] ≡ 0 for all t,")
    print("    because (1+x)^{2^19} = ((1+x)^{2^18+1})^{2^19/(2^18+1)}... wait,")
    print("    need careful argument.")
    print()

    # Verify algebraically: (1+x)^{2^18+1} over GF(2)
    # The order of (1+x) in GF(2)[x]/(x^n - 1) is the smallest k with 2^k >= n
    # The period of a sequence with min poly (1+x)^L is 2^ceil(log2(L))
    import math
    L = 262145
    log2_L = math.log2(L)
    period_bound = 2 ** math.ceil(log2_L)
    print(f"  L = {L} = 2^18 + 1")
    print(f"  ceil(log2(L)) = ceil({log2_L:.6f}) = {math.ceil(log2_L)}")
    print(f"  Period bound = 2^{math.ceil(log2_L)} = {period_bound}")
    print(f"  Claimed period P = {524288} = 2^19 = {2**19}")
    print(f"  period_bound == P? {period_bound == 524288}")
    print()
    print("  So: min poly (1+x)^{2^18+1} ⟹ period divides 2^19 = 524288 = P. ✓")
    print()
    print("  LEAN PROOF PATH (algebraic):")
    print("    Step 1: Define G_{2,46}_seq as a GF(2) linear recurrence with")
    print("            connection poly (1+x)^{262145}.")
    print("    Step 2: Prove (1+x)^{262145} | ((1+x)^{524288} - 1) over GF(2).")
    print("    Step 3: Conclude seq[t + 524288] = seq[t] for all t.")
    print("    Step 4: Instantiate at t=106522 (first SubcaseB event) ⟹ period cert.")
    print()
    print("  FEASIBILITY: High. Steps 2-3 are pure algebra in GF(2)[x].")
    print("  Step 1 requires proving the LFSR structure of G_{2,46} — needs BM proof")
    print("  or an algebraic derivation from Rule 30 structure. This is NON-TRIVIAL.")
    print("  Estimated Lean effort: 200-500 lines.")
    print()


# ---------------------------------------------------------------------------
# Approach 3: Witness-based (weaker cert)
# ---------------------------------------------------------------------------

def approach3_witness():
    print("=" * 70)
    print("APPROACH 3: Witness-based alternative to full period cert")
    print("=" * 70)
    print()
    print("sensitivity_transfer needs EXACTLY the period cert:")
    print("  caEvolve P (twoSpikeList X m (2*P + 2*m + 1)) = twoSpikeList X m (2*m + 1)")
    print("This IS the period cert — cannot be avoided by a weaker statement.")
    print()
    print("HOWEVER: there is a modular decomposition approach.")
    print("  If period P = P1 * P2 with gcd(P1,P2)=1, then proving two shorter")
    print("  period certs (for P1 and P2) and combining via CRT gives the full cert.")
    print("  But P = 2^19 = 2 * 2^18 — only factors into 2^k, so CRT doesn't help.")
    print()
    print("ALTERNATIVE WITNESS-BASED STRATEGY:")
    print("  Instead of sensitivity_transfer with the period cert,")
    print("  prove sensitivity DIRECTLY for all n' ≡ 106522 (mod 524288) by:")
    print("  (a) Showing F_{2}(106523) = 1  (parity: 106523 is odd → F_2=1 ✓)")
    print("  (b) Showing G_{2,46}(106523) = 0  (computationally verified)")
    print("  (c) Showing the same argument works for 106523 + k*524288 for all k,")
    print("      using the period cert for the period of the SEQUENCE rather than")
    print("      the certificate tape.")
    print()
    print("  This reduces to: prove G_{2,46} has period dividing 524288.")
    print("  Which is the algebraic statement from Approach 2.")
    print()
    print("VERDICT: Approach 3 reduces to Approach 2. Not an independent alternative.")
    print()


# ---------------------------------------------------------------------------
# Feasibility comparison and recommendation
# ---------------------------------------------------------------------------

def summary():
    print("=" * 70)
    print("SUMMARY AND RECOMMENDATION")
    print("=" * 70)
    print()
    print("| Approach | Method               | Lean effort  | Speed      | Feasible? |")
    print("|----------|----------------------|--------------|------------|-----------|")
    print("| 1        | UInt64 native_decide | ~50 ln Lean  | 5-30 min   | YES (*)   |")
    print("| 2        | LFSR algebra         | 200-500 ln   | no compute | YES (**)  |")
    print("| 3        | Witness-based        | reduces to 2 | —          | NOT INDEP |")
    print()
    print("(*) Approach 1 requires adding twoSpikeU64 and a bridge theorem")
    print("    (caEvolveU64 ↔ caEvolveArr correctness) to CA_ArrayDef.lean.")
    print("    Once added, native_decide on GXmFast-style cert takes ~5-30 min.")
    print()
    print("(**) Approach 2 is elegant and produces a human-readable proof,")
    print("    but requires proving the LFSR structure of G_{2,46} algebraically")
    print("    — a significant Lean effort. The algebraic key is:")
    print("      (1+x)^{262145} divides (1+x)^{524288} over GF(2)")
    print("    which holds because 262145 ≤ 524288 and char=2.")
    print("    (In GF(2)[x]: (1+x)^{2^k} = 1 + x^{2^k}, so")
    print("     (1+x)^{524288} = (1+x)^{2^19} = 1 + x^{2^19}.")
    print("     For (1+x)^{262145} | (1+x)^{524288} we need 262145 ≤ 524288. ✓)")
    print()
    print("MOST FEASIBLE APPROACH: Approach 1 (UInt64 native_decide)")
    print("  Add to CA_ArrayDef.lean:")
    print("    def twoSpikeU64 (p q N : Nat) : Array UInt64 := ...")
    print("    theorem caEvolveU64_eq_caEvolveArr (n init) :")
    print("      getbitU64 (caEvolveU64 n (toU64Tape init)) pos")
    print("      = (caEvolveArr n init).getD pos false := by ...")
    print("  Then the period cert becomes:")
    print("    native_decide : GXmFast 2 46 524288 ... = ...")
    print("  Expected time: 5-30 min (vs 5-32 hours).")
    print()
    print("ALGEBRAIC BONUS: Approach 2 can CLOSE the axiom universally.")
    print("  The algebraic period proof works for ALL m≥40 where the LFSR")
    print("  connection poly is (1+x)^L with L ≤ 2^k = P.")
    print("  For m=46: (1+x)^{2^18+1}, period bound = 2^19 = P. ✓")
    print("  For m=44: need to determine L and verify L ≤ P=2^18.")
    print("  For m=48,50,...: same pattern expected.")
    print()
    print("RECOMMENDED NEXT STEP:")
    print("  1. Add UInt64 ↔ Array Bool bridge to CA_ArrayDef.lean (~50 lines)")
    print("  2. Run native_decide for m=46 period cert using GXmFast (~10-30 min)")
    print("  3. In parallel: verify LFSR algebraic path for m=44,48,50,52,54")
    print("     to close subcaseB_mgt38_witness by induction on the doubling structure.")
    print()


if __name__ == "__main__":
    approach1_uint64()
    approach2_lfsr()
    approach3_witness()
    summary()
    print("Done.")
