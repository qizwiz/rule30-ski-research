"""
adversarial_loop49.py — Loop 49: Attack the period table plateau claims

The paper states (sec:period-structure):
  m∈{10,12,14} all share period 64 = 2^6
  m∈{16,20,22} all share period 256 = 2^8

These plateaus are stated as facts with direct computation citations. We independently
verify each:
  1. Period P holds: F(n'+P, m) == F(n', m) for all n' in window starting at BASE=3087
  2. Period P/2 FAILS: there exists n' in same window where F(n'+P/2,m) != F(n',m)
  3. At least one SubcaseB event (F=0) exists within the claimed period

CORRECT F(n', m) definition (from CausalConeLemmas.lean):
  F(n', m) = (caEvolve n' (spikeAtList m (2*n'+1))).getD 0 false
           = cell at position n' in infinite-tape Rule30 evolution after n' steps
             from spike at position m (tape[m]=1, all other cells 0).

Efficient computation: run a large tape with spike at m, and at each step n',
record cell at position n'. This is the "diagonal" reading: we trace the single
cell at position (n', n') in the spacetime diagram.

Rule 30: caStep(l, c, r) = l XOR (c OR r) (with zero boundary conditions).
Tape size: 2*n_max + m + 20 suffices (light cone from spike at m to position n_max
after n_max steps is safely contained).
"""

import numpy as np
import time

# ──────────────────────────────────────────────────────────────────────────────
# Rule 30 simulation
# ──────────────────────────────────────────────────────────────────────────────

def rule30_step_np(tape):
    """One step of Rule 30. Zero-boundary (finite tape, no wrap)."""
    l = np.empty_like(tape); l[0] = 0; l[1:] = tape[:-1]
    r = np.empty_like(tape); r[-1] = 0; r[:-1] = tape[1:]
    return l ^ (tape | r)

def compute_F_sequence(m, n_max, extra=20):
    """
    Compute F(n', m) for n' = 0, 1, ..., n_max using the diagonal trick.

    F(n', m) = cell at position n' at step n' of Rule30 starting from spike at m.
    (Verified equivalent to caEvolve definition from CausalConeLemmas.lean)

    Tape size: n_max + m + extra (light cone from spike at m reaches at most
    m + n_max to the right after n_max steps, and n_max to the left; we only
    read positions 0..n_max so left boundary is fine since spike is at m >= 0).
    """
    L = n_max + m + extra
    tape = np.zeros(L, dtype=bool)
    tape[m] = True

    F = np.zeros(n_max + 1, dtype=bool)
    F[0] = tape[0]  # n'=0: read position 0 (= 0 since spike is at m, not 0)

    for step in range(1, n_max + 1):
        tape = rule30_step_np(tape)
        if step < L:
            F[step] = tape[step]   # diagonal: read position = step number

    return F

# ──────────────────────────────────────────────────────────────────────────────
# Verify F definition matches caEvolve (small test)
# ──────────────────────────────────────────────────────────────────────────────

def F_caEvolve_reference(n_prime, m):
    """Reference: correct caEvolve-based F(n',m) for verification."""
    def step(t):
        return [t[i-1] ^ (t[i] | t[i+1]) for i in range(1, len(t)-1)]
    t = [1 if k == m else 0 for k in range(2*n_prime + 1)]
    for _ in range(n_prime):
        t = step(t)
    return t[0] if t else 0

print("=" * 70)
print("VERIFICATION: diagonal trick matches caEvolve reference")
print("=" * 70)

for m_test in [4, 6, 10, 20]:
    F_diag = compute_F_sequence(m_test, 30)
    matches = all(
        int(F_diag[n]) == F_caEvolve_reference(n, m_test)
        for n in range(1, 25)
    )
    print(f"  m={m_test:2d}: diagonal == caEvolve for n=1..24: {'PASS' if matches else 'FAIL'}")
    if not matches:
        for n in range(1, 25):
            a = int(F_diag[n])
            b = F_caEvolve_reference(n, m_test)
            if a != b:
                print(f"    First mismatch at n={n}: diag={a}, caEvolve={b}")
                break
print()

# ──────────────────────────────────────────────────────────────────────────────
# Period verification function
# ──────────────────────────────────────────────────────────────────────────────

BASE = 3087  # paper's SubcaseB analysis base

def verify_period_exactly(m, claimed_period, window_reps=4):
    """
    Verify F(n', m) has EXACTLY period P starting from BASE.

    1. Compute F for n' in [0, BASE + window_reps * P]
    2. Check period P holds: F[BASE+k] == F[BASE+P+k] for k=0..P-1
    3. Check period 3 repetitions: also check vs F[BASE+2P+k]
    4. Check period P/2 FAILS: find k where F[BASE+k] != F[BASE+P//2+k]
    5. Count SubcaseB events (F=0) in [BASE, BASE+P)
    """
    P = claimed_period
    n_max = BASE + window_reps * P + 1

    t0 = time.time()
    F = compute_F_sequence(m, n_max)
    elapsed = time.time() - t0

    # 1. Period P holds over 3 repetitions
    period_holds = True
    first_fail_k = None
    for rep in range(1, 4):
        for k in range(P):
            if F[BASE + k] != F[BASE + rep*P + k]:
                period_holds = False
                first_fail_k = (rep, k)
                break
        if not period_holds:
            break

    # 2. Period P/2 fails (minimality)
    half_P = P // 2
    half_period_fails = False
    half_fail_witness = None
    for k in range(half_P):
        if F[BASE + k] != F[BASE + half_P + k]:
            half_period_fails = True
            half_fail_witness = (BASE + k, int(F[BASE + k]), BASE + half_P + k, int(F[BASE + half_P + k]))
            break

    # 3. SubcaseB events in [BASE, BASE+P)
    subcaseB_indices = [BASE + k for k in range(P) if not F[BASE + k]]
    subcaseB_count = len(subcaseB_indices)

    # 4. Distribution in first period
    ones = int(np.sum(F[BASE:BASE + P]))
    zeros = P - ones

    return {
        'm': m,
        'P': P,
        'period_holds': period_holds,
        'first_fail': first_fail_k,
        'half_period_fails': half_period_fails,
        'half_fail_witness': half_fail_witness,
        'subcaseB_count': subcaseB_count,
        'subcaseB_first_few': subcaseB_indices[:5],
        'zeros': zeros,
        'ones': ones,
        'elapsed': elapsed,
    }

# ──────────────────────────────────────────────────────────────────────────────
# Run verification
# ──────────────────────────────────────────────────────────────────────────────

print("=" * 70)
print("ADVERSARIAL LOOP 49: Period table plateau verification")
print(f"Base n': {BASE}")
print("=" * 70)

# Reference (non-plateau) cases
reference_cases = [(4, 8), (6, 16), (8, 32)]
# Plateau 1: m∈{10,12,14} → period 64
plateau1_cases = [(10, 64), (12, 64), (14, 64)]
# Plateau 2: m∈{16,20,22} → period 256
plateau2_cases = [(16, 256), (20, 256), (22, 256)]

all_cases = reference_cases + plateau1_cases + plateau2_cases

print("\nRunning simulations...")
results = {}
for m, P in all_cases:
    print(f"  m={m:2d}, P={P:4d}...", end='', flush=True)
    r = verify_period_exactly(m, P)
    results[(m, P)] = r
    status = "OK" if r['period_holds'] and r['half_period_fails'] else "ISSUE"
    print(f" {status} ({r['elapsed']:.1f}s)")

# ──────────────────────────────────────────────────────────────────────────────
# Results table
# ──────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 70)
print("RESULTS TABLE")
print("=" * 70)
print(f"{'m':>4}  {'P':>5}  {'P holds?':>10}  {'P/2 fails?':>11}  {'SubcaseB':>10}  {'0s/1s in P':>12}")
print("-" * 70)

for group_name, cases in [("Reference (non-plateau)", reference_cases),
                           ("Plateau 1: m∈{10,12,14}", plateau1_cases),
                           ("Plateau 2: m∈{16,20,22}", plateau2_cases)]:
    print(f"  [{group_name}]")
    for m, P in cases:
        r = results[(m, P)]
        p_str = "YES" if r['period_holds'] else "FAIL"
        h_str = "YES" if r['half_period_fails'] else "FAIL"
        sb = r['subcaseB_count']
        sb_str = f"{sb} ({'OK' if sb > 0 else 'ZERO!'})"
        ratio = f"{r['zeros']}/{r['ones']}"
        print(f"{m:>4}  {P:>5}  {p_str:>10}  {h_str:>11}  {sb_str:>10}  {ratio:>12}")

# ──────────────────────────────────────────────────────────────────────────────
# Detailed findings
# ──────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 70)
print("DETAILED FINDINGS")
print("=" * 70)

for m, P in all_cases:
    r = results[(m, P)]
    print(f"\n--- m={m}, claimed period={P} ---")

    if r['period_holds']:
        print(f"  [PASS] Period {P} holds over 3 repetitions from n'={BASE}")
    else:
        rep, k = r['first_fail']
        print(f"  [FAIL] Period {P} does NOT hold!")
        print(f"         First failure: rep={rep}, k={k}, n'={BASE+k}")
        print(f"         F[{BASE+k}]={int(results[(m,P)]['m'])} vs F[{BASE+rep*P+k}]")

    if r['half_period_fails']:
        w = r['half_fail_witness']
        print(f"  [PASS] Period {P//2} FAILS (period is minimal):")
        print(f"         F[{w[0]}]={w[1]} != F[{w[2]}]={w[3]}")
    else:
        print(f"  [FAIL] Period {P//2} ALSO HOLDS — period is NOT minimal!")

    sb = r['subcaseB_count']
    if sb > 0:
        print(f"  [PASS] SubcaseB events (F=0) in [{BASE}, {BASE+P}): count={sb}")
        print(f"         First few n': {r['subcaseB_first_few']}")
    else:
        print(f"  [FAIL] NO SubcaseB events in [{BASE}, {BASE+P}) — no witnesses!")

    print(f"  Distribution: {r['zeros']} zeros, {r['ones']} ones in first period")

# ──────────────────────────────────────────────────────────────────────────────
# Plateau consistency: are the F-sequences for same-plateau m values the SAME?
# ──────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 70)
print("PLATEAU CONSISTENCY: Are F-sequences identical within each plateau?")
print("=" * 70)

print("\nGroup 1 (period=64): m∈{10,12,14}")
n_max_g1 = BASE + 2*64
seqs_g1 = {m: compute_F_sequence(m, n_max_g1)[BASE:BASE+64] for m in [10,12,14]}
for i, m1 in enumerate([10,12,14]):
    for m2 in [10,12,14][i+1:]:
        same = np.all(seqs_g1[m1] == seqs_g1[m2])
        print(f"  F[{BASE}..{BASE+64}] for m={m1} vs m={m2}: {'IDENTICAL' if same else 'DIFFERENT'}", end='')
        if not same:
            diff_k = np.where(seqs_g1[m1] != seqs_g1[m2])[0][0]
            print(f" (first diff at offset {diff_k}: m={m1}→{int(seqs_g1[m1][diff_k])}, m={m2}→{int(seqs_g1[m2][diff_k])})", end='')
        print()

print("\nGroup 2 (period=256): m∈{16,20,22}")
n_max_g2 = BASE + 2*256
seqs_g2 = {m: compute_F_sequence(m, n_max_g2)[BASE:BASE+256] for m in [16,20,22]}
for i, m1 in enumerate([16,20,22]):
    for m2 in [16,20,22][i+1:]:
        same = np.all(seqs_g2[m1] == seqs_g2[m2])
        print(f"  F[{BASE}..{BASE+256}] for m={m1} vs m={m2}: {'IDENTICAL' if same else 'DIFFERENT'}", end='')
        if not same:
            diff_k = np.where(seqs_g2[m1] != seqs_g2[m2])[0][0]
            print(f" (first diff at offset {diff_k}: m={m1}→{int(seqs_g2[m1][diff_k])}, m={m2}→{int(seqs_g2[m2][diff_k])})", end='')
        print()

# ──────────────────────────────────────────────────────────────────────────────
# Overall verdict
# ──────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 70)
print("ADVERSARIAL VERDICT")
print("=" * 70)

def group_pass(cases):
    return all(
        results[(m, P)]['period_holds'] and
        results[(m, P)]['half_period_fails'] and
        results[(m, P)]['subcaseB_count'] > 0
        for m, P in cases
    )

ref_ok = group_pass(reference_cases)
plt1_ok = group_pass(plateau1_cases)
plt2_ok = group_pass(plateau2_cases)

print(f"\nReference (m=4→8, m=6→16, m=8→32):          {'ALL CONFIRMED' if ref_ok else 'FAILURES'}")
print(f"Plateau 1 (m∈{{10,12,14}} → period 64):       {'ALL CONFIRMED' if plt1_ok else 'FAILURES'}")
print(f"Plateau 2 (m∈{{16,20,22}} → period 256):      {'ALL CONFIRMED' if plt2_ok else 'FAILURES'}")

if plt1_ok and plt2_ok and ref_ok:
    print("\nOVERALL: All period-plateau claims INDEPENDENTLY CONFIRMED.")
    print("  - Period P holds (3 repetitions) from n'=3087 for every m")
    print("  - Period P/2 fails (minimality) for every m")
    print("  - SubcaseB events (F=0) exist in [BASE, BASE+P) for every active m")
    print()
    # Note on plateau identity
    g1_same = all(np.all(seqs_g1[10] == seqs_g1[m]) for m in [12,14])
    g2_same = all(np.all(seqs_g2[16] == seqs_g2[m]) for m in [20,22])
    print(f"  NOTE: Within plateau 1, all F-sequences are {'IDENTICAL' if g1_same else 'DIFFERENT'}")
    print(f"  NOTE: Within plateau 2, all F-sequences are {'IDENTICAL' if g2_same else 'DIFFERENT'}")
    if not g1_same or not g2_same:
        print("  → Each m has the same PERIOD but a different F-SEQUENCE pattern (expected)")
        print("    The paper claims only shared period, not identical sequences.")
    print()
    print("ADVERSARIAL CONCLUSION:")
    print("  The plateau claims are arithmetically correct and independently verified.")
    print("  No errors found in the period table for m < 24.")
else:
    print("\nOVERALL: FAILURES FOUND — investigate above for details.")

print()
print("Script: adversarial_loop49.py")
print(f"Date: 2026-03-24")
print(f"Base n': {BASE}")
print("Method: diagonal trick (spike at m, read position n' at step n')")
print("        verified equivalent to caEvolve definition from CausalConeLemmas.lean")
