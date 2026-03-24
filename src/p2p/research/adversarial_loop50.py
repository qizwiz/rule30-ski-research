"""
adversarial_loop50.py — Loop 50: Fix simulation bug and re-verify period claims

CRITICAL BUG FOUND in loop 49:
- Used wrong simulation: spike at center-m (middle of tape), reading center each step
- Correct definition (Lean/paper): spike at absolute position m (near left edge),
  reading position n'+1 at step n' (the "moving center" / diagonal read)

Why these differ:
- Wrong: fixed tape, spike in middle, read fixed center → eventually corrupted by
  boundary reflections after n' > N - m steps
- Correct: spike near left edge, read diagonal → causal cone of position n'+1 at
  time n' covers [1, 2n'+1], NEVER includes left boundary (pos 0), so no boundary effects

This loop:
1. Verifies the corrected Lean definition matches F(n',2) = (n' even)
2. Verifies period 8 for m=4, period 64 for m∈{10,12,14}, period 256 for m∈{16,20,22}
3. Checks SubcaseB event density in each period at base n'=3087
"""

import numpy as np
import sys

# ──────────────────────────────────────────────────────────────────────────────
# Rule 30 core
# ──────────────────────────────────────────────────────────────────────────────

def rule30_step_np(tape):
    """One step of Rule 30 with zero boundary."""
    l = np.roll(tape, 1); l[0] = 0
    c = tape
    r = np.roll(tape, -1); r[-1] = 0
    return l ^ (c | r)

def simulate_F_all(m, n_max):
    """
    Compute F(n', m) for n' = 0, 1, ..., n_max using diagonal-read method.

    Correct Lean/paper definition:
    - tape[m] = 1, all else 0
    - At step n', read position n'+1 (the 'center' of a tape of size 2n'+3)

    Uses ONE large fixed tape. Valid because: the causal cone of position n'+1
    at time n' covers columns [1, 2n'+1], which never includes column 0 (left
    boundary), so the boundary condition at -1 (= 0) is irrelevant.

    Tape size: 2*n_max + m + 20 (the rightward cone from spike at m reaches
    m + n_max after n_max steps, and we need to read position n_max+1).
    """
    tape_len = 2 * n_max + m + 20
    tape = np.zeros(tape_len, dtype=bool)
    tape[m] = True  # spike at absolute position m (near left edge)

    F_seq = np.zeros(n_max + 1, dtype=bool)
    # F(n', m) = tape[n'+1] after n'+1 steps (step first, then read)
    for n_prime in range(n_max + 1):
        tape = rule30_step_np(tape)   # apply step n'+1
        pos = n_prime + 1
        if pos < tape_len:
            F_seq[n_prime] = tape[pos]
        else:
            print(f"WARNING: tape too small at n'={n_prime}", file=sys.stderr)

    return F_seq

# ──────────────────────────────────────────────────────────────────────────────
# Period verification
# ──────────────────────────────────────────────────────────────────────────────

BASE = 3087

def verify_period(m, claimed_period, n_reps=4):
    """
    Verify F(n', m) has EXACTLY claimed_period starting at n'=BASE.

    Checks:
    1. Period P holds over n_reps complete repetitions
    2. Period P/2 fails (minimality)
    3. SubcaseB events (F=0) exist within one period
    """
    P = claimed_period
    n_max = BASE + (n_reps + 1) * P + 2

    print(f"\n  Computing m={m}, P={P}, n_max={n_max} ...", flush=True)
    F = simulate_F_all(m, n_max)

    # 1. Period P holds over n_reps reps
    period_holds = True
    first_fail_k = None
    for rep in range(1, n_reps + 1):
        for k in range(P):
            i1 = BASE + k
            i2 = BASE + rep * P + k
            if i2 < len(F) and F[i1] != F[i2]:
                period_holds = False
                first_fail_k = (rep, k, i1, int(F[i1]), i2, int(F[i2]))
                break
        if not period_holds:
            break

    # 2. Period P/2 fails
    half = P // 2
    half_fails = False
    half_witness = None
    for k in range(half):
        i1 = BASE + k
        i2 = BASE + half + k
        if i2 < len(F) and F[i1] != F[i2]:
            half_fails = True
            half_witness = (i1, int(F[i1]), i2, int(F[i2]))
            break

    # 3. SubcaseB (F=0) events in [BASE, BASE+P)
    zeros = [BASE + k for k in range(P) if not F[BASE + k]]
    ones = [BASE + k for k in range(P) if F[BASE + k]]

    return {
        'm': m, 'P': P,
        'period_holds': period_holds,
        'first_fail': first_fail_k,
        'half_fails': half_fails,
        'half_witness': half_witness,
        'subcaseB_count': len(zeros),
        'ones_count': len(ones),
        'subcaseB_first': zeros[:5],
    }

# ──────────────────────────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────────────────────────

print("=" * 70)
print("ADVERSARIAL LOOP 50: Fix simulation bug, re-verify period claims")
print("=" * 70)

# Step 1: Sanity check — verify F(n', 2) = (n' even) for n'=0..200
print("\n--- SANITY CHECK: F(n', m=2) = (n' even) ---")
F2 = simulate_F_all(2, 200)
errors = [(n, int(F2[n]), int(n%2==0)) for n in range(201) if int(F2[n]) != int(n%2==0)]
if errors:
    print(f"  FAIL: {errors[:5]}")
    print("  STOPPING — simulation is wrong!")
    sys.exit(1)
else:
    print(f"  PASS: F(n',2) = (n' even) for n'=0..200 ✓")

# Step 2: Show F(n', 4) for small n'
print("\n--- F(n', m=4) for n'=0..31 ---")
F4_short = simulate_F_all(4, 31)
print(''.join(str(int(x)) for x in F4_short[0:32]))
print("(pattern 01011010 repeated × 4 expected for period 8)")

# Step 3: Verify period claims
print("\n" + "=" * 70)
print("PERIOD VERIFICATION (correct simulation)")
print("=" * 70)

cases = [
    (4, 8), (6, 16), (8, 32),           # reference
    (10, 64), (12, 64), (14, 64),        # plateau 1
    (16, 256), (20, 256), (22, 256),     # plateau 2
]

results = {}
for m, P in cases:
    results[(m, P)] = verify_period(m, P)

# Summary table
print("\n" + "=" * 70)
print("RESULTS TABLE")
print("=" * 70)
print(f"{'m':>4}  {'P':>6}  {'P holds?':>10}  {'P/2 fails?':>11}  {'SubcaseB':>10}  {'0s/1s':>8}")
print("-" * 70)

all_ok = True
for m, P in cases:
    r = results[(m, P)]
    p_ok  = "PASS" if r['period_holds']  else "FAIL"
    h_ok  = "PASS" if r['half_fails']    else "FAIL"
    sb    = r['subcaseB_count']
    sb_ok = "" if sb > 0 else " ZERO!"
    ratio = f"{r['subcaseB_count']}/{r['ones_count']}"
    print(f"{m:>4}  {P:>6}  {p_ok:>10}  {h_ok:>11}  {sb:>6}{sb_ok:<6}  {ratio:>8}")
    if p_ok != "PASS" or h_ok != "PASS":
        all_ok = False

print()
print("=" * 70)
print("DETAILED FINDINGS")
print("=" * 70)
for m, P in cases:
    r = results[(m, P)]
    print(f"\n--- m={m}, claimed period P={P} ---")
    if r['period_holds']:
        print(f"  [PASS] Period {P} holds ({4} repetitions from n'={BASE})")
    else:
        f = r['first_fail']
        print(f"  [FAIL] Period {P} FAILS at rep={f[0]}, k={f[1]}:")
        print(f"         F[{f[2]}]={f[3]} != F[{f[4]}]={f[5]}")
    if r['half_fails']:
        w = r['half_witness']
        print(f"  [PASS] Period {P//2} fails (minimality): F[{w[0]}]={w[1]} != F[{w[2]}]={w[3]}")
    else:
        print(f"  [FAIL] Period {P//2} also holds — period not minimal!")
    sb = r['subcaseB_count']
    print(f"  SubcaseB (F=0) in [{BASE},{BASE+P}): {sb} events (first: {r['subcaseB_first']})")

print("\n" + "=" * 70)
print("VERDICT")
print("=" * 70)
if all_ok:
    print("\nALL PERIOD CLAIMS CONFIRMED with correct simulation.")
    print("  Prior loop 49 failures were due to simulation bug (wrong spike position).")
    print("  The paper's period table is correct.")
else:
    print("\nFAILURES FOUND even with correct simulation — paper claims may be wrong.")

print(f"\nScript: adversarial_loop50.py")
print(f"Base n': {BASE}")
