"""
adversarial_loop51.py — Loop 51: Attack the period-doubling law for large m

Paper claim (sec:period-structure, lines 580-592):
  "The cluster period P_m grows with m (empirical):
   m=22→256, m=24→512, m=26→1024, m=28→2048, m=30→4096,
   m=34→8192, m=36→16384, m=38→32768.
   All periods are verified by direct computation and period-minimality
   is confirmed: period P_m/2 fails for every active m with 4 ≤ m ≤ 38."

The DOUBLING LAW: each consecutive active step doubles the period.
Active sequence: {4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38}
Gaps: 4→6 (+2), 6→8 (+2), ..., 16→20 (+4), 20→22 (+2), 22→24 (+2), ...
Periods: 8,16,32,64,64,64,256,256,256,512,1024,2048,4096,8192,16384,32768

Wait — the doubling isn't strict (64 appears 3 times, 256 appears 3 times).
The claim is "doubling per active STEP for m≥22" which means each consecutive
active m above 22 doubles. Let's verify:
  22→256, 24→512 (×2 ✓), 26→1024 (×2 ✓), 28→2048 (×2 ✓), 30→4096 (×2 ✓),
  34→8192 (×2 ✓ from 30 to 34?), 36→16384 (×2 ✓), 38→32768 (×2 ✓)

But wait — m=32 is INACTIVE. The active sequence skips from 30 to 34.
Does the doubling skip m=32 (inactive)? That would mean 30→4096 and 34→8192,
a factor of 2 jump. Paper says yes.

This loop attacks:
1. Period of m=24 should be 512 (not 256 or 1024)
2. Period of m=26 should be 1024
3. Period of m=28 should be 2048
4. Period of m=30 should be 4096
5. Skip over inactive m=32: m=34 should be 8192

Uses the correct diagonal-read simulation (bug fixed in loop 50).
"""

import numpy as np
import sys

# ──────────────────────────────────────────────────────────────────────────────
# Rule 30 core (diagonal-read / correct definition)
# ──────────────────────────────────────────────────────────────────────────────

def rule30_step_np(tape):
    l = np.roll(tape, 1); l[0] = 0
    c = tape
    r = np.roll(tape, -1); r[-1] = 0
    return l ^ (c | r)

def simulate_F_diagonal(m, n_max):
    """
    F(n', m) for n'=0..n_max using diagonal-read (correct definition).
    Spike at absolute position m; read position n'+1 after n'+1 steps.
    """
    tape_len = 2 * n_max + m + 30
    tape = np.zeros(tape_len, dtype=bool)
    tape[m] = True
    F_seq = np.zeros(n_max + 1, dtype=bool)
    for n_prime in range(n_max + 1):
        tape = rule30_step_np(tape)
        pos = n_prime + 1
        F_seq[n_prime] = tape[pos] if pos < tape_len else False
    return F_seq

# ──────────────────────────────────────────────────────────────────────────────
# Period verification with minimality
# ──────────────────────────────────────────────────────────────────────────────

BASE = 3087

def find_and_verify_period(m, claimed_P, n_reps=3):
    """
    Verify period P and minimality (P/2 fails).
    Also find first SubcaseB (F=0) event and count in one period.
    """
    P = claimed_P
    n_max = BASE + (n_reps + 2) * P

    print(f"  m={m}, claimed P={P}, simulating to n'={n_max} ...", flush=True)
    F = simulate_F_diagonal(m, n_max)

    # 1. Period P holds over n_reps reps
    holds = True
    fail_info = None
    for rep in range(1, n_reps + 1):
        for k in range(P):
            i1, i2 = BASE + k, BASE + rep * P + k
            if i2 < len(F) and F[i1] != F[i2]:
                holds = False
                fail_info = (rep, k, i1, int(F[i1]), i2, int(F[i2]))
                break
        if not holds:
            break

    # 2. Period P/2 fails
    half = P // 2
    half_fails = False
    half_wit = None
    for k in range(half):
        i1, i2 = BASE + k, BASE + half + k
        if i2 < len(F) and F[i1] != F[i2]:
            half_fails = True
            half_wit = (i1, int(F[i1]), i2, int(F[i2]))
            break

    # 3. SubcaseB count and first hit
    zeros = [BASE + k for k in range(P) if BASE + k < len(F) and not F[BASE + k]]

    return {
        'm': m, 'P': P,
        'holds': holds, 'fail_info': fail_info,
        'half_fails': half_fails, 'half_wit': half_wit,
        'subcaseB_count': len(zeros),
        'first_subcaseB': zeros[0] if zeros else None,
    }

# ──────────────────────────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────────────────────────

print("=" * 70)
print("ADVERSARIAL LOOP 51: Period doubling law for large m")
print("Attacking: m=24→512, m=26→1024, m=28→2048, m=30→4096, m=34→8192")
print("=" * 70)

# Cases to test
cases = [
    (24,  512),
    (26, 1024),
    (28, 2048),
    (30, 4096),
    (34, 8192),
]

results = {}
for m, P in cases:
    results[(m, P)] = find_and_verify_period(m, P, n_reps=2)

# ──────────────────────────────────────────────────────────────────────────────
# Report
# ──────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 70)
print("RESULTS TABLE")
print("=" * 70)
print(f"{'m':>4}  {'P':>6}  {'P holds?':>10}  {'P/2 fails?':>11}  {'SubcaseB in P':>14}")
print("-" * 65)

all_ok = True
for m, P in cases:
    r = results[(m, P)]
    p_ok = "PASS" if r['holds']      else "FAIL"
    h_ok = "PASS" if r['half_fails'] else "FAIL"
    sb   = r['subcaseB_count']
    print(f"{m:>4}  {P:>6}  {p_ok:>10}  {h_ok:>11}  {sb:>8} ({'OK' if sb > 0 else 'ZERO!'})")
    if p_ok != "PASS" or h_ok != "PASS":
        all_ok = False

print()
print("=" * 70)
print("DETAILED FINDINGS")
print("=" * 70)

for m, P in cases:
    r = results[(m, P)]
    print(f"\n--- m={m}, claimed P={P} ---")
    if r['holds']:
        print(f"  [PASS] Period {P} holds (2 reps from n'={BASE})")
    else:
        f = r['fail_info']
        print(f"  [FAIL] Period {P} FAILS at rep={f[0]}, k={f[1]}:")
        print(f"         F[{f[2]}]={f[3]} != F[{f[4]}]={f[5]}")

    if r['half_fails']:
        w = r['half_wit']
        print(f"  [PASS] P/2={P//2} fails: F[{w[0]}]={w[1]} != F[{w[2]}]={w[3]}")
    else:
        print(f"  [FAIL] P/2={P//2} also holds — period NOT minimal!")

    sb = r['subcaseB_count']
    fsb = r['first_subcaseB']
    print(f"  SubcaseB (F=0): {sb} events in [{BASE},{BASE+P}), first at n'={fsb}")

# ──────────────────────────────────────────────────────────────────────────────
# Doubling law check
# ──────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 70)
print("DOUBLING LAW CHECK")
print("=" * 70)

active_sequence = [(22,256),(24,512),(26,1024),(28,2048),(30,4096),(34,8192)]
print("\nActive m above 22 (periods should double each step):")
for i in range(len(active_sequence)-1):
    m1, p1 = active_sequence[i]
    m2, p2 = active_sequence[i+1]
    ratio = p2 / p1
    status = "✓" if ratio == 2.0 else f"UNEXPECTED ratio {ratio}"
    print(f"  m={m1}→{m2}: P={p1}→{p2} (ratio={ratio:.1f}) {status}")

# Note: m=32 is inactive (between 30 and 34) — the doubling skips it
print(f"\n  Note: m=32 is inactive, so 30→34 is one 'active step' with ratio 2")

print("\n" + "=" * 70)
print("VERDICT")
print("=" * 70)
if all_ok:
    print("\nALL large-m period claims CONFIRMED.")
    print("  Period doubling law holds for m=24..34.")
    print("  Paper's period table is correct for large m.")
else:
    print("\nFAILURES FOUND in large-m period claims!")
    print("  Paper may have incorrect period values.")

print(f"\nScript: adversarial_loop51.py, base n'={BASE}")
