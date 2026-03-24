#!/usr/bin/env python3
"""
Bridge Attack 2 — The "Compression" Attack on Prize 3 Bridge
Run date: 2026-03-24

The claim to attack:
  "D(rule30_n) = 2n+1, proved by the all-cells-essential theorem."
This is CORRECT. The attack is: does this help Prize 3?

The compression attack (informal):
  A TM with s-bit working tape (constant s, independent of n) can be in at most
  2^s distinct internal configurations (state × tape contents × head position).
  When such a TM reads n as input and produces s(n) = rule30_n(e_n):
    - The TM computes a function N → {0,1}
    - If the TM's working tape is bounded by a constant s (i.e., O(1) space),
      the output sequence s(0), s(1), s(2), ... must be eventually periodic.
  This is because: a TM with O(1) work space and reading n in UNARY will
  eventually revisit the same (state, tape) pair when processing different n,
  causing the output to repeat.

  Therefore: if s(n) is aperiodic, then NO bounded-constant-space TM computes it.

  But this only closes Prize 3 if s(n) is actually aperiodic — which is related
  to Prize 1 (unproved).

THE REAL GAP (the decisive attack on the compression argument):
  Prize 3 asks about TMs that read n in BINARY (standard Turing complexity).
  A TM reading n in binary uses O(log n) bits just for the input register.
  - If space is bounded by O(log n), the TM has 2^(O(log n)) = poly(n) states.
  - A poly(n)-state machine on input n can compute FAR more than eventually-
    periodic sequences — it can compute all of DSPACE(log n) = L (log-space).
  - The eventually-periodic argument only works for O(1) space (UNARY input model).
  - So the compression attack refutes a straw man: no serious complexity claim
    says s(n) needs O(1) space. Prize 3's real claim is about sub-polynomial space,
    not sub-constant space.

This script:
1. Computes s(n) = rule30_n(e_n) for n = 0..1000
2. Checks for eventual periodicity with periods T ≤ 200, tail start n_0 ≤ 200
3. Reports explicit values s(0)..s(50)
4. Reports density (fraction of 1s)
5. Checks for simple patterns: constant, alternating, modular-2, modular-3, etc.
6. Summarizes the implications for the bridge argument
"""

import numpy as np
import sys


def make_en(n):
    """Single-black-cell initial condition: length 2n+1, 1 at position n."""
    c = np.zeros(2 * n + 1, dtype=np.uint8)
    c[n] = 1
    return c


def rule30_n_center(c, n):
    """
    Compute center cell after n steps of Rule 30.
    Input c has length 2n+1. Each step shrinks by 2. After n steps: length 1.
    Rule: new[i] = left[i] XOR (center[i] OR right[i])
    i.e., a[i-1] XOR (a[i] OR a[i+1])
    The formula from Rule 30 number: 0b00011110 = 30.
    (l, c, r) -> (l XOR (c OR r))  — verified: 000->0,001->1,010->1,011->1,100->1,101->0,110->0,111->0
    """
    a = c.astype(np.uint8).copy()
    for _ in range(n):
        if len(a) < 3:
            break
        a = a[:-2] ^ (a[1:-1] | a[2:])
    return int(a[0]) if len(a) > 0 else 0


# ---------------------------------------------------------------------------
# Verification of the rule implementation
# ---------------------------------------------------------------------------
# Rule 30 table: 000->0, 001->1, 010->1, 011->1, 100->1, 101->0, 110->0, 111->0
# n=1 from [0,1,0]: apply rule to positions 0,1,2 (boundary = 0 outside)
#   l=0, c=0, r=1 -> 0 XOR (0 OR 1) = 1  (but we compute on interior only)
# After 1 step on [0,1,0]: shrinks to [1] (center cell). Rule: a[0]=0^(1|0)=1. Correct.
e1 = make_en(1)
assert rule30_n_center(e1, 1) == 1, f"Verification failed: rule30_1([0,1,0]) should be 1, got {rule30_n_center(e1, 1)}"

# n=2 from [0,0,1,0,0]:
# Step 1: apply a[i-1]^(a[i]|a[i+1]) for i=1,2,3 -> [0^(0|1), 0^(1|0), 1^(0|0)] = [1,1,1]
# Step 2: apply to [1,1,1] -> [1^(1|1)] = [0]? 1^(1|1)=1^1=0. Hmm.
# Let's just check with our function:
e2 = make_en(2)
s2 = rule30_n_center(e2, 2)
# We'll verify below by printing.

print("=== Bridge Attack 2: Compression Attack on Prize 3 ===\n")
print("Computing s(n) = rule30_n(e_n) for n = 0..1000")
print("Checking for eventual periodicity...")
print()

# ---------------------------------------------------------------------------
# Compute s(n) for n = 0..1000
# ---------------------------------------------------------------------------
N_MAX = 1001
s_vals = []
for n in range(N_MAX):
    c = make_en(n)
    s_vals.append(rule30_n_center(c, n))
    if n % 100 == 0:
        print(f"  ... computed up to n={n}", flush=True)

s_arr = np.array(s_vals, dtype=np.int32)
print(f"  Done. Computed s(0)..s({N_MAX-1}).\n")

# ---------------------------------------------------------------------------
# Section 1: Explicit values s(0)..s(50)
# ---------------------------------------------------------------------------
print("--- Section 1: Explicit values s(0)..s(50) ---")
print("  n  : s(n)")
for n in range(51):
    print(f"  {n:3d}: {s_vals[n]}", end="  ")
    if (n + 1) % 10 == 0:
        print()
print("\n")

# Display as a bit string for easy reading
bitstr = "".join(str(x) for x in s_vals[:51])
print(f"  Bit string s(0)..s(50): {bitstr}\n")

# ---------------------------------------------------------------------------
# Section 2: Density
# ---------------------------------------------------------------------------
total_ones = sum(s_vals)
density = total_ones / len(s_vals)
print(f"--- Section 2: Density ---")
print(f"  s(n)=1 count : {total_ones} / {len(s_vals)}")
print(f"  Density      : {density:.4f}  (expected ~0.5 if pseudo-random)\n")

# Density in sub-ranges
for start, end in [(0, 100), (100, 200), (200, 500), (500, 1001)]:
    sub = s_vals[start:end]
    d = sum(sub) / len(sub)
    print(f"  Density in [{start},{end}): {d:.4f}")
print()

# ---------------------------------------------------------------------------
# Section 3: Simple pattern checks
# ---------------------------------------------------------------------------
print("--- Section 3: Simple pattern checks ---")

# Constant?
if all(x == s_vals[0] for x in s_vals):
    print("  CONSTANT: YES (all values are the same)")
else:
    print(f"  Constant: NO  (first 10: {s_vals[:10]})")

# Alternating (period 2)?
period2 = all(s_vals[i] == s_vals[i % 2] for i in range(len(s_vals)))
print(f"  Period-2 (alternating): {'YES' if period2 else 'NO'}")

# Modular checks: does s(n) = n mod k for small k?
for k in [2, 3, 4, 5]:
    matches = sum(1 for n in range(len(s_vals)) if s_vals[n] == (n % k) % 2)
    print(f"  s(n) = (n mod {k}) mod 2: {matches}/{len(s_vals)} matches "
          f"({'YES' if matches == len(s_vals) else 'NO'})")

print()

# ---------------------------------------------------------------------------
# Section 4: Eventual periodicity search
# ---------------------------------------------------------------------------
print("--- Section 4: Eventual periodicity search ---")
print("  Checking: does there exist T ≤ 200, n_0 ≤ 200 such that")
print("  s(n) = s(n+T) for all n ≥ n_0?\n")

found_period = None
found_n0 = None

for T in range(1, 201):
    for n0 in range(0, 201):
        # Check if s(n) = s(n+T) for ALL n in [n0, N_MAX - T - 1]
        tail = s_arr[n0: N_MAX - T]
        shifted = s_arr[n0 + T: N_MAX]
        if np.array_equal(tail, shifted):
            found_period = T
            found_n0 = n0
            break
    if found_period is not None:
        break
    if T % 50 == 0:
        print(f"  ... checked periods up to T={T}", flush=True)

print()
if found_period is not None:
    print(f"  *** PERIODIC FOUND: T={found_period}, n_0={found_n0} ***")
    print(f"  s(n) = s(n + {found_period}) for all n ≥ {found_n0}")
    print()
    print(f"  Repeating block (length {found_period}): "
          f"{''.join(str(x) for x in s_vals[found_n0:found_n0+found_period])}")
    print()
    print("  IMPLICATION FOR THE BRIDGE:")
    print("  If s is eventually periodic with period T, then it IS computable by")
    print("  a finite automaton — in O(1) space (just store n mod T and a lookup table).")
    print("  This would directly refute the bridge argument's assumption that s is hard!")
    print("  But it would NOT immediately settle Prize 3 — the question is whether a")
    print("  TM in sub-polynomial space can compute s(n), and a period-T automaton")
    print("  does so in O(1) space (which IS sub-polynomial).")
    print()
    print("  PRIZE 3 RELEVANCE: if s is eventually periodic, Prize 3 is FALSE —")
    print("  there exists a fast formula (automaton) for the center column.")
    print("  This would be a discovery in its own right.")
else:
    print(f"  No period T ≤ 200 found with tail starting at n_0 ≤ 200.")
    print(f"  (Checked all T in [1..200], n_0 in [0..200], over {N_MAX} data points)")
    print()
    print("  This is evidence (but not proof) that s(n) is aperiodic.")

print()

# ---------------------------------------------------------------------------
# Section 5: Runs analysis (consecutive same values)
# ---------------------------------------------------------------------------
print("--- Section 5: Run-length analysis ---")
runs = []
current_val = s_vals[0]
current_len = 1
for v in s_vals[1:]:
    if v == current_val:
        current_len += 1
    else:
        runs.append((current_val, current_len))
        current_val = v
        current_len = 1
runs.append((current_val, current_len))

run_lengths = [r[1] for r in runs]
max_run = max(run_lengths)
avg_run = sum(run_lengths) / len(run_lengths)
print(f"  Total runs    : {len(runs)}")
print(f"  Max run length: {max_run}")
print(f"  Avg run length: {avg_run:.3f}")
print(f"  Longest runs  : {sorted(run_lengths, reverse=True)[:10]}")
print()
if max_run <= 3:
    print("  Short runs: no long constant stretches. Consistent with pseudo-random behavior.")
else:
    print(f"  Run of length {max_run} found — may indicate local structure.")
print()

# ---------------------------------------------------------------------------
# Section 6: Autocorrelation — looking for hidden periodicity
# ---------------------------------------------------------------------------
print("--- Section 6: Autocorrelation (normalized) ---")
print("  Computing autocorrelation C(T) = (1/N) sum_n s(n)*s(n+T) for T=1..50\n")

centered = s_arr.astype(np.float64) - density  # mean-center
N = len(centered)
var = np.var(centered)

autocorr = []
for T in range(1, 51):
    c = np.mean(centered[T:] * centered[:-T]) / var if var > 0 else 0.0
    autocorr.append((T, c))

print("  T : C(T)    (|C| >> 0 suggests periodicity at T)")
for T, c in autocorr:
    bar = "#" * int(abs(c) * 40)
    sign = "+" if c >= 0 else "-"
    print(f"  {T:2d}: {c:+.4f}  {sign}{bar}")
print()

max_autocorr = max(autocorr, key=lambda x: abs(x[1]))
print(f"  Peak autocorrelation: T={max_autocorr[0]}, C={max_autocorr[1]:.4f}")
if abs(max_autocorr[1]) > 0.1:
    print(f"  Noteworthy: |C| > 0.1 at T={max_autocorr[0]} — possible period or near-period.")
else:
    print(f"  All |C(T)| < 0.1: no strong periodicity signal detected.")
print()

# ---------------------------------------------------------------------------
# Section 7: Summary — the gap in the compression argument
# ---------------------------------------------------------------------------
print("=" * 70)
print("=== SUMMARY: The Compression Attack and Its Fatal Gap ===")
print("=" * 70)
print()
print("THE COMPRESSION ARGUMENT (what it claims):")
print("  A TM with O(1) working tape is a finite automaton.")
print("  A finite automaton on input n (in unary) computes only eventually-periodic")
print("  sequences. If s(n) is aperiodic, it cannot be computed in O(1) space.")
print()

if found_period is not None:
    print("  *** COMPUTATIONAL FINDING: s(n) IS eventually periodic (period found above)! ***")
    print("  *** This means the compression argument's premise (aperiodicity) is FALSE. ***")
    print("  *** The bridge argument cannot assume aperiodicity — it must prove it. ***")
else:
    print("  COMPUTATIONAL FINDING: No period T ≤ 200 found in first 1001 values.")
    print("  This is consistent with (but does not prove) aperiodicity.")
    print()
    print("  IMPORTANT: 'No short period found' is NOT a proof of aperiodicity.")
    print("  The sequence might be periodic with a very long period, or it might")
    print("  be genuinely aperiodic. We cannot tell from finite data.")

print()
print("THE FATAL GAP IN THE COMPRESSION ARGUMENT:")
print()
print("  The compression argument works ONLY for O(1) space (constant bounded tape).")
print("  Prize 3 is about whether s(n) can be computed in sub-polynomial space.")
print()
print("  If the TM reads n in BINARY (as is standard in complexity theory):")
print("    - Input length = O(log n) bits")
print("    - A TM using O(log n) space has 2^(O(log n)) = poly(n) possible states")
print("    - This is FAR more than a finite automaton — it can compute L (log-space)")
print("    - Log-space TMs can compute many sequences that are NOT eventually periodic")
print("    - The 'finite automaton = eventually periodic' argument FAILS completely")
print()
print("  Example: the sequence s(n) = (n's Hamming weight) mod 2 is NOT eventually")
print("  periodic, but IS computable in O(log n) space (read bits of n, XOR them).")
print("  The compression argument would incorrectly claim this requires Omega(1) space.")
print()
print("  If the TM reads n in UNARY:")
print("    - Then O(1) space = finite automaton, and the argument is valid.")
print("    - But unary input is NOT standard for Prize 3 (which is about time complexity")
print("      of computing the nth value, with n presented in binary/as an integer).")
print("    - The compression attack on O(1) unary-space is a valid lower bound,")
print("      but it proves only that s(n) requires Omega(log n) bits of memory")
print("      (just to store n in binary) — which is trivially true and vacuous.")
print()
print("CONCLUSION FOR THE BRIDGE:")
print()
print("  The compression attack is VALID but TRIVIAL for the unary model.")
print("  For the binary model (relevant to Prize 3), the compression attack")
print("  proves NOTHING beyond the trivial 'you need to store n'.")
print()
print("  To close Prize 3 via the bridge, you need to show that computing s(n)")
print("  requires SUPER-LOGARITHMIC space — i.e., more than O(log n) bits.")
print("  The query complexity lower bound D(rule30_n) = 2n+1 says you need")
print("  to 'consult' 2n+1 cells of the INITIAL CONDITION — but since s(n)")
print("  has a FIXED initial condition (e_n, known structurally), a TM can")
print("  'consult' all 2n+1 cells deterministically without any query oracle.")
print("  The query lower bound does not translate to a space lower bound here.")
print()
print("ATTACK VERDICT:")
print("  The compression argument is a red herring for Prize 3 in the binary model.")
print("  It is valid but trivial in the unary model.")
print("  The real barrier to closing Prize 3 via the bridge remains:")
print("  - The query lower bound lives in a worst-case-input model.")
print("  - Prize 3 is about a single FIXED input (the integer n, not a string).")
print("  - No known technique bridges worst-case query complexity to")
print("    fixed-input space complexity for a specific sequence.")
print()
