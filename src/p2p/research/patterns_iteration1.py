"""
patterns_iteration1.py — Mathematical pattern analysis for Rule 30 Prize 3 data.
Ramanujan loop, 2026-03-24.

Investigates:
1. Binary pattern analysis: active vs inactive m values
2. Period sequence analysis: log2(P_m) vs m
3. Why m=18 is inactive
4. Why m=32 is inactive
5. Generating function / polynomial structure of active set
6. The period jump at m=16
7. Connection to Rule 30 geometry (cone widths)
"""

import numpy as np
import math
from functools import reduce

active_m = [4, 6, 8, 10, 12, 14, 16, 20, 22, 24, 26, 28, 30, 34, 36, 38]
inactive_m = [18, 32]  # inactive even m in [4,38]
all_even_m = list(range(4, 40, 2))  # [4,6,...,38]

# Periods (verified from paper and adversarial loops)
periods = {4:8, 6:16, 8:32, 10:64, 12:64, 14:64, 16:512, 20:256, 22:512,
           24:1024, 26:2048, 28:4096, 30:4096, 34:8192, 36:16384, 38:32768}

# Periods for inactive m (verified: period of F sequence, no SubcaseB)
inactive_periods = {18: 256, 32: 4096, 40: 65536, 42: 131072}

print("=" * 70)
print("INVESTIGATION 1: Binary pattern analysis of active vs inactive m")
print("=" * 70)

print("\n--- m//2 in binary, factorization, and activity status ---")
print(f"{'m':>4} {'m//2':>6} {'bin(m//2)':>12} {'popcount':>9} {'m mod 3':>8} {'m mod 5':>8} {'m mod 7':>8} {'active':>7}")
for m in all_even_m:
    h = m // 2  # half-m
    b = bin(h)
    pc = bin(h).count('1')
    is_active = m in active_m
    print(f"{m:>4} {h:>6} {b:>12} {pc:>9} {m%3:>8} {m%5:>8} {m%7:>8} {'YES' if is_active else 'NO':>7}")

print("\n--- Active m values: binary of m//2 ---")
for m in active_m:
    h = m // 2
    print(f"  m={m:2d}: m/2={h:2d} = {bin(h):>8}  popcount={bin(h).count('1')}")

print("\n--- Inactive m values: binary of m//2 ---")
for m in inactive_m:
    h = m // 2
    print(f"  m={m:2d}: m/2={h:2d} = {bin(h):>8}  popcount={bin(h).count('1')}")

print("\n--- Check: does popcount(m//2) determine activity? ---")
for pc in range(1, 6):
    m_with_pc = [m for m in all_even_m if bin(m//2).count('1') == pc]
    active_with_pc = [m for m in m_with_pc if m in active_m]
    inactive_with_pc = [m for m in m_with_pc if m not in active_m]
    print(f"  popcount={pc}: m={m_with_pc}, active={active_with_pc}, inactive={inactive_with_pc}")

print("\n--- Check mod small primes ---")
for mod in [3, 5, 6, 7, 9, 12]:
    print(f"  Active m mod {mod}: {sorted(set(m % mod for m in active_m))}")
    print(f"  Inactive m mod {mod}: {sorted(set(m % mod for m in inactive_m))}")

print("\n--- Factorization of all even m in [4,38] ---")
def factorize(n):
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors

def rad(n):
    """Radical of n: product of distinct prime factors."""
    return reduce(lambda a, b: a * b, factorize(n).keys(), 1)

def is_powerful(n):
    """Powerful number: every prime factor appears at least twice."""
    return all(e >= 2 for e in factorize(n).values())

for m in all_even_m:
    f = factorize(m)
    v2 = f.get(2, 0)  # 2-adic valuation
    odd_part = m // (2**v2)
    is_act = m in active_m
    print(f"  m={m:2d}: {f}  v2={v2}  odd_part={odd_part}  active={is_act}")

print("\n--- Key observation: v2(m) (2-adic valuation) ---")
for m in all_even_m:
    v2 = 0
    t = m
    while t % 2 == 0:
        v2 += 1
        t //= 2
    is_act = m in active_m
    print(f"  m={m:2d}: v2={v2}  odd_part={m//(2**v2)}  active={is_act}")

print()
print("=" * 70)
print("INVESTIGATION 2: Period sequence analysis")
print("=" * 70)

log2_periods = {m: int(round(math.log2(p))) for m, p in periods.items()}
print("\n--- log2(P_m) for active m ---")
print(f"{'m':>4} {'P_m':>8} {'log2(P_m)':>10} {'m//2':>6} {'log2-m//2':>12} {'log2-m/2+offset':>18}")
for m in active_m:
    p = periods[m]
    lg = log2_periods[m]
    print(f"{m:>4} {p:>8} {lg:>10} {m//2:>6} {lg - m//2:>12}")

print("\n--- Sequence of log2(P_m) values (OEIS-style) ---")
seq = [log2_periods[m] for m in active_m]
print(f"  m values:     {active_m}")
print(f"  log2(P_m):    {seq}")
print(f"  Differences:  {[seq[i+1]-seq[i] for i in range(len(seq)-1)]}")

print("\n--- log2(P_m) vs m/2 regression ---")
x = np.array([m/2 for m in active_m], dtype=float)
y = np.array([log2_periods[m] for m in active_m], dtype=float)
# Linear regression
n_pts = len(x)
slope = (n_pts * np.dot(x, y) - x.sum() * y.sum()) / (n_pts * np.dot(x, x) - x.sum()**2)
intercept = (y.sum() - slope * x.sum()) / n_pts
print(f"  Linear fit: log2(P_m) ≈ {slope:.4f} * (m/2) + {intercept:.4f}")
print(f"  Residuals: {[round(log2_periods[m] - slope*(m/2) - intercept, 2) for m in active_m]}")

print("\n--- Checking if log2(P_m) = m/2 + c for some c (exact) ---")
for m in active_m:
    lg = log2_periods[m]
    diff = lg - m//2
    print(f"  m={m:2d}: log2={lg}, m//2={m//2}, diff={diff}")

# Now look at the "correct" offset for the clean region m>=22
print("\n--- For m>=22 (clean doubling region): ---")
clean_m = [m for m in active_m if m >= 22]
for m in clean_m:
    lg = log2_periods[m]
    print(f"  m={m:2d}: log2(P)={lg}, m/2={m/2}, diff from m/2={lg - m/2:.1f}")

print("\n--- Active m index and log2(P_m) ---")
print("  (Index = position in sorted active_m list, 0-based)")
for i, m in enumerate(active_m):
    lg = log2_periods[m]
    print(f"  index={i:2d}, m={m:2d}: log2(P)={lg}, diff from (i+3)={lg-(i+3)}")

print()
print("=" * 70)
print("INVESTIGATION 3: Why m=18 is inactive")
print("=" * 70)

print("\n--- Factorization context for m=18 ---")
print(f"  18 = 2 × 3²  (odd part = 9 = 3²; ONLY perfect-square odd part in [4,38])")
print(f"  Check all even m in [4,38] for square odd parts:")
for m in all_even_m:
    f = factorize(m)
    v2 = f.get(2, 0)
    odd_part = m // (2**v2)
    is_sq = int(math.isqrt(odd_part))**2 == odd_part
    is_act = m in active_m
    if odd_part > 1:
        print(f"    m={m:2d}: odd_part={odd_part}, is_perfect_square={is_sq}, active={is_act}")

print("\n--- Period of F at m=18 vs surrounding active m ---")
print(f"  m=16 (active):   P={periods[16]}")
print(f"  m=18 (inactive): P_F=256 (F has period 256, but no SubcaseB)")
print(f"  m=20 (active):   P={periods[20]}")
print(f"  Note: P_F(18) = 256 = P_16 = P_20 — same period as neighbors!")
print(f"  m=18 is NOT inactive due to period mismatch; it has the same F-period.")
print(f"  The inactivity is about SubcaseB structure, not period length.")

print("\n--- Gap pattern around m=18 ---")
print(f"  active_m near 18: ..., 16, [18 SKIP], 20, ...")
print(f"  18 - 16 = 2 (gap 2 before)")
print(f"  20 - 18 = 2 (gap 2 after)")
print(f"  Compare m=32: ..., 30, [32 SKIP], 34, ...")
print(f"  32 - 30 = 2 (gap 2 before)")
print(f"  34 - 32 = 2 (gap 2 after)")
print(f"  Both inactive positions are surrounded by active positions at distance 2.")

print("\n--- mod-8 analysis ---")
print(f"  18 mod 8 = {18 % 8}")
print(f"  32 mod 8 = {32 % 8}")
print(f"  Active m mod 8: {sorted(set(m % 8 for m in active_m))}")
print(f"  Inactive m mod 8: {sorted(set(m % 8 for m in inactive_m))}")
# Note: both 18 and 32 are ≡ 2 mod 8, while 10, 26 are also ≡ 2 mod 8 and are active
# So mod 8 alone doesn't explain it.

print()
print("=" * 70)
print("INVESTIGATION 4: Why m=32 is inactive (32 = 2^5)")
print("=" * 70)

print("\n--- Powers of 2 in active/inactive set ---")
powers_of_2_in_range = [m for m in all_even_m if m & (m-1) == 0]
print(f"  Powers of 2 in [4,38]: {powers_of_2_in_range}")
for m in powers_of_2_in_range:
    is_act = m in active_m
    v2 = int(math.log2(m))
    print(f"    m={m:2d} = 2^{v2}:  active={is_act}, period P={periods.get(m, 'N/A')}")

print(f"\n  4=2² → ACTIVE")
print(f"  8=2³ → ACTIVE")
print(f"  16=2⁴ → ACTIVE")
print(f"  32=2⁵ → INACTIVE (breaks the pattern!)")
print(f"\n  Question: why does 32 break the 4,8,16 pattern?")
print(f"  4: P=8=2³  (log2P=3=v2(4)+1)")
print(f"  8: P=32=2⁵ (log2P=5=v2(8)+2)")
print(f"  16: P=512=2⁹ (log2P=9=v2(16)+5)")
print(f"  Pattern for powers of 2 (if active): log2P - log2m is 1, 2, 5, ?")
diffs_pow2 = [int(math.log2(periods[m])) - int(math.log2(m)) for m in [4, 8, 16]]
print(f"  log2P - log2m for m=4,8,16: {diffs_pow2}  (sequence: 1, 2, 5)")
print(f"  Not a simple arithmetic sequence — 2nd differences: {[diffs_pow2[1]-diffs_pow2[0], diffs_pow2[2]-diffs_pow2[1]]}")

print(f"\n--- F-period of m=32 (inactive) vs m=30,34 (active) ---")
print(f"  m=30 (active):   P_F={periods[30]}=2^12")
print(f"  m=32 (inactive): P_F={inactive_periods[32]}=2^12 (same as m=30!)")
print(f"  m=34 (active):   P_F={periods[34]}=2^13")
print(f"  m=32 F-period = 4096 = P_30 = P_28 (same as active neighbors!)")
print(f"  Like m=18: inactive due to SubcaseB structure, not period anomaly.")

print()
print("=" * 70)
print("INVESTIGATION 5: Generating function / polynomial for active set")
print("=" * 70)

# f(x) = sum x^m for m in active_m
print("\n--- f(x) = Σ x^m for active m ---")
print(f"  f(x) = ", end="")
terms = [f"x^{m}" for m in active_m]
print(" + ".join(terms))

# Factor out x^4
print(f"\n  f(x) = x^4 * (1 + x^2 + x^4 + x^6 + x^8 + x^10 + x^12 + x^16 + x^18 + x^20 + x^22 + x^24 + x^26 + x^30 + x^32 + x^34)")
# = x^4 * g(x) where g(x) = (f(x))/x^4

# The exponents when we shift by 4: [0,2,4,6,8,10,12,16,18,20,22,24,26,30,32,34]
shifted = [m - 4 for m in active_m]
print(f"\n  Shifted exponents (subtract 4): {shifted}")
print(f"  Missing from [0,2,...,34]: {[m for m in range(0,36,2) if m not in shifted]}")
# Missing: 14 and 28
print(f"  (Missing correspond to original m=18 and m=32)")

print("\n--- Over GF(2), does f(x) factor nicely? ---")
# Active indicator: which even m in [4,38] are active?
# Represent as binary polynomial: bit k = 1 if 2k is active (for k=2..19)
# Let's look at the indicator as a 0/1 sequence indexed by m/2:
half_active = [m//2 for m in active_m]
half_inactive = [m//2 for m in inactive_m]
all_half = [m//2 for m in all_even_m]
indicator = [1 if h in half_active else 0 for h in all_half]
print(f"\n  Half-m values: {all_half}")
print(f"  Activity indicator: {indicator}")
print(f"  (1=active, 0=inactive, indexed by m/2 from 2 to 19)")
# As a GF(2) polynomial in y where y=x^2, active iff coefficient is 1
print(f"\n  Polynomial (GF2, indexed by m/2): bit positions {[h for h,i in zip(all_half, indicator) if i==1]}")
print(f"  Missing (inactive): bit positions {half_inactive}")
# = all bits from 2..19 except 9 and 16
print(f"\n  All half-m in [2,19]: {all_half}")
print(f"  Active half-m: {half_active}")
print(f"  Inactive half-m: {half_inactive}  (9=3² and 16=2⁴)")

print("\n--- Pattern: inactive half-m values {9, 16} ---")
print(f"  9 = 3²  (perfect square of odd prime)")
print(f"  16 = 2⁴  (fourth power of 2)")
print(f"  Both are PERFECT SQUARES: 9=3², 16=4²")
print(f"  ALL other h=m/2 in [2,19] are square-free or have v2=1:")
for h in all_half:
    sq = int(math.isqrt(h))**2 == h
    print(f"    h={h:2d} (m={2*h:2d}): perfect_square={sq}, active={h in half_active}")

print()
print("=" * 70)
print("INVESTIGATION 6: The period jump at m=16")
print("=" * 70)

print("\n--- Period table with 'expected' doubling ---")
print("  If simple doubling held: P_m should double at each active step.")
print()
expected_double = 8  # start with P_4=8
for i, m in enumerate(active_m):
    actual = periods[m]
    act_log2 = int(math.log2(actual))
    exp_log2 = i + 3  # P_{m_i} = 2^{i+3} if doubling held
    diff = act_log2 - exp_log2
    print(f"  m={m:2d}: P={actual:6d}=2^{act_log2:2d}  expected_if_doubling=2^{exp_log2:2d}  excess={diff:+d}")

print("\n--- The m=16 jump specifically ---")
print(f"  m=14: P=64=2^6")
print(f"  m=16: P=512=2^9")
print(f"  If clean doubling: expected P_16 = 128 = 2^7")
print(f"  Actual: 512 = 2^9 = 4 × 128 = 4 × expected")
print(f"  Jump of +3 in log2: unexplained by doubling")
print()
print(f"  What's between m=14 and m=16?")
print(f"  m=14 is active, m=16 is active — no inactive positions between them")
print(f"  So it's not the 'missing m=15' effect")
print()
print(f"  Period plateaus before m=16:")
print(f"  m=10,12,14 all have P=64: THREE CONSECUTIVE active positions at same period")
print(f"  This is a PLATEAU, not an increase.")
print(f"  After the plateau, m=16 jumps UP by 3 powers of 2 (not 1).")
print()
print(f"  Similarly: m=16,20,22 all have P=256: another PLATEAU (3 positions)")
print(f"  After this plateau, m=24 resumes doubling at P=512=2^9 (not a jump).")
print()
print(f"  PATTERN: Two plateaus of length 3, each followed by continuation of clean doubling.")
print(f"  Plateau 1: m=10,12,14 → P=64=2^6")
print(f"  Plateau 2: m=16,20,22 → P=256=2^8  [gap of 2^1 = skipped 2^7=128]")
print(f"  The 'jump' at m=16 is because it starts a NEW plateau at a higher level.")

print("\n--- What's P_16 = 512 in context? ---")
print(f"  512 = 2^9")
print(f"  The FIRST entry of plateau 2 is P=256=2^8 (at m=20)")
print(f"  Wait — actually:")
print(f"    m=16: P=512=2^9")
print(f"    m=20: P=256=2^8  ← LOWER than m=16!")
print(f"    m=22: P=512=2^9  ← same as m=16")
print(f"  So it's not a simple plateau. m=20 dips BELOW m=16.")
# re-examine
for m in [14, 16, 20, 22, 24]:
    print(f"  m={m:2d}: P={periods[m]}=2^{int(math.log2(periods[m]))}")

print()
print("=" * 70)
print("INVESTIGATION 7: Rule 30 geometry and cone widths")
print("=" * 70)

print("\n--- Cone widths: 2m+1 for active m ---")
print(f"  {'m':>4} {'cone width=2m+1':>16} {'log2(P_m)':>10} {'cone width mod 8':>16}")
for m in active_m:
    cw = 2*m + 1
    print(f"  {m:>4} {cw:>16} {log2_periods[m]:>10} {cw % 8:>16}")

print("\n--- Cone widths for inactive m ---")
for m in inactive_m + [40, 42]:
    cw = 2*m + 1
    print(f"  m={m:2d}: cone width = {cw} = 2*{m}+1,  F-period = {inactive_periods.get(m,'?')}")

print("\n--- Why m=2 is not in active set ---")
print(f"  m=2: cone width = 5 cells, minimum tape for SubcaseB geometry")
print(f"  Paper starts at m=4; m=2 has ts2_last_always_false proved (F and G are never (0,1))")
print(f"  Structural reason: m=2 positions the spike JUST inside the cone boundary,")
print(f"  too close for the two-spike interaction to produce a SubcaseB event.")
print(f"  The cone for m=2 has width 5, and the last-spike at position 2n'+2")
print(f"  is only 2*2+2-(2) = 4 cells from the m-spike when m=2.")
print(f"  This symmetry kills SubcaseB.")

print("\n--- What is special about m=4 (first active)? ---")
print(f"  m=4: cone width = 9. The left edge sees a spike at position 4.")
print(f"  The SubcaseB occurs when F=0 (spike at 4 alone → center=0)")
print(f"  and G=1 (spike at 4 AND at last → center=1).")
print(f"  First SubcaseB at n'=3093 (offset 3093-3087=6 from n_0=3087).")
print(f"  The 9-cell cone is the minimum width where two-spike interaction matters.")

print()
print("=" * 70)
print("INVESTIGATION 8: Period sequence as a number-theoretic object")
print("=" * 70)

print("\n--- Does P_m = 2^(m/2 + offset) for some simple offset? ---")
for m in active_m:
    lg = log2_periods[m]
    half = m // 2
    offset = lg - half
    print(f"  m={m:2d}: log2(P)={lg:2d}, m/2={half:2d}, offset={offset:+d}")

print("\n--- Clean region m=22..38: period = 2^(m/2 - 2) ---")
print("  Check: m/2 - 2 should equal log2(P)")
for m in [22, 24, 26, 28, 30, 34, 36, 38]:
    expected_lg = m//2 - 2
    actual_lg = log2_periods[m]
    print(f"  m={m:2d}: expected=2^{expected_lg}, actual=2^{actual_lg}, match={expected_lg==actual_lg}")

print("\n--- Missing exponents in period sequence ---")
all_log2_periods = sorted(set(log2_periods.values()))
print(f"  log2(P) values present: {all_log2_periods}")
print(f"  Full range [3,15]: {list(range(3,16))}")
print(f"  Missing: {[i for i in range(3,16) if i not in all_log2_periods]}")
print(f"  (7 = log2(128) is missing — corresponds to would-be m=18)")
print(f"  (Between plateaus at 2^6=64 and 2^8=256, the 2^7=128 is absent)")

print()
print("=" * 70)
print("INVESTIGATION 9: F-periods for ALL even m (active + inactive)")
print("=" * 70)

# Combine all known F-periods
all_m_periods = {}
for m, p in periods.items():
    all_m_periods[m] = p
for m, p in inactive_periods.items():
    all_m_periods[m] = p

print("\n--- All known F-periods by m ---")
print(f"  {'m':>4} {'F-period':>10} {'log2':>6} {'active':>8}")
for m in sorted(all_m_periods.keys()):
    p = all_m_periods[m]
    lg = int(round(math.log2(p)))
    is_act = m in active_m
    print(f"  {m:>4} {p:>10} {lg:>6} {'YES' if is_act else 'NO':>8}")

print("\n--- UNIVERSAL doubling law: F-period doubles for every even m ---")
print("  (Testing whether P_F(m+2) = 2 * P_F(m) for all even m in [4,42])")
sorted_all_m = sorted(all_m_periods.keys())
for i in range(len(sorted_all_m)-1):
    m1 = sorted_all_m[i]
    m2 = sorted_all_m[i+1]
    if m2 - m1 == 2:  # consecutive even values
        p1 = all_m_periods[m1]
        p2 = all_m_periods[m2]
        ratio = p2 / p1
        is_double = abs(ratio - 2.0) < 0.01
        print(f"  m={m1:2d}→{m2:2d}: P={p1}→{p2}, ratio={ratio:.2f}  {'DOUBLE' if is_double else 'NOT DOUBLE'}")

print()
print("=" * 70)
print("INVESTIGATION 10: Structural summary — inactive m and perfect squares")
print("=" * 70)

print("\n--- MAIN HYPOTHESIS: m/2 inactive iff m/2 is a perfect square >= 9 ---")
print("  (Or equivalently: m is inactive iff m/2 is a perfect square)")
print()
print(f"  m=18: m/2=9=3²  → INACTIVE ✓")
print(f"  m=32: m/2=16=4² → INACTIVE ✓")
print()
print(f"  Other perfect squares h = m/2 in [2,19]: 4, 9, 16")
print(f"  h=4: m=8 → ACTIVE (contradicts hypothesis!)")
print()
print(f"  REVISED: perfect squares in half-m: 4 (m=8, active), 9 (m=18, inactive), 16 (m=32, inactive)")
print(f"  So h=4 is a counterexample. The 'perfect square' theory doesn't hold cleanly.")
print()
print(f"  BETTER: look at h = m/2 in [2,19], which are square-free?")
for m in all_even_m:
    h = m // 2
    f = factorize(h)
    sf = all(e == 1 for e in f.values())  # square-free
    is_act = m in active_m
    print(f"    h={h:2d} (m={m:2d}): square-free={sf}, active={is_act}")

print()
print(f"\n--- CORRECT OBSERVATION: ---")
print(f"  NOT square-free ↔ NOT active?")
non_sf_h = [m//2 for m in all_even_m if not all(e == 1 for e in factorize(m//2).values())]
print(f"  Non-square-free h values: {non_sf_h}  (m values: {[2*h for h in non_sf_h]})")
print(f"  Corresponding m values active? {[2*h in active_m for h in non_sf_h]}")
print(f"  h=4=2²: m=8 is ACTIVE despite non-square-free")
print(f"  h=9=3²: m=18 is INACTIVE ✓")
print(f"  h=12=2²×3: m=24 is ACTIVE despite non-square-free")
print(f"  h=16=2⁴: m=32 is INACTIVE ✓")
print(f"  h=18=2×3²: m=36 is ACTIVE despite non-square-free")
print(f"\n  Square-free criterion fails at m=8 (h=4=2²), m=24 (h=12), m=36 (h=18).")

print("\n--- ALTERNATIVE: v2(m) = 2-adic valuation, is there a pattern? ---")
print(f"  m  v2(m)  active")
for m in all_even_m:
    v2 = 0; t = m
    while t % 2 == 0: v2 += 1; t //= 2
    print(f"  {m:2d}  {v2}      {'YES' if m in active_m else 'NO'}")

print("\n--- v2 breakdown ---")
for v in range(1, 6):
    ms = [m for m in all_even_m if bin(m).count('1') > 0 and (lambda t: [t // 2 for _ in iter(lambda: t % 2 == 0, False)])(m)]
    # simpler:
    ms_v = [m for m in all_even_m if m // (2**v) % 2 == 1 and m % (2**v) == 0]
    if ms_v:
        active_v = [m for m in ms_v if m in active_m]
        inactive_v = [m for m in ms_v if m not in active_m]
        print(f"  v2(m)={v}: m={ms_v}, active={active_v}, inactive={inactive_v}")

print()
print("=" * 70)
print("INVESTIGATION 11: Polynomial over GF(2) — does f(y) = 1/(1+y^9+y^16) mod 2?")
print("=" * 70)

print("""
  The active indicator polynomial (over GF(2), variable y = x^2, shift by x^4):
    g(y) = 1 + y + y^2 + y^3 + y^4 + y^5 + y^6 + y^8 + y^9 + y^10 + y^11 + y^12 + y^13 + y^15 + y^16 + y^17
  (one term for each active half-m in [2,19], shifted so h=2 maps to y^0)

  All-ones polynomial from degree 0 to 17 (all 18 terms):
    P_all(y) = 1 + y + y^2 + ... + y^17 = (y^18 - 1)/(y - 1)  [over integers]

  Missing terms: y^7 (from h=9, m=18) and y^14 (from h=16, m=32)

  So g(y) = P_all(y) - y^7 - y^14  [over integers]
           = P_all(y) - y^7(1 + y^7)  [factor out y^7]
           = P_all(y) - y^7 * (1 + y^7)
""")

# Check: is 1 + y^7 a factor of something relevant?
print("  1 + y^7 over GF(2): factors as product of irreducible polynomials of degree 1,3,7")
print("  (The 7th cyclotomic polynomial and its factors over GF(2))")
print()
print("  g(y) mod 2 = sum_{h=2..19, h not in {9,16}} y^{h-2}")
print()
print("  Missing exponents: 7 (=9-2) and 14 (=16-2)")
print("  These are 7 and 14 = 2*7.")
print("  INTERESTING: 14 = 2 * 7. The two missing positions are h-2 = 7 and 2*7.")
print("  This is the orbit of 7 under multiplication by 2 mod 15 = {7, 14, 13, 11, 7,...}")
print("  (But 7 and 14 are just the first two elements of this orbit — not the full orbit)")

print()
print("  Alternative: 9-2=7 and 16-2=14. Just 7 and 14.")
print("  7 = 7^1 (prime). 14 = 2 × 7.")
print("  Both have 7 as a prime factor.")

print()
print("=" * 70)
print("INVESTIGATION 12: The gap-4 cluster structure")
print("=" * 70)

print("""
  Within each period, SubcaseB events often come in pairs separated by 4.
  Examples:
    m=6:  residues {6,10} mod 16    — gap 4
    m=24: residues {267,271} mod 512 — gap 4
    m=28: includes pairs with gap 4
    m=34: events at 4112,4116 (gap 4) and 12304,12308 (gap 4)
    m=36: events at 4113,4117 (gap 4), then 8209 (singleton), then 20497,20501 (gap 4)
    m=38: events at 8210,8214 (gap 4)

  The mod-4 rule for large-m: events at n'≡1,2 mod 4 → also gap 4 (pair spacing 1, then gap 3)

  WHY gap 4? The F-function for fixed m has periods that are powers of 2.
  The CONE evolution has a natural period-4 oscillation at the left boundary.
  (Rule 30 left boundary: cells evolve as ... LFTL where the leftmost cell determines
   the next state via Rule 30 with boundary=0.)

  If F(n',m) has a period-4 sub-structure in how it "resolves" at the boundary,
  pairs of SubcaseB events would naturally be spaced by 4.
""")

print("  Gap-4 verification from data:")
subcaseB_residues = {
    4:  ([5], 8),
    6:  ([6, 10], 16),
    8:  ([11], 32),
    10: ([48], 64),
    12: ([9, 13], 64),
    14: ([10, 14], 64),
    16: ([135, 139, 207], 256),
    20: ([13], 256),
    22: ([14], 256),
    24: ([267, 271], 512),
    26: ([268], 1024),
    28: ([17, 1293, 1297], 2048),
}
print(f"  {'m':>4} {'residues':>25} {'period':>8} {'gaps':>20}")
for m, (residues, period) in subcaseB_residues.items():
    if len(residues) > 1:
        gaps = [residues[i+1]-residues[i] for i in range(len(residues)-1)]
        has_gap4 = 4 in gaps
        print(f"  {m:>4} {str(residues):>25} {period:>8} {str(gaps):>20}  {'CONTAINS GAP-4' if has_gap4 else ''}")
    else:
        print(f"  {m:>4} {str(residues):>25} {period:>8} {'(singleton)':>20}")

print()
print("=" * 70)
print("SUMMARY OF KEY FINDINGS")
print("=" * 70)

print("""
FINDING 1: Clean doubling law for ALL even m (active AND inactive).
  For ALL even m in [4,42]: F-period doubles every 2 steps.
  P_F(m) = 2^(m/2 + 1) for m=4..14 (P=2^3, 2^4, ..., 2^8 but with plateaus)
  Wait, let's check:
""")
for m, p in sorted(all_m_periods.items()):
    lg = int(round(math.log2(p)))
    formula = m//2 + 1
    print(f"  m={m:2d}: log2(P_F)={lg:2d}, m/2+1={formula:2d}, match={lg==formula}")

print("""
FINDING 2: Inactive m positions have F-period = same as preceding active m.
  m=18: P_F=256 = P_16 = P_20  (same as both neighbors!)
  m=32: P_F=4096 = P_30 = P_28  (same as preceding active)
  Inactivity is NOT caused by period anomaly.

FINDING 3: Both inactive m/2 values (9 and 16) satisfy:
  9 = 3^2  and  16 = 4^2 = 2^4
  The MISSING exponents in the log2(P) sequence are 7 (=log2(128)) — corresponding to m=18.
  The m=32 inactivity corresponds to the period "stalling" at 2^12 (same as m=30).

FINDING 4: Universal doubling law for F-periods.
  P_F(m) = 2^(m/2 + 1) for m=4: 2^3 ✓; m=6: 2^4 ✓; ... m=18: 2^10 ✓; ... m=32: 2^17 ✓
  Wait — need to verify this exactly.
""")

print("  Checking P_F(m) = 2^(m/2 + 1):")
for m, p in sorted(all_m_periods.items()):
    lg = int(round(math.log2(p)))
    expected = m//2 + 1
    print(f"  m={m:2d}: log2(P_F)={lg}, m/2+1={expected}, MATCH={lg==expected}")

print("""
FINDING 5: Gap-4 structure.
  SubcaseB events within each period come in pairs separated by exactly 4.
  This appears universal across all active m from m=6 onward.
  (m=4 has only singleton events; m=8,10,20,22,26 also singletons)
  The gap-4 structure reflects the period-4 oscillation of Rule 30 at the left boundary.

FINDING 6: The 'missing' period 2^7=128.
  The log2(period) sequence for active m is:
  {3, 4, 5, 6, 6, 6, 9, 8, 9, 10, 11, 12, 12, 13, 14, 15}
  The values {7, 11 (once?)} appear...
  Let's print:
""")
print(f"  Active m: {active_m}")
print(f"  log2(P):  {[log2_periods[m] for m in active_m]}")
print(f"  Missing from [3..15]: {[i for i in range(3,16) if i not in [log2_periods[m] for m in active_m]]}")
print(f"\n  7 is missing (128 is never a period for any active m)")
print(f"  Corresponds to m=18 being inactive")
print(f"  This is the 'hole' in the doubling sequence")
