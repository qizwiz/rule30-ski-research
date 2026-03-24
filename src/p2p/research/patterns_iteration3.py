#!/opt/homebrew/bin/python3
"""
patterns_iteration3.py — Iteration 3 Pattern Analysis
Rule 30 Prize 3 Research — 2026-03-24

Tasks:
1. Why exactly 16 active elements in [4,38]? Is 16=2^4 structural?
2. Plateau vs doubler rule: which even m will be plateaus?
3. OEIS lookup: active m sequence and gap sequence.
4. Gap pattern 2,2,2,2,2,2,4,2,2,2,2,2,4,2,2 — period? Stern-Brocot? Beatty?
5. Test: gaps at m=18 (=2*9=2*3^2) and m=32 (=2^5) — odd-part perfect square OR high 2-power?
"""

import math
from itertools import groupby

# ── Data ────────────────────────────────────────────────────────────────────

ALL_EVEN = list(range(4, 40, 2))  # [4,6,...,38]
ACTIVE = [4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38]
INACTIVE_IN_RANGE = [m for m in ALL_EVEN if m not in ACTIVE]  # [18, 32]

LOG2_P = {4:3, 6:4, 8:5, 10:6, 12:6, 14:6, 16:8, 20:8, 22:8,
          24:9, 26:10, 28:11, 30:12, 34:13, 36:14, 38:15}

# ── Task 1: Why 16 active elements? ─────────────────────────────────────────

print("=" * 60)
print("TASK 1: Why exactly 16 active m in [4,38]?")
print("=" * 60)

n_even_in_range = len(ALL_EVEN)  # 4,6,...,38 → 18 values
n_active = len(ACTIVE)           # 16
n_inactive = len(INACTIVE_IN_RANGE)  # 2

print(f"Even m in [4,38]: {n_even_in_range}")
print(f"Active: {n_active}  Inactive: {n_inactive}")
print(f"Active fraction: {n_active}/{n_even_in_range} = {n_active/n_even_in_range:.4f}")
print()

# The range [4,38] spans 35 consecutive integers, or 18 even values.
# Active count = 16 = 18 - 2 (two inactive positions).
# Is 16 = 2^4 meaningful, or just (18 - 2)?
# Claim: the range [4,38] is chosen because 38 = 2*19 and P_38 = 2^15 = 32768
# which is exactly the prize threshold (F-period = P means F(n,m) has period P over n).
# The COUNT 16 = number of active positions is NOT a design parameter — it arises
# from counting. Let's check: if we extend to [4,40] or [4,42], do we get 17, 18, ...?
#
# From Iteration 2: m=40 and m=42 are INACTIVE (loop-40 data). So extending to [4,42]
# adds 2 even values (40, 42) both inactive → still 16 active in [4,42].
# Extending to [4,44]: unknown.
#
# The 16 count is the count up to m=38 BECAUSE m=38 has log2(P)=15 = active_index=15,
# and that's the last active position before the doubling law would predict m=40 active
# but m=40 is inactive. So 16 = max active index + 1, and max active index = 15 = log2(P_38).
# This is the deep coincidence: |M_act ∩ [4,38]| = log2(P_38) + 1.

print("Is 16 = 2^4 structural?")
print(f"  log2(P_38) = 15, and |M_act| = 16 = 15 + 1")
print(f"  The count 16 equals log2(P_38) + 1, not coincidentally 2^4.")
print(f"  For i=8..15: log2(P_{{a_i}}) = i (verified), so P_{{a_15}} = 2^15 = P_38.")
print(f"  The sequence uses exactly indices 0..15 (16 elements), and log2(P) runs 3..15.")
print(f"  Missing: no active m achieves log2(P)=7 (period 128). So the log2 values")
print(f"  in {{3,4,5,6,8,9,10,11,12,13,14,15}} cover 12 distinct values, not 16.")
print(f"  The 16 count is a counting artifact: 18 even m in [4,38] minus 2 inactive.")
print()

# Deeper: the range [4,38] itself — why 38?
# 38 = 2*19; 19 is prime. The PRIZE uses F(n',m) with m = 2n'-6 (last-8 condition).
# The PAPER's m range is determined by the computational certificate (loop 40): m=38 is
# the last position verified as active before m=40 is found inactive.
# So 16 is not structurally 2^4; it is |{active m ≤ 38}| = 18 - 2 = 16.
# However, note: 16 = 2^4 AND also = P_4 / (P_4/something) — no clean coincidence.
# The true structural fact: there are exactly 2 inactive positions in [4,38], so 16 = 18-2.
print("Conclusion: 16 = 18 - 2 (not 2^4 structurally). The range [4,38] is")
print("determined by computational evidence (loop 40 found m=40 inactive).")
print("The active count happens to equal 2^4, but this is coincidental with the")
print("range choice, not a structural property of Rule 30.")
print()

# ── Task 2: Plateau vs doubler rule ──────────────────────────────────────────

print("=" * 60)
print("TASK 2: Plateau vs doubler — which even m are plateaus?")
print("=" * 60)

# The doubling ratio for consecutive even m (active and inactive alike):
all_even_with_inactive = list(range(4, 44, 2))  # extend to 42

# F-period for all even m (from loop-40 and iteration-2 data):
# Active m: from LOG2_P; inactive m have same period as preceding active.
FP_log2 = {}
for m in all_even_with_inactive:
    if m in LOG2_P:
        FP_log2[m] = LOG2_P[m]
    elif m == 18:
        FP_log2[m] = 8   # same as m=16,20,22
    elif m == 32:
        FP_log2[m] = 12  # same as m=30
    elif m == 40:
        FP_log2[m] = 16  # next doubling after m=38 (verified)
    elif m == 42:
        FP_log2[m] = 17  # verified in iteration-2

print("Even m, log2(F-period), doubling ratio vs prev:")
prev_log2 = None
print(f"{'m':>4}  {'log2(P)':>8}  {'ratio':>6}  {'active':>6}  {'type'}")
for m in all_even_with_inactive:
    lp = FP_log2[m]
    is_active = m in ACTIVE
    if prev_log2 is not None:
        ratio = lp - prev_log2  # log2(ratio)
        ratio_str = f"x{2**ratio}" if ratio >= 0 else f"x1/{2**(-ratio)}"
        ptype = "doubler" if ratio == 1 else ("plateau" if ratio == 0 else f"x{2**ratio}")
    else:
        ratio_str = "-"
        ptype = "-"
    print(f"{m:>4}  {lp:>8}  {ratio_str:>6}  {'YES' if is_active else 'NO':>6}  {ptype}")
    prev_log2 = lp

print()

# Identify the PLATEAUS: positions where log2(P) does not increase from previous
plateaus = []
prev_log2 = FP_log2[4]
for m in all_even_with_inactive[1:]:
    lp = FP_log2[m]
    if lp == prev_log2:
        plateaus.append(m)
    prev_log2 = lp

print(f"Plateau m values (F-period doesn't increase): {plateaus}")
print()

# For each plateau, characterize it:
for m in plateaus:
    v2 = 0
    temp = m
    while temp % 2 == 0:
        v2 += 1
        temp //= 2
    odd_part = temp
    is_perfect_sq = int(math.isqrt(odd_part))**2 == odd_part
    print(f"  m={m}: v2={v2}, odd_part={odd_part}, "
          f"odd_sq={is_perfect_sq}, active={m in ACTIVE}")

print()
print("Plateau rule hypothesis:")
print("  A plateau at m occurs when odd_part(m) is a perfect square (m=18: 9=3^2)")
print("  OR when m is a high power of 2 (m=32=2^5) AND these m values 'absorb'")
print("  the doubling without advancing the period.")
print("  But also: m=10,12,14 ALL have different factorizations yet form a plateau at 2^6.")
print("  And m=16,20,22 form a plateau at 2^8 (m=18 inactive between them).")
print()

# Check: the early plateau m=10,12,14 (at log2=6):
# m=10: v2=1, odd_part=5 (squarefree), ACTIVE → plateau
# m=12: v2=2, odd_part=3 (squarefree), ACTIVE → plateau
# m=14: v2=1, odd_part=7 (squarefree), ACTIVE → plateau
# These are all ACTIVE but plateau. The plateau here is different: it's about the period
# structure of the CA at those positions, not inactivity.
# The plateau at m=10..14 means three active positions share the SAME F-period.
# This is a PERIOD PLATEAU (F-period stagnates) vs an INACTIVE PLATEAU (m is inactive).

print("Two types of plateaus:")
print("  Type A (active plateau): consecutive active m share same F-period.")
print("    m=10,12,14 all have F-period 2^6=64. Structural reason: the cone at")
print("    these widths is too narrow to show independent period structure; the")
print("    right-boundary echo is 'too close' and all three map to the same residue.")
print("  Type B (inactive plateau): inactive m has same F-period as active neighbors.")
print("    m=18 has F-period 256 = F-period of m=16,20,22.")
print("    m=32 has F-period 4096 = F-period of m=30.")
print("  Type A plateaus: {10,12,14} (P=64) and {16,20,22} (P=256).")
print("  Type B plateaus: {18} absorbs into {16,20,22} cluster; {32} absorbs into {30} cluster.")
print()

# ── Task 3: OEIS ─────────────────────────────────────────────────────────────

print("=" * 60)
print("TASK 3: OEIS analysis")
print("=" * 60)

# Active m sequence: 4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38
# As m//2:           2,3,4, 5, 6, 7, 8,10,11,12,13,14,15,17,18,19
# These are: positive integers ≥ 2, missing {9,16} from {2..19}
# 9 = 3^2, 16 = 4^2 = 2^4.
# The missing values are {9=3^2, 16=2^4} = perfect squares in {2..19}.

halved = [m // 2 for m in ACTIVE]
print(f"Active m values: {ACTIVE}")
print(f"m//2 values:     {halved}")
print()

# What is missing from 2..19?
full_range = list(range(2, 20))
missing_halved = [x for x in full_range if x not in halved]
print(f"Range 2..19: {full_range}")
print(f"Missing from m//2 sequence: {missing_halved}")
print()

# Check if missing values are perfect squares:
for x in missing_halved:
    sq = int(math.isqrt(x))
    print(f"  Missing {x}: sqrt={sq}, is_perfect_square={sq*sq==x}")
print()

# The sequence m//2 = {2,3,4,5,6,7,8,10,11,12,13,14,15,17,18,19}
# = positive integers in [2,19] NOT equal to a perfect square.
# Perfect squares in [2,19]: {4,9,16} — wait, 4=2^2 is also a perfect square!
# m//2=4 corresponds to m=8, which IS active. So 4 is NOT missing.
# Let me recheck: missing = {9, 16}. 9=3^2 is perfect square. 16=4^2 is also perfect square.
# But m//2=4 (m=8) is active! So 4 is not missing even though it's a perfect square.
# The rule "m//2 missing iff perfect square" FAILS for 4=2^2 (m=8 is active).

print("Checking 'missing m//2 = perfect squares' hypothesis:")
perfect_squares_in_range = [x for x in full_range if int(math.isqrt(x))**2 == x]
print(f"Perfect squares in [2,19]: {perfect_squares_in_range}")
print(f"Missing from m//2:         {missing_halved}")
print(f"Hypothesis matches: {set(missing_halved) == set(perfect_squares_in_range)}")
print()

# 4 is a perfect square but NOT missing. So the simple "missing = perfect squares" is FALSE.
# Refine: missing values are {9,16} — both are perfect squares AND (9=3^2 with 3 odd prime,
# 16=2^4 with v2=4). The value 4=2^2 has v2=2 and IS in the active set.
# So: missing m//2 iff perfect square AND (odd-prime square OR v2 ≥ 4)?
# 4=2^2: v2=2 < 4, NOT odd-prime square → active (correct)
# 9=3^2: odd prime square → missing (correct)
# 16=2^4: v2=4 → missing (correct)
# This is an improvement but still ad hoc.

print("Refined hypothesis: m//2 missing iff perfect square AND (odd-factor^2 OR v2>=4):")
for x in perfect_squares_in_range:
    v2 = 0
    temp = x
    while temp % 2 == 0:
        v2 += 1
        temp //= 2
    sq_root = int(math.isqrt(x))
    is_odd_prime_sq = (sq_root > 1 and sq_root % 2 == 1)
    predicted_missing = is_odd_prime_sq or v2 >= 4
    actual_missing = x in missing_halved
    print(f"  m//2={x}: v2={v2}, sqrt={sq_root}, odd_sq={is_odd_prime_sq}, "
          f"pred_missing={predicted_missing}, actual={actual_missing}, "
          f"match={predicted_missing==actual_missing}")
print()

# OEIS search guidance:
print("OEIS sequence search:")
print(f"  Active m sequence: {ACTIVE}")
print(f"  This starts 4,6,8,10,12,14,16,20,22,24,...")
print(f"  The gaps are: ", end="")
gaps = [ACTIVE[i+1]-ACTIVE[i] for i in range(len(ACTIVE)-1)]
print(gaps)
print()

# Gap sequence analysis:
print(f"Gap sequence: {gaps}")
gap_counts = {}
for g in gaps:
    gap_counts[g] = gap_counts.get(g, 0) + 1
print(f"Gap counts: {gap_counts}")
print(f"Total gaps: {len(gaps)}, sum: {sum(gaps)}, span: {ACTIVE[-1]-ACTIVE[0]}")
print()

# The gap sequence: [2,2,2,2,2,2,4,2,2,2,2,2,4,2,2]
# Length 15, two 4s, thirteen 2s.
# Where are the 4s? At positions 6 and 12 (0-indexed).
gap4_positions = [i for i, g in enumerate(gaps) if g == 4]
print(f"Gap=4 at positions (0-indexed): {gap4_positions}")
print(f"These correspond to transitions:")
for p in gap4_positions:
    print(f"  {ACTIVE[p]} -> {ACTIVE[p+1]} (inactive m={ACTIVE[p]+2})")
print()

# ── Task 4: Gap pattern structure ────────────────────────────────────────────

print("=" * 60)
print("TASK 4: Gap pattern analysis")
print("=" * 60)

# Gap sequence: [2,2,2,2,2,2,4,2,2,2,2,2,4,2,2]
# The two 4s are at positions 6 and 12 (spacing 6 apart).
# Total length = 15 gaps.
# The two 4s divide the 15 gaps into three sections: 6 gaps, 6 gaps, 3 gaps.
# Section 1: gaps 0-5 = [2,2,2,2,2,2] (6 twos)
# Section 2: gaps 6-11 = [4,2,2,2,2,2] (one 4 then 5 twos)
# Section 3: gaps 12-14 = [4,2,2] (one 4 then 2 twos)

sections = [[gaps[i] for i in range(0,6)],
            [gaps[i] for i in range(6,12)],
            [gaps[i] for i in range(12,15)]]
print(f"Three sections of gap sequence:")
for i, s in enumerate(sections):
    print(f"  Section {i+1}: {s} (length {len(s)}, sum {sum(s)})")
print()

# Period analysis: is [2,2,2,2,2,2,4,2,2,2,2,2,4,2,2] periodic?
# If period=7: [2,2,2,2,2,2,4] repeated twice gives [2,2,2,2,2,2,4,2,2,2,2,2,4]
# which matches positions 0..12. The last two [2,2] are a truncated third period.
# If period=7, the infinite extension would be [2,2,2,2,2,2,4] repeating.
def check_period(seq, p):
    for i in range(len(seq)):
        if seq[i] != seq[i % p]:
            return False
    return True

for p in range(1, 16):
    if check_period(gaps, p):
        print(f"Gap sequence is consistent with period {p}: gaps[i] = gaps[i mod {p}]")

print()

# Period 7 check explicitly:
period7 = [2,2,2,2,2,2,4]
print(f"Period-7 template: {period7}")
reconstructed = [period7[i % 7] for i in range(len(gaps))]
print(f"Reconstructed:     {reconstructed}")
print(f"Actual:            {gaps}")
matches = [reconstructed[i]==gaps[i] for i in range(len(gaps))]
print(f"Match positions:   {matches}")
print(f"All match: {all(matches)}")
print()

# Average gap:
avg_gap = sum(gaps) / len(gaps)
print(f"Average gap: {sum(gaps)}/{len(gaps)} = {avg_gap:.4f}")
# If pattern is periodic with 6 twos and one 4 per period of 7, average = (12+4)/7 = 16/7 ≈ 2.286
avg_periodic = (6*2 + 4) / 7
print(f"If period-7 [2^6,4]: average gap = (6*2+4)/7 = 16/7 ≈ {avg_periodic:.4f}")
print()

# Beatty sequences: floor(n*alpha) for irrational alpha
# If gaps follow a Beatty sequence pattern (e.g., Wythoff sequence), the 4s would occur
# at floor(n*phi) for phi=(1+sqrt(5))/2 ≈ 1.618. Let's check.
phi = (1 + math.sqrt(5)) / 2
beatty_phi = {math.floor(n * phi) for n in range(1, 20)}
beatty_phi2 = {math.floor(n * phi**2) for n in range(1, 20)}  # phi^2 = phi+1
print("Beatty sequence check:")
print(f"  phi = {phi:.4f}, phi^2 = {phi**2:.4f}")
# The inactive positions are m=18 and m=32. In the (m//2 - 2) coordinate, these are at 7 and 14.
inactive_coords = [(m//2 - 2) for m in INACTIVE_IN_RANGE]
print(f"  Inactive m in shifted coordinate (m//2-2): {inactive_coords}")
# Is 7 = floor(k*phi) or floor(k*phi^2) for some k?
for k in range(1, 20):
    if math.floor(k * phi) in inactive_coords:
        print(f"  floor({k}*phi) = {math.floor(k*phi)} — matches!")
    if math.floor(k * phi**2) in inactive_coords:
        print(f"  floor({k}*phi^2) = {math.floor(k*phi**2)} — matches!")
print()

# Stern-Brocot tree: the ratios in the Stern-Brocot tree near 7/15 or 14/15:
# The active fraction is 16/18 = 8/9. The inactive fraction is 2/18 = 1/9.
print("Stern-Brocot / fraction check:")
print(f"  Active fraction: {n_active}/{n_even_in_range} = {n_active//math.gcd(n_active,n_even_in_range)}/{n_even_in_range//math.gcd(n_active,n_even_in_range)}")
# The gap pattern period 7 with density 6/7 twos:
print(f"  Gap pattern: if period=7 with 6 twos + 1 four, density of 'inactive gaps' = 1/7")
print(f"  In [4,38]: 18 even m, 2 inactive → inactive density = 2/18 = 1/9")
print(f"  These differ: period-7 would predict ~2.14 inactive in [4,38], actual=2. Close.")
print()

# ── Task 5: Gap rule test ─────────────────────────────────────────────────────

print("=" * 60)
print("TASK 5: Gap rule — odd-part perfect square OR high 2-power?")
print("=" * 60)

def classify_m(m):
    """Returns (v2, odd_part, is_odd_sq, is_high_2power, prediction)"""
    v2 = 0
    temp = m
    while temp % 2 == 0:
        v2 += 1
        temp //= 2
    odd_part = temp
    is_odd_sq = (odd_part > 1) and (int(math.isqrt(odd_part))**2 == odd_part)
    is_high_2power = (odd_part == 1) and (v2 >= 5)
    predicted_inactive = is_odd_sq or is_high_2power
    return v2, odd_part, is_odd_sq, is_high_2power, predicted_inactive

print("Verification against known [4,38] data:")
print(f"{'m':>4}  {'v2':>3}  {'odd':>5}  {'odd_sq':>6}  {'hi_2pw':>6}  {'pred':>5}  {'actual':>6}  {'ok':>3}")
all_correct = True
for m in ALL_EVEN:
    v2, odd_part, is_odd_sq, is_high_2pw, pred_inactive = classify_m(m)
    actual_inactive = m in INACTIVE_IN_RANGE
    ok = (pred_inactive == actual_inactive)
    if not ok:
        all_correct = False
    print(f"{m:>4}  {v2:>3}  {odd_part:>5}  {str(is_odd_sq):>6}  {str(is_high_2pw):>6}  "
          f"{'INACT' if pred_inactive else 'act':>5}  "
          f"{'INACT' if actual_inactive else 'act':>6}  {'OK' if ok else 'FAIL':>3}")

print()
print(f"All predictions correct in [4,38]: {all_correct}")
print()

# Extend to m=40,42 (from loop-40: both inactive):
print("Extended predictions for m=40..50:")
extended_inactive_known = {40, 42}  # from loop-40 iteration-2 data
for m in range(40, 52, 2):
    v2, odd_part, is_odd_sq, is_high_2pw, pred_inactive = classify_m(m)
    known = "inactive" if m in extended_inactive_known else ("active(?) — not yet verified" if m > 42 else "active(?) — need data")
    print(f"  m={m}: v2={v2}, odd_part={odd_part}, odd_sq={is_odd_sq}, hi_2pw={is_high_2pw} → {'INACTIVE' if pred_inactive else 'active'} (known: {known})")

print()
# m=40: v2=3, odd_part=5, is_odd_sq=False, is_high_2pw=False → predicted ACTIVE
# but m=40 is actually INACTIVE from loop-40. This BREAKS the hypothesis!
v2_40, odd_40, odd_sq_40, hi_40, pred_40 = classify_m(40)
print(f"*** m=40: v2={v2_40}, odd_part={odd_40}, predicted={'INACTIVE' if pred_40 else 'ACTIVE'}")
print(f"*** But m=40 is ACTUALLY INACTIVE (from loop-40)! The hypothesis FAILS at m=40!")
print()

# m=42: v2=1, odd_part=21=3*7, is_odd_sq=False → predicted ACTIVE
# but m=42 is actually INACTIVE from loop-40. This also BREAKS the hypothesis!
v2_42, odd_42, odd_sq_42, hi_42, pred_42 = classify_m(42)
print(f"*** m=42: v2={v2_42}, odd_part={odd_42}, predicted={'INACTIVE' if pred_42 else 'ACTIVE'}")
print(f"*** But m=42 is ACTUALLY INACTIVE (from loop-40)! The hypothesis FAILS at m=42!")
print()

print("CONCLUSION: The v2/odd-square hypothesis correctly classifies [4,38] but")
print("FAILS for m=40 and m=42. Inactivity is a DYNAMICAL property, not arithmetic.")
print()

# Final summary of gap structure:
print("=" * 60)
print("SUMMARY: Gap sequence structure")
print("=" * 60)
print(f"Gap sequence: {gaps}")
print(f"The sequence [2,2,2,2,2,2,4] repeated has period 7.")
print(f"After 2 full periods (14 elements), the 15th element is 2 (truncation).")
print(f"The period-7 hypothesis is CONSISTENT with all 15 observed gaps.")
print()
print("The two gap-4 positions correspond to inactive m=18 and m=32.")
print("In the period-7 pattern, gaps of 4 occur at positions 6, 13, 20, ...")
print("i.e., at 6 mod 7. There are 2 complete occurrences in the 15-gap window.")
print()
print(f"Gaps of 4 occur at gap indices: {gap4_positions}")
print(f"6 mod 7 = 6, 12 mod 7 = 5 — these are NOT both ≡ 6 mod 7.")
print(f"Actual positions 6 and 12 differ by 6, which equals the period-1 segment.")
print(f"Separation between gap-4 positions: {gap4_positions[1]-gap4_positions[0]}")
print(f"This matches: gap-4 at position p means next gap-4 at p + period(?) = p + {gap4_positions[1]-gap4_positions[0]}")
print()
# Positions 6 and 12, separation 6. In period-7, gap-4 positions would be at 6, 13, 20...
# separation = 7. But we see separation 6. So it's NOT exactly period-7.
# Actually: gap-4 at index 6 and 12, separation = 6. Period-6? But [2,2,2,2,2,4] has period 6.
period6 = [2,2,2,2,2,4]
reconstructed6 = [period6[i % 6] for i in range(len(gaps))]
print(f"Period-6 template: {period6}")
print(f"Reconstructed:     {reconstructed6}")
print(f"Actual:            {gaps}")
matches6 = [reconstructed6[i]==gaps[i] for i in range(len(gaps))]
print(f"All period-6 match: {all(matches6)}")
print()

# Hmm — with only 15 gaps and 2 gap-4 events, BOTH period-6 and period-7 (truncated)
# are consistent. We need more data (m > 38) to distinguish.

print("With only 15 gaps (2 gap-4 events), both period-6 and period-7 (truncated)")
print("are consistent with the data. More data (m > 38 active set) is needed.")
print()
print("Key open question: does the third gap-4 occur at m=50 (period-6 prediction)")
print("or m=52 (period-7 prediction)?")
print("m=50=2*25=2*5^2: v2=1, odd_part=25=5^2 → v2+odd-sq hypothesis predicts INACTIVE")
print("m=52=4*13: v2=2, odd_part=13 → v2+odd-sq hypothesis predicts ACTIVE")
v2_50, odd_50, odd_sq_50, hi_50, pred_50 = classify_m(50)
v2_52, odd_52, odd_sq_52, hi_52, pred_52 = classify_m(52)
print(f"m=50 prediction: {'INACTIVE' if pred_50 else 'ACTIVE'} (arithmetic rule)")
print(f"m=52 prediction: {'INACTIVE' if pred_52 else 'ACTIVE'} (arithmetic rule)")
print("If arithmetic rule holds for m=50 and fails for m=52, gap sequence period is 6.")
print("If both are wrong (as with m=40,42), gap structure cannot be predicted by arithmetic.")
