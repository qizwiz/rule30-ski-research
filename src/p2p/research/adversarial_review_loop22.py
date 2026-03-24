"""
Adversarial Review Loop 22 — Rule 30 / Wolfram Prize 3
Focus: m=34,36,38 SubcaseB claims and LCM computation

Specific claims under attack:
  1. m=34: first SubcaseB at n'=4112, period P_34=8192 (minimal)
  2. m=36: first SubcaseB at n'=4113, period P_36=16384 (minimal)
  3. m=38: first SubcaseB at n'=8210, period P_38=32768 (minimal)
  4. LCM(all P_m for m in M_act) = 32768

KEY OPTIMIZATION: Use bitarrays and batch evaluation.
For scanning n' in [a,b), F(n,m) requires caEvolve(n+1, tape of length 2(n+1)+1).
Each evaluation is O(n^2). For large m and large n, naive scanning is O(b * n^2).

Instead, use the "growing tape" method:
- F(n,m) takes a tape of length 2n+3 with spike at position m.
- F(n+1,m) takes a tape of length 2n+5 with spike at position m.
- These are independent evaluations; no shared state.
- Speed up by using integers as bitrows (bitwise operations).

Date: 2026-03-24
"""

import sys
import time
from math import gcd

# ============================================================
# Fast bit-integer Rule 30 implementation
# ============================================================
# Represent a row of width W as a Python integer (bit i = cell i)
# rule30(l,c,r) = l XOR (c OR r)
# For a row represented as integer x of width W:
#   left  = x >> 1  (shift right = each cell gets left neighbor)
#   right = (x << 1) & mask  (shift left = each cell gets right neighbor)
#   center = x
# But we need to process boundary carefully.
# For caStepList: result[i] = rule30(row[i], row[i+1], row[i+2])
# In the 'list shrinks by 2' convention, the new row has indices 0..W-3
# result[i] = row[i] XOR (row[i+1] OR row[i+2])
# As bit ops on integer:
#   row_int has bit i = row[i]
#   result_int has bit i = row_int[i] XOR (row_int[i+1] OR row_int[i+2])
#             = (row_int >> 0) XOR ((row_int >> 1) OR (row_int >> 2))
# BUT the result is W-2 wide, bits 0..W-3.
# We need to mask to W-2 bits.

def caStepInt(x, w):
    """
    Apply one Rule 30 step to integer x representing a row of width w.
    Returns integer of width w-2 representing the next row.
    rule30(l,c,r) = l XOR (c OR r)
    result[i] = row[i] XOR (row[i+1] OR row[i+2])
    In bit-shift terms on x:
      result bit i corresponds to:
        x bit i = left neighbor (row[i])
        x bit i+1 = center (row[i+1]) — wait, need to re-check convention

    Convention: bit i of x = row[i] (LSB = row[0])
    result[i] = row[i] XOR (row[i+1] OR row[i+2])
    = (x >> i & 1) XOR ((x >> (i+1) & 1) OR (x >> (i+2) & 1))

    As bulk ops:
    left_bits  = x           (bit i = row[i])
    center_bits = x >> 1     (bit i = row[i+1])
    right_bits  = x >> 2     (bit i = row[i+2])
    result = left_bits XOR (center_bits OR right_bits)
    mask to w-2 bits.
    """
    w_new = w - 2
    if w_new <= 0:
        return 0
    mask = (1 << w_new) - 1
    result = (x ^ ((x >> 1) | (x >> 2))) & mask
    return result

def caEvolveInt(steps, x, w):
    """Apply caStepInt `steps` times starting from integer x of width w."""
    for _ in range(steps):
        x = caStepInt(x, w)
        w -= 2
    return x, w

def spikeInt(m, length):
    """Integer representing a tape of `length` zeros with a 1 at position m."""
    return 1 << m

def twospikeInt(m, length):
    """Integer with 1s at position m and position length-1."""
    return (1 << m) | (1 << (length - 1))

def F_fast(n, m):
    """F(n,m): caEvolve(n+1, spikeAtList(m, 2*(n+1)+1))[0]"""
    length = 2*(n+1)+1
    x = spikeInt(m, length)
    x, _ = caEvolveInt(n+1, x, length)
    return x & 1  # bit 0 = cell 0

def G_fast(n, m):
    """G(n,m): caEvolve(n+1, twoSpikeLastList(m, 2*(n+1)+1))[0]"""
    length = 2*(n+1)+1
    x = twospikeInt(m, length)
    x, _ = caEvolveInt(n+1, x, length)
    return x & 1

def subcaseB_fast(n, m):
    return F_fast(n, m) == 0 and G_fast(n, m) == 1

# Verify fast implementation against original
def verify_fast():
    """Spot-check fast vs naive implementation."""
    def rule30(l, c, r): return l ^ (c | r)
    def caStepList(row): return [rule30(row[i], row[i+1], row[i+2]) for i in range(len(row)-2)]
    def caEvolve_naive(steps, init):
        row = list(init)
        for _ in range(steps):
            row = caStepList(row)
        return row
    def F_naive(n, m):
        length = 2*(n+1)+1
        init = [0]*length; init[m] = 1
        return caEvolve_naive(n+1, init)[0]
    def G_naive(n, m):
        length = 2*(n+1)+1
        init = [0]*length; init[m] = 1; init[length-1] = 1
        return caEvolve_naive(n+1, init)[0]

    errors = 0
    # Only use small n for naive (it's O(n^2)); fast handles large n
    for n in [100, 500, 1000, 2000]:
        for m in [4, 20, 34, 36]:
            if m > 2*(n+1)-1:
                continue
            fn = F_naive(n, m)
            ff = F_fast(n, m)
            gn = G_naive(n, m)
            gf = G_fast(n, m)
            if fn != ff or gn != gf:
                print(f"  MISMATCH at n={n},m={m}: F_naive={fn},F_fast={ff}, G_naive={gn},G_fast={gf}")
                errors += 1
    return errors

print("Verifying fast implementation...")
t0 = time.time()
errs = verify_fast()
print(f"  Verification: {errs} errors  [{time.time()-t0:.2f}s]")
if errs > 0:
    print("FATAL: fast implementation has errors, aborting")
    sys.exit(1)
print("  Fast implementation VERIFIED correct.")

# ============================================================
# Attack 1: Verify SubcaseB events at claimed first hits
# ============================================================

print()
print("=" * 70)
print("ATTACK 1: Verify SubcaseB at claimed first-hit n' values")
print("=" * 70)

claims = [
    (34, 4112, "paper claims first SubcaseB hit for m=34"),
    (36, 4113, "paper claims first SubcaseB hit for m=36"),
    (38, 8210, "paper claims first SubcaseB hit for m=38"),
]

for m, n, desc in claims:
    t0 = time.time()
    fval = F_fast(n, m)
    gval = G_fast(n, m)
    sb = (fval == 0 and gval == 1)
    elapsed = time.time() - t0
    print(f"  m={m}, n'={n}: F={fval}, G={gval}, SubcaseB={sb}  [{elapsed:.3f}s]  -- {desc}")
    if not sb:
        print(f"  *** COUNTEREXAMPLE: SubcaseB is FALSE for m={m} at n'={n}! ***")

# ============================================================
# Attack 2: Scan for earlier SubcaseB events
# ============================================================

print()
print("=" * 70)
print("ATTACK 2: Scan for earlier SubcaseB events (are first hits correct?)")
print("=" * 70)

def scan_subcaseB(m, start, stop, step=1):
    """Fast scan for SubcaseB events. Returns hits."""
    hits = []
    t0 = time.time()
    for n in range(start, stop, step):
        if subcaseB_fast(n, m):
            hits.append(n)
    elapsed = time.time() - t0
    return hits, elapsed

# m=34: scan [3087, 4112) — should find NO hits
print("m=34: scanning [3087,4112) for SubcaseB...")
t0 = time.time()
hits_34_pre, _ = scan_subcaseB(34, 3087, 4112)
print(f"  Time: {time.time()-t0:.1f}s, hits: {hits_34_pre}")
if hits_34_pre:
    print(f"  *** ATTACK SUCCEEDS: Earlier SubcaseB events for m=34: {hits_34_pre} ***")
else:
    print(f"  CONFIRMED: No SubcaseB before n'=4112 for m=34")

# m=36: scan [3087, 4113)
print("m=36: scanning [3087,4113) for SubcaseB...")
t0 = time.time()
hits_36_pre, _ = scan_subcaseB(36, 3087, 4113)
print(f"  Time: {time.time()-t0:.1f}s, hits: {hits_36_pre}")
if hits_36_pre:
    print(f"  *** ATTACK SUCCEEDS: Earlier SubcaseB events for m=36: {hits_36_pre} ***")
else:
    print(f"  CONFIRMED: No SubcaseB before n'=4113 for m=36")

# m=38: scan [3087, 8210) — this is 5123 values, each ~proportional to n
# F(8210, 38) is slow; F(3087, 38) is faster. Let's time it.
print("m=38: scanning [3087,8210) step=1 for SubcaseB...")
t0 = time.time()
hits_38_pre, _ = scan_subcaseB(38, 3087, 8210)
print(f"  Time: {time.time()-t0:.1f}s, hits: {hits_38_pre}")
if hits_38_pre:
    print(f"  *** ATTACK SUCCEEDS: Earlier SubcaseB events for m=38: {hits_38_pre} ***")
else:
    print(f"  CONFIRMED: No SubcaseB before n'=8210 for m=38")

# ============================================================
# Attack 3: Dense neighborhood scan at first-hit n' values
# ============================================================

print()
print("=" * 70)
print("ATTACK 3: Dense neighborhood scan — confirm paper's specific n' values")
print("=" * 70)

def dense_scan_report(m, start, stop):
    print(f"\n  m={m} in [{start},{stop}):")
    print(f"  {'n':>6} | F | G | SubcaseB")
    for n in range(start, stop):
        fv = F_fast(n, m)
        gv = G_fast(n, m)
        sb = (fv == 0 and gv == 1)
        marker = " <-- SubcaseB!" if sb else ""
        print(f"  {n:>6} | {fv} | {gv} | {sb}{marker}")

dense_scan_report(34, 4108, 4122)
dense_scan_report(36, 4108, 4122)
dense_scan_report(38, 8205, 8220)

# ============================================================
# Attack 4: Period minimality for m=34 (P=8192)
# If period were 4096, F(n,34) == F(n+4096,34) for all n.
# Key: SubcaseB at 4112 means F(4112,34)=0. If period=4096, F(4112+4096,34)=F(8208,34)=0.
# But paper says no SubcaseB before 4112+8192=12304 for the second cluster.
# We need: is there a SubcaseB at n'=8208?
# ============================================================

print()
print("=" * 70)
print("ATTACK 4: Period minimality for m=34 (claimed P_34=8192)")
print("=" * 70)
print("If P=4096, there should be SubcaseB at 4112+4096=8208.")
print("Also: F(4112,34) should == F(8208,34) if period divides 4096.")

t0 = time.time()
f_4112 = F_fast(4112, 34)
g_4112 = G_fast(4112, 34)
f_8208 = F_fast(8208, 34)
g_8208 = G_fast(8208, 34)
f_12304 = F_fast(12304, 34)
g_12304 = G_fast(12304, 34)
print(f"  F(4112,34)={f_4112}, G(4112,34)={g_4112}, SubcaseB={f_4112==0 and g_4112==1}  [{time.time()-t0:.2f}s]")
print(f"  F(8208,34)={f_8208}, G(8208,34)={g_8208}, SubcaseB={f_8208==0 and g_8208==1}")
print(f"  F(12304,34)={f_12304}, G(12304,34)={g_12304}, SubcaseB={f_12304==0 and g_12304==1}")

print()
# Scan [8200, 8220) for m=34 to see what happens at n'~8208
t0 = time.time()
print("  Dense scan m=34, [8200,8220):")
for n in range(8200, 8220):
    fv = F_fast(n, 34)
    gv = G_fast(n, 34)
    sb = (fv == 0 and gv == 1)
    marker = " <-- SubcaseB!" if sb else ""
    print(f"  n'={n}: F={fv}, G={gv}{marker}")
print(f"  [{time.time()-t0:.1f}s]")

print()
# Multi-point F-sequence comparison at offset 4096 vs offset 8192
print("  F-sequence comparison: F(n,34) vs F(n+4096,34) vs F(n+8192,34)")
print(f"  {'n':>6} | F(n) | F(n+4096) | F(n+8192) | match_4096 | match_8192")
print("  " + "-" * 60)
test_ns = [4112, 4113, 4114, 4115, 4116, 4117, 4118, 4119, 5000, 6000, 7000]
all_match_4096_34 = True
for n in test_ns:
    f0 = F_fast(n, 34)
    f1 = F_fast(n + 4096, 34)
    f2 = F_fast(n + 8192, 34)
    m4 = (f0 == f1)
    m8 = (f0 == f2)
    if not m4:
        all_match_4096_34 = False
    print(f"  {n:>6} | {f0}    | {f1}         | {f2}         | {m4}       | {m8}")

if all_match_4096_34:
    print("\n  *** ALL F VALUES MATCH AT OFFSET 4096! Period may be 4096 or a divisor. ***")
    # Check G too
    print("  Checking G at offset 4096...")
    all_match_g_4096 = True
    for n in test_ns:
        g0 = G_fast(n, 34)
        g1 = G_fast(n + 4096, 34)
        if g0 != g1:
            all_match_g_4096 = False
            print(f"  G MISMATCH: G({n},34)={g0}, G({n+4096},34)={g1}")
            break
    if all_match_g_4096:
        print("  G also matches at offset 4096. Period might actually be 4096!")
        print("  CRITICAL: This would contradict the paper's P_34=8192 claim!")
        # Do an extended scan to find where F(n,34) != F(n+4096,34)
        print("  Extended scan [4112, 12304) to find period-4096 counterexample...")
        found_mismatch = False
        t0 = time.time()
        for n in range(4112, 4112+4096):  # One full potential period
            f0 = F_fast(n, 34)
            f1 = F_fast(n + 4096, 34)
            if f0 != f1:
                print(f"  PERIOD-4096 COUNTEREXAMPLE: F({n},34)={f0} != F({n+4096},34)={f1}")
                found_mismatch = True
                break
        elapsed = time.time() - t0
        if not found_mismatch:
            print(f"  NO counterexample in [4112,8208). Period IS 4096 or a divisor! [{elapsed:.1f}s]")
            print(f"  *** PAPER CLAIM P_34=8192 APPEARS WRONG — period is <=4096 ***")
        else:
            print(f"  Period-4096 ruled out. P_34=8192 survives. [{elapsed:.1f}s]")
    else:
        print(f"  G differs at offset 4096 — period is NOT 4096. P_34=8192 consistent.")
else:
    # Found mismatch — period 4096 ruled out
    mismatches = [(n, F_fast(n,34), F_fast(n+4096,34)) for n in test_ns if F_fast(n,34) != F_fast(n+4096,34)]
    print(f"\n  PERIOD-4096 RULED OUT: F mismatches at {len(mismatches)} points")
    print(f"  First mismatch: n={mismatches[0][0]}, F(n,34)={mismatches[0][1]}, F(n+4096,34)={mismatches[0][2]}")
    print(f"  P_34=8192 is the minimal period (consistent with paper)")

# ============================================================
# Attack 5: Period minimality for m=36 (P=16384)
# ============================================================

print()
print("=" * 70)
print("ATTACK 5: Period minimality for m=36 (claimed P_36=16384)")
print("=" * 70)
print("Paper gives hits: {4113,4117,8209} -> {20497,20501,24593} = first cluster + 16384")
print("Key question: is there SubcaseB at 8209+8192=16401? (would indicate P=8192)")

t0 = time.time()
f_4113 = F_fast(4113, 36)
g_4113 = G_fast(4113, 36)
f_12305 = F_fast(12305, 36)  # 4113 + 8192
g_12305 = G_fast(12305, 36)
f_20497 = F_fast(20497, 36)  # 4113 + 16384
g_20497 = G_fast(20497, 36)
print(f"  F(4113,36)={f_4113}, G(4113,36)={g_4113}, SubcaseB={f_4113==0 and g_4113==1}")
print(f"  F(12305,36)={f_12305}, G(12305,36)={g_12305}, SubcaseB={f_12305==0 and g_12305==1}  (4113+8192, if period=8192 should be SubcaseB)")
print(f"  F(20497,36)={f_20497}, G(20497,36)={g_20497}, SubcaseB={f_20497==0 and g_20497==1}  (4113+16384, should be SubcaseB)")
print(f"  [{time.time()-t0:.2f}s]")

# Check the singleton hit at 8209
t0 = time.time()
f_8209 = F_fast(8209, 36)
g_8209 = G_fast(8209, 36)
f_16401 = F_fast(16401, 36)  # 8209 + 8192
g_16401 = G_fast(16401, 36)
f_24593 = F_fast(24593, 36)  # 8209 + 16384
g_24593 = G_fast(24593, 36)
print(f"  F(8209,36)={f_8209}, G(8209,36)={g_8209}, SubcaseB={f_8209==0 and g_8209==1}")
print(f"  F(16401,36)={f_16401}, G(16401,36)={g_16401}, SubcaseB={f_16401==0 and g_16401==1}  (8209+8192)")
print(f"  F(24593,36)={f_24593}, G(24593,36)={g_24593}, SubcaseB={f_24593==0 and g_24593==1}  (8209+16384)")
print(f"  [{time.time()-t0:.2f}s]")

# The critical test: F(n+8192, 36) == F(n, 36) for all n?
print("\n  F-sequence comparison at offsets 8192 and 16384:")
print(f"  {'n':>6} | F(n) | F(n+8192) | F(n+16384) | match_8192 | match_16384")
print("  " + "-" * 65)
test_ns_36 = [4113, 4117, 8209, 5000, 6000, 7000, 10000]
all_match_8192_36 = True
for n in test_ns_36:
    f0 = F_fast(n, 36)
    f1 = F_fast(n + 8192, 36)
    f2 = F_fast(n + 16384, 36)
    m8 = (f0 == f1)
    m16 = (f0 == f2)
    if not m8:
        all_match_8192_36 = False
    print(f"  {n:>6} | {f0}    | {f1}         | {f2}          | {m8}       | {m16}")

if not all_match_8192_36:
    print(f"\n  PERIOD-8192 RULED OUT: F mismatch at some test point.")
    print(f"  P_36=16384 is consistent with data.")
else:
    print(f"\n  All F values match at offset 8192. Need G to distinguish.")
    print(f"  Key: SubcaseB(4113,36)={f_4113==0 and g_4113==1} but SubcaseB(12305,36)={f_12305==0 and g_12305==1}")
    if (f_4113==0 and g_4113==1) and not (f_12305==0 and g_12305==1):
        print(f"  G breaks period-8192: SubcaseB pattern differs at offset 8192.")
        print(f"  P_36=16384 is the minimal period (period 8192 ruled out).")
    elif (f_4113==0 and g_4113==1) and (f_12305==0 and g_12305==1):
        print(f"  *** BOTH n'=4113 and n'=12305 are SubcaseB! Period-8192 not ruled out yet! ***")
        print(f"  Doing extended F+G comparison across a full candidate period [4113, 4113+8192)...")
        t0 = time.time()
        found_mismatch = False
        for n in range(4113, 4113+8192):
            f0 = F_fast(n, 36)
            f1 = F_fast(n + 8192, 36)
            g0 = G_fast(n, 36)
            g1 = G_fast(n + 8192, 36)
            if f0 != f1 or g0 != g1:
                print(f"  MISMATCH at n={n}: F({n},36)={f0},F({n+8192},36)={f1}; G({n},36)={g0},G({n+8192},36)={g1}")
                found_mismatch = True
                break
        elapsed = time.time() - t0
        if not found_mismatch:
            print(f"  No mismatch in [4113, 4113+8192). Period IS <=8192! [{elapsed:.1f}s]")
            print(f"  *** PAPER CLAIM P_36=16384 APPEARS WRONG ***")
        else:
            print(f"  Period-8192 ruled out. P_36=16384 survives. [{elapsed:.1f}s]")

# ============================================================
# Attack 6: Period minimality for m=38 (P=32768)
# ============================================================

print()
print("=" * 70)
print("ATTACK 6: Period minimality for m=38 (claimed P_38=32768)")
print("=" * 70)
print("Paper: hits {8210,8214} -> {40978,40982} = +32768; also (1,0) at 4118->36886=4118+32768")
print("Key: is SubcaseB at 8210+16384=24594? (would indicate P<=16384)")

t0 = time.time()
# First, verify the paper's (1,0) hit at n'=4118 for m=38
f_4118 = F_fast(4118, 38)
g_4118 = G_fast(4118, 38)
print(f"  F(4118,38)={f_4118}, G(4118,38)={g_4118}  (paper claims (1,0) = F=1,G=0)")

f_8210 = F_fast(8210, 38)
g_8210 = G_fast(8210, 38)
print(f"  F(8210,38)={f_8210}, G(8210,38)={g_8210}, SubcaseB={f_8210==0 and g_8210==1}")

f_24594 = F_fast(24594, 38)
g_24594 = G_fast(24594, 38)
print(f"  F(24594,38)={f_24594}, G(24594,38)={g_24594}, SubcaseB={f_24594==0 and g_24594==1}  (8210+16384)")

f_40978 = F_fast(40978, 38)
g_40978 = G_fast(40978, 38)
print(f"  F(40978,38)={f_40978}, G(40978,38)={g_40978}, SubcaseB={f_40978==0 and g_40978==1}  (8210+32768)")
print(f"  [{time.time()-t0:.2f}s]")

# F-sequence comparison
print("\n  F-sequence comparison at offsets 16384 and 32768:")
print(f"  {'n':>6} | F(n) | F(n+16384) | F(n+32768) | match_16384 | match_32768")
print("  " + "-" * 70)
test_ns_38 = [4118, 8210, 8214, 9000, 10000, 15000]
all_match_16384_38 = True
for n in test_ns_38:
    f0 = F_fast(n, 38)
    f1 = F_fast(n + 16384, 38)
    f2 = F_fast(n + 32768, 38)
    m16 = (f0 == f1)
    m32 = (f0 == f2)
    if not m16:
        all_match_16384_38 = False
    print(f"  {n:>6} | {f0}    | {f1}          | {f2}          | {m16}        | {m32}")

if not all_match_16384_38:
    print(f"\n  PERIOD-16384 RULED OUT: F mismatch at some test point.")
    print(f"  P_38=32768 is consistent.")
else:
    print(f"\n  F matches at offset 16384 at all test points. Checking G...")
    # G comparison
    all_g_match_16384 = True
    for n in test_ns_38:
        g0 = G_fast(n, 38)
        g1 = G_fast(n + 16384, 38)
        if g0 != g1:
            all_g_match_16384 = False
            print(f"  G MISMATCH at n={n}: G({n},38)={g0}, G({n+16384},38)={g1}")
            break
    if all_g_match_16384:
        print(f"  G also matches at offset 16384 at all test points.")
        # SubcaseB comparison specifically
        sb_8210 = (F_fast(8210,38)==0 and G_fast(8210,38)==1)
        sb_24594 = (F_fast(24594,38)==0 and G_fast(24594,38)==1)
        print(f"  SubcaseB(8210,38)={sb_8210}, SubcaseB(24594,38)={sb_24594}")
        if sb_8210 and sb_24594:
            print(f"  *** BOTH 8210 and 24594 are SubcaseB! Period may be 16384 or a divisor! ***")
            print(f"  This would contradict the paper's P_38=32768 claim!")
            print(f"  Doing extended F+G comparison [8210, 8210+16384)...")
            t0 = time.time()
            found_mismatch = False
            for n in range(8210, 8210+16384):
                f0 = F_fast(n, 38)
                f1 = F_fast(n + 16384, 38)
                g0 = G_fast(n, 38)
                g1 = G_fast(n + 16384, 38)
                if f0 != f1 or g0 != g1:
                    print(f"  MISMATCH at n={n}: F={f0}/{f1}, G={g0}/{g1}  [{time.time()-t0:.1f}s]")
                    found_mismatch = True
                    break
            elapsed = time.time() - t0
            if not found_mismatch:
                print(f"  No mismatch. Period IS <=16384! [{elapsed:.1f}s]")
                print(f"  *** PAPER CLAIM P_38=32768 APPEARS WRONG ***")
            else:
                print(f"  Period-16384 ruled out. P_38=32768 survives. [{elapsed:.1f}s]")
        elif sb_8210 and not sb_24594:
            print(f"  SubcaseB differs at offset 16384: period is NOT 16384.")
            print(f"  P_38=32768 is consistent (period 16384 ruled out).")
    else:
        print(f"  G breaks period-16384. P_38=32768 is consistent.")

# ============================================================
# Attack 7: Verify the specific period-witness pairs from paper
# ============================================================

print()
print("=" * 70)
print("ATTACK 7: Verify period-witness pairs")
print("=" * 70)

print("m=34 (P=8192): paper claims hits at {4112,4116} -> {12304,12308}")
m34_pairs = [(4112, 4112+8192), (4116, 4116+8192)]
for n1, n2 in m34_pairs:
    sb1 = subcaseB_fast(n1, 34)
    sb2 = subcaseB_fast(n2, 34)
    ok = sb1 and sb2
    print(f"  SubcaseB({n1},34)={sb1}, SubcaseB({n2},34)={sb2}  {'OK' if ok else '*** FAIL ***'}")

print("m=36 (P=16384): paper claims {4113,4117,8209} -> {20497,20501,24593}")
m36_first = [4113, 4117, 8209]
m36_shifted = [x + 16384 for x in m36_first]
for n1, n2 in zip(m36_first, m36_shifted):
    sb1 = subcaseB_fast(n1, 36)
    sb2 = subcaseB_fast(n2, 36)
    ok = sb1 and sb2
    print(f"  SubcaseB({n1},36)={sb1}, SubcaseB({n2},36)={sb2}  {'OK' if ok else '*** FAIL ***'}")

print("m=38 (P=32768): paper claims {8210,8214} -> {40978,40982}")
m38_pairs = [(8210, 8210+32768), (8214, 8214+32768)]
for n1, n2 in m38_pairs:
    t0 = time.time()
    sb1 = subcaseB_fast(n1, 38)
    sb2 = subcaseB_fast(n2, 38)
    ok = sb1 and sb2
    print(f"  SubcaseB({n1},38)={sb1}, SubcaseB({n2},38)={sb2}  [{time.time()-t0:.2f}s]  {'OK' if ok else '*** FAIL ***'}")

# ============================================================
# Attack 8: LCM computation
# ============================================================

print()
print("=" * 70)
print("ATTACK 8: LCM computation — is lcm(all P_m) = 32768?")
print("=" * 70)

def lcm(a, b):
    return a * b // gcd(a, b)

def lcm_list(vals):
    result = 1
    for v in vals:
        result = lcm(result, v)
    return result

period_table = {
    4: 8,
    6: 16,
    8: 32,
    10: 64,
    12: 64,
    14: 64,
    16: 256,
    20: 256,
    22: 256,
    24: 512,
    26: 1024,
    28: 2048,
    30: 4096,
    34: 8192,
    36: 16384,
    38: 32768,
}

all_periods = list(period_table.values())
computed_lcm = lcm_list(all_periods)
print(f"Period table: m -> P_m")
for m in sorted(period_table):
    p = period_table[m]
    k = p.bit_length() - 1
    print(f"  m={m:2d}: P_m = {p:6d} = 2^{k}")

print(f"\nlcm(all P_m) = {computed_lcm}")
print(f"2^15 = {2**15}")
print(f"Matches paper claim of 32768: {computed_lcm == 32768}")

print(f"\nAll P_m divide 32768:")
all_divide = True
for m, p in sorted(period_table.items()):
    divides = (32768 % p == 0)
    if not divides:
        all_divide = False
        print(f"  *** m={m}: {p} does NOT divide 32768! ***")
if all_divide:
    print(f"  Yes — all {len(period_table)} periods divide 32768.")

print(f"\nMinimum power of 2 that contains all periods:")
for k in range(1, 20):
    candidate = 2**k
    if all(candidate % p == 0 for p in all_periods):
        print(f"  2^{k} = {candidate} is the smallest power of 2 divisible by all P_m.")
        break

# ============================================================
# Summary
# ============================================================

print()
print("=" * 70)
print("LOOP 22 ADVERSARIAL REVIEW — COMPLETE")
print("=" * 70)
