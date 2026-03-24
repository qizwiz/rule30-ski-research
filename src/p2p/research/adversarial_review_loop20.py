#!/usr/bin/env python3
"""
Adversarial review — Loop 20.

Three specific claims to attack:

Q1: Is the active m-set COMPLETE for m in [4,38]?
    Paper claims M_act = {4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38}.
    This means m in {2,18,32} are inactive (no SubcaseB ever).
    Test: for EACH even m in [4,38], scan [3087, 3087+10*P_m) and confirm
    either (a) SubcaseB events found (active, matches claim) or
    (b) NO SubcaseB events found (inactive, matches claim for m=18,32).
    Any discrepancy is a finding.

Q2: Are "inactive" positions permanently inactive or just long-period?
    Paper says m=18 has "zero (0,1) in [3087,10000) (27 full periods)".
    Actually scan [3087,10000) for m=18 and verify this claim.
    Also scan m=32 which has period 4096 and check [3087,3087+3*4096).

Q3: Is the period-P bound tight?
    Paper says P_m are: m=4→8, m=6→16, m=8→32, m=10→64, m=12→64,
    m=14→64, m=16→256, m=20→256, m=22→256, m=24→512, m=26→1024,
    m=28→2048, m=30→4096, m=34→8192, m=36→16384, m=38→32768.
    Test: for each active m, check if period P/2 works (i.e., is the
    stated period the MINIMAL period, or could it be half as long?).
    Method: collect all SubcaseB n' values in [3087, 3087+2*P_m),
    then check whether the gap between consecutive hits is always
    divisible by P_m/2 (would indicate period P_m/2 suffices).

Rule 30: rule30(l,c,r) = l XOR (c OR r)
F(n', m) = center of tape of size 2n'+3 after n'+1 steps from spike-at-m
G(n', m) = center of tape of size 2n'+3 after n'+1 steps from two-spike {m, last=2n'+2}
SubcaseB: F=0 AND G=1
"""

import numpy as np
import sys

OUTPUT = "/Users/jonathanhill/src/p2p/research/adversarial_loop20_results.txt"

# ---- Core CA routines ----

def rule30_step_np(t):
    l = np.roll(t, 1)
    r = np.roll(t, -1)
    return l ^ (t | r)

def rule30_center(n_prime, tape_np):
    """Evolve n_prime+1 steps; return center cell (position n_prime+1)."""
    t = tape_np.copy().astype(np.int8)
    for _ in range(n_prime + 1):
        t = rule30_step_np(t)
    return int(t[n_prime + 1])

def make_spike(size, pos):
    t = np.zeros(size, dtype=np.int8)
    t[pos] = 1
    return t

def check_FG(n_prime, m_pos):
    """Return (F, G) = (rule30_center from spike-m, rule30_center from two-spike)."""
    size = 2*(n_prime+1)+1
    last = size - 1
    # F
    sp = make_spike(size, m_pos)
    F = rule30_center(n_prime, sp)
    # G
    ts2 = make_spike(size, m_pos)
    ts2[last] = 1
    G = rule30_center(n_prime, ts2)
    return F, G

def is_subcaseB(n_prime, m_pos):
    F, G = check_FG(n_prime, m_pos)
    return F == 0 and G == 1

def is_valid_m(n_prime, m_pos):
    """m must be even, in [2, 2n'], not equal to last (2n'+2)."""
    last = 2*(n_prime+1)
    return (2 <= m_pos < last and m_pos % 2 == 0)

# ---- Claimed periods ----
CLAIMED_ACTIVE = [4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38]
CLAIMED_INACTIVE_EVEN = [2, 18, 32]  # within m < 40

CLAIMED_PERIOD = {
    4: 8, 6: 16, 8: 32, 10: 64, 12: 64, 14: 64,
    16: 256, 20: 256, 22: 256,
    24: 512, 26: 1024, 28: 2048, 30: 4096,
    34: 8192, 36: 16384, 38: 32768,
}

lines = []

def pr(s):
    print(s, flush=True)
    lines.append(s)

def save():
    with open(OUTPUT, 'w') as f:
        f.write('\n'.join(lines) + '\n')

pr("Adversarial Review Loop 20")
pr("=" * 60)
pr("")

# ================================================================
# Q1: Active m-set completeness — ALL even m in [4,38]
# For each m, scan [3087, 3087+20*P_claimed) (or [3087,3200) for
# claimed inactive m=18,32 which have known periods 256,4096).
# ================================================================

pr("Q1: Active m-set completeness")
pr("-" * 40)
pr("Scanning all even m in [4,38] to verify active/inactive classification.")
pr("")

# First pass: small window [3087, 3343) to find which m ever fire
SCAN_N_START = 3087

# For each active m, collect SubcaseB n' values in [3087, 3087 + 2*P)
# For each claimed-inactive m in [4,38], scan [3087, 3087 + at least 5 claimed periods)

q1_results = {}  # m -> list of SubcaseB n' in window

# Active m: scan 2 full periods from first hit (need to know first hit)
# We'll scan [3087, 3087 + 2*P_m) for each active m
# For m=34,36,38 with large periods, 2*P is enormous; instead scan [3087, 3087+P_m+1000)

MAX_SCAN = {
    4: 3087 + 2*8 + 100,      # 3203
    6: 3087 + 2*16 + 100,     # 3219
    8: 3087 + 2*32 + 100,     # 3251
    10: 3087 + 2*64 + 100,    # 3315
    12: 3087 + 2*64 + 100,
    14: 3087 + 2*64 + 100,
    16: 3087 + 2*256 + 100,   # 3599
    18: 3087 + 10*256,        # inactive, period 256; scan 10 periods = 3087+2560 = 5647
    20: 3087 + 2*256 + 100,
    22: 3087 + 2*256 + 100,
    24: 3087 + 2*512 + 100,   # 4211
    26: 3087 + 2*1024 + 100,  # 5235
    28: 3087 + 2*2048 + 100,  # 7283
    30: 3087 + 2*4096 + 100,  # 11375
    32: 3087 + 3*4096,        # inactive, claimed period 4096; scan 3 periods = 15375
    34: 3087 + 8192 + 5000,   # first hit ~4112; scan one period + buffer = 16279
    36: 3087 + 16384 + 5000,  # first hit ~4113; scan one period + buffer = 24471
    38: 3087 + 32768 + 5000,  # first hit ~8210; scan one period + buffer = 40855
}

# For Q1 and Q3 we need all even m in [4,38] EXCEPT we defer 34,36,38 to confirm
# claimed period (too slow to scan 2 full periods for large m)
# Strategy: for m=34,36,38 we just verify they ARE active (SubcaseB events exist) and
# check period minimality by looking at the known hit structure.

for m in range(4, 40, 2):
    if m not in MAX_SCAN:
        continue
    end = MAX_SCAN[m]
    hits = []
    for n_p in range(SCAN_N_START, end):
        if not is_valid_m(n_p, m):
            continue
        if is_subcaseB(n_p, m):
            hits.append(n_p)
    q1_results[m] = hits

    is_claimed_active = (m in CLAIMED_ACTIVE)
    found_active = len(hits) > 0

    status = "ACTIVE" if found_active else "INACTIVE"
    expected = "ACTIVE" if is_claimed_active else "INACTIVE"
    discrepancy = "MISMATCH!" if (found_active != is_claimed_active) else "OK"

    pr(f"  m={m:2d}: {status} ({len(hits):4d} SubcaseB hits in [3087,{end})) "
       f"— expected {expected} [{discrepancy}]")
    if hits:
        pr(f"       first hits: {hits[:6]}")
    save()

pr("")
pr("Q1 SUMMARY: Any MISMATCH above means paper is wrong about active/inactive classification.")
pr("")

# ================================================================
# Q2: Permanent inactivity of m=18 and m=32
# Paper says: m=18 has "zero (0,1) in [3087,10000) (27 full periods)"
# Paper says: m=32 has period 4096 with "zero (0,1) in [3087,8000)"
# Test: scan [3087,10000) for m=18 and [3087,8000) for m=32
# Also: does m=18's period hold exactly (check period 128 vs 256)?
# ================================================================

pr("Q2: Permanent inactivity verification")
pr("-" * 40)

# m=18 full scan [3087, 10000)
pr("m=18: scanning [3087, 10000) for SubcaseB (paper claims: zero)...")
m18_FG = []
for n_p in range(3087, 10000):
    F, G = check_FG(n_p, 18)
    if F == 0 and G == 1:
        m18_FG.append(('SubcaseB', n_p, F, G))
    elif F != G:
        m18_FG.append(('F≠G', n_p, F, G))

m18_subcaseB = [(n,F,G) for (t,n,F,G) in m18_FG if t=='SubcaseB']
m18_FneqG = [(n,F,G) for (t,n,F,G) in m18_FG if t=='F≠G']

pr(f"  m=18 SubcaseB count in [3087,10000): {len(m18_subcaseB)}")
if m18_subcaseB:
    pr(f"  ALERT: SubcaseB events found: {m18_subcaseB[:10]}")
else:
    pr(f"  CONFIRMED: zero SubcaseB events for m=18 in [3087,10000)")
pr(f"  m=18 F≠G (any type) count: {len(m18_FneqG)}")
if m18_FneqG[:8]:
    pr(f"  First F≠G events: {m18_FneqG[:8]}")

# Check period claim for m=18: paper says period 256
# Method: collect (F,G) sequence and check if it repeats with period 256 vs 128
m18_sequence = []
for n_p in range(3087, 3087+256*2):
    F, G = check_FG(n_p, 18)
    m18_sequence.append((F,G))

period_256_ok = all(m18_sequence[i] == m18_sequence[i+256] for i in range(256))
period_128_ok = all(m18_sequence[i] == m18_sequence[i+128] for i in range(128))
pr(f"  m=18 period-256 check: {period_256_ok} (should be True)")
pr(f"  m=18 period-128 check: {period_128_ok} (should be False per paper)")
save()

# m=32 full scan [3087, 8000)
pr("")
pr("m=32: scanning [3087, 8000) for SubcaseB (paper claims: zero (0,1))...")
m32_subcaseB = []
m32_FneqG = []
for n_p in range(3087, 8000):
    F, G = check_FG(n_p, 32)
    if F == 0 and G == 1:
        m32_subcaseB.append(n_p)
    elif F != G:
        m32_FneqG.append((n_p, F, G))

pr(f"  m=32 SubcaseB count in [3087,8000): {len(m32_subcaseB)}")
if m32_subcaseB:
    pr(f"  ALERT: SubcaseB events found: {m32_subcaseB[:10]}")
else:
    pr(f"  CONFIRMED: zero SubcaseB events for m=32 in [3087,8000)")
pr(f"  m=32 F≠G events: {[(n,F,G) for n,F,G in m32_FneqG[:10]]}")

# Does m=32's claimed period 4096 hold exactly?
m32_sequence = []
for n_p in range(3087, 3087+4096*2):
    F, G = check_FG(n_p, 32)
    m32_sequence.append((F,G))

period_4096_ok = all(m32_sequence[i] == m32_sequence[i+4096] for i in range(4096))
period_2048_ok = all(m32_sequence[i] == m32_sequence[i+2048] for i in range(2048))
pr(f"  m=32 period-4096 check: {period_4096_ok}")
pr(f"  m=32 period-2048 check: {period_2048_ok}")
save()

pr("")
pr("Q2 SUMMARY: Permanent inactivity requires proving NO SubcaseB ever — periodicity")
pr("argument must show the pattern in the checked window repeats forever.")
pr("")

# ================================================================
# Q3: Period minimality check for all active m
# For each active m, test whether P_m/2 would also work as a period
# (i.e., is the period tighter than claimed?).
# Method: check if sequence repeats with period P_m/2 (starting from 3087).
# If P_m is odd or P_m < 4, skip.
# ================================================================

pr("Q3: Period minimality — is P_m the MINIMAL period?")
pr("-" * 40)
pr("For each active m, test period P_m/2 (should fail if P_m is minimal).")
pr("")

# For small periods (m=4..22) we have already computed sequences above via MAX_SCAN
# Recompute as needed

period_minimal = {}

for m in CLAIMED_ACTIVE:
    P = CLAIMED_PERIOD[m]
    if P < 4:
        pr(f"  m={m}: P={P} too small to halve — skip")
        period_minimal[m] = True
        continue

    half_P = P // 2

    # Scan [3087, 3087 + P + half_P) to get enough data
    # For large m, we already know the hit structure
    # Instead of full scan, check period directly:
    # Collect sequence of length 2*P starting at 3087
    if P <= 1024:
        seq = []
        for n_p in range(3087, 3087 + 2*P):
            F, G = check_FG(n_p, m)
            seq.append((F,G))
        half_period_ok = all(seq[i] == seq[i+half_P] for i in range(half_P))
        full_period_ok = all(seq[i] == seq[i+P] for i in range(P))
        minimal = (not half_period_ok) and full_period_ok
        period_minimal[m] = minimal
        status = "MINIMAL" if minimal else ("HALF_PERIOD_WORKS!" if half_period_ok else "FULL_PERIOD_BROKEN!")
        pr(f"  m={m:2d}: P={P:5d}, P/2={half_P:5d}  "
           f"full_period={full_period_ok}, half_period={half_period_ok}  => {status}")
    else:
        # For large periods, use known hit structure from q1_results
        hits = q1_results.get(m, [])
        if len(hits) < 2:
            pr(f"  m={m:2d}: P={P:5d} — not enough hits in scan window to test minimality")
            period_minimal[m] = None
            continue
        # Check if all gaps between consecutive hits are multiples of half_P
        gaps = [hits[i+1] - hits[i] for i in range(len(hits)-1)]
        # A shorter period would mean some gap < P or not divisible by P
        min_gap = min(gaps) if gaps else 0
        # If min_gap < P: shorter period might exist
        pr(f"  m={m:2d}: P={P:5d}  hits in window: {hits[:6]}  gaps: {gaps[:6]}")
        pr(f"         min_gap={min_gap}, P/2={half_P}")
        if min_gap < P:
            pr(f"         NOTE: min gap < P — period might be shorter (min_gap={min_gap})")
        period_minimal[m] = None  # inconclusive for large m from limited data

    save()

pr("")
pr("Q3 SUMMARY:")
problems_found = False
for m in CLAIMED_ACTIVE:
    if period_minimal.get(m) == False:
        pr(f"  PROBLEM: m={m} — claimed period P={CLAIMED_PERIOD[m]} is NOT minimal (P/2 works!)")
        problems_found = True
if not problems_found:
    pr("  All verified active m values have minimal period (or inconclusive for large m).")
pr("")

# ================================================================
# FINAL SUMMARY
# ================================================================

pr("=" * 60)
pr("FINAL SUMMARY")
pr("=" * 60)
pr("")

# Q1 summary
claimed_active_set = set(CLAIMED_ACTIVE)
found_active_set = set(m for m, hits in q1_results.items() if hits)
pr(f"Q1 — Active m-set completeness (even m in [4,38]):")
pr(f"  Claimed active: {sorted(claimed_active_set & set(range(4,40,2)))}")
pr(f"  Found active:   {sorted(found_active_set & set(range(4,40,2)))}")
extra_active = found_active_set - claimed_active_set
missed_active = (claimed_active_set & set(range(4,40,2))) - found_active_set
if extra_active:
    pr(f"  ALERT — extra active m found (not in paper's list): {sorted(extra_active)}")
if missed_active:
    pr(f"  ALERT — claimed active m with NO hits in scan window: {sorted(missed_active)}")
    pr(f"  (These may have first hits beyond the scan window)")
if not extra_active and not missed_active:
    pr(f"  All checks consistent with paper's M_act claim.")
pr("")

pr(f"Q2 — Permanent inactivity (m=18, m=32):")
pr(f"  m=18: {len(m18_subcaseB)} SubcaseB in [3087,10000) "
   f"({'ZERO — supports paper' if not m18_subcaseB else 'ALERT: found!'})")
pr(f"  m=32: {len(m32_subcaseB)} SubcaseB in [3087,8000) "
   f"({'ZERO — supports paper' if not m32_subcaseB else 'ALERT: found!'})")
pr(f"  m=18 period-256 holds: {period_256_ok}")
pr(f"  m=18 period-128 fails: {not period_128_ok} (paper says period is 256, not 128)")
pr(f"  m=32 period-4096 holds: {period_4096_ok}")
pr(f"  m=32 period-2048 fails: {not period_2048_ok}")
pr("")

pr("Q3 — Period minimality:")
for m in CLAIMED_ACTIVE:
    if m in CLAIMED_PERIOD:
        P = CLAIMED_PERIOD[m]
        v = period_minimal.get(m)
        if v is False:
            pr(f"  m={m}: P={P} NOT MINIMAL (P/2 would work)")
        elif v is None:
            pr(f"  m={m}: P={P} inconclusive (scan window too small)")
pr("")

save()
pr(f"Results written to {OUTPUT}")
