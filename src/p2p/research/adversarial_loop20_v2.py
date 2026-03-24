#!/usr/bin/env python3
"""
Adversarial Review Loop 20 — v2.

Three targeted questions:

Q1: Is the active m-set complete? Check all even m in [4,38].
    Use efficient open-boundary small-tape trick for each m.
    For fixed m, F(n', m) for large n' = value at position (n'+1) in an evolving
    open tape with spike at m. Key insight: for n' >> m, only the m-sized
    causal cone matters. We use tapes of size n'+m+5 but only scan a window [3087, N).

Q2: m=18 inactivity — scan [3087, 3343) to verify zero SubcaseB (one 256-period).
    m=32 inactivity — scan [3087, 3087+4096) for zero SubcaseB (one period).

Q3: Period minimality — for each active m with period P, check if P/2 could work.

SPEED: For m ≤ 16 (period ≤ 256), scan is fast (few hundred steps with ~6800-cell tapes).
For m=18 (period 256): scan 256 values, each with tape ~6200 cells, ~3200 steps = ~5B ops.
  Too slow for naive per-n' approach. Use DIAGONAL SCAN instead:

DIAGONAL SCAN: For fixed m, evolve open tape of size T=6800 with spike at m.
Step by step, at step t, read cell at position t (= center for n'=t-1).
This computes F(0..T-2, m) in O(T^2) total.

For G: need the two-spike tape. Can't easily diagonalize because last changes.
BUT: G = F XOR 1 XOR I, and I has same period P as F.
So: compute I for one period directly (small n' window), then use periodicity.

For the period-256 check (m=18), I need I for [3087, 3343).
I(n', m) = G(n', m) XOR F(n', m) XOR 1.
For each n', G requires evolving a tape with last spike at 2n'+2.
Alternative: compute I by reading off the diagonal too.

ALTERNATIVE FOR G: Since H=1 always, and G(n', m) = center after n'+1 steps
from spikes at (m, 2n'+2), we can split:
  G(n', m) = F(n', m) XOR H(n') XOR I(n', m) = F(n', m) XOR 1 XOR I(n', m)
The interaction I depends on the "distance" 2n'+2-m = last-m.

Key: when last-m is very large (last-m >> P_m), the right spike's cone hasn't
overlapped with the left spike's cone at the center yet. In this regime, I=0.
But near SubcaseB events, I=0 exactly when F=0.

For n'=3087, m=18: last-m = 2*3087+2-18 = 6158. The period P_18=256.
Since last-m = 6158 >> P_18, the spikes are far apart.
Yet SubcaseB events still occur for active m!

This means the interaction I is NOT zero in general just because last-m is large.
The interaction depends on the MODULAR behavior of last-m with respect to P.

For active m, I=0 iff last-m ≡ specific residues mod P.
last-m = 2n'+2-m, so as n' varies, last-m varies with step 2.
Residues of last-m mod P that give I=0 are the SubcaseB residues.

For the scan: compute FG pairs directly (no shortcut for G).
Limit to periods that are computationally feasible.

For m=18 (P=256): 256 values at n' in [3087, 3343).
  Each: tape size = 2*n'+3 ≈ 6200-6700. Steps = n'+1 ≈ 3088-3344.
  Per n': ~6400 * 3200 = ~20M ops (np.uint8 arrays).
  Total: 256 * 20M = ~5B ops ≈ 5-20 seconds in numpy (feasible!)

For m=32 (P=4096): 4096 values at n' in [3087, 7183).
  Each: tape ~14500 cells, ~5100 steps ≈ 74M ops.
  Total: 4096 * 74M = ~300B ops ≈ 30 minutes. Too slow!

SHORTCUT FOR m=32: The paper says m=32 has zero (0,1) in [3087,6000).
  Scan [3087, 7183) (one full 4096-period). Use the FAST diagnostic:
  only compute G when F=0 (saves time since F=0 is rare for inactive m).
  From previous data: m=32 has (1,0) events at 3347, 4111, 4115.
  So F=1 at most n'. We only compute G when F=0.

  Estimated F=0 frequency for m=32: ~100 events per 4096 window.
  G computation only when F=0: 100 * 74M ≈ 7.4B ops ≈ 10 seconds. Fast!
"""

import numpy as np
import sys
import time

OUTPUT = "/Users/jonathanhill/src/p2p/research/adversarial_loop20_results.txt"

lines = []

def pr(s):
    print(s, flush=True)
    lines.append(s)

def save():
    with open(OUTPUT, 'w') as f:
        f.write('\n'.join(lines) + '\n')

pr("Adversarial Review Loop 20 (v2 — fast)")
pr("=" * 60)
pr("")

CLAIMED_ACTIVE = [4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38]
CLAIMED_PERIOD = {
    4: 8, 6: 16, 8: 32, 10: 64, 12: 64, 14: 64,
    16: 256, 20: 256, 22: 256,
    24: 512, 26: 1024, 28: 2048, 30: 4096,
    34: 8192, 36: 16384, 38: 32768,
}
INACTIVE_PERIOD = {18: 256, 32: 4096}
N_START = 3087

# ---- Core CA step (open boundary) ----
def ca_step_open(t):
    """Single Rule 30 step with open (zero-padded) boundaries."""
    n = len(t)
    l = np.zeros(n, dtype=np.uint8)
    r = np.zeros(n, dtype=np.uint8)
    l[1:] = t[:-1]
    r[:-1] = t[1:]
    return l ^ (t | r)

def evolve_n(tape, steps):
    """Evolve in-place for given steps; return final state."""
    t = tape.copy()
    for _ in range(steps):
        t = ca_step_open(t)
    return t

def compute_F(n_p, m):
    """Compute F(n', m) — spike at m, evolve n'+1 steps, read center n'+1."""
    size = 2*(n_p+1)+1
    t = np.zeros(size, dtype=np.uint8)
    t[m] = 1
    for _ in range(n_p + 1):
        t = ca_step_open(t)
    return int(t[n_p + 1])

def compute_G(n_p, m):
    """Compute G(n', m) — two-spike at (m, last), evolve n'+1 steps, read center."""
    size = 2*(n_p+1)+1
    last = size - 1
    t = np.zeros(size, dtype=np.uint8)
    t[m] = 1
    t[last] = 1
    for _ in range(n_p + 1):
        t = ca_step_open(t)
    return int(t[n_p + 1])

def check_FG(n_p, m):
    F = compute_F(n_p, m)
    G = compute_G(n_p, m) if F == 0 else None  # Only compute G when F=0
    return F, G

def check_FG_full(n_p, m):
    """Compute both F and G unconditionally."""
    F = compute_F(n_p, m)
    G = compute_G(n_p, m)
    return F, G

# ================================================================
# Q1: Active m-set completeness
# For each even m in [4,38], scan [3087, 3087+2*P) and check SubcaseB.
# For m with period > 2048, only scan [3087, 3087+P) (one period).
# Skip m=34,36,38 (periods 8192,16384,32768 — too slow for full scan).
# ================================================================
pr("Q1: Active m-set completeness (m in [4,38], even)")
pr("-" * 40)
pr("")

q1_data = {}  # m -> (hits, inact_or_active, expected_match)

t0 = time.time()
for m in range(4, 40, 2):
    period = CLAIMED_PERIOD.get(m) or INACTIVE_PERIOD.get(m)
    if period is None:
        pr(f"  m={m}: no period info, skip")
        continue
    if period > 4096:
        pr(f"  m={m}: period {period} — too large to scan fully, deferred")
        q1_data[m] = ([], 'deferred', None)
        continue

    n_end = N_START + 2 * period if period <= 1024 else N_START + period
    hits = []

    for n_p in range(N_START, n_end):
        F = compute_F(n_p, m)
        if F == 0:
            G = compute_G(n_p, m)
            if G == 1:
                hits.append(n_p)

    is_claimed_active = (m in CLAIMED_ACTIVE)
    found_active = len(hits) > 0
    match = "OK" if (found_active == is_claimed_active) else "MISMATCH!"
    status = "ACTIVE" if found_active else "INACTIVE"
    exp = "ACTIVE" if is_claimed_active else "INACTIVE"

    pr(f"  m={m:2d} (P={period:5d}, scanned [{N_START},{n_end})): "
       f"{status:8s} ({len(hits):4d} hits) — expected {exp} [{match}]")
    if hits:
        pr(f"         first hits: {hits[:6]}")

    q1_data[m] = (hits, status, match)
    save()

pr(f"\nQ1 complete ({time.time()-t0:.1f}s)")
save()

# ================================================================
# Q2: m=18 — scan full period [3087, 3343) and second period [3343, 3599)
# ================================================================
pr("")
pr("Q2a: m=18 — scanning two full periods [3087, 3599) for SubcaseB")
pr("-" * 40)

t_m18 = time.time()
m18_seq = []
m18_hits = []
for n_p in range(3087, 3599):
    F, G_or_none = check_FG(n_p, 18)
    G = G_or_none if G_or_none is not None else compute_G(n_p, 18)
    m18_seq.append((F, G))
    if F == 0 and G == 1:
        m18_hits.append(n_p)

pr(f"m=18 scan done ({time.time()-t_m18:.1f}s)")
pr(f"  SubcaseB events in [3087,3599): {len(m18_hits)}")
if m18_hits:
    pr(f"  ALERT! SubcaseB found at: {m18_hits}")
else:
    pr(f"  CONFIRMED: zero SubcaseB for m=18 in [3087,3599) (2 periods)")

# Period-256 check: compare [3087,3343) vs [3343,3599)
period256_ok = (m18_seq[:256] == m18_seq[256:512])
pr(f"  Period-256 exact match: {period256_ok}")

# Check period 128 (would mean 256 is not minimal)
period128_ok = (m18_seq[:128] == m18_seq[128:256])
pr(f"  Period-128 check (subperiod of 256?): {period128_ok}")
pr(f"  Interpretation: paper claims period=256 (not 128). Subperiod-128 should be False.")

# (1,0) events
m18_10 = [(3087+i, F, G) for i, (F, G) in enumerate(m18_seq) if F==1 and G==0]
pr(f"  (1,0) events in [3087,3343): {[(n,) for n,F,G in m18_10 if n < 3343]}")
save()

# ================================================================
# Q2b: m=32 — scan first period [3087, 7183) for SubcaseB
# Use lazy G computation (only compute G when F=0)
# ================================================================
pr("")
pr("Q2b: m=32 — scanning [3087, 7183) for SubcaseB (one 4096-period, lazy G)")
pr("-" * 40)

t_m32 = time.time()
m32_seq = []
m32_hits = []
m32_10 = []

for n_p in range(3087, 3087 + 4096):
    F = compute_F(n_p, 32)
    if F == 0:
        G = compute_G(n_p, 32)
        m32_seq.append((F, G))
        if G == 1:
            m32_hits.append(n_p)
        elif G == 0:
            pass  # F=0, G=0
        elapsed = time.time() - t_m32
    else:
        G = 0  # placeholder (not computed)
        m32_seq.append((F, None))  # None = not computed
        if F == 1:  # potential (1,0)
            # Need G for this
            G2 = compute_G(n_p, 32)
            m32_seq[-1] = (F, G2)
            if G2 == 0:
                m32_10.append((n_p, F, G2))

    if (n_p - 3087) % 200 == 199:
        elapsed = time.time() - t_m32
        pr(f"  m=32: n'={n_p} ({n_p-3087+1}/4096), elapsed {elapsed:.0f}s, "
           f"SubcaseB so far: {len(m32_hits)}")
        save()

pr(f"m=32 scan done ({time.time()-t_m32:.1f}s)")
pr(f"  SubcaseB in [3087,7183): {len(m32_hits)}")
if m32_hits:
    pr(f"  ALERT! SubcaseB found: {m32_hits}")
else:
    pr(f"  CONFIRMED: zero SubcaseB for m=32 in [3087,7183)")
pr(f"  (1,0) events for m=32: {[(n,) for n,F,G in m32_10[:10]]}")
save()

# Verify period-4096 by checking second period
pr("")
pr("Q2b: m=32 — checking second period [7183, 11279) for period verification...")
t_m32b = time.time()
m32_seq2 = []
for n_p in range(3087 + 4096, 3087 + 2*4096):
    F = compute_F(n_p, 32)
    G = compute_G(n_p, 32)
    m32_seq2.append((F, G))
    if (n_p - 3087 - 4096) % 200 == 199:
        pr(f"  m=32 period2: n'={n_p}, elapsed {time.time()-t_m32b:.0f}s")
        save()

# Build full sequences for period check
m32_full_seq = [m32_seq[i] for i in range(4096)]  # None -> need to fill
# Actually we computed G for all n_p (the lazy approach was modified to compute G always)
# Re-verify: seq has (F, G) with no None for the period check
m32_full_seq2 = m32_seq2

period4096_ok = (m32_full_seq == m32_full_seq2)
period2048_ok = (m32_full_seq[:2048] == m32_full_seq[2048:4096])
pr(f"  m=32 period-4096 verification: {period4096_ok}")
pr(f"  m=32 period-2048 check (subperiod?): {period2048_ok}")
save()

# ================================================================
# Q3: Period minimality for active m ≤ 2048
# ================================================================
pr("")
pr("Q3: Period minimality for active m (period ≤ 2048)")
pr("-" * 40)
pr("")

for m in CLAIMED_ACTIVE:
    P = CLAIMED_PERIOD[m]
    if P > 2048:
        pr(f"  m={m}: P={P} — not scanned (too large for full period check)")
        continue

    hits_in_2P = q1_data.get(m, [[]])[0]
    if not hits_in_2P:
        pr(f"  m={m}: P={P} — no hits found (unexpected!)")
        continue

    # Gaps between consecutive hits
    gaps = [hits_in_2P[i+1] - hits_in_2P[i] for i in range(len(hits_in_2P)-1)] if len(hits_in_2P) > 1 else []
    half_P = P // 2

    if not gaps:
        pr(f"  m={m}: P={P} — only {len(hits_in_2P)} hit, cannot check gaps")
        continue

    # All gaps divisible by half_P but not all by P?
    all_div_halfP = all(g % half_P == 0 for g in gaps)
    all_div_P = all(g % P == 0 for g in gaps)
    min_gap = min(gaps)

    if all_div_halfP and not all_div_P:
        verdict = f"POSSIBLE SHORTER PERIOD P/2={half_P} (gaps div by P/2 but not all by P)"
    elif all_div_P:
        verdict = f"Period P={P} consistent (all gaps div by P)"
    else:
        verdict = f"Gaps not uniformly divisible — complex structure"

    pr(f"  m={m:2d}: P={P:5d}, {len(hits_in_2P)} hits, min_gap={min_gap}, all_div_P={all_div_P}, all_div_halfP={all_div_halfP}")
    pr(f"         {verdict}")
    if gaps[:8]:
        pr(f"         gaps: {gaps[:8]}")

save()

# ================================================================
# FINAL SUMMARY
# ================================================================
pr("")
pr("=" * 60)
pr("FINAL SUMMARY")
pr("=" * 60)
pr("")

pr("Q1 — Active m-set completeness:")
mismatches_q1 = []
for m in range(4, 40, 2):
    if m not in q1_data:
        continue
    hits, status, match = q1_data[m]
    if match == "MISMATCH!":
        mismatches_q1.append(m)
if mismatches_q1:
    pr(f"  ERRORS FOUND: m values with wrong classification: {mismatches_q1}")
else:
    pr(f"  All verified m values match claimed active/inactive classification.")
    pr(f"  Deferred (too slow): m=34,36,38 (periods 8192,16384,32768)")
    pr(f"  Note: m=18 and m=32 verified as inactive.")
pr("")

pr("Q2 — Permanent inactivity:")
pr(f"  m=18: SubcaseB in [3087,3599)={len(m18_hits)}, period-256={period256_ok}, "
   f"subperiod-128={period128_ok}")
pr(f"  m=32: SubcaseB in [3087,7183)={len(m32_hits)}, period-4096={period4096_ok}, "
   f"subperiod-2048={period2048_ok}")
pr("")

pr("Q3 — Period minimality:")
pr("  See detailed output above. Any POSSIBLE SHORTER PERIOD flags a problem.")
pr("")

total_time = time.time() - t0
pr(f"Total runtime: {total_time:.0f}s")
save()
pr(f"Results saved to {OUTPUT}")
