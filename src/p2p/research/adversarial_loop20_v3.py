#!/usr/bin/env python3
"""
Adversarial Review Loop 20 — v3 (diagonal scan, fast).

Key insight: F(n', m) = value at position n'+1 in the open-boundary Rule 30
evolution starting from spike at m.

We can compute ALL F(n', m) for n' in [0, N-1] using a SINGLE tape of
size N+m+5 with spike at m, evolved N steps. At step t, read position t.

For G: use H=1 theorem. G(n', m) = F(n', m) XOR 1 XOR I(n', m).
I(n', m) can be computed as follows: I(n', m) = G(n', m) XOR F(n', m) XOR 1.
G requires the two-spike tape. We can also diagonalize G:
  Use tape with spikes at m AND at 2n'+2. But 2n'+2 changes with n'...

ALTERNATIVE: Only compute G at SubcaseB candidates (F=0 positions).
  From the diagonal F computation, find all n' where F=0.
  Then for each such n', compute G directly.
  For inactive m, F=0 is rare (most of the time F=1 for inactive positions).

Actually from the existing data:
- m=18: (1,0) events at 3280,3336,3340,... → F=1 at these. F=0 at most.
  The question is: for those n' where F=0, is G always 0?

- m=32: (1,0) at 3347,4111,4115 → F=1 at these. Need to verify G for F=0 cases.

The diagonal scan gives F for ALL n' efficiently.
Then we only compute G for the F=0 cases.

For active m: F=0 occurs with frequency ~1/P, and G=1 for the SubcaseB events.

PLAN:
1. Diagonal scan: compute F(n', m) for all n' in [3087, 3087+2*P_m)
   using a tape of size 3087+2*P_m+m+5.
   Time: O((3087+2*P_m)^2 / 2) total (single evolution).
   For m=28, P=2048: tape size ~7200, steps=7183 → 26M ops total (fast!).
   For m=30, P=4096: tape size ~11300, steps=11283 → 64M ops total (fast!).
   For m=32, P=4096: same range → 64M ops total.

2. For each n' where F=0, compute G directly using a smaller computation:
   G(n', m) = result of evolving tape of size 2n'+3 with spikes at (m, 2n'+2) for n'+1 steps.

   But this tape has size 2n'+3 ≈ 6200-15400. Each takes ~n'^2/2 ops.

   SMART ALTERNATIVE: Use the periodicity of I.
   Since I is periodic with period P_m, compute I for one period only.
   How? Compute G for n' in [3087, 3087+P_m) directly.
   There are ~P_m/2 positions where F=0 (half the time roughly).
   For P=4096 (m=30,32): ~2048 positions where F=0.
   Each G computation: ~n'^2/2 ≈ 5000^2/2 = 12.5M ops.
   Total: 2048 * 12.5M = 26B ops ≈ 60 seconds. Feasible!

But actually for m=32 (inactive), F=1 most of the time, so far fewer G computations needed.
Let's count: in one 4096-period, m=32 has maybe 10-50 F=0 positions (mostly F=1).
That's 50 * 12.5M = 625M ops ≈ 1-2 seconds.

For m=28 (active): ~2048 F=0 positions per 2048-period? No, it's sparser.
From data: 3 cluster hits per period → only 3 G computations needed for SubcaseB check.
But we need to verify ZERO false SubcaseBs (G=0 for all F=0). So still need G for ALL F=0.

BEST STRATEGY:
1. Diagonal scan to get F for entire period.
2. For each F=0 position, compute G directly.
3. Count SubcaseB events (F=0, G=1).

For m=32 (period 4096), compute the whole period efficiently.
"""

import numpy as np
import time
import sys

OUTPUT = "/Users/jonathanhill/src/p2p/research/adversarial_loop20_results.txt"
lines = []

def pr(s):
    print(s, flush=True)
    lines.append(s)

def save():
    with open(OUTPUT, 'w') as f:
        f.write('\n'.join(lines) + '\n')

pr("Adversarial Review Loop 20 (v3 — diagonal scan)")
pr("=" * 60)
pr("")

# ---- Diagonal scan for F ----
def diagonal_F_scan(m, n_start, n_end):
    """
    Compute F(n', m) for n' in [n_start, n_end) using diagonal scan.

    Uses a tape of size n_end + m + 5 with spike at position m.
    Evolves step-by-step; at step t, reads position t (= center for n'=t-1).

    Returns dict {n': F_value} for n' in [n_start, n_end).
    """
    T = n_end + m + 5
    tape = np.zeros(T, dtype=np.uint8)
    tape[m] = 1  # spike at position m

    F_vals = {}

    for step in range(1, n_end + 1):
        n_p = step - 1
        if n_start <= n_p < n_end:
            # Center for n'=n_p is at position n_p+1 in standard tape of size 2n_p+3
            # But in our diagonal tape, spike is at m, center at step t = n_p+1.
            # Check: at t=1, n'=0: center at position 1, spike at m → F(0, m) = spike[1] after 1 step.
            # Actually after 1 step of Rule 30 from spike-at-m:
            #   position i gets rule30(spike[i-1], spike[i], spike[i+1])
            #   only positions m-1, m, m+1 are affected.
            #   position 1 = 1 iff m-1=0 or m=1: only if m=1 (but m is even and >=4).
            #   So F(0, 4) = position 1 after 1 step from spike at 4 = 0.
            # This seems off. Let me re-derive.

            # In the standard formulation:
            #   tape size = 2*(n_p+1)+1 = 2n_p+3
            #   center position = n_p+1
            #   spike at position m (0-indexed)
            #   evolve n_p+1 steps
            #   F(n_p, m) = tape[n_p+1] after n_p+1 steps

            # In diagonal tape of size T, spike at m:
            #   after t steps, position t is the value that would be at the "wavefront"
            #   from the spike. The cell at position t is:
            #   It gets contribution from spike at m only if t >= m (else it's 0).
            #   For t = n_p+1:
            #     Reading position n_p+1 in a tape of size T after n_p+1 steps from spike at m
            #     This IS the same as reading position n_p+1 in a tape of size T after n_p+1 steps.
            #   For this to match F(n_p, m) = center in tape of size 2n_p+3:
            #     Center in size 2n_p+3 tape = position n_p+1.
            #     Spike at m in size T vs spike at m in size 2n_p+3:
            #     The evolution up to step n_p+1 is identical as long as the cone from spike
            #     doesn't reach the boundaries. For open-boundary evolution (no wrap):
            #     Cone from spike at m extends from m-(n_p+1) to m+(n_p+1) at step n_p+1.
            #     Right extent: m+(n_p+1). For n_p >= m-1: this reaches >= m+m-1.
            #     Left extent: m-(n_p+1). For n_p >= m: this is <= -1 (hits left boundary).
            #     But the left part doesn't matter for the center at position n_p+1 >= m+1.
            #     Right: cone reaches m+(n_p+1). Position n_p+1 is inside cone iff n_p+1 >= m.
            #     So for n_p >= m-1, position n_p+1 IS inside the cone.
            #     The result at position n_p+1 (from spike-at-m, after n_p+1 steps, open boundary)
            #     is the same in any tape where:
            #       (a) Left boundary is further left than m-(n_p+1)
            #       (b) Right boundary is further right than n_p+1+(n_p+1) = 2(n_p+1)
            #           (so the right boundary effect doesn't propagate back to center)
            #     Our tape has size T = n_end + m + 5.
            #     Right boundary = T-1 = n_end+m+4 > 2n_end (for m < n_end, which is true).
            #     Left boundary = 0. Cone left extent = m-(n_p+1) < 0 for large n_p.
            #     Left boundary DOES affect cells near position 0 at late steps.
            #     But the center position n_p+1 is far from the left boundary (n_p+1 > 0).
            #     The influence of left boundary on position n_p+1:
            #       Left boundary at 0 can affect positions within n_p+1 steps of 0 = [0, n_p+1].
            #       Position n_p+1 is at the EDGE of this range!
            #
            #     CONCLUSION: the diagonal tape open-boundary computation DOES NOT give the
            #     same result as the standard computation for all n_p.
            #     Specifically, the left boundary at position 0 affects position n_p+1 at step n_p+1
            #     (since the boundary is n_p+1 steps away from the center).

            # This is the fundamental issue. The diagonal tape trick doesn't cleanly isolate F.

            # CORRECT DIAGONAL: place spike at position n_start (not at m),
            # in a tape where center is always at the same position.
            # OR: use a semi-infinite tape (no left boundary effect).

            # SIMPLEST CORRECT APPROACH: just loop over n' and compute F directly.
            # The insight is: for F(n', m) with OPEN boundaries, the left boundary
            # affects the result only if m < n'+1 (which is always true for n' >> m).
            # But with the standard tape of size 2n'+3 and OPEN (zero) boundaries,
            # the left and right edges are zero, and the zero padding is consistent.
            #
            # The diagonal scan works ONLY if we use an INFINITE tape (no boundary effects).
            # For large n', the left boundary effect on position n'+1 is:
            #   At step 0: left boundary cell = 0.
            #   The zero left boundary propagates rightward.
            #   At step n'+1: the boundary's cone reaches position n'+1.
            #   Since the boundary is 0, its effect is to enforce the "correct" open-boundary result.
            #
            # Actually, for open-boundary evolution (zero boundaries), the standard and diagonal
            # are equivalent! The open boundary = zero = no additional information.
            # A zero left boundary means: tape[-1] = 0 (fictitious cell), which is the same
            # as padding the spike tape with zeros on the left.
            #
            # So: diagonal scan DOES work for open-boundary!
            # The left boundary effect is zero (it contributes 0 cells = natural padding).
            # Therefore F(n', m) = value at position n'+1 in diagonal tape at step n'+1.

            F_vals[n_p] = int(tape[step])  # step = n_p+1

        # Evolve one step (open boundary = zero padding)
        l = np.zeros(T, dtype=np.uint8)
        r = np.zeros(T, dtype=np.uint8)
        l[1:] = tape[:-1]
        r[:-1] = tape[1:]
        tape = l ^ (tape | r)

    return F_vals


def compute_G_single(n_p, m):
    """Compute G(n', m) using direct evolution. Returns G value."""
    size = 2*(n_p+1)+1
    last = size - 1
    t = np.zeros(size, dtype=np.uint8)
    t[m] = 1
    t[last] = 1
    for _ in range(n_p + 1):
        l = np.zeros(size, dtype=np.uint8)
        r = np.zeros(size, dtype=np.uint8)
        l[1:] = t[:-1]
        r[:-1] = t[1:]
        t = l ^ (t | r)
    return int(t[n_p + 1])


def scan_active(m, P, n_start, n_periods=2, label=""):
    """
    Scan n' in [n_start, n_start + n_periods * P) for SubcaseB events.
    Uses diagonal F scan + direct G for F=0 positions.
    Returns list of SubcaseB n'.
    """
    n_end = n_start + n_periods * P
    t0 = time.time()

    # Diagonal F scan
    F_vals = diagonal_F_scan(m, n_start, n_end)
    t_diag = time.time() - t0

    F_zero = [n for n, F in sorted(F_vals.items()) if F == 0]

    hits = []
    for n_p in F_zero:
        G = compute_G_single(n_p, m)
        if G == 1:
            hits.append(n_p)

    t_total = time.time() - t0
    pr(f"  {label or f'm={m}'}: {len(hits)} SubcaseB in [{n_start},{n_end}), "
       f"F=0 count: {len(F_zero)}, "
       f"diag: {t_diag:.1f}s, total: {t_total:.1f}s")
    if hits:
        pr(f"    hits: {hits[:8]}")

    return hits, F_vals


# ================================================================
# Q1: Verify active/inactive for m=28, 30, 32 (these were slow before)
# Using diagonal scan
# ================================================================
pr("Q1: Active m-set completeness — fast diagonal scan")
pr("-" * 40)
pr("Verifying m=28 (P=2048), m=30 (P=4096), m=32 (P=4096)")
pr("")

N_START = 3087

CLAIMED_ACTIVE = {4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38}
CLAIMED_PERIOD = {
    4: 8, 6: 16, 8: 32, 10: 64, 12: 64, 14: 64,
    16: 256, 20: 256, 22: 256,
    24: 512, 26: 1024, 28: 2048, 30: 4096,
    34: 8192, 36: 16384, 38: 32768,
}
INACTIVE_PERIOD = {18: 256, 32: 4096}

# m=28
hits28, F28 = scan_active(28, 2048, N_START, n_periods=2, label="m=28 (P=2048, active)")
match28 = "OK" if hits28 else "MISMATCH!"
pr(f"  m=28 classification: {'ACTIVE' if hits28 else 'INACTIVE'} — expected ACTIVE [{match28}]")
save()

# m=30
hits30, F30 = scan_active(30, 4096, N_START, n_periods=1, label="m=30 (P=4096, active, 1 period)")
match30 = "OK" if hits30 else "MISMATCH (no SubcaseB found — need larger window)!"
pr(f"  m=30 classification: {'ACTIVE' if hits30 else 'INACTIVE'} — expected ACTIVE [{match30}]")
save()

# m=32 (inactive)
hits32, F32 = scan_active(32, 4096, N_START, n_periods=1, label="m=32 (P=4096, inactive)")
match32 = "OK" if not hits32 else "MISMATCH — SubcaseB FOUND for supposedly inactive m=32!"
pr(f"  m=32 classification: {'INACTIVE' if not hits32 else 'ACTIVE!'} — expected INACTIVE [{match32}]")
save()

# ================================================================
# Q2: Precise period verification for m=18 and m=32
# ================================================================
pr("")
pr("Q2: Period minimality for inactive m=18 and m=32")
pr("-" * 40)

# m=18: scan 4 periods, check if period-128 or period-256 is minimal
pr("m=18: scanning 4 periods [3087, 4111) for period verification...")
t0 = time.time()
F18_vals = diagonal_F_scan(18, 3087, 3087+4*256)
F18_zero = [n for n, F in sorted(F18_vals.items()) if F == 0]
pr(f"  F=0 positions for m=18 in [3087,4111): {len(F18_zero)} positions")

# Compute G for ALL n' in 4 periods to get full (F,G) sequence
m18_FG = {}
t_G_start = time.time()
# For period-256 check we need (F,G) for all n' not just F=0
# Use diagonal for F; compute G only for F=0
m18_hits_4p = []
for n_p in F18_zero:
    G = compute_G_single(n_p, 18)
    m18_FG[n_p] = (0, G)
    if G == 1:
        m18_hits_4p.append(n_p)
        pr(f"  ALERT! m=18 SubcaseB at n'={n_p}")

# For period check, also need F=1 positions' G values
# We only need (F, G) pattern, but since F=1 → (1, G) and SubcaseB requires F=0,
# we can check SubcaseB-free by just checking F=0 positions.
pr(f"  m=18 SubcaseB hits in 4 periods: {len(m18_hits_4p)}")
if not m18_hits_4p:
    pr(f"  CONFIRMED: zero SubcaseB for m=18 in [3087,4111) (4 full periods)")

# For period check: look at the F sequence alone (G not needed for non-SubcaseB check)
# Period-256: does F(n'+256, 18) == F(n', 18) for all n' in [3087, 3087+256)?
F18_list = [F18_vals[n] for n in sorted(F18_vals.keys())]
period256 = all(F18_list[i] == F18_list[i+256] for i in range(256))
period128 = all(F18_list[i] == F18_list[i+128] for i in range(128))
period64  = all(F18_list[i] == F18_list[i+64] for i in range(64))

pr(f"  m=18 F-sequence period check:")
pr(f"    period-256: {period256}")
pr(f"    period-128: {period128} (subperiod? False means 256 is minimal)")
pr(f"    period-64:  {period64}  (finer subperiod?)")
pr(f"  Runtime: {time.time()-t0:.1f}s")
save()

# m=32: period verification
pr("")
pr("m=32: verifying period structure in [3087, 7183)...")
F32_list = [F32[n] for n in sorted(F32.keys())]
if len(F32_list) == 4096:
    period4096_32 = all(True for i in range(1))  # just check SubcaseB
    period2048_32 = all(F32_list[i] == F32_list[i+2048] for i in range(2048))
    period1024_32 = all(F32_list[i] == F32_list[i+1024] for i in range(1024))
    pr(f"  m=32 F-sequence (only F values from diagonal scan):")
    pr(f"    period-2048: {period2048_32} (is P=4096 minimal? False means 2048 suffices)")
    pr(f"    period-1024: {period1024_32}")
else:
    pr(f"  m=32 scan returned {len(F32_list)} values (expected 4096)")
pr(f"  m=32 SubcaseB hits in [3087,7183): {len(hits32)}")
save()

# ================================================================
# Q3: Period minimality for active m (comprehensive)
# ================================================================
pr("")
pr("Q3: Period minimality for active m (all periods ≤ 4096)")
pr("-" * 40)
pr("")

period_check_results = {}

for m, P in [(4,8),(6,16),(8,32),(10,64),(12,64),(14,64),
             (16,256),(20,256),(22,256),(24,512),(26,1024),(28,2048),(30,4096)]:
    # Diagonal F scan for 2 periods
    F_vals = diagonal_F_scan(m, N_START, N_START + 2*P)
    F_list = [F_vals[n] for n in sorted(F_vals.keys())]

    if len(F_list) < 2*P:
        pr(f"  m={m}: only {len(F_list)} values, skip")
        continue

    # Check minimal period
    period_P_ok = all(F_list[i] == F_list[i+P] for i in range(P))
    period_halfP = P // 2
    period_halfP_ok = all(F_list[i] == F_list[i+period_halfP] for i in range(period_halfP)) if period_halfP >= 1 else False

    if period_halfP_ok:
        verdict = f"SHORTER PERIOD POSSIBLE: P/2={period_halfP} also works for F!"
    else:
        verdict = f"Period P={P} is minimal for F-sequence"

    pr(f"  m={m:2d}: P={P:5d}, period_P_ok={period_P_ok}, period_P/2_ok={period_halfP_ok} → {verdict}")
    period_check_results[m] = (period_P_ok, period_halfP_ok)

save()

# ================================================================
# FINAL SUMMARY
# ================================================================
pr("")
pr("=" * 60)
pr("FINAL SUMMARY — Adversarial Review Loop 20")
pr("=" * 60)
pr("")

pr("Q1 — Active m-set completeness for m in {28, 30, 32}:")
pr(f"  m=28: {'ACTIVE (OK)' if hits28 else 'INACTIVE (MISMATCH!)'} — {len(hits28)} hits in 2 periods")
pr(f"  m=30: {'ACTIVE (OK)' if hits30 else 'NOT ACTIVE in 1 period (check larger window)!'}")
pr(f"  m=32: {'INACTIVE (OK)' if not hits32 else 'ACTIVE (MISMATCH!)'} — {len(hits32)} hits in 1 period")
pr("")

pr("Q2 — Permanent inactivity of inactive positions:")
pr(f"  m=18: SubcaseB in 4 periods = {len(m18_hits_4p)}, period-256={period256}, period-128={period128}")
if period128:
    pr(f"  FINDING: m=18 F-sequence has period 128, NOT 256! Paper overclaims period.")
    pr(f"           But the SubcaseB condition (F=0 AND G=1) may still have period 256.")
elif period256:
    pr(f"  CONFIRMED: m=18 period-256 is minimal (period-128 fails).")
pr(f"  m=32: SubcaseB in 1 period = {len(hits32)}")
if len(F32_list) == 4096:
    pr(f"  m=32: F-sequence period-2048={period2048_32}")
    if period2048_32:
        pr(f"  FINDING: m=32 F-sequence has period 2048, not 4096!")
        pr(f"           Paper claims period 4096 for m=32 — may overclaim by 2x.")
pr("")

pr("Q3 — Period minimality:")
problems = [(m, P) for m, (p_ok, hp_ok) in period_check_results.items()
            if hp_ok for P in [CLAIMED_PERIOD.get(m, 0)]]
if problems:
    pr(f"  FINDINGS: Some active m have shorter F-periods than claimed!")
    for m, P in problems:
        hp = P // 2
        pr(f"    m={m}: claimed P={P}, but P/2={hp} works for F-sequence!")
else:
    pr(f"  All checked active m have minimal periods (P/2 doesn't work for F-sequence).")
pr("")

save()
pr(f"Results written to {OUTPUT}")
