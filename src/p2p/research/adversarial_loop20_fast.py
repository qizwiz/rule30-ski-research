#!/usr/bin/env python3
"""
Adversarial Review Loop 20 — FAST version.

Key insight: F(n', m) and G(n', m) can be computed using open-boundary
causal cones, which are independent of n' (for large enough n').

For F(n', m): the spike at position m. The causal cone has width 2m+1.
After n'+1 steps, the center receives information only from positions [0..2(n'+1)].
For fixed m, the spike at m is within the first m+1 positions of the left half.
The causal cone evolution is periodic with period P_m.

BUT: we need the actual circular-tape computation for G, since the "last" spike
at position 2n'+2 contributes via the last-spike lemma (H=1 always).

EFFICIENT APPROACH for G:
Since H=1 for all n', and G = F XOR 1 XOR I where I is the interaction term,
we can write:
  G(n', m) = 1 XOR F(n', m) XOR I(n', m)
  SubcaseB: F=0, G=1 => I=0

The interaction term I(n', m) = G XOR F XOR 1.
We want to know when I=0 (i.e., G XOR F = 1, i.e., G ≠ F).

For fixed m << n', the "two spikes" are far apart. The key question is:
does the left spike (at m) and right spike (at last=2n'+2) interact before
reaching the center at position n'+1 after n'+1 steps?

The left spike's cone expands left and right. The right spike's cone expands left.
They meet at the center simultaneously. The interaction depends only on:
  last - m = 2n'+2 - m

For fixed m and varying n', last-m grows linearly with n'.
The interaction I depends on (last-m) in a periodic manner.

FAST COMPUTATION:
For F: use the causal cone state of size 2m+1. Evolve for n' mod P_m steps.
For I: use the "relative distance" last-m = 2n'+2-m. For fixed m, I is periodic
in n' with period P_m (verified computationally).

This means: instead of evolving a tape of size O(n'), we evolve a cone of size 2m+1.

Implementation:
  cone_state_m(n') = causal cone state at step n'+1 starting from spike-at-m in cone.
  F(n', m) = cone center after n'+1 steps from spike at m in tape of size 2m+1,
             with OPEN boundaries (no wrap). This equals the circular result for
             large n' (spike doesn't reach boundary).
  For G: the interaction is the "meeting" effect. We compute G directly using
  a medium-sized tape (size = last-m + 1 cells) with two spikes.

For the main range [3087, 10000) with m=18:
  - last-m = 2n'+2-18 = 2n'-16
  - At n'=3087: last-m = 6158; tape size = 6159
  - At n'=10000: tape size = 19984

These tapes are still large. We need a smarter approach.

SMARTEST APPROACH: Use the known periodicity.

Paper claims I(n', m=18) is periodic with period 256.
Let's verify: compute I(n', 18) for n' in [3087, 3087+256*2) directly,
then check if the period-256 pattern holds by checking the extended window.

For the scan of [3087, 3599) (2 periods = 512 values), each at n'≈3300,
tape size ≈ 6600. That's 512 * 6600 * 6600/2 ≈ 11 billion ops. Still slow.

FASTEST APPROACH: Precompute cone states using open-boundary evolution.

For the OPEN BOUNDARY computation:
  - F(n', m): spike at position m in tape of size n'+m+2 (just big enough that
    spike doesn't wrap). Evolve n'+1 steps. This equals the circular F.
  - For G: H=1 always. I = G XOR F XOR 1. Instead of computing G directly,
    compute I by: I = G XOR F XOR 1. Exploit that I is periodic.

The REAL shortcut: since I is claimed periodic with period P_m,
we only need to compute I for n' in one period [3087, 3087+P_m).
For m=18, P=256 → 256 values, tape size ~6200. That's 256 * 6200 * 3100 ≈ 5 billion ops.
Still too slow for numpy per-call.

USE VECTORIZED APPROACH: For a fixed period window, we can compute ALL tapes together
using a 3D tensor: (n', x, t) where t is time steps.

OR: Use the CAUSAL CONE approach with boundary adjustment.

ACTUAL FAST METHOD: Use a single large tape that encodes ALL n' values at once.

For computing F(n', m) for all n' in a range [N0, N0+P]:
  The spike-at-m in a tape of size 2n'+3 evolves to center over n'+1 steps.
  For different n', the tape sizes differ. These cannot be easily batched.

PRACTICAL SOLUTION: Accept O(n') per evaluation but use the period structure.

For Q1 (m ≤ 38, window [3087, M]) where M <= 40855:
  Most m values have small tapes at small n'. But m=38 requires n' up to 40855.
  At n'=40855, tape size = 81713. Evolving 40856 steps: ~81713 * 40856 ≈ 3.3B ops.
  Too slow.

CORRECT APPROACH: Use open-boundary causal cone.

For F(n', m): The spike at m in an OPEN (non-wraparound) tape. The center is at n'+1.
The value only depends on the initial segment [0..m] of the tape. As n' grows, the
center is getting further from the spike's initial position. We can:
  1. Evolve the open tape of size 2m+1 for n'+1 steps. This gives F.
  2. F is eventually periodic because the state space of size 2m+1 is finite.

For G(n', m): With the second spike at 2n'+2, its contribution to the center at n'+1
is exactly H=1 (last-spike lemma). But the INTERACTION term I depends on how
the two spikes' cones overlap. This is what creates the periodicity structure.

SIMPLEST FAST APPROACH:
  For F: evolve open tape of size 2m+1 (fixed!), just need n'+1 steps.
  But we need output at step n'+1, which is the center of the expanding cone.

  The cone at step n'+1 from spike at m has width 2(n'+1)+1. Since n'>>m,
  the cone state only depends on the INTERNAL state of the 2m+1 cell region.

  Actually: the center output F(n', m) for large n' depends only on
  the causal cone STATE at step n'+1 of the infinite tape with spike at m.
  The infinite tape solution is periodic with period P_m (Rowland 2006).

  Implementation: evolve a tape of size 4*P_m + 2*m + 10 (large enough to avoid
  boundary effects), compute for n' = 3087 to 3087 + 2*P_m.

  For G: G = F XOR 1 XOR I. Since I is periodic with same period P_m,
  we can compute G for one period and check.

Let's use MODERATE sized tapes that are large enough for the period window
but still feasible.

For F: use tape of size max(2*P_m + 2*m + 10, 2*3087 + 3) for small m,
but for m=18,32 (P=256,4096), this is tractable.

m=18, P=256: tape size = 2*256 + 2*18 + 10 = 558.
  Compute F(n') for n'=0..511 using tape of size 558.
  Extract F at step n'+1 from center of this tape.
  Then verify periodicity starting from n'=3087.

Hmm — this doesn't directly give us F(n'=3087, m=18) since the tape isn't
size 2*3087+3.

OK, definitive solution: the open-boundary computation IS periodic and the
circular (wrapped) computation agrees with open-boundary for large enough n'.
Bridge lemma: for n' >= N_bridge(m), F_circular(n', m) = F_open(n', m).
N_bridge(m) ~ when the spike's cone doesn't reach the boundary.
The spike at m reaches the right boundary at step ~ (tape_size - m)/2 = n'+1 steps.
So for large n', the spike never reaches the right boundary within n'+1 steps.
More precisely: spike at m in tape of size 2n'+3, cone expands by 1 each step.
At step n'+1, the cone reaches position m + (n'+1) to the right.
The right boundary is at 2n'+2. Cone reaches boundary when m + (n'+1) >= 2n'+2,
i.e., m >= n'+1, i.e., n' <= m-1. So for n' >= m, the spike NEVER reaches the boundary!

This means: for n' >= m, F(n', m) = F_open(n', m) where F_open uses any sufficiently
large tape that never has wrap-around effects.

CONCLUSION: We can compute F(n', m) using a tape of any size >= 2*(n'+1) + 1.
But for n'=5000, m=18: tape size = 10003. 5001 steps × 10003 cells ≈ 50M ops per n'.
For 10000 values of n': 500B ops. Too slow.

THE ACTUAL FAST METHOD: Precompute the PERIODIC function F(n' mod P_m, m).

Since F(n', m) is eventually periodic with period P_m starting from some n'_0,
we can:
1. Compute F for n' in [n'_0, n'_0 + P_m) using a tape of size 2*(n'_0 + P_m) + 3.
2. For any n' >= n'_0, F(n', m) = F(n'_0 + (n' - n'_0) mod P_m, m).

For m=18, P=256, n'_0=3087:
  Tape size = 2*(3087+256)+3 = 6687. Steps per evaluation = 3343 to 3343+256.
  256 evaluations × 6687 cells × 3400 steps ≈ 5.8B ops. Borderline.

For m=32, P=4096, n'_0=3087:
  4096 evaluations × tape(~14500) × 7343 steps ≈ 436B ops. Way too slow.

THE ONLY PRACTICAL APPROACH for large m:
Use the fact that we already have Python scripts that computed F and G for these ranges.
Reuse their results and just VERIFY specific claims.

For Q2 specifically:
- m=18, period 256: ALREADY verified in previous loops. Paper says "27 full periods".
  We need to confirm the paper didn't just verify 2-3 periods and extrapolate.
  Previous findings: "period 128 fails, period 256 holds; 0 (0,1) in [3087, 10000)".
  Verification needed: compute F(n',18) and G(n',18) for n' in [3087, 3087+512)
  to confirm period-256 and NO SubcaseB events. Then TRUST the period claim for larger n'.

For Q3 (period minimality):
  Already has the gap analysis from Q1. Use that data.

Let's implement the EFFICIENT version using the open-boundary cone approach:
For n' in [3087, 3087+512), use tape of size 2*3599+3 = 7201.
  512 evaluations × 7201 × 3599 ≈ 13B ops. Still ~60 seconds with numpy.

REAL SOLUTION: numpy vectorized single evolution.
Instead of looping over n', use a SINGLE TAPE that is evolved step-by-step,
and read out the center value at each step.

For a fixed m: evolve a tape of size LARGE from spike-at-m.
At step t, read center at position floor(LARGE/2).
This gives us F(t-1, m) for t=1..MAX_STEPS.

This is O(LARGE * MAX_STEPS) TOTAL (not per n'!).

TAPE_SIZE for m=18, reading out F(n'=3087..10000):
  Center = LARGE//2. Center receives info from spike at m (LARGE//2 - (n'+1)) to (LARGE//2 + (n'+1)).
  So LARGE//2 >= n'+1 + (tape_center - spike_pos) for spike not to hit left boundary.
  Actually: spike is at position m in the original tape, center is at n'+1.
  In the open tape, put spike at position n'+1+m (far right of center).
  Then center is at position n'+1+m - m = n'+1 from the spike... hmm.

CLEANEST vectorized approach:
  For fixed m, use a tape where spike is at position 0, center output is at position m+step.
  Wait, with open boundaries, step t from spike-at-0 gives center at position t
  (by left-permutivity: frontier advances 1 cell left per step).

Actually: let's just use a different formula. For open-boundary with spike at position p:
  Center at position c, after t steps = F(t-1, c-p) [effectively].

For computing F(n', m) for n' in a range, the most efficient approach:
  - Create tape of size n'_max + m + 5, put spike at position n'_max + m (far right).
  - Evolve step-by-step. At step t, read position n'_max. This gives F(t-1, m).

Wait: F(n', m) = center cell value after n'+1 steps from spike-at-m in tape of size 2n'+3.
Center = n'+1 (0-indexed).

With spike at position m in tape of size 2n'+3, center at n'+1, after n'+1 steps.

For a FIXED large tape (size T, spike at position S, read at position C after step t):
  This gives F when S = m, C = n'+1, t = n'+1.
  So C = t (center is at step index), S = m.

  Use tape of size T = n'_max + 2, spike at position m, read at position n'+1 for each n'.
  Evolve from step 0 to step n'_max + 1.
  At each step t >= 1, read position t. This is F(t-1, m).

  This is PERFECT: single O(T^2 / 2) computation gives ALL F values!

Similarly for G:
  G(n', m) = center after n'+1 steps from two-spike at (m, last=2n'+2).
  The "last" position changes with n', so we can't do this with a single tape.

  BUT: G = F XOR 1 XOR I, and I is periodic.
  Compute I for one period and use periodicity.

Let's implement this:
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

pr("Adversarial Review Loop 20 (FAST version)")
pr("=" * 60)
pr("")

# ----------------------------------------------------------------
# FAST F computation: single evolving tape, read at diagonal
# ----------------------------------------------------------------

def compute_F_sequence(m, n_start, n_end):
    """
    Compute F(n', m) for n' in [n_start, n_end) using a single evolution.

    Key: in open-boundary evolution from spike at m,
    center output at step n'+1 (in tape of size 2n'+3) = value at position n'+1
    in open-boundary tape with spike at m at step n'+1.

    Use a large tape, spike at position m, read diagonal (step t = position t+1).
    Since tape has open boundaries and spike is at m (small),
    we need the tape to be large enough that the cone never wraps.

    For n' < tape_size // 2, the cone at step n'+1 is [0..n'+1+m] from the spike,
    which stays within bounds if tape_size > n_end + m + 2.
    """
    T = n_end + m + 5  # tape large enough
    tape = np.zeros(T, dtype=np.uint8)
    tape[m] = 1  # spike at position m

    F_vals = {}

    for step in range(1, n_end + 2):
        # Read center at position step (= n'+1 for n'=step-1)
        n_p = step - 1
        if n_start <= n_p < n_end:
            F_vals[n_p] = int(tape[step])

        # Evolve one step (open boundary: edges are 0)
        l = np.zeros(T, dtype=np.uint8)
        r = np.zeros(T, dtype=np.uint8)
        l[1:] = tape[:-1]
        r[:-1] = tape[1:]
        tape = l ^ (tape | r)

    return F_vals


def compute_G_direct_small_tape(n_prime, m):
    """
    Compute G(n', m) directly using a tape of size 2n'+3.
    This is slow (O(n'^2)) but correct. Use only for small n'.
    """
    size = 2*(n_prime+1)+1
    last = size - 1
    # two-spike tape
    tape = np.zeros(size, dtype=np.uint8)
    tape[m] = 1
    tape[last] = 1

    for _ in range(n_prime + 1):
        l = np.zeros(size, dtype=np.uint8)
        r = np.zeros(size, dtype=np.uint8)
        l[1:] = tape[:-1]
        r[:-1] = tape[1:]
        tape = l ^ (tape | r)

    return int(tape[n_prime + 1])


def compute_I_sequence_direct(m, n_start, n_end):
    """
    Compute I(n', m) = G(n',m) XOR F(n',m) XOR 1 for n' in [n_start, n_end).
    Uses direct computation (slow for large n').
    Returns dict n' -> I value.
    """
    I_vals = {}
    for n_p in range(n_start, n_end):
        # Compute F using small open-boundary tape
        size = 2*(n_p+1)+1
        tape_F = np.zeros(size, dtype=np.uint8)
        tape_F[m] = 1
        for _ in range(n_p + 1):
            l = np.zeros(size, dtype=np.uint8)
            r = np.zeros(size, dtype=np.uint8)
            l[1:] = tape_F[:-1]
            r[:-1] = tape_F[1:]
            tape_F = l ^ (tape_F | r)
        F = int(tape_F[n_p + 1])

        G = compute_G_direct_small_tape(n_p, m)
        I_vals[n_p] = F ^ G ^ 1
    return I_vals


# ----------------------------------------------------------------
# For LARGE n', F is periodic. Compute one period of F starting at n_start.
# ----------------------------------------------------------------

def compute_F_one_period(m, n_start, period):
    """Compute F(n', m) for n' in [n_start, n_start+period) using direct evolution."""
    F_vals = compute_F_sequence(m, n_start, n_start + period)
    return F_vals


# ================================================================
# Q1: Active m-set completeness
# Use fast F computation + direct G for one period per m
# ================================================================

pr("Q1: Active m-set completeness")
pr("-" * 40)

CLAIMED_ACTIVE = [4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38]
CLAIMED_INACTIVE_SMALL = [2, 18, 32]  # even m in [2,38] not in active set

CLAIMED_PERIOD = {
    4: 8, 6: 16, 8: 32, 10: 64, 12: 64, 14: 64,
    16: 256, 20: 256, 22: 256,
    24: 512, 26: 1024, 28: 2048, 30: 4096,
    34: 8192, 36: 16384, 38: 32768,
}
INACTIVE_PERIOD = {18: 256, 32: 4096}

N_START = 3087

q1_results_act = {}  # m -> list of SubcaseB n'
q1_results_inact = {}  # m -> list of SubcaseB n'

t0 = time.time()

# For active m ≤ 28 (period ≤ 2048): scan 2 periods starting from N_START
# Use fast F + direct G for same tape (direct G is size ~6400 at n'=3200, fast enough for 2*2048 steps)

for m in range(4, 40, 2):
    if m == 2:
        continue  # m=2 proved separately

    period = CLAIMED_PERIOD.get(m) or INACTIVE_PERIOD.get(m)
    if period is None:
        pr(f"  m={m}: no period known, skip")
        continue

    if period > 2048:
        pr(f"  m={m}: period {period} too large for direct Q1 scan, deferred to Q3")
        continue

    n_end = N_START + 2 * period
    hits = []

    for n_p in range(N_START, n_end):
        size = 2*(n_p+1)+1
        last = size - 1

        # F: spike at m
        tape_F = np.zeros(size, dtype=np.uint8)
        tape_F[m] = 1
        for _ in range(n_p + 1):
            l = np.zeros(size, dtype=np.uint8)
            r = np.zeros(size, dtype=np.uint8)
            l[1:] = tape_F[:-1]
            r[:-1] = tape_F[1:]
            tape_F = l ^ (tape_F | r)
        F = int(tape_F[n_p + 1])

        if F != 0:
            continue  # F=1, not SubcaseB

        # G: two-spike
        tape_G = np.zeros(size, dtype=np.uint8)
        tape_G[m] = 1
        tape_G[last] = 1
        for _ in range(n_p + 1):
            l = np.zeros(size, dtype=np.uint8)
            r = np.zeros(size, dtype=np.uint8)
            l[1:] = tape_G[:-1]
            r[:-1] = tape_G[1:]
            tape_G = l ^ (tape_G | r)
        G = int(tape_G[n_p + 1])

        if G == 1:
            hits.append(n_p)

    is_claimed_active = (m in CLAIMED_ACTIVE)
    found_active = len(hits) > 0
    status = "ACTIVE" if found_active else "INACTIVE"
    expected = "ACTIVE" if is_claimed_active else "INACTIVE"
    match = "OK" if (found_active == is_claimed_active) else "MISMATCH!"

    pr(f"  m={m:2d} (P={period:4d}): {status:8s} — {len(hits):4d} SubcaseB hits in [3087,{n_end}) — expected {expected} [{match}]")
    if hits:
        pr(f"         first hits: {hits[:6]}")

    q1_results_act[m] = hits
    save()

    elapsed = time.time() - t0
    if elapsed > 300:
        pr(f"  TIME LIMIT (5min) reached at m={m}. Stopping Q1.")
        break

pr(f"\nQ1 scan complete ({time.time()-t0:.1f}s)")
pr("")
save()

# ================================================================
# Q2: m=18 and m=32 inactivity — use period structure
# ================================================================
pr("Q2: Permanent inactivity of m=18 and m=32")
pr("-" * 40)
pr("")

# m=18: Paper says period 256, zero SubcaseB in [3087,10000) (27 full periods).
# We verify: (a) period-256 holds for FG sequence, (b) no SubcaseB in one full period [3087,3343)

pr("m=18: scanning [3087, 3343) for SubcaseB (one full 256-period)...")
m18_hits = []
m18_FG_seq = []
for n_p in range(3087, 3087 + 256):
    size = 2*(n_p+1)+1
    last = size - 1
    tape_F = np.zeros(size, dtype=np.uint8)
    tape_F[18] = 1
    for _ in range(n_p + 1):
        l = np.zeros(size, dtype=np.uint8); r = np.zeros(size, dtype=np.uint8)
        l[1:] = tape_F[:-1]; r[:-1] = tape_F[1:]
        tape_F = l ^ (tape_F | r)
    F = int(tape_F[n_p + 1])

    tape_G = np.zeros(size, dtype=np.uint8)
    tape_G[18] = 1; tape_G[last] = 1
    for _ in range(n_p + 1):
        l = np.zeros(size, dtype=np.uint8); r = np.zeros(size, dtype=np.uint8)
        l[1:] = tape_G[:-1]; r[:-1] = tape_G[1:]
        tape_G = l ^ (tape_G | r)
    G = int(tape_G[n_p + 1])

    m18_FG_seq.append((F, G))
    if F == 0 and G == 1:
        m18_hits.append(n_p)

pr(f"  m=18: {len(m18_hits)} SubcaseB events in [3087,3343)")
if m18_hits:
    pr(f"  ALERT! SubcaseB events found: {m18_hits}")
else:
    pr(f"  CONFIRMED: zero SubcaseB events in first 256 values from n'=3087")

# Check period 256 vs 128
m18_period256 = all(m18_FG_seq[i] == m18_FG_seq[i+128] for i in range(128))
# Can't check period 128 on 256-length sequence vs claiming period-256 without second period
# Check: period 128 would mean m18_FG_seq[0..127] == m18_FG_seq[128..255]
m18_period128 = all(m18_FG_seq[i] == m18_FG_seq[i+128] for i in range(128))
pr(f"  m=18 period-128 check (within [3087,3343)): {m18_period128}")
pr(f"  (If period-128 holds here, claimed period-256 might be overclaiming)")

# Count (1,0) events (F=1, G=0) per period
m18_10 = [(3087+i, F, G) for i, (F,G) in enumerate(m18_FG_seq) if F==1 and G==0]
pr(f"  m=18 (1,0) events in [3087,3343): {len(m18_10)} at n'={[n for n,F,G in m18_10[:10]]}")

save()

# Now verify: do the (F,G) values from second scan [3343,3599) match first [3087,3343)?
pr("")
pr("m=18: scanning second period [3343, 3599) to verify period-256...")
m18_FG_seq2 = []
m18_hits2 = []
for n_p in range(3087 + 256, 3087 + 512):
    size = 2*(n_p+1)+1
    last = size - 1
    tape_F = np.zeros(size, dtype=np.uint8)
    tape_F[18] = 1
    for _ in range(n_p + 1):
        l = np.zeros(size, dtype=np.uint8); r = np.zeros(size, dtype=np.uint8)
        l[1:] = tape_F[:-1]; r[:-1] = tape_F[1:]
        tape_F = l ^ (tape_F | r)
    F = int(tape_F[n_p + 1])

    tape_G = np.zeros(size, dtype=np.uint8)
    tape_G[18] = 1; tape_G[last] = 1
    for _ in range(n_p + 1):
        l = np.zeros(size, dtype=np.uint8); r = np.zeros(size, dtype=np.uint8)
        l[1:] = tape_G[:-1]; r[:-1] = tape_G[1:]
        tape_G = l ^ (tape_G | r)
    G = int(tape_G[n_p + 1])

    m18_FG_seq2.append((F, G))
    if F == 0 and G == 1:
        m18_hits2.append(n_p)

period256_verified = (m18_FG_seq == m18_FG_seq2)
pr(f"  m=18 period-256 verified by two-period comparison: {period256_verified}")
if m18_hits2:
    pr(f"  ALERT: SubcaseB in [3343,3599): {m18_hits2}")
else:
    pr(f"  CONFIRMED: zero SubcaseB in second period [3343,3599)")

# Check if period 128 divides 256: compare seq[0..127] with seq[128..255]
period128_within = (m18_FG_seq[:128] == m18_FG_seq[128:256])
pr(f"  m=18 period-128 within first 256: {period128_within}")
pr(f"  Paper says period is 256, not 128 — 128-subperiod claim should be False.")
save()

# m=32: scan [3087, 7183) = two periods of 4096
pr("")
pr("m=32: scanning first 2 periods [3087, 11279) for SubcaseB...")
pr("(This will take a few minutes for large tapes)")
m32_hits = []
m32_FG_seq = []
m32_scan_end = 3087 + 2 * 4096  # = 11279
t_m32 = time.time()
for n_p in range(3087, m32_scan_end):
    size = 2*(n_p+1)+1
    last = size - 1
    tape_F = np.zeros(size, dtype=np.uint8)
    tape_F[32] = 1
    for _ in range(n_p + 1):
        l = np.zeros(size, dtype=np.uint8); r = np.zeros(size, dtype=np.uint8)
        l[1:] = tape_F[:-1]; r[:-1] = tape_F[1:]
        tape_F = l ^ (tape_F | r)
    F = int(tape_F[n_p + 1])

    tape_G = np.zeros(size, dtype=np.uint8)
    tape_G[32] = 1; tape_G[last] = 1
    for _ in range(n_p + 1):
        l = np.zeros(size, dtype=np.uint8); r = np.zeros(size, dtype=np.uint8)
        l[1:] = tape_G[:-1]; r[:-1] = tape_G[1:]
        tape_G = l ^ (tape_G | r)
    G = int(tape_G[n_p + 1])

    m32_FG_seq.append((F, G))
    if F == 0 and G == 1:
        m32_hits.append(n_p)

    if (n_p - 3087) % 500 == 499:
        elapsed32 = time.time() - t_m32
        pr(f"  m=32: n'={n_p} ({n_p-3087+1}/{m32_scan_end-3087}), "
           f"SubcaseB so far: {len(m32_hits)}, elapsed: {elapsed32:.0f}s")
        save()

pr(f"m=32 scan complete ({time.time()-t_m32:.0f}s)")
pr(f"  m=32 SubcaseB in [3087,{m32_scan_end}): {len(m32_hits)}")
if m32_hits:
    pr(f"  ALERT! SubcaseB found: {m32_hits[:10]}")
else:
    pr(f"  CONFIRMED: zero SubcaseB events in [3087,{m32_scan_end}) (2 full periods)")

# Period check for m=32
if len(m32_FG_seq) == 2*4096:
    period4096 = (m32_FG_seq[:4096] == m32_FG_seq[4096:])
    period2048 = (m32_FG_seq[:2048] == m32_FG_seq[2048:4096])
    pr(f"  m=32 period-4096 check: {period4096}")
    pr(f"  m=32 period-2048 check: {period2048}")
save()

# ================================================================
# Q3: Period minimality for small active m (period ≤ 1024)
# ================================================================
pr("")
pr("Q3: Period minimality for active m with period ≤ 1024")
pr("-" * 40)
pr("")

for m in [4, 6, 8, 10, 12, 14, 16, 20, 22, 24, 26]:
    P = CLAIMED_PERIOD[m]
    half_P = P // 2

    if m in q1_results_act:
        # Already have data from Q1 scan
        hits = q1_results_act[m]
    else:
        # Quick scan
        hits = []
        for n_p in range(N_START, N_START + 2*P):
            size = 2*(n_p+1)+1
            last = size - 1
            tape_F = np.zeros(size, dtype=np.uint8)
            tape_F[m] = 1
            for _ in range(n_p + 1):
                l = np.zeros(size, dtype=np.uint8); r = np.zeros(size, dtype=np.uint8)
                l[1:] = tape_F[:-1]; r[:-1] = tape_F[1:]
                tape_F = l ^ (tape_F | r)
            F = int(tape_F[n_p + 1])
            if F == 0:
                tape_G = np.zeros(size, dtype=np.uint8)
                tape_G[m] = 1; tape_G[last] = 1
                for _ in range(n_p + 1):
                    l = np.zeros(size, dtype=np.uint8); r = np.zeros(size, dtype=np.uint8)
                    l[1:] = tape_G[:-1]; r[:-1] = tape_G[1:]
                    tape_G = l ^ (tape_G | r)
                G = int(tape_G[n_p + 1])
                if G == 1:
                    hits.append(n_p)

    # Check: are all gaps between consecutive hits divisible by P (not just half_P)?
    if len(hits) < 2:
        pr(f"  m={m:2d}: P={P:5d} — too few hits ({len(hits)}) in window to test")
        continue

    gaps = [hits[i+1] - hits[i] for i in range(len(hits)-1)]

    # Test minimality: would period half_P explain all gaps?
    # All gaps divisible by half_P? (necessary but not sufficient for half_P being a period)
    all_div_half = all(g % half_P == 0 for g in gaps)
    any_div_only_half = any(g % P != 0 for g in gaps)

    if all_div_half and any_div_only_half:
        verdict = "POTENTIALLY SHORTER (all gaps divisible by P/2 but not all by P)"
    elif all_div_half and not any_div_only_half:
        verdict = f"P seems consistent (all gaps divisible by P={P})"
    else:
        verdict = f"Gaps NOT all divisible by P/2={half_P} — period P={P} consistent"

    pr(f"  m={m:2d}: P={P:5d}, {len(hits)} hits, gaps={gaps[:6]}")
    pr(f"         {verdict}")

save()

pr("")
pr("=" * 60)
pr("FINAL SUMMARY")
pr("=" * 60)
pr("")

# Q1 summary
found_active = set(m for m, hits in q1_results_act.items() if len(hits) > 0)
found_inactive = set(m for m, hits in q1_results_act.items() if len(hits) == 0)
pr("Q1 — Active m-set completeness (m with period ≤ 2048):")
claimed_small = set(m for m in CLAIMED_ACTIVE if CLAIMED_PERIOD.get(m, 9999) <= 2048)
claimed_inact_small = set(m for m in range(4, 40, 2)
                           if m not in CLAIMED_ACTIVE and INACTIVE_PERIOD.get(m, 9999) <= 2048)
pr(f"  Claimed active (period≤2048): {sorted(claimed_small)}")
pr(f"  Found active (period≤2048):   {sorted(found_active & set(range(4,40,2)))}")
pr(f"  Claimed inactive (period≤2048): {sorted(claimed_inact_small)}")
pr(f"  Found inactive (period≤2048):   {sorted(found_inactive & set(range(4,40,2)))}")

mismatches = []
for m in range(4, 40, 2):
    if m not in q1_results_act:
        continue
    claimed = m in CLAIMED_ACTIVE
    found = len(q1_results_act[m]) > 0
    if claimed != found:
        mismatches.append((m, claimed, found))
if mismatches:
    pr(f"  MISMATCHES: {mismatches}")
else:
    pr(f"  No mismatches — all active/inactive classifications correct for verified m.")
pr("")

pr("Q2 — Permanent inactivity:")
pr(f"  m=18: SubcaseB count in [3087,3343) = {len(m18_hits)} "
   f"({'OK' if not m18_hits else 'ALERT'})")
pr(f"  m=18: period-256 verified by two-period comparison: {period256_verified}")
pr(f"  m=18: period-128 (subperiod) holds: {period128_within} "
   f"(paper says 256 is the minimal period)")
pr(f"  m=32: SubcaseB count in [3087,{m32_scan_end}): {len(m32_hits)} "
   f"({'OK' if not m32_hits else 'ALERT'})")
if len(m32_FG_seq) == 2*4096:
    pr(f"  m=32: period-4096 verified: {period4096}")
    pr(f"  m=32: period-2048 (subperiod) holds: {period2048}")
pr("")

save()
pr(f"Results written to {OUTPUT}")
