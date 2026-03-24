#!/usr/bin/env python3
"""
Adversarial Review Loop 40 — Period verification for early active m-values
Run date: 2026-03-24

TARGET CLAIMS (paper lines 537-583):

1. Period table: m=4→8, m=6→16, m=8→32, m=10,12,14→64, m=16,20,22→256, m=24→512
2. The "doubling law kicks in at m≥24" — the block m={16,20,22} ALL have period 256
   (three positions, not a simple doubling)
3. m=16 has period 256 with 3 hits per period at offsets {0,4,72} (gaps 4,68,184)
4. m=20 has period 256 with 1 hit per period
5. m=22 has period 256 with 1 hit per period
6. m=24 has period 512 (first step of doubling law)

SUSPICIOUS PATTERN TO INVESTIGATE:
- m=16 is listed with "period 256" but has a complex internal structure (3 hits vs 1-2 for neighbors)
- m=22 and m=20 both have period 256 — is this a real plateau or two coincidental 256s?
- The doubling law claim says m≥24. What happens at exactly m=22 and m=24?
  If m=22→256 and m=24→512, that's a factor-of-2 doubling (consistent with law).
  If m=22→512 (not 256), that would mean the plateau is only {16,20} and m=22 starts doubling.
- Loop-20 found: m=22 has period 256 with residue {14} mod 256 (one event per period).
  But loop-24 found residues for m=22 at exactly period 256. Is 512 ruled out?

METHOD:
Use the compute_F_triangle function to directly compute F(n', m) for all n' in [0, N_max)
from a single CA triangle. This gives the EXACT F sequence without any bias.
Then:
  (a) Find the period of F(n', m) by looking at the spacing of SubcaseB events
  (b) Verify the period via F-certificate: caEvolve(P)(spike_m(2P+2m+1)) = spike_m(2m+1)
  (c) Check that P/2 fails as a period
  (d) For m=16 specifically: verify the 3-hits-per-period internal structure
  (e) For m=22 specifically: verify only 1 hit per period at residue 14 mod 256
  (f) For m=20 specifically: verify only 1 hit per period at residue 13 mod 256

Also directly compute SubcaseB events (F=0, G=1) using compute_G_single for the first
few events of each m value, to verify the period from SubcaseB spacing.
"""

import numpy as np
import time
import sys

# ============================================================
# Core CA functions (provided in task spec)
# ============================================================

def compute_F_triangle(m, N_max):
    """
    Compute F(n', m) for n' = 0..N_max-1 using a single CA triangle.
    F(n', m) = center cell after n'+1 steps from spike at position m,
    in an open-boundary tape of width 2*(n'+1)+1.

    Key insight: the leftmost cell after k steps of open-boundary evolution from
    spike_m in tape size 2*N_max+1 equals F(k-1, m) = center after k steps
    (actually it equals the leftmost cell of the shrinking cone).

    Implementation: use one large triangle:
      - Start: array of length 2*N_max+1 with 1 at position m
      - At step k: leftmost cell = F(k-1, m)
    """
    a = np.zeros(2 * N_max + 1, dtype=np.uint8)
    a[m] = 1
    F = np.zeros(N_max, dtype=np.uint8)
    for k in range(1, N_max + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
        F[k - 1] = a[0]
    return F


def compute_G_single(n_prime, m):
    """
    Compute G(n', m): center cell after n'+1 steps from two-spike tape:
    spike at m AND spike at last = 2n'+2, in tape of size 2n'+3.
    SubcaseB = (F=0 AND G=1).
    """
    L = 2 * (n_prime + 1) + 1
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L - 1] = 1
    for _ in range(n_prime + 1):
        if len(g) < 3:
            break
        g = g[:-2] ^ (g[1:-1] | g[2:])
    return bool(g[0])


def caEvolve(n_steps, a):
    """Apply Rule 30 open-boundary for n_steps steps (array shrinks by 2 per step)."""
    a = a.copy()
    for _ in range(n_steps):
        if len(a) < 3:
            break
        a = a[:-2] ^ (a[1:-1] | a[2:])
    return a


def f_cert_check(m, P):
    """
    Check F-period certificate: caEvolve(P)(spike_m(2*P+2*m+1)) == spike_m(2*m+1).
    Returns (holds: bool, mismatch_positions: list).
    """
    L_in = 2 * P + 2 * m + 1
    L_out = 2 * m + 1
    a = np.zeros(L_in, dtype=np.uint8)
    a[m] = 1
    result = caEvolve(P, a)
    expected = np.zeros(L_out, dtype=np.uint8)
    if m < L_out:
        expected[m] = 1
    if len(result) != len(expected):
        return False, [f"length mismatch: got {len(result)}, expected {len(expected)}"]
    mismatches = [i for i in range(len(result)) if result[i] != expected[i]]
    return len(mismatches) == 0, mismatches


# ============================================================
# Period detection from F sequence
# ============================================================

def find_period_from_F(F, claimed_P, candidates_to_check=None):
    """
    Given F(n') sequence, verify whether the sequence has period claimed_P.
    Also check claimed_P/2 to test minimality.

    Returns dict with:
      - period_P_holds: bool
      - period_P_half_holds: bool
      - actual_period: estimated from SubcaseB spacing (if detectable)
      - first_mismatch_P: n' where F(n') != F(n'+P) (or None if P holds)
      - first_mismatch_P_half: same for P/2
    """
    N = len(F)

    # Check period P
    period_P_holds = True
    first_mismatch_P = None
    check_limit = min(N - claimed_P, 5000)
    for n in range(check_limit):
        if F[n] != F[n + claimed_P]:
            period_P_holds = False
            first_mismatch_P = n
            break

    # Check period P/2
    P_half = claimed_P // 2
    period_P_half_holds = True
    first_mismatch_P_half = None
    check_limit_half = min(N - P_half, 5000)
    for n in range(check_limit_half):
        if F[n] != F[n + P_half]:
            period_P_half_holds = False
            first_mismatch_P_half = n
            break

    return {
        'period_P_holds': period_P_holds,
        'period_P_half_holds': period_P_half_holds,
        'first_mismatch_P': first_mismatch_P,
        'first_mismatch_P_half': first_mismatch_P_half,
    }


def find_subcaseB_events(m, F, N_max, n_start=3087, max_events=10):
    """
    For each n' in [n_start, N_max) where F[n']=0, compute G(n', m) and
    collect SubcaseB events (F=0, G=1).
    Returns list of SubcaseB n' values (up to max_events).
    """
    events = []
    n_prime_vals = [n for n in range(n_start, min(N_max, len(F))) if F[n] == 0]
    print(f"    m={m}: found {len(n_prime_vals)} F=0 candidates in [{n_start}, {min(N_max, len(F))})")
    for n_prime in n_prime_vals:
        if len(events) >= max_events:
            break
        g = compute_G_single(n_prime, m)
        if g:
            events.append(n_prime)
    return events


def analyze_spacing(events, claimed_P):
    """
    Given a list of SubcaseB event positions, analyze their spacing
    and check consistency with period claimed_P.
    """
    if len(events) < 2:
        return {'gaps': [], 'consistent_with_period': None}
    gaps = [events[i+1] - events[i] for i in range(len(events)-1)]
    # Check if spacing is consistent with period: each gap should divide claimed_P
    # or be exactly claimed_P (for singletons per period)
    consistent = all(claimed_P % g == 0 or g % claimed_P == 0 for g in gaps)
    return {'gaps': gaps, 'consistent_with_period': consistent}


# ============================================================
# Main analysis
# ============================================================

# Period table from paper
CLAIMED_PERIODS = {
    4:  8,
    6:  16,
    8:  32,
    10: 64,
    12: 64,
    14: 64,
    16: 256,
    20: 256,
    22: 256,
    24: 512,  # included to verify the transition
}

# Expected SubcaseB residues from loop-20 findings.md
EXPECTED_RESIDUES = {
    4:  [5],
    6:  [6, 10],
    8:  [11],
    10: [48],
    12: [9, 13],
    14: [10, 14],
    16: [135, 139, 207],   # 3 hits per period at offsets {0,4,72} from first hit
    20: [13],
    22: [14],
    24: [267, 271],        # pairs
}

def main():
    print("=" * 70)
    print("ADVERSARIAL REVIEW LOOP 40")
    print("Period verification for early active m-values: m in {4,6,8,10,12,14,16,20,22,24}")
    print("Run date: 2026-03-24")
    print("=" * 70)
    print()

    results = {}

    for m in [4, 6, 8, 10, 12, 14, 16, 20, 22, 24]:
        claimed_P = CLAIMED_PERIODS[m]
        # We need enough n' to check at least 3 full periods starting from 3087
        # i.e., N_max >= 3087 + 3*P
        N_max = 3087 + 3 * claimed_P + 200
        print(f"\n{'='*60}")
        print(f"m = {m}, claimed period P = {claimed_P}")
        print(f"Computing F triangle: N_max = {N_max}")
        t0 = time.time()
        F = compute_F_triangle(m, N_max)
        t1 = time.time()
        print(f"  Triangle computed in {t1-t0:.2f}s")

        # Step 1: Verify period P holds and P/2 fails
        pcheck = find_period_from_F(F, claimed_P)

        print(f"  Period P={claimed_P} holds: {pcheck['period_P_holds']}", end="")
        if pcheck['first_mismatch_P'] is not None:
            print(f"  (first mismatch at n'={pcheck['first_mismatch_P']}: F={F[pcheck['first_mismatch_P']]}, F+P={F[pcheck['first_mismatch_P']+claimed_P]})", end="")
        print()

        P_half = claimed_P // 2
        print(f"  Period P/2={P_half} holds: {pcheck['period_P_half_holds']}", end="")
        if pcheck['first_mismatch_P_half'] is not None:
            print(f"  (first mismatch at n'={pcheck['first_mismatch_P_half']}: F={F[pcheck['first_mismatch_P_half']]}, F+P/2={F[pcheck['first_mismatch_P_half']+P_half]})", end="")
        print()

        # Step 2: F-certificate check
        print(f"  Checking F-cert(P={claimed_P})...", end=" ", flush=True)
        t0 = time.time()
        cert_P_holds, cert_P_mismatches = f_cert_check(m, claimed_P)
        t1 = time.time()
        print(f"holds={cert_P_holds}, time={t1-t0:.3f}s", end="")
        if not cert_P_holds:
            print(f"  FAIL: mismatches at positions {cert_P_mismatches[:5]}", end="")
        print()

        print(f"  Checking F-cert(P/2={P_half})...", end=" ", flush=True)
        t0 = time.time()
        cert_Ph_holds, cert_Ph_mismatches = f_cert_check(m, P_half)
        t1 = time.time()
        print(f"holds={cert_Ph_holds}, time={t1-t0:.3f}s", end="")
        if cert_Ph_holds:
            print(f"  WARNING: P/2 cert PASSES — period may divide P/2!", end="")
        else:
            print(f"  (fails at positions {cert_Ph_mismatches[:3]})", end="")
        print()

        # Step 3: Find actual SubcaseB events in [3087, 3087+3*P)
        # to determine period from spacing
        search_end = min(3087 + 3 * claimed_P + 100, N_max)
        print(f"  Finding SubcaseB events in [3087, {search_end})...")
        t0 = time.time()
        subcaseB_events = find_subcaseB_events(m, F, search_end, n_start=3087, max_events=12)
        t1 = time.time()
        print(f"  SubcaseB events found: {subcaseB_events[:12]} ({t1-t0:.1f}s)")

        if len(subcaseB_events) >= 2:
            spacing = analyze_spacing(subcaseB_events, claimed_P)
            print(f"  Gaps between events: {spacing['gaps']}")
            print(f"  Consistent with period {claimed_P}: {spacing['consistent_with_period']}")

            # Check if spacing suggests a different (shorter) period
            if len(subcaseB_events) >= 3:
                # Look for the cluster-repeat period: gap from first cluster to next cluster
                # For m=16: events at offsets 0,4,72 within period; cluster repeats at P
                # The "cluster period" is the gap from first event to first event of next period
                # Find events that are exactly claimed_P apart
                e0 = subcaseB_events[0]
                cluster_matches = [e for e in subcaseB_events if abs((e - e0) % claimed_P) == 0 and e != e0]
                if cluster_matches:
                    print(f"  First cluster at n'={e0}, next at n'={cluster_matches[0]}, gap={cluster_matches[0]-e0}")
                else:
                    print(f"  No repeat of first cluster found in window (may need larger range)")

        # Step 4: Verify SubcaseB spacing matches claimed_P
        # Find SubcaseB events that are "period apart"
        if len(subcaseB_events) >= 2:
            # Check that each event e has a corresponding event at e + P in the window
            print(f"  Checking period-P pairs (n', n'+{claimed_P}):")
            for e in subcaseB_events[:5]:
                e2 = e + claimed_P
                if e2 < search_end:
                    f_at_e2 = int(F[e2]) if e2 < len(F) else '?'
                    g_at_e2 = compute_G_single(e2, m) if e2 < search_end else '?'
                    subcaseB_e2 = (f_at_e2 == 0 and g_at_e2 == True)
                    print(f"    n'={e}: SubcaseB=True, n'={e2}: F={f_at_e2}, G={g_at_e2}, SubcaseB={subcaseB_e2}")

        # Step 5: Verify residues match expected
        if m in EXPECTED_RESIDUES:
            exp_res = EXPECTED_RESIDUES[m]
            if subcaseB_events:
                actual_residues = sorted(set(e % claimed_P for e in subcaseB_events))
                print(f"  Expected residues mod {claimed_P}: {sorted(exp_res)}")
                print(f"  Actual residues found:           {actual_residues}")
                # The expected residues are computed relative to a different base;
                # let's compute from the first event
                if subcaseB_events:
                    e0 = subcaseB_events[0]
                    base = e0 - (e0 % claimed_P)
                    within_period_offsets = sorted(set((e - base) % claimed_P for e in subcaseB_events))
                    print(f"  Within-period offsets (relative to period boundary n'={base}): {within_period_offsets}")

        results[m] = {
            'claimed_P': claimed_P,
            'period_P_holds': pcheck['period_P_holds'],
            'period_P_half_holds': pcheck['period_P_half_holds'],
            'cert_P_holds': cert_P_holds,
            'cert_Ph_holds': cert_Ph_holds,
            'subcaseB_events': subcaseB_events[:12],
        }

    # ============================================================
    # Summary
    # ============================================================
    print()
    print("=" * 70)
    print("SUMMARY TABLE")
    print("=" * 70)
    print(f"{'m':>4} {'P_claimed':>10} {'P holds':>8} {'P/2 fails':>10} {'cert(P)':>8} {'cert(P/2) fails':>16} {'SubcaseB events (first 5)':>30}")
    print("-" * 90)
    any_discrepancy = False
    for m in [4, 6, 8, 10, 12, 14, 16, 20, 22, 24]:
        r = results[m]
        P = r['claimed_P']
        P_ok = "OK" if r['period_P_holds'] else "FAIL"
        Ph_ok = "OK" if not r['period_P_half_holds'] else "WARN"
        cert_ok = "OK" if r['cert_P_holds'] else "FAIL"
        cert_ph = "OK" if not r['cert_Ph_holds'] else "WARN"
        events_str = str(r['subcaseB_events'][:5])
        print(f"{m:>4} {P:>10} {P_ok:>8} {Ph_ok:>10} {cert_ok:>8} {cert_ph:>16} {events_str:>30}")
        if not r['period_P_holds'] or r['period_P_half_holds'] or not r['cert_P_holds'] or r['cert_Ph_holds']:
            any_discrepancy = True

    print()
    if any_discrepancy:
        print("⚠️  DISCREPANCY FOUND — see above for details")
    else:
        print("✓ All period claims VERIFIED: periods are correct and minimal.")

    # ============================================================
    # Focused check: m=16 vs m=22 period claim
    # ============================================================
    print()
    print("=" * 70)
    print("FOCUSED CHECK: m=16, m=20, m=22 — do they ALL have period 256?")
    print("(Paper claims 256 for all three; user asks if 512 is possible)")
    print("=" * 70)

    for m in [16, 20, 22]:
        r = results[m]
        events = r['subcaseB_events']
        print(f"\nm={m} (claimed P=256):")
        print(f"  SubcaseB events found: {events}")
        if len(events) >= 2:
            gaps = [events[i+1]-events[i] for i in range(len(events)-1)]
            print(f"  Gaps: {gaps}")
            # Check if smallest gap equals 256 (i.e., period is 256 not smaller)
            # Also check if 512 divides all gaps (would mean period is 512)
            if all(g % 512 == 0 for g in gaps):
                print(f"  WARNING: All gaps are multiples of 512 — could period be 512?")
                # Do a direct check
                N2 = 3087 + 1024 + 20
                F2 = compute_F_triangle(m, N2)
                for n_test in range(3087, min(3087+512, N2)):
                    if F2[n_test] != F2[n_test + 512]:
                        print(f"  Period-512 check: FAILS at n'={n_test} → P=256 is confirmed minimal (not 512)")
                        break
                else:
                    print(f"  Period-512 check: HOLDS in [3087, {3087+512}) — ambiguous, need more data")
            elif all(g % 256 == 0 for g in gaps):
                print(f"  All gaps divisible by 256 ✓ (consistent with period 256)")
                if any(g == 256 for g in gaps):
                    print(f"  Found gap = 256 exactly → period = 256 confirmed")
            else:
                print(f"  Irregular gaps — investigate")
        print(f"  Period-256 holds: {r['period_P_holds']}")
        print(f"  Period-128 would hold: {r['period_P_half_holds']}")
        print(f"  F-cert(256) passes: {r['cert_P_holds']}")
        print(f"  F-cert(128) fails: {not r['cert_Ph_holds']}")

    # ============================================================
    # Doubling law transition: m=22 → m=24
    # ============================================================
    print()
    print("=" * 70)
    print("DOUBLING LAW TRANSITION CHECK: m=22 (P=256) → m=24 (P=512)")
    print("Paper: 'clean doubling kicks in at m≥24 — not m≥22'")
    print("Verification: m=22 period should be 256 (NOT 512)")
    print("              m=24 period should be 512 (DOUBLES from m=22)")
    print("=" * 70)
    r22 = results[22]
    r24 = results[24]
    print(f"\nm=22: period 256 holds={r22['period_P_holds']}, P/2=128 holds={r22['period_P_half_holds']}")
    print(f"m=24: period 512 holds={r24['period_P_holds']}, P/2=256 holds={r24['period_P_half_holds']}")

    if r22['period_P_holds'] and not r22['period_P_half_holds'] and r24['period_P_holds'] and not r24['period_P_half_holds']:
        print("\n✓ CONFIRMED: m=22→256 and m=24→512 are both correct minimal periods.")
        print("  The transition from 256 to 512 occurs between m=22 and m=24 (NOT between 20 and 22).")
        print("  m=16, m=20, m=22 are a TRUE plateau at period 256.")
        print("  The doubling law starts at m=24 (as the paper claims).")
    else:
        print("\n⚠️  DISCREPANCY: period claims for m=22 or m=24 are incorrect!")

    # ============================================================
    # m=16 internal structure verification
    # ============================================================
    print()
    print("=" * 70)
    print("m=16 INTERNAL STRUCTURE: Paper claims 3 hits per period at offsets {0,4,72}")
    print("  (gaps 4, 68, 184 summing to 256)")
    print("=" * 70)
    r16 = results[16]
    events16 = r16['subcaseB_events']
    if len(events16) >= 6:
        e0 = events16[0]
        base = e0 - (e0 % 256)
        offsets_in_period = [(e - base) % 256 for e in events16[:9]]
        print(f"  First 9 SubcaseB events: {events16[:9]}")
        print(f"  First period starts at n'={base}")
        # Group into periods
        period_groups = {}
        for e in events16:
            period_idx = (e - events16[0]) // 256
            period_groups.setdefault(period_idx, []).append(e)
        for idx, grp in sorted(period_groups.items()):
            if idx < 3:
                base_e = events16[0] + idx * 256
                offsets = [(e - base_e) for e in grp]
                print(f"  Period {idx}: events={grp}, offsets from start={offsets}")
        # Check gap structure within first period
        if len(events16) >= 3:
            g1 = events16[1] - events16[0]
            g2 = events16[2] - events16[1]
            g3 = events16[3] - events16[2] if len(events16) >= 4 else None
            print(f"  Gaps within/across first two periods: {g1}, {g2}, {g3}")
            if g1 == 4 and g2 == 68 and g3 == 184:
                print(f"  ✓ Internal structure CONFIRMED: gaps (4, 68, 184) sum to 256")
            elif g1 + g2 + g3 == 256 if g3 else False:
                print(f"  Internal structure present but offsets differ from paper claim")
            else:
                print(f"  ⚠️  Gap structure differs from paper's claimed (4, 68, 184)")
    else:
        print(f"  Only {len(events16)} events found — need at least 6 for structure analysis")
        # Extend search for m=16
        print(f"  Extending search to 3*256+3087=3855 for m=16...")
        N16 = 4200
        F16 = compute_F_triangle(16, N16)
        events16_ext = find_subcaseB_events(16, F16, 4200, n_start=3087, max_events=20)
        print(f"  Extended SubcaseB events for m=16: {events16_ext}")
        if len(events16_ext) >= 3:
            gaps16 = [events16_ext[i+1]-events16_ext[i] for i in range(min(5, len(events16_ext)-1))]
            print(f"  Gaps: {gaps16}")

    print()
    print("=" * 70)
    print("LOOP 40 COMPLETE")
    print("=" * 70)


if __name__ == "__main__":
    main()
