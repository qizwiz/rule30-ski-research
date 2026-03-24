#!/usr/bin/env python3
"""
Adversarial Review Loop 41 — Active m-set completeness above m=38
Run date: 2026-03-24

TARGET CLAIM (weakest in paper):
  "m=40,42,44 are inactive (SubcaseB never occurs)"
  - m=40: checked to n'=110000 (loop-16, resonance test at n'=16403)
  - m=42: triangle method to n'=20001 + exhaustive G-check in [3087,7000)
  - m=44: triangle method to n'=20001 + exhaustive G-check in [3087,7000)

WHY THIS IS THE WEAKEST CLAIM:
  - F-periods: m=40→65536=2^16, m=42→131072=2^17, m=44→(predicted)262144=2^18
  - For m=42, F-period = 131072, so resonant SubcaseB (if it exists) should appear
    near n' ~ 65536 + 3087 = 68623. The triangle scan only goes to n'=20001.
  - For m=44, F-period = 262144, resonant n' ~ 131072 + 3087 = 134159. Far beyond any scan.
  - The paper's coverage for m=42,44 is STRUCTURALLY WEAK: it covers less than 1/3 of
    one F-period for m=42, and less than 1/16 of one F-period for m=44.
  - The paper compares this to m=40's comprehensive coverage (n'=110000 > F-period=65536)
    but doesn't flag the asymmetry for m=42,44.

INVESTIGATION PLAN:
  1. Verify F-period of m=42 is 131072 (certified by loop-27). Run independently.
  2. Run triangle scan for m=42,44 to n'=500 to understand the F/G structure.
  3. Run the resonance test: check F(n',m) and G(n',m) at the predicted
     first-SubcaseB resonant positions for m=42 and m=44.
  4. For m=40: extend the known check. Run F(n',40) and G(n',40) for n' in [3087,500].
     Confirm this matches "only (0,0) and (1,1) in [3087,500)".
  5. Assess: does the paper need a caveat about m=42,44 coverage being < 1 full F-period?

METHOD:
  - F(n',m) = center cell after n'+1 steps from spike at position m, open-boundary tape
  - G(n',m) = center cell after n'+1 steps from two-spike tape (spikes at m and last=2n'+2)
  - SubcaseB = (F=0, G=1)
  - Rule 30: new[i] = old[i-1] XOR (old[i] OR old[i+1])

All computations use numpy vectorization.
"""

import numpy as np
import time
import sys

# ============================================================
# Core CA functions
# ============================================================

def rule30_step(row):
    """Apply one step of Rule 30 to a 1D boolean array (open boundary = 0 outside)."""
    left  = np.roll(row, 1); left[0]  = 0
    right = np.roll(row, -1); right[-1] = 0
    return left ^ (row | right)

def ca_evolve(tape, n_steps):
    """Evolve tape for n_steps, return final tape."""
    for _ in range(n_steps):
        tape = rule30_step(tape)
    return tape

def make_spike(m, width):
    """Make boolean array of given width with 1 at position m."""
    tape = np.zeros(width, dtype=bool)
    tape[m] = True
    return tape

def compute_F_single(n_prime, m):
    """
    Compute F(n', m) = center cell after (n'+1) steps from spike at position m.
    Tape width = 2*(n'+1)+1, center = n'+1.
    """
    n = n_prime + 1
    width = 2*n + 1
    tape = make_spike(m, width)
    tape = ca_evolve(tape, n)
    return bool(tape[n])

def compute_G_single(n_prime, m):
    """
    Compute G(n', m) = center cell after (n'+1) steps from two-spike tape.
    Spikes at positions m and last = 2*(n'+1)+1 - 1 = 2*n'+2 (0-indexed: position 2n'+2).
    Tape width = 2*(n'+1)+1.
    Center = n'+1.
    """
    n = n_prime + 1
    width = 2*n + 1
    tape = make_spike(m, width)
    last = 2*n_prime + 2   # = width - 1
    tape[last] = True
    tape = ca_evolve(tape, n)
    return bool(tape[n])

def compute_FG_range(m, n_start, n_end):
    """
    Compute (F(n',m), G(n',m)) for n' in [n_start, n_end).
    Returns list of (n', F, G) tuples.
    Uses individual computations (safe but slow for large ranges).
    """
    results = []
    for n_prime in range(n_start, n_end):
        F = compute_F_single(n_prime, m)
        G = compute_G_single(n_prime, m)
        results.append((n_prime, F, G))
    return results

def compute_F_triangle(m, N_max):
    """
    Compute F(n', m) for n' = 0..N_max-1 using a single CA triangle.
    Much faster than computing each F individually.

    Uses tape of width 2*N_max+1. The center cell after (n'+1) steps
    is extracted from each row of the evolving CA.
    """
    width = 2*N_max + 1
    tape = make_spike(m, width)
    F_vals = np.zeros(N_max, dtype=bool)
    for step in range(1, N_max + 1):
        tape = rule30_step(tape)
        n_prime = step - 1
        center = N_max  # fixed center of the large tape
        # The actual center for generation n'+1 is at position n'+1 in the
        # open-boundary tape. In a fixed-width tape, we need to check if the
        # spike's influence has reached the boundaries.
        # For the triangle method: center cell of the large tape = F(N_max-1, m)
        # is NOT what we want. We want the center of each shrinking cone.
        # Correct: center for F(n', m) is position n'+1 in width 2*(n'+1)+1.
        # In the large tape, this is just position step (= n'+1).
        # NOTE: this works because the large tape has enough zeros on both sides
        # that the evolution matches the open-boundary result for each n'.
        F_vals[n_prime] = tape[step]
    return F_vals

# ============================================================
# F-period certificate check (Lean-style)
# ============================================================

def check_F_period_certificate(m, P):
    """
    Check: caEvolve(P)(spike_m(2P+2m+1)) = spike_m(2m+1)
    i.e., evolving spike at position m in tape of size 2P+2m+1 for P steps
    returns a tape equal to spike_m in tape of size 2m+1.

    Returns (passes, time_s).
    """
    width = 2*P + 2*m + 1
    tape = make_spike(m, width)
    t0 = time.time()
    tape = ca_evolve(tape, P)
    elapsed = time.time() - t0
    # After P steps, the tape should be spike_m in the smaller width (2m+1),
    # padded with zeros. The center of the tape is at position P+m.
    # Actually: certificate checks that tape[P+m] = True (center of result) and
    # tape[P+m - j] = False for j != 0 within the 2m+1 window,
    # and tape[P+m + j] = False similarly.
    # Simplified: the final tape restricted to the causal window should equal spike_m.
    # Since spike_m(2m+1) has 1 only at position m, we check:
    center = P + m
    passes = bool(tape[center]) and not any(tape[center-m:center]) and not any(tape[center+1:center+m+1])
    return passes, elapsed

def check_F_period_certificate_v2(m, P):
    """
    Alternative: check that F(n'+P, m) == F(n', m) for n' in a window.
    This is the empirical period check rather than the Lean-style cert.
    More robust but requires F_triangle.
    """
    N_test = P + 200  # check P values past some offset
    F_vals = compute_F_triangle(m, N_test)
    # Check F(3087+k+P) == F(3087+k) for k=0..99
    base = 3087
    if base + P + 100 >= N_test:
        return None, 0  # range too small
    mismatches = 0
    for k in range(100):
        if F_vals[base + k] != F_vals[base + k + P]:
            mismatches += 1
    return (mismatches == 0), mismatches

# ============================================================
# Resonance test: where would the first SubcaseB be if m were active?
# ============================================================

def resonance_prediction(m, P_m):
    """
    Under the doubling law, if m were active with F-period P_m,
    the first SubcaseB event should appear near n' ~ P_m/2 + 3087.
    (Analogous to m=38: P=32768, first hit at n'=8210 ~ 3087 + P/4? Actually let's check.)

    Known data points:
    - m=38: P=32768, first SubcaseB at n'=8210  → offset = 8210-3087 = 5123 ~ P/6.4
    - m=36: P=16384, first SubcaseB at n'=4113  → offset = 4113-3087 = 1026 ~ P/16
    - m=34: P=8192,  first SubcaseB at n'=4112  → offset = 4112-3087 = 1025 ~ P/8
    - m=30: P=4096,  first SubcaseB at n'=4112  → offset = 4112-3087 = 1025 ~ P/4

    No simple formula. But the resonance for inactive m=40: paper says n'=16403 is (0,0).
    16403 - 3087 = 13316. P_40 = 65536. 13316 ~ P/5.

    For m=42 (P=131072): resonance would be at n' ~ 3087 + 13316*2 = 29719?
    Or using the (last-m) = 2^k criterion from the paper:
    - m=40 resonance at last-m = 2^15: last = 2n'+2, m=40, so 2n'+2-40=2^15 → n'=(32768+38)/2=16403. Correct!
    - m=42 resonance at last-m = 2^16: 2n'+2-42=65536 → n'=(65536+40)/2=32788.
    - m=44 resonance at last-m = 2^17: 2n'+2-44=131072 → n'=(131072+42)/2=65557.

    So the resonance tests for m=42,44 are at n'=32788 and n'=65557 respectively.
    The paper checks m=40 at n'=16403 but does NOT report checking m=42 at n'=32788!
    """
    if m == 40:
        return 16403  # (last-m = 2^15)
    elif m == 42:
        return 32788  # (last-m = 2^16)
    elif m == 44:
        return 65557  # (last-m = 2^17)
    else:
        # Generic: last-m = P_m/2, so n' = (P_m/2 + m - 2) / 2
        return (P_m // 2 + m - 2) // 2

# ============================================================
# Main investigation
# ============================================================

def main():
    print("=" * 70)
    print("ADVERSARIAL REVIEW LOOP 41")
    print("Target: Active m-set completeness above m=38")
    print("Date: 2026-03-24")
    print("=" * 70)

    results = {}

    # ----------------------------------------------------------
    # PART 1: Quick sanity check — verify known active m=38
    # ----------------------------------------------------------
    print("\n--- PART 1: Sanity check — m=38 (known active, P=32768) ---")
    t0 = time.time()
    F38 = compute_F_single(8210, 38)
    G38 = compute_G_single(8210, 38)
    t1 = time.time()
    print(f"  m=38, n'=8210: F={int(F38)}, G={int(G38)}  (expect F=0, G=1 = SubcaseB)")
    print(f"  Time: {t1-t0:.2f}s")

    if not (F38 == False and G38 == True):
        print("  ERROR: Known SubcaseB event at (38, 8210) not confirmed!")
        results['sanity_m38'] = 'FAILED'
    else:
        print("  PASS: Known SubcaseB confirmed.")
        results['sanity_m38'] = 'PASS'

    # ----------------------------------------------------------
    # PART 2: Triangle method scan for m=40,42,44 up to n'=500
    # ----------------------------------------------------------
    print("\n--- PART 2: F-sequence for m=40,42,44 in [0, 500) ---")
    for m in [40, 42, 44]:
        t0 = time.time()
        F_vals = compute_F_triangle(m, 500)
        t1 = time.time()
        n_ones = np.sum(F_vals[3087:] if 500 > 3087 else F_vals)
        n_ones_all = np.sum(F_vals)
        print(f"  m={m}: F=1 count in [0,500) = {n_ones_all}, time={t1-t0:.2f}s")
        # Show first few F=0 positions
        f0_positions = np.where(~F_vals[:min(100, 500)])[0]
        print(f"    First F=0 positions (up to n'=100): {list(f0_positions[:20])}")

    # ----------------------------------------------------------
    # PART 3: Triangle method for m=40,42,44 up to n'=2000
    # Check F(n',m) for all n' in [0,2000), look at structure
    # ----------------------------------------------------------
    print("\n--- PART 3: Extended triangle scan for m=40,42,44 up to n'=2000 ---")
    for m in [40, 42, 44]:
        t0 = time.time()
        N = 2000
        F_vals = compute_F_triangle(m, N)
        t1 = time.time()
        f0_positions = np.where(~F_vals)[0].tolist()
        f1_positions = np.where(F_vals)[0].tolist()
        print(f"  m={m}: F-sequence in [0,{N}): "
              f"{np.sum(F_vals)} ones, {np.sum(~F_vals)} zeros, time={t1-t0:.2f}s")
        print(f"    F=0 gaps (first 10 gaps between consecutive F=1): ", end='')
        f1_arr = np.array(f1_positions)
        if len(f1_arr) > 1:
            gaps = np.diff(f1_arr[:20])
            print(list(gaps[:10]))
        else:
            print("too few F=1 values to compute gaps")
        print(f"    First 5 F=0 positions: {f0_positions[:5]}")
        print(f"    Last 5 F=1 positions:  {f1_positions[-5:]}")

    # ----------------------------------------------------------
    # PART 4: THE KEY TEST — Resonance test at predicted first-SubcaseB positions
    # Paper reports m=40 resonance (0,0) at n'=16403. But does NOT report m=42 resonance!
    # ----------------------------------------------------------
    print("\n--- PART 4: RESONANCE TEST for m=40,42,44 ---")
    print("  Predicted resonance n' values (last-m = 2^k criterion):")
    print("  m=40: n'=16403  (paper reports this as (0,0) — but we verify independently)")
    print("  m=42: n'=32788  (paper does NOT report checking this!)")
    print("  m=44: n'=65557  (paper does NOT report checking this!)")
    print()

    resonance_points = {
        40: [16403, 8211, 32787],  # last-m = 2^15, 2^14, 2^16
        42: [32788, 16404, 65572], # last-m = 2^16, 2^15, 2^17
        44: [65557, 32794, 131093],# last-m = 2^17, 2^16, 2^18
    }

    for m in [40, 42, 44]:
        print(f"  m={m} resonance checks:")
        for n_prime in resonance_points[m]:
            t0 = time.time()
            F = compute_F_single(n_prime, m)
            G = compute_G_single(n_prime, m)
            t1 = time.time()
            subcaseB = (F == False and G == True)
            flag = " *** SUBCASEB ***" if subcaseB else ""
            print(f"    n'={n_prime:7d}: F={int(F)}, G={int(G)}{flag}  ({t1-t0:.2f}s)")
        print()

    results['resonance_m40_16403'] = None  # will be set below

    # ----------------------------------------------------------
    # PART 5: Dense scan for m=42,44 in a targeted range
    # If F-period of m=42 is 131072, check n' in [3087, 500] densely for SubcaseB
    # ALSO: check at the analogous "offset 5123" position (like m=38's first hit)
    # For m=38: first SubcaseB at n'=8210 = 3087 + 5123 = 3087 + P/6.4
    # For m=40 (if active): would be at n'=3087 + 5123*2 ~ 13333 (not seen)
    # For m=42 (if active with P=131072): would be at n' ~ 3087 + 5123*4 ~ 23579
    # ----------------------------------------------------------
    print("\n--- PART 5: Dense SubcaseB scan for m=42,44 in [3087, 500] ---")
    # Small range to be fast
    for m in [42, 44]:
        t0 = time.time()
        subcaseB_events = []
        f0_G_checked = 0
        for n_prime in range(3087, 3200):
            F = compute_F_single(n_prime, m)
            if not F:
                G = compute_G_single(n_prime, m)
                f0_G_checked += 1
                if G:
                    subcaseB_events.append(n_prime)
        t1 = time.time()
        print(f"  m={m}, n' in [3087,3200): SubcaseB={subcaseB_events}, "
              f"F=0 candidates checked={f0_G_checked}, time={t1-t0:.2f}s")

    # ----------------------------------------------------------
    # PART 6: Check the "analogy offset" positions for m=42,44
    # Pattern from active m: first SubcaseB near 3087 + (specific offsets)
    # m=34: offset 1025; m=36: offset 1026; m=38: offset 5123
    # If m=42 were active, extrapolate the offset
    # Also test at n' = 3087 + offsets that match the mod-4 structure
    # ----------------------------------------------------------
    print("\n--- PART 6: Analogy-offset and mod-4 window checks for m=42,44 ---")
    # For m=38, first hit at n'=8210, period=32768
    # For m=40 (inactive), resonance n'=16403 gives (0,0)
    # If m=42 followed the pattern: first hit at n'=8210+2*5123=18456? Or some other pattern
    # Let's check a range around the predicted "analogous first hit" positions

    analogy_ranges = {
        42: [(8210, 8230), (18456, 18476), (16404, 16424), (32788, 32808)],
        44: [(8210, 8230), (32788, 32808), (65557, 65577)],
    }

    for m, ranges in analogy_ranges.items():
        print(f"\n  m={m} analogy checks:")
        for (lo, hi) in ranges:
            events = []
            t0 = time.time()
            for n_prime in range(lo, hi):
                F = compute_F_single(n_prime, m)
                G = compute_G_single(n_prime, m)
                if not F and G:
                    events.append((n_prime, int(F), int(G)))
            t1 = time.time()
            if events:
                print(f"    n' in [{lo},{hi}): SUBCASEB FOUND: {events}  ({t1-t0:.2f}s)")
            else:
                sample = []
                for n_prime in range(lo, min(lo+5, hi)):
                    F = compute_F_single(n_prime, m)
                    G = compute_G_single(n_prime, m)
                    sample.append(f"({int(F)},{int(G)})")
                print(f"    n' in [{lo},{hi}): 0 SubcaseB. First-5 FG: {' '.join(sample)}  ({t1-t0:.2f}s)")

    # ----------------------------------------------------------
    # PART 7: Summarize coverage gap analysis
    # ----------------------------------------------------------
    print("\n--- PART 7: Coverage gap analysis ---")
    coverage_analysis = {
        'm=40': {
            'F_period': 65536,
            'max_checked': 110000,
            'periods_covered': 110000 / 65536,
            'resonance_checked': True,
            'resonance_result': '(0,0) at n\'=16403',
        },
        'm=42': {
            'F_period': 131072,
            'max_checked': 20001,
            'periods_covered': 20001 / 131072,
            'resonance_checked': False,  # KEY FINDING
            'resonance_result': 'NOT CHECKED (n\'=32788)',
        },
        'm=44': {
            'F_period': '~262144 (predicted)',
            'max_checked': 20001,
            'periods_covered': 20001 / 262144.0,
            'resonance_checked': False,  # KEY FINDING
            'resonance_result': 'NOT CHECKED (n\'=65557)',
        },
    }

    print("\n  Coverage summary:")
    hdr = "max n' checked"
    print(f"  {'m':>4} | {'F-period':>12} | {hdr:>15} | {'periods':>8} | {'resonance':>10}")
    print(f"  {'-'*4}-+-{'-'*12}-+-{'-'*15}-+-{'-'*8}-+-{'-'*10}")
    for m_str, info in coverage_analysis.items():
        p_cov = info['periods_covered'] if isinstance(info['periods_covered'], float) else 0
        print(f"  {m_str:>4} | {str(info['F_period']):>12} | {info['max_checked']:>15} | "
              f"{p_cov:>7.2f}x | {'YES' if info['resonance_checked'] else 'NO':>10}")

    print("\n  KEY FINDING: m=42 and m=44 have NOT been checked at their resonance points!")
    print("  m=42: resonance at n'=32788 is the analog of m=40's n'=16403 check.")
    print("        The paper reports m=40 resonance (0,0) as 'decisive', but the")
    print("        analogous check for m=42 is ABSENT from the paper.")
    print("  m=44: resonance at n'=65557 also unchecked.")
    print()
    print("  PAPER CLAIM STRENGTH:")
    print("  - m=40: STRONG (1.68x F-period coverage + resonance test)")
    print("  - m=42: WEAK  (0.15x F-period coverage, no resonance test)")
    print("  - m=44: VERY WEAK (0.076x F-period coverage, no resonance test)")

    # ----------------------------------------------------------
    # PART 8: Actually run the m=42 resonance test (n'=32788)
    # This is computationally expensive (~30s) but decisive
    # ----------------------------------------------------------
    print("\n--- PART 8: CRITICAL — Running m=42 resonance test at n'=32788 ---")
    print("  (This is O(n'^2) ~ 32788^2 ~ 10^9 operations; using numpy...)")

    t0 = time.time()
    F42 = compute_F_single(32788, 42)
    t1 = time.time()
    print(f"  m=42, n'=32788: F={int(F42)}  ({t1-t0:.2f}s)")

    if not F42:  # F=0, so SubcaseB is possible
        t2 = time.time()
        G42 = compute_G_single(32788, 42)
        t3 = time.time()
        subcaseB_42 = (not F42 and G42)
        print(f"  m=42, n'=32788: G={int(G42)}  ({t3-t2:.2f}s)")
        if subcaseB_42:
            print(f"  *** SUBCASEB FOUND at m=42, n'=32788! Paper claim is WRONG! ***")
            results['m42_resonance'] = 'SUBCASEB_FOUND'
        else:
            print(f"  m=42, n'=32788: (F=0, G=0) — consistent with inactivity")
            results['m42_resonance'] = f'(0,{int(G42)}) — no SubcaseB'
    else:
        print(f"  m=42, n'=32788: F=1, so SubcaseB impossible here (F must be 0)")
        results['m42_resonance'] = f'F=1 — resonance test inconclusive for SubcaseB but (1,G)≠SubcaseB'

    # Also check n'=32788+4 (mod-4 neighbor, as SubcaseB often comes in pairs for active m)
    print(f"\n  Also checking n'=32792 (32788+4, mod-4 neighbor):")
    t0 = time.time()
    F42b = compute_F_single(32792, 42)
    G42b = compute_G_single(32792, 42)
    t1 = time.time()
    print(f"  m=42, n'=32792: F={int(F42b)}, G={int(G42b)}  ({t1-t0:.2f}s)")
    subcaseB_42b = (not F42b and G42b)
    if subcaseB_42b:
        print(f"  *** SUBCASEB FOUND at m=42, n'=32792! ***")
        results['m42_resonance_plus4'] = 'SUBCASEB_FOUND'
    else:
        results['m42_resonance_plus4'] = f'({int(F42b)},{int(G42b)}) — no SubcaseB'

    # ----------------------------------------------------------
    # PART 9: Check m=44 resonance at n'=65557 if time permits
    # ----------------------------------------------------------
    print("\n--- PART 9: m=44 resonance test at n'=65557 ---")
    print("  (O(n'^2) ~ 65557^2 ~ 4×10^9 operations; may be slow...)")

    t0 = time.time()
    F44 = compute_F_single(65557, 44)
    t1 = time.time()
    print(f"  m=44, n'=65557: F={int(F44)}  ({t1-t0:.2f}s)")

    if not F44:
        t2 = time.time()
        G44 = compute_G_single(65557, 44)
        t3 = time.time()
        subcaseB_44 = (not F44 and G44)
        print(f"  m=44, n'=65557: G={int(G44)}  ({t3-t2:.2f}s)")
        if subcaseB_44:
            print(f"  *** SUBCASEB FOUND at m=44, n'=65557! ***")
            results['m44_resonance'] = 'SUBCASEB_FOUND'
        else:
            print(f"  m=44, n'=65557: (F=0, G={int(G44)}) — consistent with inactivity")
            results['m44_resonance'] = f'(0,{int(G44)}) — no SubcaseB'
    else:
        print(f"  m=44, n'=65557: F=1 — SubcaseB impossible here")
        results['m44_resonance'] = f'F=1 at resonance'

    # ----------------------------------------------------------
    # FINAL SUMMARY
    # ----------------------------------------------------------
    print("\n" + "=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)

    print("\nResults dictionary:")
    for k, v in results.items():
        print(f"  {k}: {v}")

    subcaseb_found = any('SUBCASEB_FOUND' in str(v) for v in results.values())

    if subcaseb_found:
        print("\n*** PAPER CORRECTION NEEDED: SubcaseB found above m=38! ***")
        print("    Active set M_act is INCOMPLETE.")
    else:
        print("\nNo SubcaseB found above m=38 in tested positions.")
        print("Inactivity supported, but coverage gap for m=42,44 is real:")
        print("  - m=42 resonance test now performed (loop 41 — new)")
        print("  - m=44 resonance test now performed (loop 41 — new)")
        print("\nPaper should add: resonance tests at n'=32788 (m=42) and n'=65557 (m=44)")
        print("to match the evidentiary standard applied to m=40.")

    return results, subcaseb_found


if __name__ == '__main__':
    t_total = time.time()
    results, found = main()
    print(f"\nTotal time: {time.time()-t_total:.1f}s")
    sys.exit(0 if not found else 1)
