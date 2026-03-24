"""
adversarial_loop45.py

Attack target: The paper claims certain even m in [2,38] are "inactive" —
meaning G(n',m)=0 for ALL n' where the SubcaseB condition is applicable
(i.e., n' large enough that m < 2n'+3, so the spike at m is within the tape).

From the paper (Section 4):
  M_act = {4, 6, 8, 10, 12, 14, 16, 20, 22, 24, 26, 28, 30, 34, 36, 38}
  Inactive in [2,38]: {2, 18, 32}

Definitions:
  rule30(l,c,r) = l XOR (c OR r)
  tape size for n': sz = 2*n' + 3, center = n'+1, last = 2*n'+2
  F(n',m): spike at m only, evolved n'+1 steps, read center
           (only meaningful when m < sz, i.e., n' >= ceil((m-2)/2))
  G(n',m): spikes at m AND last=2*n'+2, evolved n'+1 steps, read center
  SubcaseB(n',m) = F(n',m)==0 AND G(n',m)==1

  Valid range for m: n' >= n_min(m) where n_min(m) = ceil((m-2)/2)
    m=2: n_min=0 (always valid)
    m=18: n_min=8
    m=32: n_min=15

For each inactive m, scan G(n',m) for n' in [n_min(m), N_max].
Report any SubcaseB (F=0, G=1) — that would break the paper's claim.
"""

import numpy as np
import sys
import time
import math

def step(tape):
    """One step of Rule 30: rule30(l,c,r) = l XOR (c OR r). Open boundary."""
    l = np.empty_like(tape)
    r = np.empty_like(tape)
    l[1:] = tape[:-1]; l[0] = 0
    r[:-1] = tape[1:]; r[-1] = 0
    return (l ^ (tape | r)).astype(np.uint8)

def compute_F_big_triangle(m, N_min, N_max):
    """
    Compute F(n',m) for all n' in [N_min, N_max] using ONE big tape.

    F(n',m) = center of tape(size=2n'+3, spike at m) after n'+1 steps.

    Using big tape of size W=2*N_max+3 with spike at m:
    At step t = n'+1, by the causal-cone argument, big_tape[t] = F(n'=t-1, m).
    (The center of a tape of size 2n'+3 is at position n'+1 = t in the big tape,
     and the causal cone [0, 2n'+2] contains the spike at m since m <= N_max.)
    """
    W = 2 * N_max + 3
    tape = np.zeros(W, dtype=np.uint8)
    if 0 <= m < W:
        tape[m] = 1

    F = {}
    for t in range(1, N_max + 2):
        tape = step(tape)
        n_prime = t - 1
        if N_min <= n_prime <= N_max:
            F[n_prime] = int(tape[t])  # position t = n'+1 = center
    return F

def compute_G_single(m, n_prime):
    """
    Compute G(n',m) for a single n'.
    G = center of tape(size=2n'+3, spikes at m and last=2n'+2) after n'+1 steps.
    """
    sz = 2 * n_prime + 3
    last = sz - 1  # = 2*n'+2
    center = n_prime + 1

    tape = np.zeros(sz, dtype=np.uint8)
    if m < sz:
        tape[m] = 1
    tape[last] = 1

    for _ in range(n_prime + 1):
        tape = step(tape)

    return int(tape[center])

def n_min_for_m(m):
    """Smallest n' such that m < 2n'+3, i.e., m is within the tape."""
    # m < 2n'+3 => n' > (m-3)/2 => n' >= ceil((m-2)/2)
    return math.ceil((m - 2) / 2)

def scan_m(m, N_max):
    """
    Scan F(n',m) and G(n',m) for n' in [n_min(m), N_max].
    Uses fast big-triangle for F, per-n' for G.
    """
    n_min = n_min_for_m(m)
    print(f"  n_min(m={m}) = {n_min} (spike at m is outside tape for n' < {n_min})")

    print(f"  Building F big-triangle (m={m}, N=[{n_min},{N_max}])...", end='', flush=True)
    t0 = time.time()
    F_dict = compute_F_big_triangle(m, n_min, N_max)
    print(f" {time.time()-t0:.1f}s", flush=True)

    print(f"  Computing G(n',m) for n' in [{n_min},{N_max}]...", end='', flush=True)
    t0 = time.time()

    G_arr = {}
    n_range = list(range(n_min, N_max + 1))

    for i, n_prime in enumerate(n_range):
        G_arr[n_prime] = compute_G_single(m, n_prime)
        if (i + 1) % 1000 == 0:
            elapsed = time.time() - t0
            print(f"\n    n'={n_prime}: {elapsed:.1f}s elapsed", end='', flush=True)

    print(f" total: {time.time()-t0:.1f}s", flush=True)

    return F_dict, G_arr, n_min


def main():
    # All even m in [2,38]
    all_even = list(range(2, 40, 2))
    M_act = {4, 6, 8, 10, 12, 14, 16, 20, 22, 24, 26, 28, 30, 34, 36, 38}
    inactive = [m for m in all_even if m not in M_act]

    print("=" * 70)
    print("ADVERSARIAL LOOP 45: Inactive m verification (valid n' range only)")
    print("=" * 70)
    print(f"All even m in [2,38]: {all_even}")
    print(f"M_act (active, per paper): {sorted(M_act)}")
    print(f"Inactive m in [2,38] (claimed by paper): {inactive}")
    print()

    # Scan ranges: cover known periods with buffer, from n_min(m) to N_max.
    # m=2:  n_min=0, Lean-proved inactive. Scan [0, 1000].
    # m=18: n_min=8, period 256, verified clean in [3087,3599). Scan [8, 4000].
    # m=32: n_min=15, period 4096, verified clean in [3087,7183). Scan [15, 7200].
    scan_ranges = {
        2:  1000,
        18: 4000,
        32: 7200,
    }

    print("Scan parameters (per-m, valid n' range only):")
    for m in inactive:
        n_min = n_min_for_m(m)
        print(f"  m={m}: n' in [{n_min}, {scan_ranges.get(m, 8000)}]")
    print()

    critical_errors = []
    all_confirmed = []
    t0_total = time.time()

    for m in inactive:
        N_max = scan_ranges.get(m, 8000)
        n_min = n_min_for_m(m)
        count = N_max - n_min + 1
        print(f"{'='*60}")
        print(f"  m = {m}  (n' in [{n_min}, {N_max}], {count} values)")
        print(f"{'='*60}")
        sys.stdout.flush()

        F_dict, G_dict, n_min_actual = scan_m(m, N_max)

        # Analyze results
        subcaseb = []
        g_hits = []
        f_zero_count = 0

        for n_prime in range(n_min, N_max + 1):
            F = F_dict[n_prime]
            G = G_dict[n_prime]
            if F == 0:
                f_zero_count += 1
            if G == 1:
                g_hits.append((n_prime, F, G))
            if F == 0 and G == 1:
                subcaseb.append(n_prime)

        total_scanned = N_max - n_min + 1
        print(f"  F=0 count: {f_zero_count} / {total_scanned}")
        print(f"  G=1 count: {len(g_hits)} / {total_scanned}")
        print(f"  SubcaseB (F=0,G=1) count: {len(subcaseb)}")

        if subcaseb:
            print(f"  *** CRITICAL ERROR: SubcaseB found at n' = {subcaseb[:20]} ***")
            critical_errors.append((m, subcaseb))
        elif g_hits:
            sample = g_hits[:5]
            print(f"  G=1 found {len(g_hits)} times but ALWAYS with F=1 => weakly inactive, confirmed")
            print(f"  Sample (n', F, G): {sample}")
            all_confirmed.append((m, "weakly_inactive", len(g_hits)))
        else:
            print(f"  G NEVER 1 in [{n_min},{N_max}] => strictly inactive, confirmed")
            all_confirmed.append((m, "strictly_inactive", 0))
        print()

    total_elapsed = time.time() - t0_total

    print("=" * 70)
    print("FINAL VERDICT")
    print("=" * 70)
    print(f"Total time: {total_elapsed:.1f}s")
    print()

    if critical_errors:
        print("*** CRITICAL ERRORS — PAPER CLAIM VIOLATED ***")
        for m, hits in critical_errors:
            print(f"  m={m}: SubcaseB at n' = {hits[:10]}...")
        print("\nThese m values appear to be ACTIVE, not inactive. Paper needs correction.")
        return critical_errors
    else:
        print("All inactive m in {2, 18, 32} CONFIRMED: no SubcaseB in valid scan range.")
        print()
        for m, status, count in all_confirmed:
            r = scan_ranges.get(m, 8000)
            n_min = n_min_for_m(m)
            if status == "weakly_inactive":
                print(f"  m={m}: weakly inactive — G=1 occurs {count} times in [{n_min},{r}] but always with F=1")
            else:
                print(f"  m={m}: strictly inactive — G never 1 in [{n_min},{r}]")
        print()
        print("Paper claim STANDS: no inactive m in [2,38] has a SubcaseB event in valid range.")
        return []


if __name__ == "__main__":
    errors = main()
    sys.exit(1 if errors else 0)
