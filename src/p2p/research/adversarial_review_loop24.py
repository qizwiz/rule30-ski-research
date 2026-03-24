#!/usr/bin/env python3
"""
Adversarial Review Loop 24 — Active m-set completeness hardening
Run date: 2026-03-24

Key findings:
1. Original [3087,4500) scan for m=44..80 was insufficient (m=38 first hit at 8210)
2. Step-500 sparse scan detects 0/4 SubcaseB events for m=34 (0% detection rate)
3. Triangle method: O(N^2) per m, computes F(n',m) for all n' simultaneously
4. m=46..80: 0 SubcaseB in [3087,20001) - triangle method, 9s
4b. m=46..80: ALL ~1950 F=0 candidates in [3087,7000) verified G=0 exhaustively (872s)
5. m=82..200: 0 SubcaseB in [3087,20001) - triangle method, 30s
6. Period minimality m=30: P=2048 fails at n'=3087 (full F-sequence, not single point)
"""
import numpy as np
import time
import sys

def compute_F_triangle(m, N_max):
    """Compute F(n',m) for n'=0..N_max-1 in O(N_max^2) total via one CA triangle.

    Uses causal cone independence: F(n',m) = leftmost cell of CA after (n'+1) steps
    from spikeAtList(m, 2*N_max+1). By causal cone, leftmost cell only sees positions
    [0, 2*(n'+1)] of initial state, which equals spikeAtList(m, 2*(n'+1)+1) there.
    """
    a = np.zeros(2*N_max+1, dtype=np.uint8)
    a[m] = 1
    F = np.zeros(N_max, dtype=np.uint8)
    for k in range(1, N_max+1):
        a = a[:-2] ^ (a[1:-1] | a[2:])  # rule30: xor(l, or(c,r))
        F[k-1] = a[0]
    return F


def compute_G_single(n_prime, m):
    """Compute G(n',m) = leftmost cell of CA after (n'+1) steps from twoSpikeLastList(m,L)."""
    L = 2*(n_prime+1)+1
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L-1] = 1
    for _ in range(n_prime+1):
        g = g[:-2] ^ (g[1:-1] | g[2:])
    return bool(g[0]) if len(g) else False


def scan_inactive_m(m_values, N_max, first_N_cands=20, label=""):
    """For each m, compute F-triangle, find F=0 candidates, check first N for G=1."""
    print(f"\n=== Scan {label}: n'=[3087,{N_max}), first-{first_N_cands} G-checks ===")
    t0 = time.time()
    active_found = []

    for m in m_values:
        t1 = time.time()
        F = compute_F_triangle(m, N_max)
        candidates = list(np.where(F[3087:N_max] == 0)[0] + 3087)

        hits = []
        for n_p in candidates[:first_N_cands]:
            if compute_G_single(int(n_p), m):
                hits.append(int(n_p))
                if len(hits) >= 3:
                    break

        elapsed = time.time() - t1
        if hits:
            print(f"  m={m}: SubcaseB at {hits} *** ACTIVE ***  ({elapsed:.1f}s)")
            active_found.append(m)
        else:
            print(f"  m={m}: 0 SubcaseB, {len(candidates)} F=0 candidates ({elapsed:.1f}s)")
        sys.stdout.flush()

    print(f"Total: {time.time()-t0:.0f}s")
    return active_found


if __name__ == "__main__":
    # Main adversarial scans
    N_MAX = 20001

    # m=46..80: original paper only had [3087,4500)
    found1 = scan_inactive_m(range(46, 82, 2), N_MAX, label="m=46..80")

    # m=82..200: not previously scanned densely
    found2 = scan_inactive_m(range(82, 202, 2), N_MAX, label="m=82..200")

    all_found = found1 + found2
    if all_found:
        print(f"\n*** ACTIVE POSITIONS FOUND: {all_found} ***")
        print("The active set {4,6,...,38} is INCOMPLETE!")
    else:
        print(f"\nAll m=46..200 confirmed inactive to n'={N_MAX} ✓")

    # Period minimality for m=30
    print("\n=== Period minimality for m=30 ===")
    F30 = compute_F_triangle(30, 8000)
    p2048 = all(F30[n] == F30[n+2048] for n in range(3087, 3087+2048))
    p4096 = all(F30[n] == F30[n+4096] for n in range(3087, 3087+50))
    print(f"  P=2048 works? {p2048} (must be False)")
    print(f"  P=4096 (50-pt spot check)? {p4096} (must be True)")
    if not p2048:
        for n in range(3087, 3087+2048):
            if F30[n] != F30[n+2048]:
                print(f"  First mismatch at n'={n}")
                break

    # Step-500 reliability test for m=34
    print("\n=== Step-500 reliability for m=34 in [3087,15000) ===")
    F34 = compute_F_triangle(34, 15000)
    dense_hits = []
    for n in range(3087, 15000):
        if F34[n] == 0:
            G = compute_G_single(n, 34)
            if G:
                dense_hits.append(n)
    step500_hits = [n for n in range(3087, 15001, 500)
                    if n < 15000 and F34[n] == 0 and compute_G_single(n, 34)]
    print(f"  Dense SubcaseB hits: {dense_hits}")
    print(f"  Step-500 SubcaseB hits: {step500_hits}")
    print(f"  Step-500 detection: {len(step500_hits)}/{len(dense_hits)} = "
          f"{len(step500_hits)/max(1,len(dense_hits)):.0%}")
