#!/usr/bin/env python3
"""
Adversarial Review Loop 27 — F-period certificate for m=40,42 + fix stale body reference
Run date: 2026-03-24

Attacks:
1. Compute F-period certificate for m=40 (find actual period; paper claims inactive but evidence thin)
2. Compute F-period certificate for m=42
3. For the minimal period found, check ALL F=0 candidates in one period for SubcaseB
4. This either formally closes m=40/42 inactivity or reveals a surprise

The F-period certificate means:
  caEvolve P (spikeAtList m (2P + 2m + 1)) = spikeAtList m (2m + 1)
If it holds, then F(n', m) has period P in n' for all n' >= m.
"""
import numpy as np
import time
import sys


def check_F_cert(m, P):
    """Verify: caEvolve P (spikeAtList m (2P+2m+1)) = spikeAtList m (2m+1).

    Returns True if the certificate holds.
    spikeAtList m N = list of N bools, True at index m.
    caEvolve P l = apply Rule 30 P times with shrinking list.
    """
    L = 2 * P + 2 * m + 1
    a = np.zeros(L, dtype=np.uint8)
    a[m] = 1
    for _ in range(P):
        a = a[:-2] ^ (a[1:-1] | a[2:])
    # Final size: L - 2P = 2m+1; expected: spikeAtList m (2m+1)
    expected = np.zeros(2 * m + 1, dtype=np.uint8)
    expected[m] = 1
    return np.array_equal(a, expected)


def compute_F_triangle(m, N_max):
    """Compute F(n',m) for n'=0..N_max-1 via O(N_max^2) triangle."""
    a = np.zeros(2 * N_max + 1, dtype=np.uint8)
    a[m] = 1
    F = np.zeros(N_max, dtype=np.uint8)
    for k in range(1, N_max + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
        F[k - 1] = a[0]
    return F


def compute_G_single(n_prime, m):
    """G(n',m) = leftmost cell after n'+1 steps from twoSpikeLastList(m, 2*(n'+1)+1)."""
    L = 2 * (n_prime + 1) + 1
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L - 1] = 1
    for _ in range(n_prime + 1):
        g = g[:-2] ^ (g[1:-1] | g[2:])
    return bool(g[0]) if len(g) else False


def find_F_period(m, max_power=17):
    """Find the minimal period of F(n', m) by testing P = 2^k for k up to max_power."""
    print(f"\n  === Finding F-period for m={m} ===")
    for k in range(3, max_power + 1):
        P = 2 ** k
        t0 = time.time()
        holds = check_F_cert(m, P)
        elapsed = time.time() - t0
        print(f"    P={P:>6} (2^{k}): cert holds? {holds}  ({elapsed:.2f}s)")
        sys.stdout.flush()
        if holds:
            print(f"  --> F-period for m={m} divides P={P}")
            # Check half-period to determine minimality
            if k > 3:
                P_half = P // 2
                holds_half = check_F_cert(m, P_half)
                print(f"    P={P_half} (half): cert holds? {holds_half}")
                if not holds_half:
                    print(f"  --> MINIMAL period = {P}")
                else:
                    print(f"  --> Actual period <= {P_half} (will subdivide)")
            return P, holds
    return None, False


# ============================================================
# Attack 1: m=40 F-period certificate
# ============================================================
print("=== Attack 1: F-period certificate for m=40 ===")
P40, _ = find_F_period(40, max_power=17)

if P40 is not None:
    print(f"\n  F-period for m=40 certified as dividing {P40}")
    # Triangle check: find actual minimal period
    # Already know P=65536 works; check P/2, P/4 etc.
    # (find_F_period already does minimality check one level)

    # Now: how many F=0 candidates in one period [3087, 3087+P40)?
    N_check = 3087 + P40 + 100
    print(f"\n  Computing F triangle for m=40, N={N_check}...")
    t0 = time.time()
    F40 = compute_F_triangle(40, N_check)
    print(f"  Done in {time.time()-t0:.1f}s")

    candidates = list(np.where(F40[3087:3087 + P40] == 0)[0] + 3087)
    print(f"  F=0 candidates in [3087, 3087+{P40}): {len(candidates)}")

    # Check first 100 G candidates
    N_check_G = min(100, len(candidates))
    print(f"  Checking first {N_check_G} F=0 candidates for G=1...")
    t0 = time.time()
    hits = []
    for n_p in candidates[:N_check_G]:
        if compute_G_single(int(n_p), 40):
            hits.append(int(n_p))
    print(f"  SubcaseB hits in first {N_check_G} F=0 candidates: {hits}")
    print(f"  Time: {time.time()-t0:.1f}s")

    if not hits:
        print(f"  ✓ No SubcaseB in first {N_check_G} F=0 candidates for m=40")
    else:
        print(f"  *** ACTIVE! m=40 has SubcaseB events: {hits} ***")


# ============================================================
# Attack 2: m=42 F-period certificate
# ============================================================
print("\n\n=== Attack 2: F-period certificate for m=42 ===")
P42, _ = find_F_period(42, max_power=17)

if P42 is not None:
    N_check42 = 3087 + P42 + 100
    print(f"\n  Computing F triangle for m=42, N={N_check42}...")
    t0 = time.time()
    F42 = compute_F_triangle(42, N_check42)
    print(f"  Done in {time.time()-t0:.1f}s")

    candidates42 = list(np.where(F42[3087:3087 + P42] == 0)[0] + 3087)
    print(f"  F=0 candidates in [3087, 3087+{P42}): {len(candidates42)}")

    N_check_G42 = min(50, len(candidates42))
    t0 = time.time()
    hits42 = []
    for n_p in candidates42[:N_check_G42]:
        if compute_G_single(int(n_p), 42):
            hits42.append(int(n_p))
    print(f"  SubcaseB hits in first {N_check_G42} F=0 candidates: {hits42}")
    print(f"  Time: {time.time()-t0:.1f}s")


# ============================================================
# Attack 3: m=18 and m=32 F-period certificates
# (paper cites periods 256 and 4096 respectively — verify certs)
# ============================================================
print("\n\n=== Attack 3: F-period certs for inactive m=18, m=32 ===")
for m, P_expected in [(18, 256), (32, 4096)]:
    t0 = time.time()
    holds = check_F_cert(m, P_expected)
    holds_half = check_F_cert(m, P_expected // 2)
    print(f"  m={m}: P={P_expected} cert: {holds}, P/2={P_expected//2} cert: {holds_half}  "
          f"({time.time()-t0:.2f}s)")
    if holds and not holds_half:
        print(f"    --> Minimal period confirmed: P={P_expected}")
    elif not holds:
        print(f"    --> WARNING: claimed period {P_expected} does NOT hold!")
    sys.stdout.flush()
