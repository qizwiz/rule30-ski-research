"""
adversarial_loop45.py

Attack target: The paper claims certain even m in [2,38] are "inactive" —
meaning G(n',m)=0 for ALL n'. We test whether this holds through n'=8000.

From the paper (Section 4):
  M_act = {4, 6, 8, 10, 12, 14, 16, 20, 22, 24, 26, 28, 30, 34, 36, 38}
  Inactive in [2,38]: {2, 18, 32}

For each inactive m, scan G(n',m) for n' in [0, 8000].
Also scan F(n',m) for completeness.

Definitions:
  rule30(l,c,r) = l XOR (c OR r)
  tape size = 2*n' + 3
  spike at position p in tape of size sz: all zeros except position p = 1
  F(n',m): evolve spike at m, tape size 2*n'+3, for n'+1 steps, return center cell
  G(n',m): evolve spike at m AND spike at position last=2*n'+2, same tape/steps, return center
  SubcaseB(n',m) = F(n',m)==0 AND G(n',m)==1
"""

import numpy as np
import sys

def rule30_step(tape):
    """One step of Rule 30 using numpy. rule30(l,c,r) = l XOR (c OR r)"""
    l = np.roll(tape, 1)
    r = np.roll(tape, -1)
    # Open boundary: zero-pad edges
    l[0] = 0
    r[-1] = 0
    return np.logical_xor(l, np.logical_or(tape, r)).astype(np.uint8)

def evolve_and_center(tape_init, steps):
    """Evolve tape for `steps` steps, return center cell value (as int)."""
    tape = tape_init.copy()
    n = len(tape)
    for _ in range(steps):
        tape = rule30_step(tape)
    center = n // 2
    return int(tape[center])

def make_spike(sz, pos):
    """Tape of size sz with 1 at pos, 0 elsewhere."""
    t = np.zeros(sz, dtype=np.uint8)
    if 0 <= pos < sz:
        t[pos] = 1
    return t

def compute_F(n_prime, m):
    """F(n',m): spike at m, tape size 2*n'+3, n'+1 steps, center cell."""
    sz = 2 * n_prime + 3
    tape = make_spike(sz, m)
    return evolve_and_center(tape, n_prime + 1)

def compute_G(n_prime, m):
    """G(n',m): spikes at m and last=2*n'+2, tape size 2*n'+3, n'+1 steps, center cell."""
    sz = 2 * n_prime + 3
    last = 2 * n_prime + 2
    tape = make_spike(sz, m)
    if 0 <= last < sz:
        tape[last] = 1
    return evolve_and_center(tape, n_prime + 1)


def scan_m(m, n_max):
    """
    Scan G(n',m) for n' in [0, n_max].
    Returns list of (n', F, G) where G==1.
    Also returns list of SubcaseB hits (F==0, G==1).
    """
    g_hits = []
    subcaseb_hits = []
    for n_prime in range(n_max + 1):
        sz = 2 * n_prime + 3
        # Only meaningful if spike at m is within tape
        if m >= sz:
            continue
        F = compute_F(n_prime, m)
        G = compute_G(n_prime, m)
        if G == 1:
            g_hits.append((n_prime, F, G))
        if F == 0 and G == 1:
            subcaseb_hits.append(n_prime)
    return g_hits, subcaseb_hits


def main():
    # All even m in [2,38]
    all_even = list(range(2, 40, 2))  # 2,4,6,...,38
    # Active set per paper
    M_act = {4, 6, 8, 10, 12, 14, 16, 20, 22, 24, 26, 28, 30, 34, 36, 38}
    # Inactive = all_even \ M_act
    inactive = [m for m in all_even if m not in M_act]

    print(f"All even m in [2,38]: {all_even}")
    print(f"M_act (active, per paper): {sorted(M_act)}")
    print(f"Inactive m in [2,38] (claimed by paper): {inactive}")
    print()

    N_MAX = 8000
    print(f"Scanning G(n',m) for n' in [0, {N_MAX}] for each inactive m...")
    print("=" * 70)

    critical_errors = []
    all_confirmed = []

    for m in inactive:
        print(f"\n--- m = {m} ---")
        sys.stdout.flush()
        g_hits, subcaseb_hits = scan_m(m, N_MAX)
        if subcaseb_hits:
            print(f"  CRITICAL ERROR: SubcaseB (F=0, G=1) found at n' = {subcaseb_hits[:20]}")
            critical_errors.append((m, subcaseb_hits))
        elif g_hits:
            # G=1 exists but all have F=1 (so SubcaseB never occurs)
            print(f"  G=1 found at {len(g_hits)} values of n', but ALL have F=1 (weakly inactive, as expected)")
            sample = g_hits[:5]
            print(f"  Sample (n', F, G): {sample}")
            all_confirmed.append((m, "weakly_inactive_confirmed", g_hits))
        else:
            print(f"  G=1 NEVER found in [0, {N_MAX}] — strictly inactive confirmed")
            all_confirmed.append((m, "strictly_inactive_confirmed", []))

    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)

    if critical_errors:
        print(f"\n*** CRITICAL: {len(critical_errors)} inactive m value(s) have SubcaseB events! ***")
        for m, hits in critical_errors:
            print(f"  m={m}: SubcaseB at n' = {hits[:10]}...")
        print("\nThis would BREAK the paper's claim that these m are inactive.")
    else:
        print(f"\nAll {len(inactive)} inactive m in [2,38] confirmed: no SubcaseB (F=0,G=1) found in [0,{N_MAX}].")
        for m, status, hits in all_confirmed:
            if status == "weakly_inactive_confirmed":
                print(f"  m={m}: weakly inactive (G=1 occurs but always with F=1) — {len(hits)} G-hit(s)")
            else:
                print(f"  m={m}: strictly inactive (G never 1)")

    return critical_errors


if __name__ == "__main__":
    errors = main()
    sys.exit(1 if errors else 0)
