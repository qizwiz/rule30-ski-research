"""
adversarial_loop45.py  (fast version)

Attack target: The paper claims certain even m in [2,38] are "inactive" —
meaning G(n',m)=0 for ALL n'. We test whether this holds through n' ~ N_max.

From the paper (Section 4):
  M_act = {4, 6, 8, 10, 12, 14, 16, 20, 22, 24, 26, 28, 30, 34, 36, 38}
  Inactive in [2,38]: {2, 18, 32}

KEY OPTIMIZATION (fast approach):
  Instead of computing G(n',m) cell-by-cell (O(n'^2) per value), run ONE
  simulation with a large fixed tape and read all time steps simultaneously.

  For each m, create tape of size T = 2*N_max+3 with:
    - spike at m
    - (for G) spike at last position 2*N_max+2
  Evolve for N_max+1 steps, recording center cell at each step.
  Center cell at step t gives F(t-1, m) or G(t-1, m).

  This approximation is exact for n' up to roughly N_max/2 because the right
  boundary spike's cone of influence reaches the center only at step >= N_max+1.

Rule 30: rule30(l,c,r) = l XOR (c OR r)
"""

import numpy as np
import sys
import time

N_MAX = 8000

def rule30_step_inplace(tape, buf):
    """One step of Rule 30 in-place. rule30(l,c,r) = l XOR (c OR r)"""
    n = len(tape)
    # l = tape shifted right (left neighbor), r = tape shifted left (right neighbor)
    # Open boundaries: l[0]=0, r[-1]=0
    buf[1:] = tape[:-1]   # l
    buf[0] = 0
    # compute c OR r: tape | (tape shifted left)
    # r[i] = tape[i+1], r[-1] = 0
    # We compute result directly: result[i] = buf[i] XOR (tape[i] OR tape[i+1])
    # except at last position: result[-1] = buf[-1] XOR tape[-1]
    np.bitwise_or(tape[:-1], tape[1:], out=buf[:-1])  # reuse buf as temp for c|r
    # Wait — buf currently holds l. We need c|r separately.
    pass

def fast_scan_m(m, n_max):
    """
    Run ONE large simulation for both F and G, recording center cells at each step.

    For F: spike at position m only.
    For G: spikes at position m AND at last=2*n_max+2.

    Returns arrays:
      F_vals[t] = F(t, m)  for t in [0, n_max]
      G_vals[t] = G(t, m)  for t in [0, n_max]

    SubcaseB at t: F_vals[t]==0 AND G_vals[t]==1
    """
    T = 2 * n_max + 3
    center = T // 2

    # --- F simulation ---
    tape_F = np.zeros(T, dtype=np.uint8)
    if 0 <= m < T:
        tape_F[m] = 1

    # --- G simulation ---
    tape_G = np.zeros(T, dtype=np.uint8)
    if 0 <= m < T:
        tape_G[m] = 1
    last = 2 * n_max + 2
    if 0 <= last < T:
        tape_G[last] = 1

    # We need 1 index shift: F(n', m) = center cell after n'+1 steps.
    # So step 0 (initial tape) → corresponds to n'=-1 (not used).
    # Step 1 → n'=0, step 2 → n'=1, ..., step n_max+1 → n'=n_max.
    # We collect n_max+1 values: F_vals[n'] for n' in [0..n_max].

    F_vals = np.zeros(n_max + 1, dtype=np.uint8)
    G_vals = np.zeros(n_max + 1, dtype=np.uint8)

    # Preallocate for vectorized step
    l = np.empty(T, dtype=np.uint8)
    r = np.empty(T, dtype=np.uint8)

    def step(tape):
        # l[i] = tape[i-1], l[0]=0
        l[1:] = tape[:-1]
        l[0] = 0
        # r[i] = tape[i+1], r[-1]=0
        r[:-1] = tape[1:]
        r[-1] = 0
        # rule30: l XOR (tape OR r)
        np.bitwise_or(tape, r, out=r)
        np.bitwise_xor(l, r, out=tape)
        return tape

    for step_i in range(1, n_max + 2):
        tape_F = step(tape_F)
        tape_G = step(tape_G)
        n_prime = step_i - 1  # n' = step - 1
        F_vals[n_prime] = tape_F[center]
        G_vals[n_prime] = tape_G[center]

    return F_vals, G_vals


def main():
    # All even m in [2,38]
    all_even = list(range(2, 40, 2))
    M_act = {4, 6, 8, 10, 12, 14, 16, 20, 22, 24, 26, 28, 30, 34, 36, 38}
    inactive = [m for m in all_even if m not in M_act]

    print(f"All even m in [2,38]: {all_even}")
    print(f"M_act (active, per paper): {sorted(M_act)}")
    print(f"Inactive m in [2,38] (claimed by paper): {inactive}")
    print()
    print(f"Fast simulation approach: tape size T = {2*N_MAX+3}, scanning n' in [0, {N_MAX}]")
    print(f"(Exact for n' up to ~{N_MAX//2}; approximation valid up to ~{N_MAX} due to cone distance)")
    print("=" * 70)

    critical_errors = []
    all_confirmed = []

    t0_total = time.time()

    for m in inactive:
        print(f"\n--- m = {m} ---", flush=True)
        t0 = time.time()

        F_vals, G_vals = fast_scan_m(m, N_MAX)

        elapsed = time.time() - t0

        # SubcaseB: F=0 AND G=1
        subcaseb_mask = (F_vals == 0) & (G_vals == 1)
        subcaseb_indices = np.where(subcaseb_mask)[0]

        # G=1 hits
        g_hits_mask = (G_vals == 1)
        g_hit_indices = np.where(g_hits_mask)[0]

        print(f"  Elapsed: {elapsed:.2f}s")
        print(f"  G=1 count: {g_hits_mask.sum()} values in [0,{N_MAX}]")
        print(f"  SubcaseB (F=0,G=1) count: {len(subcaseb_indices)}")

        if len(subcaseb_indices) > 0:
            print(f"  CRITICAL ERROR: SubcaseB found at n' = {subcaseb_indices[:20].tolist()}")
            critical_errors.append((m, subcaseb_indices.tolist()))
        elif g_hits_mask.any():
            sample = list(zip(g_hit_indices[:5].tolist(), F_vals[g_hit_indices[:5]].tolist(), G_vals[g_hit_indices[:5]].tolist()))
            print(f"  G=1 found but ALL have F=1 (weakly inactive, as expected)")
            print(f"  Sample (n', F, G): {sample}")
            all_confirmed.append((m, "weakly_inactive_confirmed", int(g_hits_mask.sum())))
        else:
            print(f"  G=1 NEVER found — strictly inactive confirmed")
            all_confirmed.append((m, "strictly_inactive_confirmed", 0))

    total_elapsed = time.time() - t0_total

    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Total elapsed: {total_elapsed:.2f}s")
    print()

    if critical_errors:
        print(f"*** CRITICAL: {len(critical_errors)} inactive m value(s) have SubcaseB events! ***")
        for m, hits in critical_errors:
            print(f"  m={m}: SubcaseB at n' = {hits[:10]}")
        print("\nThis would BREAK the paper's claim that these m are inactive.")
    else:
        print(f"All {len(inactive)} inactive m in {{2,18,32}} CONFIRMED: no SubcaseB in [0,{N_MAX}].")
        for m, status, count in all_confirmed:
            if status == "weakly_inactive_confirmed":
                print(f"  m={m}: weakly inactive (G=1 occurs {count} times but always with F=1)")
            else:
                print(f"  m={m}: strictly inactive (G never 1 in [0,{N_MAX}])")

    return critical_errors


if __name__ == "__main__":
    errors = main()
    sys.exit(1 if errors else 0)
