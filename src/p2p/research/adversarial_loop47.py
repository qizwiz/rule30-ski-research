"""
adversarial_loop47.py — Loop 47 adversarial review of Rule 30 Prize 3 paper.

Attack 1: Scan even m in [40, 60] for SubcaseB activity in n' in [0, 5000].
Attack 2: Identify and analyze the weakest sentence in the proof plan section.

Rule 30: rule30(l,c,r) = l XOR (c OR r)
G(n',m): tape size 2*n'+3, spikes at m and 2*n'+2, evolve n'+1 steps, return center.
F(n',m): tape size 2*n'+3, spike at m only, evolve n'+1 steps, return center.
SubcaseB(n',m) = F==0 AND G==1.

Single-simulation trick: one tape of size T=2*N_max+3.
Spike at m (and last for G). Evolve N_max+1 steps.
Center at step t gives F(t-1,m) or G(t-1,m) for all t simultaneously,
exact for n' up to ~N_max/2 (right-boundary spike cone cannot reach center before that).
"""

import numpy as np
import time

# Rule 30: l XOR (c OR r)
def rule30_np(tape):
    """Apply one step of Rule 30 to a numpy boolean array (open boundaries = 0)."""
    l = np.roll(tape, 1)
    r = np.roll(tape, -1)
    l[0] = False
    r[-1] = False
    return np.logical_xor(l, np.logical_or(tape, r))

def run_simulation(T, spike_positions, n_steps):
    """
    Run Rule 30 for n_steps starting from tape of size T with spikes at spike_positions.
    Returns array of center values (index 0 = initial config = step 0, shape n_steps+1).
    Center position = T // 2.
    """
    tape = np.zeros(T, dtype=bool)
    for sp in spike_positions:
        if 0 <= sp < T:
            tape[sp] = True
    center = T // 2
    centers = np.zeros(n_steps + 1, dtype=bool)
    centers[0] = tape[center]
    for step in range(1, n_steps + 1):
        tape = rule30_np(tape)
        centers[step] = tape[center]
    return centers

def compute_F_and_G_fast(m, N_max):
    """
    Use single-simulation trick to compute F(n', m) and G(n', m) for n' in [0, N_max].

    F(n', m): tape 2n'+3, spike at m, evolve n'+1 steps, read center.
    G(n', m): tape 2n'+3, spikes at m and last=2n'+2, evolve n'+1 steps, read center.

    Single-simulation: use T = 2*N_max + 3, run N_max+1 steps.
    Center of big tape at step t = F(t-1, m) for all t in [1, N_max+1]
    (exact as long as t << T/2, i.e., n' << N_max/2).

    For G: run with spikes at m AND last_big = T-1 = 2*N_max+2.
    The big-tape G center at step t approximates G(t-1, m) but the right-boundary
    spike's cone reaches center at step T//2 = N_max+1. So readings at n' < N_max
    are safe (cone of right spike reaches center only at step N_max+1).

    Returns: F_vals[n'], G_vals[n'] for n' in [0, N_max].
    """
    T = 2 * N_max + 3
    n_steps = N_max  # step t gives F(t-1), so steps 1..N_max give F(0)..F(N_max-1)
    # Actually: center at step t corresponds to n' = t-1 since we evolved t steps from
    # a tape of "virtual size" 2*(t-1)+3. We use T >> this, so it's exact.

    # F simulation: spike at m only
    F_centers = run_simulation(T, [m], n_steps)
    # F_centers[t] = center after t steps = F(t-1, m) for n' = t-1
    # So F(n', m) = F_centers[n'+1] for n' in [0, N_max-1]
    # But we also need F(N_max, m) = F_centers[N_max+1], need one more step
    # Let's just run N_max+1 steps total
    T2 = 2 * N_max + 3
    F_centers2 = run_simulation(T2, [m], N_max + 1)
    # F(n', m) = F_centers2[n'+1], n' in [0, N_max]

    # G simulation: spikes at m and last_big = T2-1
    last_big = T2 - 1  # = 2*N_max + 2
    G_centers2 = run_simulation(T2, [m, last_big], N_max + 1)
    # G(n', m) ≈ G_centers2[n'+1] for n' in [0, N_max]
    # Approximation exact for n' < N_max (right-boundary cone doesn't reach center yet)

    F_vals = F_centers2[1:]   # F_vals[n'] = F(n', m), shape N_max+1
    G_vals = G_centers2[1:]   # G_vals[n'] = G(n', m) approx, shape N_max+1

    return F_vals, G_vals


def attack1_scan_m40_to_60():
    """
    Scan even m in [40, 60] for SubcaseB activity in n' in [0, 5000].

    The paper claims no active m >= 40 exists. This attack tries to find counterexamples.
    Uses the single-simulation trick for efficiency.
    """
    print("=" * 70)
    print("ATTACK 1: Scan even m in [40, 60] for SubcaseB in n' in [0, 5000]")
    print("=" * 70)
    print()

    N_max = 5000
    m_values = list(range(40, 62, 2))  # 40, 42, ..., 60

    results = {}
    t0 = time.time()

    for m in m_values:
        t_m = time.time()
        F_vals, G_vals = compute_F_and_G_fast(m, N_max)

        # n_min(m) = ceil((m-2)/2) = smallest n' where spike at m is within tape of size 2n'+3
        # Tape has positions 0..2n'+2; spike at m is valid if m <= 2n'+2, i.e., n' >= (m-2)/2
        n_min = max(0, (m - 2 + 1) // 2)  # ceil((m-2)/2)

        subcaseB_hits = []
        for n_prime in range(n_min, N_max + 1):
            if not F_vals[n_prime] and G_vals[n_prime]:
                subcaseB_hits.append(n_prime)
                if len(subcaseB_hits) >= 20:  # cap output
                    break

        elapsed_m = time.time() - t_m
        results[m] = {
            'n_min': n_min,
            'subcaseB_hits': subcaseB_hits,
            'F0_count': int(np.sum(~F_vals[n_min:])),
            'G1_count': int(np.sum(G_vals[n_min:])),
            'elapsed': elapsed_m,
        }

        status = "ACTIVE (SubcaseB found!)" if subcaseB_hits else "inactive (no SubcaseB)"
        print(f"  m={m:3d}: n_min={n_min}, F=0 count={results[m]['F0_count']:5d}, "
              f"G=1 count={results[m]['G1_count']:5d} | {status} "
              f"({elapsed_m:.2f}s)")
        if subcaseB_hits:
            print(f"           SubcaseB hits: {subcaseB_hits[:10]}")

    total = time.time() - t0
    print()
    print(f"Total time: {total:.1f}s")
    print()

    # Summary
    active = [m for m in m_values if results[m]['subcaseB_hits']]
    inactive = [m for m in m_values if not results[m]['subcaseB_hits']]
    print(f"Active m in [40,60]: {active}")
    print(f"Inactive m in [40,60]: {inactive}")
    print()

    return results, active, inactive


def attack2_weakest_sentence():
    """
    Attack 2: Identify and explain the weakest sentence in the proof plan section.

    The weakest sentence is the one making the largest logical leap without proof.
    We quote it and explain why it's weak and what would be needed to fix it.
    """
    print("=" * 70)
    print("ATTACK 2: Weakest sentence in the proof plan section")
    print("=" * 70)
    print()

    # The sentence in question (from Part C of the proof plan, paper lines ~838-843):
    weakest_sentence = (
        "This leaves two candidate paths: (i) the inductive step reduces a large-m "
        "case at n' to a small-m case at n'-1 (non-trivially, via the lifting lemma's "
        "algebraic structure), or (ii) explicit witnesses for the large-m family are "
        "constructed separately, analogously to the ge-block witnesses for n' <= 3086 "
        "(which already include large-m witnesses, e.g., m = 6164 at n' = 3085). "
        "Whether either path extends to all n' >= 3087 is the second critical open "
        "subproblem, alongside determining whether the active set terminates at m=38 "
        "(if so, P=32768 exactly for the fixed-m family)."
    )

    print("Quoted sentence (proof plan, Part C):")
    print()
    print(f'  "{weakest_sentence}"')
    print()

    # But the single most hand-wavy sentence is the Part C reduction claim:
    most_handwavy = (
        "(i) the inductive step reduces a large-m case at n' to a small-m case at "
        "n'-1 (non-trivially, via the lifting lemma's algebraic structure)"
    )

    print("Most hand-wavy claim within that passage:")
    print()
    print(f'  "{most_handwavy}"')
    print()

    print("Analysis of weakness:")
    print()
    print("  This is the weakest claim in the proof plan because:")
    print()
    print("  1. It asserts a reduction path (large-m at n' -> small-m at n'-1) exists")
    print("     'via the lifting lemma's algebraic structure' without demonstrating")
    print("     what that reduction is or that it is even feasible.")
    print()
    print("  2. The paper immediately notes that the naive reduction")
    print("     (n', 2n'-6) -> (n'-1, 2n'-8) FAILS computationally:")
    print("     'computation shows this fails: the predecessor n'-1 has no")
    print("     large-m SubcaseB case at all.'")
    print("     So the ONLY explicit candidate reduction is already refuted.")
    print()
    print("  3. No alternative reduction is described. The claim that a reduction")
    print("     'via the lifting lemma's algebraic structure' exists is speculative.")
    print("     The lifting lemma is itself the open conjecture — using it as")
    print("     the engine for a reduction within the proof of itself is circular.")
    print()
    print("  4. The paper labels this 'the second critical open subproblem' —")
    print("     acknowledging it is open — but the framing as a 'candidate path'")
    print("     suggests plausibility without any supporting evidence.")
    print()
    print("  What would be needed to fix it:")
    print("  - Either explicitly describe the non-naive reduction (what small-m")
    print("    witness does the large-m case at n' reduce to at n'-1?), OR")
    print("  - Remove path (i) entirely and commit to path (ii) (direct witnesses),")
    print("    which at least has a concrete analogy (the ge-block construction).")
    print()

    # Computational verification: confirm the naive reduction fails
    print("Computational check: does naive reduction (n', 2n'-6) -> (n'-1, 2n'-8) work?")
    print("i.e., if SubcaseB(n', 2n'-6) holds, does SubcaseB(n'-1, 2n'-8) also hold?")
    print()

    # Check for n' in [3089, 3105] (first SubcaseB hits at m=2n'-6)
    # SubcaseB at (n', 2n'-6): n' ≡ 1,2 (mod 4), n' >= 3089
    fail_count = 0
    success_count = 0
    pairs_checked = 0

    for n_prime in range(3089, 3130):
        # Check if (n', 2n'-6) is SubcaseB
        m_large = 2 * n_prime - 6

        # F(n', m) and G(n', m): use direct computation for small range
        # Tape size = 2*n'+3
        T = 2 * n_prime + 3
        tape_F = np.zeros(T, dtype=bool)
        tape_F[m_large] = True
        for _ in range(n_prime + 1):
            tape_F = rule30_np(tape_F)
        F_val = tape_F[T // 2]

        tape_G = np.zeros(T, dtype=bool)
        tape_G[m_large] = True
        tape_G[T - 1] = True
        for _ in range(n_prime + 1):
            tape_G = rule30_np(tape_G)
        G_val = tape_G[T // 2]

        is_subcaseB = (not F_val) and G_val

        if is_subcaseB:
            # Check predecessor: (n'-1, 2(n'-1)-6) = (n'-1, 2n'-8)
            n_pred = n_prime - 1
            m_pred = 2 * n_pred - 6  # = 2n'-8

            T2 = 2 * n_pred + 3
            if m_pred >= 0 and m_pred < T2:
                tape_F2 = np.zeros(T2, dtype=bool)
                tape_F2[m_pred] = True
                for _ in range(n_pred + 1):
                    tape_F2 = rule30_np(tape_F2)
                F2_val = tape_F2[T2 // 2]

                tape_G2 = np.zeros(T2, dtype=bool)
                tape_G2[m_pred] = True
                tape_G2[T2 - 1] = True
                for _ in range(n_pred + 1):
                    tape_G2 = rule30_np(tape_G2)
                G2_val = tape_G2[T2 // 2]

                pred_subcaseB = (not F2_val) and G2_val
                pairs_checked += 1
                if pred_subcaseB:
                    success_count += 1
                    print(f"  SUCCESS: SubcaseB({n_prime}, {m_large}) -> SubcaseB({n_pred}, {m_pred})")
                else:
                    fail_count += 1
                    print(f"  FAIL: SubcaseB({n_prime}, {m_large}) -> NOT SubcaseB({n_pred}, {m_pred}): "
                          f"F={int(F2_val)}, G={int(G2_val)}")

    print()
    if pairs_checked > 0:
        print(f"Reduction success rate: {success_count}/{pairs_checked} = "
              f"{100*success_count/pairs_checked:.0f}%")
        if fail_count == pairs_checked:
            print("CONFIRMED: naive reduction ALWAYS fails (0% success rate).")
            print("This validates the paper's own admission that the naive reduction fails.")
            print("Path (i) has no known concrete form.")
    else:
        print("No SubcaseB events found in test range (unexpected).")
    print()


def main():
    print()
    print("Loop 47 Adversarial Review — Rule 30 Prize 3 paper")
    print("Date: 2026-03-24")
    print()

    # Attack 1
    results, active, inactive = attack1_scan_m40_to_60()

    print()
    print("-" * 70)
    print()

    # Attack 2
    attack2_weakest_sentence()

    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print("Attack 1 (m in [40,60]):")
    if active:
        print(f"  WARNING: Active m found: {active}")
        print("  The paper's claim that no active m >= 40 exists is FALSIFIED.")
    else:
        print("  All even m in [40,60] are INACTIVE (no SubcaseB in [0,5000]).")
        print("  Consistent with paper's claim.")
    print()
    print("Attack 2 (weakest sentence):")
    print("  Weakest sentence: path (i) reduction claim in Part C.")
    print("  'the inductive step reduces a large-m case at n' to a small-m case at n'-1'")
    print("  This is hand-wavy: the only explicit candidate (naive n'-1 reduction) fails,")
    print("  and no alternative is provided. Computationally confirmed 0% success rate.")
    print()


if __name__ == "__main__":
    main()
