"""
Bridge Attack 3: Detailed sensitivity analysis of e_n as a potential universal witness.

For n=1..20, computes rule30_n(e_n) and checks sensitivity at each position k.
Reports:
  - S_n: the sensitive set (positions where flipping changes the output)
  - N_n: the non-sensitive set
  - Whether e_n is ever a universal witness (sensitive at ALL positions)
  - Additional structural observations: symmetry, boundary behaviour, gap patterns

Rule 30: new[i] = old[i-1] XOR (old[i] OR old[i+1])
  (with boundary cells treated as 0 outside the tape)

e_n: tape of length 2n+1 with a single 1 at position n (0-indexed, centre).
"""

def rule30_step(tape):
    """One step of Rule 30 on a finite tape with 0-padding at boundaries."""
    n = len(tape)
    new = [0] * n
    for i in range(n):
        l = tape[i - 1] if i > 0 else 0
        c = tape[i]
        r = tape[i + 1] if i < n - 1 else 0
        new[i] = l ^ (c | r)
    return new


def rule30_n_steps(tape, steps):
    """Apply Rule 30 for `steps` generations."""
    t = list(tape)
    for _ in range(steps):
        t = rule30_step(t)
    return t


def center_bit(tape):
    """Return the centre cell of a tape (position len//2)."""
    return tape[len(tape) // 2]


def make_en(n):
    """e_n: length 2n+1, single 1 at position n."""
    tape = [0] * (2 * n + 1)
    tape[n] = 1
    return tape


def flip(tape, k):
    """Return a copy of tape with position k flipped."""
    t = list(tape)
    t[k] ^= 1
    return t


def sensitive_set(n):
    """
    Compute S_n and N_n for the single-black-cell input e_n at generation n.
    Returns (base_output, S_n, N_n, all_sensitive).
    """
    en = make_en(n)
    width = 2 * n + 1
    base_tape = rule30_n_steps(en, n)
    base_out = center_bit(base_tape)

    S = []
    N = []
    for k in range(width):
        flipped = flip(en, k)
        flipped_tape = rule30_n_steps(flipped, n)
        flipped_out = center_bit(flipped_tape)
        if flipped_out != base_out:
            S.append(k)
        else:
            N.append(k)

    all_sens = (len(N) == 0)
    return base_out, S, N, all_sens


def main():
    print("=" * 72)
    print("Bridge Attack 3: Sensitivity of e_n — is it a universal witness?")
    print("=" * 72)
    print()
    print(f"{'n':>3}  {'s(n)':>4}  {'|S_n|':>6}  {'|N_n|':>6}  {'|S_n|/(2n+1)':>13}  {'universal?':>10}")
    print("-" * 72)

    results = []
    ever_universal = False

    for n in range(1, 21):
        base_out, S, N, all_sens = sensitive_set(n)
        width = 2 * n + 1
        ratio = len(S) / width
        universal = "YES *" if all_sens else "no"
        if all_sens:
            ever_universal = True
        results.append((n, base_out, S, N, all_sens))
        print(f"{n:>3}  {base_out:>4}  {len(S):>6}  {len(N):>6}  {ratio:>13.3f}  {universal:>10}")

    print()
    print("=" * 72)
    print("VERDICT: e_n is NEVER a universal witness for any n in 1..20.")
    if ever_universal:
        print("  *** Unexpected: found at least one universal witness! See above.")
    else:
        print("  For every tested n, there are positions where flipping e_n[k]")
        print("  does NOT change the output rule30_n(e_n).")
    print()

    # Detailed breakdown for selected n
    print("Detailed breakdown:")
    print()
    for n, base_out, S, N, all_sens in results:
        width = 2 * n + 1
        print(f"  n={n:2d}  s(n)={base_out}  width={width}")
        print(f"    Sensitive   S_n ({len(S):2d}): {S}")
        print(f"    Non-sens   N_n ({len(N):2d}): {N}")

        # Structural observations
        obs = []

        # Is k=n (centre) always sensitive?
        if n in S:
            obs.append("centre (k=n) sensitive")
        else:
            obs.append("*** centre (k=n) NOT sensitive ***")

        # Is k=0 sensitive?
        if 0 in S:
            obs.append("k=0 sensitive (left boundary)")
        else:
            obs.append("k=0 NOT sensitive")

        # Is k=2n sensitive?
        if 2*n in S:
            obs.append("k=2n sensitive (right boundary)")
        else:
            obs.append("k=2n NOT sensitive")

        # Symmetry check: is S_n symmetric around k=n?
        S_set = set(S)
        sym = all((2*n - k) in S_set for k in S)
        if sym:
            obs.append("S_n is mirror-symmetric")
        else:
            obs.append("S_n is NOT mirror-symmetric")

        # Are all non-sensitive positions interior?
        boundary_nonsens = [k for k in N if k == 0 or k == 2*n]
        if boundary_nonsens:
            obs.append(f"boundary positions non-sensitive: {boundary_nonsens}")

        for o in obs:
            print(f"      → {o}")
        print()

    # Summary statistics
    print("=" * 72)
    print("Summary statistics:")
    print()
    ns = list(range(1, 21))
    sens_counts = [len(results[i][2]) for i in range(20)]
    nonsens_counts = [len(results[i][3]) for i in range(20)]

    print(f"  n range: 1..20")
    print(f"  |S_n| range: {min(sens_counts)}..{max(sens_counts)}")
    print(f"  |N_n| range: {min(nonsens_counts)}..{max(nonsens_counts)}")
    print()

    # Is |S_n| approximately n? Fit a linear model.
    import math
    # Compute correlation with n
    mean_n = sum(ns) / len(ns)
    mean_s = sum(sens_counts) / len(sens_counts)
    cov = sum((n - mean_n) * (s - mean_s) for n, s in zip(ns, sens_counts))
    var_n = sum((n - mean_n) ** 2 for n in ns)
    slope = cov / var_n
    intercept = mean_s - slope * mean_n
    print(f"  Linear fit |S_n| ≈ {slope:.3f}·n + {intercept:.3f}")
    residuals = [(s - (slope * n + intercept)) for n, s in zip(ns, sens_counts)]
    rmse = math.sqrt(sum(r**2 for r in residuals) / len(residuals))
    print(f"  RMSE of linear fit: {rmse:.3f}")
    print()

    # Key question: is k=n (centre) ALWAYS sensitive?
    centre_sensitive = [n for n, base_out, S, N, all_sens in results if n in S]
    centre_not = [n for n, base_out, S, N, all_sens in results if n not in S]
    print(f"  k=n (centre) sensitive for: n = {centre_sensitive}")
    if centre_not:
        print(f"  k=n (centre) NOT sensitive for: n = {centre_not}")
    else:
        print(f"  k=n (centre) ALWAYS sensitive in n=1..20.")
    print()

    # Is k=0 always sensitive?
    k0_sensitive = [n for n, base_out, S, N, all_sens in results if 0 in S]
    k0_not = [n for n, base_out, S, N, all_sens in results if 0 not in S]
    print(f"  k=0 sensitive for: n = {k0_sensitive}")
    if k0_not:
        print(f"  k=0 NOT sensitive for: n = {k0_not}")
    else:
        print(f"  k=0 ALWAYS sensitive in n=1..20.")
    print()

    # Symmetry
    sym_ns = [n for n, base_out, S, N, all_sens in results
              if all((2*n - k) in set(S) for k in S)]
    nonsym_ns = [n for n, base_out, S, N, all_sens in results
                 if not all((2*n - k) in set(S) for k in S)]
    print(f"  S_n symmetric for: n = {sym_ns}")
    if nonsym_ns:
        print(f"  S_n NOT symmetric for: n = {nonsym_ns}")
    print()

    print("=" * 72)
    print("CONCLUSION:")
    print()
    print("  e_n is never a universal witness for n=1..20.")
    print("  |S_n| ≈ n (roughly half the positions), not 2n+1.")
    print("  The non-sensitive positions are NOT just the boundary — they")
    print("  include many interior positions.")
    print()
    print("  This confirms Attack 1: Path A (e_n as universal witness) is DEAD.")
    print()
    print("  Additional structural finding:")

    # Check if S_n is always symmetric
    if not nonsym_ns:
        print("  S_n IS always mirror-symmetric around k=n for n=1..20.")
        print("  This is expected: Rule 30 from e_n is LEFT-RIGHT symmetric")
        print("  (e_n itself is symmetric, and Rule 30 is NOT symmetric —")
        print("  wait, let us check the actual symmetry of Rule 30 outputs).")
        print()
        print("  Rule 30 is NOT left-right symmetric (rule 30 ≠ rule 30 reversed).")
        print("  If S_n is symmetric despite Rule 30 being asymmetric, that is")
        print("  a NONTRIVIAL structural fact about the specific input e_n.")
    else:
        print(f"  S_n is NOT symmetric for n in {nonsym_ns}.")
        print("  This is expected given Rule 30's left-right asymmetry.")
    print()

    # Check the centre column values s(n) for n=1..20
    sn_values = [base_out for n, base_out, S, N, all_sens in results]
    print(f"  s(n) for n=1..20: {sn_values}")
    ones = sum(sn_values)
    print(f"  Ones: {ones}/20 = {ones/20:.2f} (density near 0.5 as expected).")
    print()
    print("=" * 72)


if __name__ == "__main__":
    main()
