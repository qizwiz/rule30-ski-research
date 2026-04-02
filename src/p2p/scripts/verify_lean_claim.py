#!/usr/bin/env python3
"""
verify_lean_claim.py — Pre-Lean computational verification pipeline.

Usage:
    python3 scripts/verify_lean_claim.py <claim_type> [options]

Claim types:
    rightedge_base        Verify rightEdgeSens base cases (T=3088,3089,3091,3094)
    rightedge_period N    Verify rightEdgeF/G period-8 for T=N..N+16
    subcaseB_mod8         Verify SubcaseB m=4 fires exactly at n'%8 ∈ {0,2,5,7}
    sensitivity k m T     Check rightEdgeSens k m T directly

Rule 30: cell[i]' = cell[i-1] XOR (cell[i] OR cell[i+1]), boundary = 0
Center = position T in tape of 2T+1.

Exit code: 0 = all verified, 1 = some failed, 2 = usage error
"""

import sys
import time

# ---------------------------------------------------------------------------
# Core CA engine
# ---------------------------------------------------------------------------

def rule30_step(tape):
    n = len(tape)
    new = [False] * n
    for i in range(n):
        left   = tape[i-1] if i > 0 else False
        center = tape[i]
        right  = tape[i+1] if i < n-1 else False
        new[i] = left ^ (center | right)
    return new

def caEvolve(steps, tape):
    for _ in range(steps):
        tape = rule30_step(tape)
    return tape

def center_of(tape):
    """Center cell of a tape of odd length 2T+1."""
    return tape[len(tape) // 2]

# ---------------------------------------------------------------------------
# rightEdge functions (match Lean definitions exactly)
# ---------------------------------------------------------------------------

def rightEdgeF(k, T):
    """caEvolve T (spikeAtList (2*T-k) (2*T+1)) center."""
    width = 2 * T + 1
    tape = [False] * width
    spike_pos = 2 * T - k
    if 0 <= spike_pos < width:
        tape[spike_pos] = True
    return caEvolve(T, tape)[T]

def rightEdgeG(k, m, T):
    """caEvolve T (twoSpikeList m (2*T-k) (2*T+1)) center."""
    width = 2 * T + 1
    tape = [False] * width
    spike_pos = 2 * T - k
    if 0 <= m < width:
        tape[m] = True
    if 0 <= spike_pos < width:
        tape[spike_pos] = True
    return caEvolve(T, tape)[T]

def rightEdgeSens(k, m, T):
    return rightEdgeF(k, T) != rightEdgeG(k, m, T)

# ---------------------------------------------------------------------------
# SubcaseB condition (m=4): spike(4) → false, twoSpike(4,last) → true
# ---------------------------------------------------------------------------

def subcaseB_fires(T):
    """Returns (hcase, hts): hcase = spike(4) gives center=false, hts = twoSpike(4,last) gives center=true."""
    width = 2 * T + 1
    # spike at m=4
    tape_spike = [False] * width
    tape_spike[4] = True
    center_spike = caEvolve(T, tape_spike)[T]
    # twoSpike at m=4 and last=2*T
    tape_two = [False] * width
    tape_two[4] = True
    tape_two[2 * T] = True
    center_two = caEvolve(T, tape_two)[T]
    hcase = (center_spike == False)
    hts   = (center_two == True)
    return hcase, hts

# ---------------------------------------------------------------------------
# Claim verifiers
# ---------------------------------------------------------------------------

def verify_rightedge_base():
    """Verify the 4 native_decide base cases."""
    cases = [
        (10, 4, 3088, "n'=3087, n'%8=7"),
        (12, 4, 3089, "n'=3088, n'%8=0"),
        (10, 4, 3091, "n'=3090, n'%8=2"),
        (10, 4, 3094, "n'=3093, n'%8=5"),
    ]
    print("rightEdge base case verification")
    print("=" * 60)
    all_ok = True
    for k, m, T, label in cases:
        t0 = time.time()
        F = rightEdgeF(k, T)
        G = rightEdgeG(k, m, T)
        elapsed = time.time() - t0
        ok = (F != G)
        status = "✓ SENSITIVE" if ok else "✗ NOT SENSITIVE"
        print(f"  T={T} k={k} ({label}): F={int(F)} G={int(G)} → {status}  [{elapsed:.1f}s]")
        if not ok:
            all_ok = False
    print()
    return all_ok

def verify_rightedge_period(T_start, length=32):
    """Verify period-8 for rightEdgeF/G around T_start."""
    print(f"Period-8 verification for T={T_start}..{T_start+length-1}")
    print("-" * 60)
    f10_vals = []
    g10_vals = []
    f12_vals = []
    g12_vals = []
    for T in range(T_start, T_start + length):
        f10_vals.append(rightEdgeF(10, T))
        g10_vals.append(rightEdgeG(10, 4, T))
        f12_vals.append(rightEdgeF(12, T))
        g12_vals.append(rightEdgeG(12, 4, T))

    all_ok = True
    for label, vals in [("F10", f10_vals), ("G10", g10_vals), ("F12", f12_vals), ("G12", g12_vals)]:
        period = None
        for p in [4, 8, 16]:
            if all(vals[i] == vals[i + p] for i in range(len(vals) - p)):
                period = p
                break
        pattern = "".join("1" if v else "0" for v in vals[:16])
        status = f"period={period}" if period else "no period found ✗"
        print(f"  {label}: {pattern}...  {status}")
        if period is None:
            all_ok = False

    print()
    return all_ok

def verify_subcaseB_mod8(T_start=3088, T_end=3200):
    """Verify SubcaseB m=4 fires exactly at n'%8 ∈ {0,2,5,7} in range."""
    print(f"SubcaseB m=4 firing pattern, T={T_start}..{T_end} (n'=T-1)")
    print("-" * 60)
    firing_residues = set()
    non_firing_residues = set()
    fails = []

    for T in range(T_start, T_end + 1):
        n_prime = T - 1
        hcase, hts = subcaseB_fires(T)
        fires = hcase and hts
        r = n_prime % 8
        if fires:
            firing_residues.add(r)
        else:
            non_firing_residues.add(r)
        # Check: if fires, must be in {0,2,5,7}
        if fires and r not in {0, 2, 5, 7}:
            fails.append((T, n_prime, r))
        # Check: if not fires, must be in {1,3,4,6}
        if not fires and r in {0, 2, 5, 7}:
            fails.append((T, n_prime, r, "should fire but doesn't"))

    print(f"  Firing residues observed: {sorted(firing_residues)}")
    print(f"  Non-firing residues observed: {sorted(non_firing_residues)}")
    all_ok = (len(fails) == 0 and firing_residues == {0, 2, 5, 7})
    if fails:
        print(f"  FAILURES: {fails[:5]}")
    else:
        print(f"  ✓ SubcaseB fires exactly at n'%8 ∈ {{0,2,5,7}}")
    print()
    return all_ok

def verify_sensitivity(k, m, T):
    """Single sensitivity check."""
    F = rightEdgeF(k, T)
    G = rightEdgeG(k, m, T)
    print(f"rightEdgeSens {k} {m} {T}: F={int(F)} G={int(G)} → {'SENSITIVE ✓' if F!=G else 'NOT SENSITIVE ✗'}")
    return F != G

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        sys.exit(2)

    claim = args[0]
    all_ok = True

    if claim == "rightedge_base":
        all_ok = verify_rightedge_base()

    elif claim == "rightedge_period":
        T = int(args[1]) if len(args) > 1 else 100
        all_ok = verify_rightedge_period(T)

    elif claim == "subcaseB_mod8":
        all_ok = verify_subcaseB_mod8()

    elif claim == "sensitivity":
        if len(args) < 4:
            print("Usage: verify_lean_claim.py sensitivity <k> <m> <T>")
            sys.exit(2)
        all_ok = verify_sensitivity(int(args[1]), int(args[2]), int(args[3]))

    elif claim == "all":
        print("Running full verification suite...")
        print()
        all_ok = verify_rightedge_base()
        all_ok &= verify_rightedge_period(100)
        all_ok &= verify_subcaseB_mod8(3088, 3150)

    else:
        print(f"Unknown claim type: {claim}")
        print(__doc__)
        sys.exit(2)

    sys.exit(0 if all_ok else 1)
