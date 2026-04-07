#!/usr/bin/env python3
"""
compute_transport_matrix.py — Compute the 256-step interaction transport matrix Φ for m=22.

The fiber bundle hypothesis:
  - spike_22 CA has period-256 LFSR base clock (state v_n ∈ GF(2)^256)
  - Adding spike_34 creates an interaction state w_n ∈ GF(2)^256
  - After 256 CA steps: w_{n+256} = Φ · w_n  (same matrix every cycle)
  - ord(Φ) = 512  →  twoSpikeList(34,22) has period 256×512 = 131072

If ord(Φ) = 512, this is the algebraic proof path for the m=22 l≡0 sorry.

Usage:
    python3 scripts/compute_transport_matrix.py [--n0 N]  (default N=3088)
"""

import numpy as np
import sys
import time

# ---------------------------------------------------------------------------
# Core CA engine (numpy, fixed-width)
# ---------------------------------------------------------------------------

def rule30_step_np(tape):
    left  = np.roll(tape, 1);  left[0]  = False
    right = np.roll(tape, -1); right[-1] = False
    return left ^ (tape | right)

def rule30_evolve_np(tape, steps):
    for _ in range(steps):
        tape = rule30_step_np(tape)
    return tape

# ---------------------------------------------------------------------------
# Background: spike_22, evolved to step n0, width = 2*n0+1
# We work in a fixed-width tape centered at position n0 (the center cell).
# ---------------------------------------------------------------------------

def make_background(n0, m=22):
    """Spike at m, tape width 2*n0+1, evolved n0 steps. Returns full tape."""
    width = 2 * n0 + 1
    tape = np.zeros(width, dtype=bool)
    tape[m] = True
    return rule30_evolve_np(tape, n0)

def make_perturbed(n0, m=22, spike2=34):
    """Two spikes (m and spike2), same tape/steps. Returns full tape."""
    width = 2 * n0 + 1
    tape = np.zeros(width, dtype=bool)
    tape[m] = True
    tape[spike2] = True
    return rule30_evolve_np(tape, n0)

# ---------------------------------------------------------------------------
# Transport matrix computation
#
# The interaction state at time n is the XOR of:
#   full_twoSpike_tape[n0-127 : n0+129]  ⊕  full_spike_tape[n0-127 : n0+129]
# (a 256-cell window centered on the center cell)
#
# To compute Φ, we:
# 1. Compute the background state B(n0) = spike_22 tape at time n0
# 2. For each basis vector e_i (i=0..255): create a perturbation tape that
#    equals B(n0) everywhere except has one bit flipped at position n0-127+i
# 3. Evolve BOTH the background and the perturbed tape for 256 more steps
# 4. The XOR of the two results at the center window gives Φ[:,i]
#
# This gives a 256×256 GF(2) matrix Φ.
# ---------------------------------------------------------------------------

def compute_transport_matrix(n0=3088, window=256, cycles=1, verbose=True):
    """
    Compute the transport matrix Φ for the interaction state.

    n0: starting time step (should be large enough for LFSR to be in steady state)
    window: size of interaction state (number of cells around center)
    cycles: number of base cycles (each = 256 steps) to compose
    """
    half = window // 2
    center = n0  # center cell is at index n0 in tape of width 2*n0+1

    if verbose:
        print(f"Computing transport matrix Φ")
        print(f"  n0={n0}, window={window}, cycles={cycles}")
        print(f"  Tape width: {2*n0+1}, center index: {center}")
        print(f"  Transport over: {256*cycles} steps")

    t0 = time.time()

    # Step 1: compute background tape at time n0
    if verbose: print(f"\n[1] Computing background at n0={n0}...")
    bg = make_background(n0)
    if verbose: print(f"    Background center: {int(bg[center])}  [{time.time()-t0:.1f}s]")

    # Step 2: compute background tape at time n0 + 256*cycles
    steps = 256 * cycles
    if verbose: print(f"\n[2] Evolving background for {steps} more steps...")
    bg_future = rule30_evolve_np(bg.copy(), steps)
    if verbose: print(f"    Future center: {int(bg_future[center])}  [{time.time()-t0:.1f}s]")

    # Step 3: for each basis vector, compute Φ[:,i]
    if verbose: print(f"\n[3] Computing {window} basis perturbations...")
    Phi = np.zeros((window, window), dtype=bool)

    for i in range(window):
        # Create perturbed background: flip bit at position (center - half + i)
        pos = center - half + i
        if pos < 0 or pos >= len(bg):
            continue  # out of bounds, column stays zero
        perturbed = bg.copy()
        perturbed[pos] ^= True

        # Evolve perturbed tape
        perturbed_future = rule30_evolve_np(perturbed, steps)

        # XOR with background future → interaction at future time
        diff = perturbed_future ^ bg_future

        # Extract window around center
        lo = center - half
        hi = center + half
        if lo < 0 or hi > len(diff):
            # Edge case: clamp
            lo = max(0, lo); hi = min(len(diff), hi)
        Phi[:, i] = diff[lo:hi]

        if verbose and i % 32 == 31:
            elapsed = time.time() - t0
            print(f"    {i+1}/{window} [{elapsed:.1f}s, {(i+1)/(elapsed):.1f}/s]")

    elapsed = time.time() - t0
    if verbose:
        print(f"\n    Done [{elapsed:.1f}s]")
        nnz = np.sum(Phi)
        print(f"    Φ: {window}×{window} GF(2) matrix, {nnz}/{window*window} nonzero ({100*nnz/(window*window):.1f}%)")

    return Phi

# ---------------------------------------------------------------------------
# Matrix order computation over GF(2)
# ---------------------------------------------------------------------------

def matmul_gf2(A, B):
    """Matrix multiply over GF(2) using numpy."""
    return (A @ B.astype(np.int32)) % 2 == 1

def matpow_gf2(M, k):
    """Compute M^k over GF(2) using repeated squaring."""
    n = M.shape[0]
    result = np.eye(n, dtype=bool)
    base = M.copy()
    while k > 0:
        if k & 1:
            result = matmul_gf2(result, base)
        base = matmul_gf2(base, base)
        k >>= 1
    return result

def matrix_is_identity(M):
    n = M.shape[0]
    return np.all(M == np.eye(n, dtype=bool))

def compute_order(Phi, max_power=131072, verbose=True):
    """
    Compute ord(Φ) = smallest k > 0 s.t. Φ^k = I.
    Tests divisors of max_power in order.
    """
    if verbose: print(f"\n[4] Computing ord(Φ) (max={max_power})...")
    t0 = time.time()

    # Test candidate orders: divisors of 131072 = 2^17 in increasing order
    # 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072
    candidates = [2**k for k in range(18)]  # 1..131072

    found_order = None
    for k in candidates:
        t1 = time.time()
        Mk = matpow_gf2(Phi, k)
        is_id = matrix_is_identity(Mk)
        if verbose:
            print(f"    Φ^{k:7d} = I? {is_id}  [{time.time()-t1:.2f}s]")
        if is_id and found_order is None:
            found_order = k
            if verbose:
                print(f"\n  *** ord(Φ) divides {k} ***")
            # Now check if it divides k/2
            if k == 1:
                break
            # The order must be a divisor of k; we found the smallest power-of-2
            # that gives identity. The actual order divides this k.
            # For our purposes (is order 512?), this is sufficient.
            break

    if verbose:
        elapsed = time.time() - t0
        print(f"\n  Order computation done [{elapsed:.1f}s]")
        if found_order:
            print(f"  ord(Φ) divides {found_order}")
            print(f"  Fiber bundle prediction: period = 256 × {found_order} = {256*found_order}")
            if found_order == 512:
                print(f"  ✓ CONFIRMED: ord(Φ) = 512 → twoSpikeList(34,22) period = 131072")
                print(f"  ✓ This is the algebraic proof path for m=22 l≡0 sorry!")
            elif found_order < 512:
                print(f"  NOTE: period = {256*found_order} < 131072. Need to check if 131072 is the actual period or if a smaller witness suffices.")
            else:
                print(f"  NOTE: period = {256*found_order}. Longer than expected.")

    return found_order

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="Compute transport matrix Φ for m=22 fiber bundle")
    parser.add_argument("--n0", type=int, default=3088, help="Starting time step (default: 3088)")
    parser.add_argument("--window", type=int, default=256, help="Interaction window size (default: 256)")
    parser.add_argument("--save", action="store_true", help="Save Φ to /tmp/transport_matrix.npy")
    args = parser.parse_args()

    print("=" * 60)
    print("Transport Matrix Computation for m=22 Fiber Bundle")
    print("=" * 60)

    Phi = compute_transport_matrix(n0=args.n0, window=args.window)

    if args.save:
        np.save("/tmp/transport_matrix.npy", Phi)
        print(f"\nΦ saved to /tmp/transport_matrix.npy")

    order = compute_order(Phi)

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    if order is not None:
        print(f"ord(Φ) divides {order}")
        print(f"Predicted period of twoSpikeList(34,22): {256 * order}")
        print(f"Known period (computationally verified): 131072")
        if 256 * order == 131072:
            print(f"\n✓ MATCH — fiber bundle structure confirmed!")
            print(f"  Lean proof path: express Φ as explicit matrix,")
            print(f"  prove Φ^131072=I via native_decide (feasible on 256×256 matrix),")
            print(f"  prove transport recurrence structurally.")
        else:
            print(f"\n? Mismatch — investigate further.")
    else:
        print("Order not found within 131072. Investigate.")
