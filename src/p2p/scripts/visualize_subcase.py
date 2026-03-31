#!/usr/bin/env python3
"""
visualize_subcase.py — Rule 30 SubcaseB geometry visualizer.

Generates PNG spacetime diagrams showing:
  1. Spacetime evolution from spike(m) — the F-cone
  2. Interaction error D between spike(w) and spike(m) — when does a witness work?
  3. Self-similar hierarchy of witness w vs v₂(n'-5) — the infinite cascade

Usage: python3 scripts/visualize_subcase.py [n_prime] [m_val] [max_w]
"""

import sys
import numpy as np
import matplotlib
matplotlib.use('Agg')  # non-interactive, save to file
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors
from pathlib import Path

OUT_DIR = Path(__file__).parent.parent / "research" / "figures"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# ── Rule 30 (Lean shrinking-tape semantics) ──────────────────────────────────

def evolve_shrinking(tape: list[bool], steps: int) -> list[list[bool]]:
    """Evolve tape using Lean caStepList semantics (shrinks by 2 per step).
    Returns list of all intermediate tapes (including initial)."""
    history = [tape[:]]
    cur = tape[:]
    for _ in range(steps):
        new = []
        for i in range(len(cur) - 2):
            new.append(cur[i] ^ (cur[i+1] | cur[i+2]))
        cur = new
        history.append(cur[:])
    return history


def spike_tape(pos: int, n_prime: int) -> list[bool]:
    """spikeAtList pos (2*(n'+1)+1)"""
    N = 2 * (n_prime + 1) + 1
    return [i == pos for i in range(N)]


def two_spike_tape(pos1: int, pos2: int, n_prime: int) -> list[bool]:
    """twoSpikeList pos1 pos2 N"""
    N = 2 * (n_prime + 1) + 1
    return [(i == pos1 or i == pos2) for i in range(N)]


def center_bit(tape: list[bool]) -> bool:
    """Get position 0 (center after shrinking)."""
    return tape[0] if tape else False


def subcase_b_fires(n_prime: int, m_val: int) -> bool:
    """Check SubcaseB: F=0 AND G=1 (twoSpikeLast)."""
    T = n_prime + 1
    f_tape = spike_tape(m_val, n_prime)
    g_tape = two_spike_tape(m_val, 2 * (n_prime + 1), n_prime)
    F = center_bit(evolve_shrinking(f_tape, T)[-1])
    G = center_bit(evolve_shrinking(g_tape, T)[-1])
    return (not F) and G


def sensitivity_check(n_prime: int, w: int, m_val: int) -> bool:
    """True if spike(w) center ≠ twoSpike(w, m_val) center."""
    T = n_prime + 1
    sp = spike_tape(w, n_prime)
    ts = two_spike_tape(w, m_val, n_prime)
    F = center_bit(evolve_shrinking(sp, T)[-1])
    H = center_bit(evolve_shrinking(ts, T)[-1])
    return F != H


def interaction_error_field(n_prime: int, w: int, m_val: int) -> np.ndarray:
    """Compute D[i,t] = evolve(A^B)[i,t] XOR evolve(A)[i,t] XOR evolve(B)[i,t].
    A = spike(w), B = spike(m_val).
    Returns 2D array shape (T+1, N-2t) padded to (T+1, N) with NaN outside.
    """
    T = n_prime + 1
    N = 2 * (n_prime + 1) + 1
    A = spike_tape(w, n_prime)
    B = spike_tape(m_val, n_prime)
    AB = [a ^ b for a, b in zip(A, B)]

    hA  = evolve_shrinking(A, T)
    hB  = evolve_shrinking(B, T)
    hAB = evolve_shrinking(AB, T)

    D = np.full((T + 1, N), np.nan)
    for t in range(T + 1):
        for i in range(len(hAB[t])):
            # position in original tape: i + t (left edge of remaining tape is at +t)
            orig_i = i + t
            d = (int(hAB[t][i]) ^ int(hA[t][i]) ^ int(hB[t][i]))
            D[t, orig_i] = d
    return D


def v2(k: int) -> int:
    if k <= 0:
        return 99
    v = 0
    while k % 2 == 0:
        k //= 2
        v += 1
    return v


# ── Figure 1: Spacetime diagram of spike(m) evolution ────────────────────────

def fig_spacetime(n_prime: int, m_val: int, max_steps: int = None):
    T = min(n_prime + 1, max_steps or n_prime + 1)
    tape = spike_tape(m_val, n_prime)
    history = evolve_shrinking(tape, T)
    N = 2 * (n_prime + 1) + 1
    center = n_prime + 1  # position 0 after full shrink

    # Build display matrix (T+1) x N, NaN outside tape
    mat = np.full((T + 1, N), np.nan)
    for t, row in enumerate(history):
        for i, v in enumerate(row):
            mat[t, i + t] = float(v)

    fig, ax = plt.subplots(figsize=(14, 8))
    cmap = mcolors.ListedColormap(['white', 'black'])
    im = ax.imshow(mat, cmap=cmap, vmin=0, vmax=1, aspect='auto',
                   origin='upper', interpolation='nearest')

    # Mark center column
    ax.axvline(x=center, color='red', linewidth=1.5, alpha=0.7, label=f'center={center}')
    # Mark spike position
    ax.axvline(x=m_val, color='blue', linewidth=1.5, alpha=0.5, linestyle='--', label=f'spike m={m_val}')
    # Mark last position
    ax.axvline(x=2*(n_prime+1), color='green', linewidth=1.5, alpha=0.5, linestyle=':', label=f'last=2(n\'+1)')

    ax.set_title(f"Rule 30 spacetime: spike at m={m_val}, n'={n_prime}\n"
                 f"SubcaseB fires: {subcase_b_fires(n_prime, m_val)}")
    ax.set_xlabel('tape position')
    ax.set_ylabel('time step t')
    ax.legend(loc='upper right', fontsize=8)
    plt.tight_layout()

    fname = OUT_DIR / f"spacetime_m{m_val}_n{n_prime}.png"
    plt.savefig(fname, dpi=120)
    plt.close()
    print(f"  saved: {fname}")
    return fname


# ── Figure 2: Interaction error D field ──────────────────────────────────────

def fig_d_field(n_prime: int, w: int, m_val: int):
    T = n_prime + 1
    N = 2 * (n_prime + 1) + 1
    center = n_prime + 1

    D = interaction_error_field(n_prime, w, m_val)
    sens = sensitivity_check(n_prime, w, m_val)

    fig, ax = plt.subplots(figsize=(14, 8))
    # 0=white (linear), 1=red (nonlinear/D≠0), NaN=gray
    cmap = mcolors.ListedColormap(['#f0f0f0', '#cc2222'])
    bounds = [-0.5, 0.5, 1.5]
    norm = mcolors.BoundaryNorm(bounds, cmap.N)
    ax.imshow(np.nan_to_num(D, nan=-1),
              cmap=mcolors.ListedColormap(['#e0e0e0', '#f0f0f0', '#cc2222']),
              vmin=-1, vmax=1,
              aspect='auto', origin='upper', interpolation='nearest')

    ax.axvline(x=center, color='red', linewidth=2, alpha=0.8, label=f'center={center}')
    ax.axvline(x=w, color='blue', linewidth=1.5, linestyle='--', alpha=0.6, label=f'w={w}')
    ax.axvline(x=m_val, color='orange', linewidth=1.5, linestyle=':', alpha=0.7, label=f'm={m_val}')

    ax.set_title(f"Interaction error D: spike({w}) ⊕ spike({m_val}), n'={n_prime}\n"
                 f"D[center,T] = {int(D[-1, center] if not np.isnan(D[-1, center]) else -1)} | "
                 f"sensitive = {sens}")
    ax.set_xlabel('tape position')
    ax.set_ylabel('time step t')
    ax.legend(loc='upper right', fontsize=8)
    plt.tight_layout()

    fname = OUT_DIR / f"D_field_w{w}_m{m_val}_n{n_prime}.png"
    plt.savefig(fname, dpi=120)
    plt.close()
    print(f"  saved: {fname}")
    return fname


# ── Figure 3: Witness w vs v₂(n'-5) for m=4 ─────────────────────────────────

def fig_witness_hierarchy(m_val: int = 4, n_max: int = 8000, max_w: int = 80):
    data = []
    for n in range(3087, n_max):
        if n % 8 != 5:
            continue
        if not subcase_b_fires(n, m_val):
            continue
        # find min even w
        w_min = None
        for w in range(2, max_w, 2):
            if w == m_val:
                continue
            if sensitivity_check(n, w, m_val):
                w_min = w
                break
        v = v2(n - 5)
        data.append((n, v, w_min))

    if not data:
        print("  no data found")
        return

    ns, vs, ws = zip(*data)
    ws_num = [w if w is not None else max_w + 2 for w in ws]

    fig, axes = plt.subplots(1, 2, figsize=(16, 6))

    # Left: w vs n'
    ax = axes[0]
    scatter = ax.scatter(ns, ws_num, c=vs, cmap='plasma', s=8, alpha=0.7)
    plt.colorbar(scatter, ax=ax, label='v₂(n\'-5)')
    ax.set_xlabel("n'")
    ax.set_ylabel("min witness w")
    ax.set_title(f"Witness w vs n' (m={m_val}, colored by v₂)")
    ax.axhline(y=max_w, color='red', linestyle='--', alpha=0.5, label='search limit')

    # Right: w vs v₂(n'-5)
    ax2 = axes[1]
    jitter = np.random.default_rng(42).uniform(-0.15, 0.15, len(vs))
    sc2 = ax2.scatter([v + j for v, j in zip(vs, jitter)], ws_num, alpha=0.4, s=6)
    # Fit line
    xs = np.array(vs, dtype=float)
    ys = np.array(ws_num, dtype=float)
    mask = np.array([w is not None for w in ws])
    if mask.sum() > 5:
        coeffs = np.polyfit(xs[mask], ys[mask], 1)
        xfit = np.linspace(min(xs), max(xs), 100)
        ax2.plot(xfit, np.polyval(coeffs, xfit), 'r-', linewidth=2,
                 label=f'linear fit: w≈{coeffs[0]:.2f}·v₂+{coeffs[1]:.2f}')
    ax2.set_xlabel("v₂(n'-5)")
    ax2.set_ylabel("min witness w")
    ax2.set_title(f"Witness w vs v₂(n'-5) (m={m_val})")
    ax2.legend(fontsize=9)

    plt.tight_layout()
    fname = OUT_DIR / f"witness_hierarchy_m{m_val}.png"
    plt.savefig(fname, dpi=120)
    plt.close()
    print(f"  saved: {fname}")
    return fname


# ── Figure 4: D-field comparison across n' values for fixed w ────────────────

def fig_d_field_comparison(m_val: int = 22, w: int = 34, n_list=None):
    """Show D-field for several n' values side by side."""
    if n_list is None:
        n_list = [35598, 35598 + 65536, 35598 + 2*65536]

    fig, axes = plt.subplots(1, len(n_list), figsize=(6 * len(n_list), 8))
    if len(n_list) == 1:
        axes = [axes]

    for ax, n_prime in zip(axes, n_list):
        T = min(n_prime + 1, 200)  # show first 200 steps for readability
        N = 2 * (n_prime + 1) + 1
        center = n_prime + 1

        # For large n', only show a window around the interaction region
        # The cones meet around position 2*n'-22+22 = area of overlap
        cone_meet = (w + m_val) // 2 + n_prime  # rough estimate
        window_half = min(200, T // 3)
        window_start = max(0, center - window_half)
        window_end = min(N, center + window_half + 50)

        D = interaction_error_field(n_prime, w, m_val)
        sens = sensitivity_check(n_prime, w, m_val)

        D_window = D[:T+1, window_start:window_end]

        ax.imshow(np.nan_to_num(D_window, nan=-0.5),
                  cmap=mcolors.ListedColormap(['#d0d0d0', '#f5f5f5', '#cc2222']),
                  vmin=-0.5, vmax=1, aspect='auto', origin='upper', interpolation='nearest')
        ax.axvline(x=center - window_start, color='red', linewidth=2, alpha=0.8)
        ax.set_title(f"n'={n_prime}\nw={w}, m={m_val}\nsensitive={sens}")
        ax.set_xlabel('position (offset)')
        ax.set_ylabel('time step t' if ax == axes[0] else '')

    plt.suptitle(f"D-field evolution: how interaction error changes with n'\n"
                 f"red=nonzero D, gray=outside tape, white=D=0", y=1.02)
    plt.tight_layout()
    fname = OUT_DIR / f"D_comparison_w{w}_m{m_val}.png"
    plt.savefig(fname, dpi=100, bbox_inches='tight')
    plt.close()
    print(f"  saved: {fname}")
    return fname


# ── Figure 5: Anti-diagonal i+t=7 in Rule 30 spacetime ───────────────────────

def fig_antidiagonal(n_prime: int = 50, m_val: int = 22):
    """Show the anti-diagonal i+t=7 (should be all-zero for spike at 0 from ∞ tape).
    For spike at m_val, this corresponds to diagonal i+t = m_val+7... let's see."""
    T = n_prime + 1
    N = 2 * (n_prime + 1) + 1

    tape = spike_tape(m_val, n_prime)
    history = evolve_shrinking(tape, T)

    mat = np.full((T + 1, N), np.nan)
    for t, row in enumerate(history):
        for i, v in enumerate(row):
            mat[t, i + t] = float(v)

    fig, ax = plt.subplots(figsize=(14, 8))
    cmap = mcolors.ListedColormap(['white', 'black'])
    ax.imshow(mat, cmap=cmap, vmin=0, vmax=1, aspect='auto',
              origin='upper', interpolation='nearest')

    center = n_prime + 1
    ax.axvline(x=center, color='red', linewidth=1.5, alpha=0.7, label='center')

    # Draw anti-diagonals: position i = m_val + 7 - t (the key one)
    # In the shrinking tape, position i at step t corresponds to mat[t, i+t]
    # Anti-diagonal i+t = m_val+7: draw line i = (m_val+7) - t
    ts = np.arange(0, min(T+1, m_val+7+1))
    xs = (m_val + 7) - ts + ts  # original position = i+t = m_val+7, so x = m_val+7
    # Actually: for shrinking tape, original position at time t, index i: original_pos = i + t
    # Anti-diagonal original_pos + something = const doesn't simplify the same way
    # Let's draw the anti-diagonal in original coordinate: orig_pos = m_val + 7 - (T - t)... hmm

    # Simpler: draw the vertical line at position m_val+7 (the relevant column in original coords)
    for offset in range(-3, 12):
        col = m_val + 7 - offset
        if 0 <= col < N:
            ax.axvline(x=col, color='cyan', linewidth=0.5, alpha=0.3)
    ax.axvline(x=m_val + 7, color='cyan', linewidth=2, alpha=0.8, linestyle='--',
               label=f'pos m+7={m_val+7}')

    ax.set_title(f"Rule 30 spacetime from spike at m={m_val}, n'={n_prime}\n"
                 f"anti-diagonal region highlighted (cyan = pos m+7±3)")
    ax.set_xlabel('tape position (original)')
    ax.set_ylabel('time step t')
    ax.legend(loc='upper right', fontsize=8)
    plt.tight_layout()

    fname = OUT_DIR / f"antidiag_m{m_val}_n{n_prime}.png"
    plt.savefig(fname, dpi=120)
    plt.close()
    print(f"  saved: {fname}")
    return fname


# ── Main ──────────────────────────────────────────────────────────────────────

if __name__ == '__main__':
    n_prime = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    m_val   = int(sys.argv[2]) if len(sys.argv) > 2 else 22
    max_w   = int(sys.argv[3]) if len(sys.argv) > 3 else 80

    print(f"\n=== Rule 30 SubcaseB Visualizer ===")
    print(f"n'={n_prime}, m={m_val}")
    print(f"SubcaseB fires: {subcase_b_fires(n_prime, m_val)}")
    print()

    print("Figure 1: Spacetime diagram")
    fig_spacetime(n_prime, m_val, max_steps=min(n_prime+1, 300))

    print("Figure 2: D-field for several witness candidates")
    for w in range(2, min(max_w, 50), 4):
        if w == m_val:
            continue
        sens = sensitivity_check(n_prime, w, m_val)
        if sens:
            print(f"  w={w}: SENSITIVE — generating D-field")
            fig_d_field(n_prime, w, m_val)
            break
    else:
        print(f"  no sensitive w found in [2,{max_w}), using w=6")
        fig_d_field(n_prime, 6, m_val)

    print("Figure 3: Witness hierarchy for m=4")
    fig_witness_hierarchy(m_val=4, n_max=4500, max_w=60)

    print("Figure 4: D-field comparison across n' values (m=22, w=34)")
    # Use small n' for tractability
    small_n = [200, 266, 330]  # 35598 is too large for Python; use proportional examples
    fig_d_field_comparison(m_val=m_val, w=min(max_w-2, 34), n_list=small_n)

    print("Figure 5: Anti-diagonal structure")
    fig_antidiagonal(n_prime=min(n_prime, 80), m_val=m_val)

    print(f"\nAll figures saved to {OUT_DIR}")
