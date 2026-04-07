#!/usr/bin/env python3
"""
dChain Phase Analysis for Rule 30 AllEssential induction proof.

Analyzes shadow regions: (n,j) pairs where dChain(n+1,j)=False AND dChain(n,j)=False.

dChain recurrence (tracking spike propagation):
  dChain(t, 0) = True           for all t
  dChain(0, k) = False          for k >= 1
  dChain(t+1, 1) = dChain(t,1) XOR 1   (since rule30Local(x, True, False) = x XOR 1)
  dChain(t+1, k+2) = dChain(t,k+2) XOR (dChain(t,k+1) | dChain(t,k))
"""

import math
import numpy as np
from gf2_variety import dchain_table

T_MAX = 500
K_MAX = 200


def find_period_from_end(seq, min_copies=3):
    """Find period by checking from the end of the sequence backward."""
    n = len(seq)
    for p in range(1, n // min_copies + 1):
        # Check last min_copies*p entries are periodic with period p
        tail = n - min_copies * p
        if tail < 0:
            continue
        ok = True
        for i in range(tail, n - p):
            if seq[i] != seq[i + p]:
                ok = False
                break
        if ok:
            # Find where periodicity starts
            start = tail
            while start > 0 and seq[start - 1] == seq[start - 1 + p]:
                start -= 1
            return start, p
    return n, 0


def main():
    print("=" * 80)
    print("dChain Phase Analysis")
    print(f"T_MAX={T_MAX}, K_MAX={K_MAX}")
    print("=" * 80)

    D = dchain_table(T_MAX, K_MAX)

    # ── Section 1: Period analysis per k ──
    print("\n--- Section 1: Period of dChain(t, k) as function of t ---")
    print(f"{'k':>4} | {'transient':>9} | {'period':>6} | {'false_per_period':>15} | {'shadow_per_period':>16} | shadow_residues")
    print("-" * 100)

    period_data = {}
    for k in range(0, min(31, K_MAX + 1)):
        seq = D[:, k].tolist()
        trans, per = find_period_from_end(seq, min_copies=3)

        if per == 0:
            print(f"{k:>4} | {'none':>9} | {'???':>6} | {'???':>15} | {'???':>16} |")
            period_data[k] = (trans, per, [], [])
            continue

        # Count false values in one period (after transient)
        period_start = trans
        false_in_period = sum(1 for i in range(period_start, period_start + per) if not seq[i])

        # Shadow: dChain(t,k)=False AND dChain(t-1,k)=False
        # Shadow at t means (n,j)=(t-1,k) is a shadow pair
        shadow_residues = []
        for t in range(max(1, period_start), period_start + per):
            if not seq[t] and not seq[t - 1]:
                shadow_residues.append(t % per)

        # Deduplicate shadow residues
        shadow_residues = sorted(set(shadow_residues))

        period_data[k] = (trans, per, false_in_period, shadow_residues)
        sr_str = str(shadow_residues) if len(shadow_residues) <= 10 else f"{shadow_residues[:5]}...({len(shadow_residues)} total)"
        print(f"{k:>4} | {trans:>9} | {per:>6} | {false_in_period:>15} | {len(shadow_residues):>16} | {sr_str}")

    # ── Section 2: Period growth ──
    print("\n--- Section 2: Period growth ---")
    periods = []
    for k in range(0, min(31, K_MAX + 1)):
        trans, per, _, _ = period_data[k]
        periods.append((k, per))
        if per > 0 and k > 0:
            prev_per = period_data.get(k - 1, (0, 0))[1]
            ratio = per / prev_per if prev_per > 0 else "N/A"
            print(f"  k={k:>2}: period={per:>6}, ratio_to_prev={ratio}")

    # ── Section 3: Shadow density at each t ──
    print("\n--- Section 3: Shadow density at each t ---")
    print(f"{'t':>5} | {'shadow_count':>12} | {'max_k_in_cone':>13} | {'density':>8} | shadow_k_values")
    print("-" * 90)

    shadow_counts = []
    for t in range(1, min(T_MAX + 1, 101)):
        max_k = min(2 * t, K_MAX)
        shadow_mask = ~D[t, 1:max_k + 1] & ~D[t - 1, 1:max_k + 1]
        shadows_at_t = (np.nonzero(shadow_mask)[0] + 1).tolist()  # +1 for k offset
        count = len(shadows_at_t)
        shadow_counts.append(count)
        density = count / (2 * t)
        k_str = str(shadows_at_t) if len(shadows_at_t) <= 8 else f"{shadows_at_t[:4]}...{shadows_at_t[-2:]} ({count} total)"
        if t <= 30 or t % 10 == 0:
            print(f"{t:>5} | {count:>12} | {2 * t:>13} | {density:>8.4f} | {k_str}")

    # ── Section 4: Shadow growth rate ──
    print("\n--- Section 4: Shadow growth analysis ---")
    ts = np.arange(1, min(T_MAX + 1, 101))
    sc = np.array(shadow_counts)
    mask = (ts >= 5) & (sc > 0)
    if mask.sum() >= 2:
        log_t = np.log(ts[mask].astype(float))
        log_s = np.log(sc[mask].astype(float))
        # Power-law fit: log(s) = a*log(t) + b  =>  s ~ t^a
        a, b = np.polyfit(log_t, log_s, 1)
        print(f"  Power-law fit: shadow_count ~ t^{a:.3f} * exp({b:.3f})")
        print(f"  Interpretation: {'polynomial' if a < 2 else 'superlinear'} growth (exponent {a:.3f})")
        # Exponential fit: log(s) = c*t + d
        c, d = np.polyfit(ts[mask].astype(float), log_s, 1)
        print(f"  Exponential fit: shadow_count ~ exp({c:.5f} * t + {d:.3f})")
        print(f"  Base per step: {math.exp(c):.5f}")
    else:
        print("  Not enough data for regression")

    # ── Section 5: Case coverage at each level ──
    print("\n--- Section 5: Case coverage breakdown at each t ---")
    print(f"{'t':>5} | {'cone_size':>9} | {'case1(T,T)':>10} | {'case2(F,T)':>10} | {'case2(T,F)':>10} | {'shadow(F,F)':>12} | shadow_frac")
    print("-" * 100)
    for t in range(1, min(T_MAX + 1, 51)):
        max_k = min(2 * t, K_MAX)
        cur = D[t, 1:max_k + 1]
        prev = D[t - 1, 1:max_k + 1]
        case1 = int(np.sum(cur & prev))
        case2a = int(np.sum(~cur & prev))
        case2b = int(np.sum(cur & ~prev))
        shadow = int(np.sum(~cur & ~prev))
        total = max_k
        sfrac = shadow / total if total > 0 else 0
        if t <= 20 or t % 5 == 0:
            print(f"{t:>5} | {total:>9} | {case1:>10} | {case2a:>10} | {case2b:>10} | {shadow:>12} | {sfrac:>8.4f}")

    # ── Section 6: Visual dChain grid (small) ──
    print("\n--- Section 6: dChain grid (t=0..30, k=0..20) ---")
    print("     ", end="")
    for k in range(0, 21):
        print(f"{k:>2}", end="")
    print()
    for t in range(0, 31):
        print(f"t={t:>2}: ", end="")
        for k in range(0, 21):
            print(" 1" if D[t, k] else " 0", end="")
        print()

    # ── Section 7: Shadow grid ──
    print("\n--- Section 7: Shadow grid (shadow=X, t=1..30, k=1..20) ---")
    print("     ", end="")
    for k in range(1, 21):
        print(f"{k:>2}", end="")
    print()
    for t in range(1, 31):
        print(f"t={t:>2}: ", end="")
        for k in range(1, 21):
            if not D[t, k] and not D[t - 1, k]:
                print(" X", end="")
            elif D[t, k]:
                print(" 1", end="")
            else:
                print(" 0", end="")
        print()

    # ── Section 8: Extended period table for larger k ──
    print("\n--- Section 8: Extended period analysis (k=0..60, T_MAX=500) ---")
    print(f"{'k':>4} | {'period':>8} | {'transient':>9} | {'false_frac':>10} | {'shadow_frac':>11}")
    print("-" * 60)
    for k in range(0, min(61, K_MAX + 1)):
        seq = D[:, k].tolist()
        trans, per = find_period_from_end(seq, min_copies=3)
        if per == 0:
            print(f"{k:>4} | {'???':>8} | {trans:>9} | {'???':>10} | {'???':>11}")
            continue
        ps = trans
        false_count = sum(1 for i in range(ps, ps + per) if not seq[i])
        shadow_count = sum(1 for i in range(max(1, ps), ps + per) if not seq[i] and not seq[i - 1])
        false_frac = false_count / per
        shadow_frac = shadow_count / per
        print(f"{k:>4} | {per:>8} | {trans:>9} | {false_frac:>10.4f} | {shadow_frac:>11.4f}")

    # ── Section 9: Key findings ──
    print("\n" + "=" * 80)
    print("KEY FINDINGS SUMMARY")
    print("=" * 80)

    # Check if periods are powers of 2
    print("\nPeriod sequence for k=0..30:")
    for k in range(0, min(31, K_MAX + 1)):
        trans, per, _, _ = period_data[k]
        is_pow2 = per > 0 and (per & (per - 1)) == 0
        print(f"  k={k:>2}: period={per:>6} {'(2^' + str(int(math.log2(per))) + ')' if is_pow2 and per > 0 else ''}")

    # Shadow fraction trend
    print("\nShadow fraction trend (fraction of cone that is shadow):")
    for t in [10, 20, 30, 50, 70, 100]:
        if t <= T_MAX:
            max_k = min(2 * t, K_MAX)
            sh = int(np.sum(~D[t, 1:max_k + 1] & ~D[t - 1, 1:max_k + 1]))
            print(f"  t={t:>3}: {sh}/{max_k} = {sh / max_k:.4f}")


if __name__ == "__main__":
    main()
