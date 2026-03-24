#!/usr/bin/env python3
"""
Fast numpy version: max_m per SubcaseB period.
Results written incrementally to max_m_results.txt.

Key: uses numpy for vectorized rule30 steps.
Each step: L ops instead of L Python loops.
~100x speedup over pure Python.
"""
import numpy as np
import sys

OUTPUT = "/Users/jonathanhill/src/p2p/research/max_m_results.txt"

def rule30_steps(tape_np, steps):
    """Apply rule30 for `steps` steps. tape_np is int8 numpy array."""
    t = tape_np.copy()
    for _ in range(steps):
        l = np.roll(t, 1)
        r = np.roll(t, -1)
        t = l ^ (t | r)
    return t

def check_subcaseB(n_prime, m_val):
    """
    SubcaseB: rule30(n'+1)(spike_m)[center] = 0 AND rule30(n'+1)(ts2_{m,last})[center] = 1
    Tape: size = 2*(n'+1)+1, center = n'+1, spike at center+m_val, last = size-1
    """
    size = 2*(n_prime+1)+1
    center = n_prime+1
    pos_m = center + m_val
    if pos_m >= size:
        return False
    steps = n_prime + 1

    # Spike tape
    sp = np.zeros(size, dtype=np.int8)
    sp[pos_m] = 1
    out_sp = rule30_steps(sp, steps)
    if out_sp[center] != 0:
        return False

    # Two-spike tape
    ts2 = np.zeros(size, dtype=np.int8)
    ts2[pos_m] = 1
    ts2[size-1] = 1
    out_ts2 = rule30_steps(ts2, steps)
    return int(out_ts2[center]) == 1

def scan_period(period_idx, base=3087, period=256, m_max=80):
    n_start = base + period_idx * period
    n_end = n_start + period
    pairs = []
    for n_prime in range(n_start, n_end):
        for m in range(4, min(m_max, n_prime), 2):
            if check_subcaseB(n_prime, m):
                pairs.append((n_prime, m))
    return pairs

# ---- main ----
PERIOD = 256
BASE = 3087
NUM_PERIODS = 8
M_MAX = 60  # check up to m=60; m=36 should appear in period 5

lines = [
    "SubcaseB max_m per period — numpy-accelerated",
    "=" * 60,
    f"Base: {BASE}, Period: {PERIOD}, M_MAX: {M_MAX}, Num periods: {NUM_PERIODS}",
    "",
]

def flush_write():
    with open(OUTPUT, 'w') as f:
        f.write('\n'.join(lines) + '\n')

flush_write()

all_m_values = set()

for pi in range(NUM_PERIODS):
    n_start = BASE + pi * PERIOD
    n_end = n_start + PERIOD
    print(f"Period {pi+1}: n' in [{n_start}, {n_end}) ...", flush=True)

    pairs = scan_period(pi, BASE, PERIOD, M_MAX)

    if pairs:
        max_m = max(m for _, m in pairs)
        m_vals = sorted(set(m for _, m in pairs))
        new_m = [m for m in m_vals if m not in all_m_values]
        all_m_values.update(m_vals)

        line1 = f"Period {pi+1}: [{n_start},{n_end}) | count={len(pairs)}, max_m={max_m}"
        line2 = f"  m values: {m_vals}"
        line3 = f"  NEW m (not in prev periods): {new_m}"
        print(line1); print(line2); print(line3, flush=True)
        lines.extend([line1, line2, line3, ""])
    else:
        line = f"Period {pi+1}: [{n_start},{n_end}) | NO SubcaseB cases"
        print(line, flush=True)
        lines.extend([line, ""])

    flush_write()

lines.append(f"All m values seen across {NUM_PERIODS} periods: {sorted(all_m_values)}")
lines.append(f"Max m seen: {max(all_m_values) if all_m_values else 'N/A'}")
flush_write()
print(f"\nDone. Results at {OUTPUT}")
