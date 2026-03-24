#!/usr/bin/env python3
"""
Investigate how max_m grows across SubcaseB periods.
Results written to max_m_results.txt — survives context compaction.
"""
import sys

OUTPUT_FILE = "/Users/jonathanhill/src/p2p/research/max_m_results.txt"

def rule30_local(l, c, r):
    return l ^ (c | r)

def rule30n(n, tape):
    t = list(tape)
    L = len(t)
    for _ in range(n):
        new_t = [0]*L
        for i in range(L):
            new_t[i] = rule30_local(t[(i-1)%L], t[i], t[(i+1)%L])
        t = new_t
    return t

def check_subcaseB(n_prime, m_val):
    """
    SubcaseB: rule30(n'+1)(spike_m)[center] = 0 AND rule30(n'+1)(ts2_{m,last})[center] = 1
    Tape size = 2*(n'+1)+1, center = n'+1, spike at position center+m_val
    """
    size = 2*(n_prime+1)+1
    center = n_prime+1
    pos_m = center + m_val
    if pos_m >= size:
        return False
    # Spike tape
    sp = [0]*size
    sp[pos_m] = 1
    out_sp = rule30n(n_prime+1, sp)
    if out_sp[center] != 0:
        return False
    # Two-spike tape
    ts2 = [0]*size
    ts2[pos_m] = 1
    ts2[size-1] = 1
    out_ts2 = rule30n(n_prime+1, ts2)
    return out_ts2[center] == 1

def find_subcaseB_in_range(n_start, n_end, m_max=80):
    results = []
    for n_prime in range(n_start, n_end):
        for m in range(4, m_max, 2):
            if check_subcaseB(n_prime, m):
                results.append((n_prime, m))
    return results

PERIOD = 256
BASE = 3087
NUM_PERIODS = 8

lines = []
lines.append("SubcaseB max_m per period investigation")
lines.append("=" * 60)
lines.append(f"Base: {BASE}, Period: {PERIOD}, Checking m up to 80")
lines.append("")

for period_idx in range(NUM_PERIODS):
    n_start = BASE + period_idx * PERIOD
    n_end = n_start + PERIOD
    msg = f"Period {period_idx+1}: n' in [{n_start}, {n_end})"
    print(msg, flush=True)
    lines.append(msg)

    pairs = find_subcaseB_in_range(n_start, n_end, m_max=80)
    if pairs:
        max_m = max(m for _, m in pairs)
        m_values = sorted(set(m for _, m in pairs))
        count_msg = f"  Count: {len(pairs)}, Max m: {max_m}"
        m_msg = f"  m values: {m_values}"
        new_m = [m for m in m_values if m > 28]
        new_msg = f"  NEW m > 28: {new_m}" if new_m else "  No m > 28"
        print(count_msg)
        print(m_msg)
        print(new_msg, flush=True)
        lines.extend([count_msg, m_msg, new_msg])
    else:
        msg2 = "  No SubcaseB cases found"
        print(msg2, flush=True)
        lines.append(msg2)
    lines.append("")

    # Write incrementally so results survive if killed
    with open(OUTPUT_FILE, 'w') as f:
        f.write('\n'.join(lines))

print(f"\nResults written to {OUTPUT_FILE}")
