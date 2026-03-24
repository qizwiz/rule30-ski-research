#!/usr/bin/env python3
"""
Scan LARGE m-positions (near right edge of tape) for SubcaseB in period 1.
For n'=3085, m=6164 is SubcaseB. What large-m positions appear in [3087, 3343)?
"""
import numpy as np

OUTPUT = "/Users/jonathanhill/src/p2p/research/large_m_results.txt"

def rule30_center_out(n_prime, initial_tape_np):
    t = initial_tape_np.copy().astype(np.int8)
    L = len(t)
    for _ in range(n_prime + 1):
        l = np.roll(t, 1)
        r = np.roll(t, -1)
        t = l ^ (t | r)
    return int(t[n_prime + 1])

def check_subcaseB(n_prime, m_pos):
    size = 2*(n_prime+1)+1
    center = n_prime+1
    last = size - 1
    if m_pos < 2 or m_pos >= last or m_pos % 2 != 0 or m_pos == 2*n_prime:
        return False, None, None
    sp = np.zeros(size, dtype=np.int8); sp[m_pos] = 1
    f_spike = rule30_center_out(n_prime, sp)
    if f_spike != 0:
        return False, f_spike, None
    ts2 = np.zeros(size, dtype=np.int8); ts2[m_pos] = 1; ts2[last] = 1
    f_ts2 = rule30_center_out(n_prime, ts2)
    return f_ts2 == 1, f_spike, f_ts2

lines = ["Large-m SubcaseB scan", "=" * 50, ""]

def flush():
    with open(OUTPUT, 'w') as f:
        f.write('\n'.join(lines) + '\n')

flush()

# For each n' in period 1, check large-m positions (from size-200 to size-2, even)
# Also check a few reference n' values
for n_p in range(3087, 3343, 8):  # every 8th n' for speed
    size = 2*(n_p+1)+1
    last = size - 1
    found = []
    # Check large positions: last-200 to last-2, even
    for m_pos in range(max(2, last-200), last, 2):
        if m_pos == 2*n_p:
            continue
        is_b, f_s, f_t = check_subcaseB(n_p, m_pos)
        if is_b:
            found.append(m_pos)
    if found:
        msg = f"  n'={n_p}: large-m SubcaseB positions = {found} (from {last-200}..{last})"
        print(msg, flush=True)
        lines.append(msg)
    else:
        msg = f"  n'={n_p}: no large-m in [{last-200},{last})"
        print(msg, flush=True)
        lines.append(msg)
    flush()

lines.append("")
lines.append("DONE")
flush()
print("Done.")
