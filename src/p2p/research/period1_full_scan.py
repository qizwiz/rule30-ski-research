#!/usr/bin/env python3
"""
Full scan of period 1: [3087, 3343), m in [2, 100).
Finds ALL SubcaseB (n', m) pairs.
Writes incrementally to file.
Answers: what is the complete m-set for period 1?
"""
import numpy as np

OUTPUT = "/Users/jonathanhill/src/p2p/research/period1_full_scan.txt"

def rule30_center_out(n_prime, tape_np):
    t = tape_np.copy().astype(np.int8)
    L = len(t)
    for _ in range(n_prime + 1):
        l = np.roll(t, 1)
        r = np.roll(t, -1)
        t = l ^ (t | r)
    return int(t[n_prime + 1])

def check_subcaseB(n_prime, m_pos):
    size = 2*(n_prime+1)+1
    last = size - 1
    if m_pos < 2 or m_pos >= last or m_pos % 2 != 0 or m_pos == 2*n_prime:
        return False
    sp = np.zeros(size, dtype=np.int8); sp[m_pos] = 1
    if rule30_center_out(n_prime, sp) != 0:
        return False
    ts2 = np.zeros(size, dtype=np.int8); ts2[m_pos] = 1; ts2[last] = 1
    return rule30_center_out(n_prime, ts2) == 1

lines = [
    "Period 1 Full Scan: [3087, 3343), m in [2, 100)",
    "=" * 60,
    "",
]

def flush():
    with open(OUTPUT, 'w') as f:
        f.write('\n'.join(lines) + '\n')

flush()

all_pairs = []
m_set = set()

for n_p in range(3087, 3343):
    found_m = []
    for m_pos in range(2, 100, 2):
        if m_pos == 2*n_p:
            continue
        if check_subcaseB(n_p, m_pos):
            found_m.append(m_pos)
            all_pairs.append((n_p, m_pos))
            m_set.add(m_pos)
    if found_m:
        msg = f"  n'={n_p}: {found_m}"
        print(msg, flush=True)
        lines.append(msg)

    if n_p % 16 == 0:
        flush()

lines.append("")
lines.append(f"Total pairs in [3087, 3343), m<100: {len(all_pairs)}")
lines.append(f"m-positions seen: {sorted(m_set)}")
lines.append(f"Max m seen: {max(m_set) if m_set else 'none'}")
lines.append("")

# Count by m
lines.append("Count per m-position:")
for m in sorted(m_set):
    cnt = sum(1 for _, mp in all_pairs if mp == m)
    lines.append(f"  m={m}: {cnt} n' values")

flush()
print(f"\nDone. Results at {OUTPUT}", flush=True)
