#!/usr/bin/env python3
"""
Targeted investigation of m (tape-position) SubcaseB structure.

CORRECT indexing (from Lean file at line 1655):
  - Tape size = 2*(n'+1)+1
  - Center = n'+1
  - Spike at POSITION m.val (NOT center+m.val!)
  - Two-spike at positions m.val and 2*(n'+1) (= last = size-1)
  - Output read at center after n'+1 steps

Valid m.val: even, in [2, 2*n'-2] (from hm_even, hm_low, hm_ne_r, hm_high constraints)

Results written incrementally to file — survives context compaction.
"""
import numpy as np

OUTPUT = "/Users/jonathanhill/src/p2p/research/targeted_m36_results.txt"

def rule30_center_out(n_prime, initial_tape_np):
    """Apply rule30 n_prime+1 steps, return center bit."""
    t = initial_tape_np.copy().astype(np.int8)
    L = len(t)
    steps = n_prime + 1
    for _ in range(steps):
        l = np.roll(t, 1)
        r = np.roll(t, -1)
        t = l ^ (t | r)
    return int(t[n_prime + 1])  # center

def check_subcaseB(n_prime, m_pos):
    """
    Check SubcaseB: spike at tape position m_pos (NOT center+m_pos).
    Returns (is_subcaseB, f_spike, f_ts2)
    """
    size = 2*(n_prime+1)+1
    center = n_prime+1
    last = size - 1  # = 2*(n'+1)

    # Validity constraints from Lean
    if m_pos < 2 or m_pos >= last or m_pos % 2 != 0 or m_pos == 2*n_prime:
        return False, None, None

    # Spike tape: 1 at m_pos
    sp = np.zeros(size, dtype=np.int8)
    sp[m_pos] = 1
    f_spike = rule30_center_out(n_prime, sp)

    if f_spike != 0:
        return False, f_spike, None  # spike→true means NOT SubcaseB

    # Two-spike tape: 1 at m_pos and last
    ts2 = np.zeros(size, dtype=np.int8)
    ts2[m_pos] = 1
    ts2[last] = 1
    f_ts2 = rule30_center_out(n_prime, ts2)

    return f_ts2 == 1, f_spike, f_ts2


lines = [
    "SubcaseB Investigation — CORRECT indexing (spike at position m, not center+m)",
    "=" * 70,
    "",
]

def flush():
    with open(OUTPUT, 'w') as f:
        f.write('\n'.join(lines) + '\n')

flush()

# ---- Q1: Verify known hard m values at n'=3085 ----
print("Q1: Verify known hard m-positions at n'=3085 (m=4,12,20,6164)...", flush=True)
lines.append("Q1: Known hard m at n'=3085 (from Lean native_decide)")
lines.append("-" * 50)
for m_pos in [4, 12, 20, 6164]:
    is_b, f_s, f_t = check_subcaseB(3085, m_pos)
    msg = f"  n'=3085, m={m_pos}: SubcaseB={is_b} (spike={f_s}, ts2={f_t})"
    print(msg, flush=True)
    lines.append(msg)
lines.append("")
flush()

# ---- Q2: Find SubcaseB m-positions at n'=3087 ----
print("Q2: Scan m-positions for n'=3087, 3093, 3101...", flush=True)
lines.append("Q2: SubcaseB m-positions for key n' values")
lines.append("-" * 50)

for n_p in [3087, 3093, 3101, 3109]:
    size = 2*(n_p+1)+1
    pairs_found = []
    for m_pos in range(2, min(size-2, 200), 2):  # first 100 even positions
        if m_pos == 2*n_p:
            continue
        is_b, f_s, f_t = check_subcaseB(n_p, m_pos)
        if is_b:
            pairs_found.append(m_pos)
    msg = f"  n'={n_p}: SubcaseB m-positions = {pairs_found}"
    print(msg, flush=True)
    lines.append(msg)
lines.append("")
flush()

# ---- Q3: Check m=36 specifically at n'=4113, 4117, 8209 ----
print("Q3: Check m=36 at n'=4113, 4117, 8209 (pre-compaction claimed these)...", flush=True)
lines.append("Q3: m=36 at pre-compaction claimed hits")
lines.append("-" * 50)
for n_p in [4113, 4117, 8209]:
    is_b, f_s, f_t = check_subcaseB(n_p, 36)
    msg = f"  n'={n_p}, m=36: SubcaseB={is_b} (spike={f_s}, ts2={f_t})"
    print(msg, flush=True)
    lines.append(msg)
lines.append("")
flush()

# ---- Q4: Scan [4000, 4300) for any new m-positions ----
print("Q4: Scan m-positions for n' in [4000, 4100)...", flush=True)
lines.append("Q4: SubcaseB pairs in n' in [4000, 4100), m in [2, 100)")
lines.append("-" * 50)

new_m_found = set()
for n_p in range(4000, 4100):
    size = 2*(n_p+1)+1
    for m_pos in range(2, min(size-2, 100), 2):
        if m_pos == 2*n_p:
            continue
        is_b, f_s, f_t = check_subcaseB(n_p, m_pos)
        if is_b:
            new_m_found.add(m_pos)
            msg = f"  n'={n_p}, m={m_pos}: SubcaseB"
            print(msg, flush=True)
            lines.append(msg)
lines.append(f"  All m-positions found in [4000,4100): {sorted(new_m_found)}")
lines.append("")
flush()

print(f"\nDone. Results at {OUTPUT}", flush=True)
lines.append("DONE")
flush()
