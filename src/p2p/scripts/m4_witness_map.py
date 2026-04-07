#!/usr/bin/env python3
"""Map m=4 SubcaseB witness structure for n' in [3087, 10000].

For each firing n' (≡5 mod 8), find the minimum even w such that:
  center(spike_w, n'+1) != center(twoSpike(w,4), n'+1)

This maps the witness hierarchy for designing the Lean proof.
"""
import sys

def rule30_step(row):
    """One step of Rule 30 (boundary = 0)."""
    n = len(row)
    new = [False] * n
    for i in range(n):
        L = row[i-1] if i > 0 else False
        C = row[i]
        R = row[i+1] if i < n-1 else False
        new[i] = L ^ (C or R)
    return new

def ca_evolve(steps, initial):
    """Evolve initial config for 'steps' steps."""
    row = list(initial)
    for _ in range(steps):
        row = rule30_step(row)
    return row

def center(row):
    """Get center cell (index 0) after evolution."""
    return row[0] if row else False

def spike_config(w, n):
    """spikeAtList w (2*(n+1)+1): tape of length 2n+3, single 1 at position w."""
    L = 2*(n+1)+1
    tape = [False] * L
    if w < L:
        tape[w] = True
    return tape

def two_spike_config(w, m_val, n):
    """twoSpikeList w m_val (2*(n+1)+1): 1s at positions w and 2*(n+1)."""
    L = 2*(n+1)+1
    tape = [False] * L
    if w < L:
        tape[w] = True
    last = 2*(n+1)
    if last < L:
        tape[last] = True
    return tape

def subcase_b_fires(n_prime, m_val=4):
    """Check if SubcaseB fires: spike_m gives center=0, twoSpikeLast gives center=1."""
    n1 = n_prime + 1
    # spike at position m_val
    sp = spike_config(m_val, n_prime)
    f = center(ca_evolve(n1, sp))
    if f:  # SubcaseB needs F=0
        return False
    # twoSpike(m_val, last=2*n1)
    ts = two_spike_config(m_val, 2*n1, n_prime)
    g = center(ca_evolve(n1, ts))
    return g  # SubcaseB needs G=1

def find_min_witness(n_prime, m_val=4, max_w=64):
    """Find minimum even w such that sensitivity holds."""
    for w in range(2, max_w, 2):
        sp = spike_config(w, n_prime)
        f_sp = center(ca_evolve(n_prime+1, sp))
        ts = two_spike_config(w, m_val, n_prime)
        f_ts = center(ca_evolve(n_prime+1, ts))
        if f_sp != f_ts:
            return w
    return None  # not found in range

def v2(k):
    """2-adic valuation of k (largest power of 2 dividing k)."""
    if k == 0:
        return float('inf')
    v = 0
    while k % 2 == 0:
        k //= 2
        v += 1
    return v

# Scan n' in [3087, 10000] for m=4 firings
print(f"{'n_prime':>8} {'j':>6} {'mod8':>4} {'mod64':>6} {'mod512':>7} {'mod1024':>8} {'v2(n-5)':>8} {'min_w':>6} {'fires':>6}")
print("-"*75)

firings = []
for n_prime in range(3087, 8000):
    if n_prime % 8 != 5:  # m=4 fires at n'≡5 mod 8
        continue
    fires = subcase_b_fires(n_prime, m_val=4)
    if not fires:
        continue
    j = (n_prime - 3093) // 8
    w = find_min_witness(n_prime, m_val=4, max_w=80)
    v = v2(n_prime - 5)
    firings.append((n_prime, j, w, v))
    print(f"{n_prime:>8} {j:>6} {n_prime%8:>4} {n_prime%64:>6} {n_prime%512:>7} {n_prime%1024:>8} {v:>8} {str(w):>6}  {'YES':>6}")

# Summarize by (mod512, min_w) groupings
print("\n--- Summary: residue classes and their witness ---")
from collections import defaultdict
by_mod512 = defaultdict(list)
for n_prime, j, w, v in firings:
    by_mod512[(n_prime % 512, w)].append(n_prime)

for (r, w), ns in sorted(by_mod512.items()):
    count = len(ns)
    print(f"  n'≡{r:3d} mod 512, w={w:2d}: {count} instances, e.g. {ns[:3]}")

# Show cases where w > 22 (the hard cases)
hard = [(n, j, w, v) for n, j, w, v in firings if w is not None and w > 22]
print(f"\n--- Hard cases (w>22): {len(hard)} total ---")
for n_prime, j, w, v in hard[:30]:
    print(f"  n'={n_prime}, j={j}, mod512={n_prime%512}, mod1024={n_prime%1024}, v2(n-5)={v}, w={w}")
