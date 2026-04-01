#!/usr/bin/env python3
"""
Find witness for SubcaseB m=22, n'=35598+65536*s (the open sorry at SubcaseBPeriod.lean:2280).

Strategy:
1. Find min even w such that F_w(35598) != H_{w,22}(35598)
2. Find period cert for that w
"""

import numpy as np
import sys

def ca_step(t):
    """One Rule 30 step on shrinking tape."""
    return t[:-2] ^ (t[1:-1] | t[2:])

def ca_evolve(tape, steps):
    """Evolve tape for steps steps (shrinking)."""
    t = np.asarray(tape, dtype=np.uint8)
    for _ in range(steps):
        if len(t) < 3:
            return t
        t = ca_step(t)
    return t

def center_val(n_prime, positions):
    """Center of config after n'+1 steps. positions = list of 1-cells in tape of size 2*(n'+1)+1."""
    N = 2 * (n_prime + 1) + 1
    tape = np.zeros(N, dtype=np.uint8)
    for p in positions:
        if 0 <= p < N:
            tape[p] = 1
    result = ca_evolve(tape, n_prime + 1)
    return int(result[0]) if len(result) > 0 else None

def is_witness(w, m, n_prime):
    """True if w witnesses SubcaseB(m) at n': F_w(n') != H_{w,m}(n')."""
    f = center_val(n_prime, [w])
    h = center_val(n_prime, [w, m])
    return f is not None and h is not None and f != h

def check_spike_period(w, P):
    """Check spike(w) period cert: caEvolve(P, spike(w, 2*P+2*w+1)) = spike(w, 2*w+1)."""
    N_start = 2*P + 2*w + 1
    tape = np.zeros(N_start, dtype=np.uint8)
    tape[w] = 1
    evolved = ca_evolve(tape, P)
    N_end = 2*w + 1
    expected = np.zeros(N_end, dtype=np.uint8)
    expected[w] = 1
    if len(evolved) != len(expected):
        return False, f"len mismatch: {len(evolved)} vs {len(expected)}"
    return bool(np.array_equal(evolved, expected)), ""

def check_twospike_period(w, m, P):
    """Check twoSpike(w,m) period cert: caEvolve(P, ts(2*P+2*max(w,m)+1)) = ts(2*max(w,m)+1)."""
    wm = max(w, m)
    N_start = 2*P + 2*wm + 1
    tape = np.zeros(N_start, dtype=np.uint8)
    tape[w] = 1
    tape[m] = 1
    evolved = ca_evolve(tape, P)
    N_end = 2*wm + 1
    expected = np.zeros(N_end, dtype=np.uint8)
    expected[w] = 1
    expected[m] = 1
    if len(evolved) != len(expected):
        return False, f"len mismatch: {len(evolved)} vs {len(expected)}"
    return bool(np.array_equal(evolved, expected)), ""

M = 22
N_PRIME = 35598

print(f"Searching for min even witness for SubcaseB m={M}, n'={N_PRIME}", flush=True)
print(f"Tape size: {2*(N_PRIME+1)+1}, steps: {N_PRIME+1}", flush=True)
print()

# First check: is n'=35598 actually a SubcaseB firing?
# SubcaseB: F_m(n')=0 and H_last(n')=1
# Here "last" = m itself for twoSpike at (w,m)
# But the actual check is: does SubcaseB fire at n'=35598 with m=22?
# We check: does ANY w witness at n'=35598?

print("Checking witnesses w=2,4,...,60 (even, ≠22):", flush=True)
found_witnesses = []
for w in range(2, 62, 2):
    if w == M:
        continue
    result = is_witness(w, M, N_PRIME)
    status = "✓" if result else "✗"
    print(f"  w={w:3d}: {status}", end="  ", flush=True)
    if result:
        found_witnesses.append(w)
    if w % 20 == 0:
        print()
print()
print()

if not found_witnesses:
    print("NO witnesses found! n'=35598 may not be a SubcaseB firing for m=22.")
    print("OR all witnesses are w>60.")
    sys.exit(1)

print(f"Witnesses found: {found_witnesses}")
min_w = found_witnesses[0]
print(f"Minimum even witness: w={min_w}")
print()

# Check period certs for min_w
print(f"Checking period certs for w={min_w}, m={M}:", flush=True)
for P in [256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]:
    ok_s, _ = check_spike_period(min_w, P)
    ok_t, _ = check_twospike_period(min_w, M, P)
    print(f"  P={P:6d}: spike={ok_s}, twoSpike={ok_t}", flush=True)
    if ok_s and ok_t:
        print(f"  -> CERT FOUND: w={min_w}, P={P}!")
        break

print()
# Also check a few other witnesses
print("Checking period certs for other witnesses:", flush=True)
for w in found_witnesses[:5]:
    if w == min_w:
        continue
    for P in [256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]:
        ok_s, _ = check_spike_period(w, P)
        ok_t, _ = check_twospike_period(w, M, P)
        if ok_s and ok_t:
            print(f"  w={w}: CERT w={w}, P={P}")
            break
    else:
        print(f"  w={w}: no cert found up to P=65536")

print()
print("Also checking specific witnesses from nearby cases (w=30 from j≡0, w=32 from l≡1):", flush=True)
for w_check in [30, 32]:
    is_wit = is_witness(w_check, M, N_PRIME)
    print(f"  w={w_check}: witnesses={'YES' if is_wit else 'NO'}", flush=True)
    if is_wit:
        for P in [32768, 65536, 131072]:
            ok_s, _ = check_spike_period(w_check, P)
            ok_t, _ = check_twospike_period(w_check, M, P)
            print(f"    P={P}: spike={ok_s}, twoSpike={ok_t}", flush=True)
            if ok_s and ok_t:
                print(f"    -> CERT w={w_check}, P={P}!")
                break
print()
print("Done.")
