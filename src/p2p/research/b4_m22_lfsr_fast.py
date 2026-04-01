#!/usr/bin/env python3
"""
B4 (fast): m=22 LFSR analysis — only affordable operations.
Skip P=65536 and P=131072 shrinking checks (those take hours in Python).
Focus on: small periods, BM structure, base sensitivity at small n'.
"""
import sys

def rule30_step_shrink(tape):
    n = len(tape)
    new = []
    for i in range(1, n - 1):
        new.append((tape[i-1] ^ (tape[i] | tape[i+1])) & 1)
    return new

def rule30_step_periodic(tape):
    n = len(tape)
    new = [0] * n
    for i in range(n):
        l = tape[(i-1) % n]
        c = tape[i]
        r = tape[(i+1) % n]
        new[i] = (l ^ (c | r)) & 1
    return new

def berlekamp_massey(s):
    n = len(s)
    C = [1]; B = [1]; L = 0; x = 1
    for i in range(n):
        d = s[i]
        for j in range(1, L+1):
            if j < len(C): d ^= C[j] * s[i-j]
        d &= 1
        if d == 0:
            x += 1
        elif 2*L <= i:
            T = C[:]
            while len(C) < len(B)+x: C.append(0)
            for j in range(len(B)): C[j+x] ^= B[j]
            L = i+1-L; B = T; x = 1
        else:
            while len(C) < len(B)+x: C.append(0)
            for j in range(len(B)): C[j+x] ^= B[j]
            x += 1
    return L, C

def make_spikeAtList(w, N):
    t = [0]*N
    for i in range(1, min(2*w+1, N)): t[i] = 1
    return t

def make_twoSpikeList(w, m, N):
    t = list(make_spikeAtList(w, N))
    off = 2*w + m
    for i in range(1, 2*w+1):
        p = off+i
        if p < N: t[p] ^= 1
    return t

def check_shrink_period(w, m, P):
    """Returns (spike_ok, twospike_ok) for shrinking cert at period P."""
    # spike
    init_s = make_spikeAtList(w, 2*P + 2*w + 1)
    target_s = make_spikeAtList(w, 2*w + 1)
    tape = init_s[:]
    for _ in range(P): tape = rule30_step_shrink(tape)
    spike_ok = (tape == target_s)
    # twospike
    mwm = max(w, m)
    init_ts = make_twoSpikeList(w, m, 2*P + 2*mwm + 1)
    target_ts = make_twoSpikeList(w, m, 2*mwm + 1)
    tape = init_ts[:]
    for _ in range(P): tape = rule30_step_shrink(tape)
    ts_ok = (tape == target_ts)
    return spike_ok, ts_ok

def check_sensitivity(w, m, n_prime):
    """Check if twoSpike(w, m) witnesses sensitivity at n'."""
    mwm = max(w, m)
    init_s = make_spikeAtList(w, 2*n_prime + 2*w + 1)
    init_ts = make_twoSpikeList(w, m, 2*n_prime + 2*mwm + 1)
    t = init_s[:]
    for _ in range(n_prime): t = rule30_step_shrink(t)
    F = t[w] if len(t) > w else -1
    t = init_ts[:]
    for _ in range(n_prime): t = rule30_step_shrink(t)
    H = t[mwm] if len(t) > mwm else -1
    return F, H, (F != H)

def center_seq_periodic(w, m, N, steps):
    if m > 0:
        # place spikes at positions w and w+2*(w+m) on periodic tape
        tape = [0]*N
        for i in range(-w, w+1): tape[(N//2 + i) % N] = 1
        sep = 2*(w+m)
        for i in range(-w, w+1): tape[(N//2 + sep + i) % N] ^= 1
    else:
        tape = [0]*N
        for i in range(-w, w+1): tape[(N//2 + i) % N] = 1
    center = N // 2
    seq = []
    for _ in range(steps):
        tape = rule30_step_periodic(tape)
        seq.append(tape[center])
    return seq

print("=" * 60)
print("B4 fast: m=22 period/LFSR analysis")
print("=" * 60)

# ── Section 1: Small period divisors of 131072 for (w=34, m=22) ──
print("\n--- Section 1: Small period divisors ≤ 16384 for w=34, m=22 ---")
# 131072 = 2^17; check 2^1 through 2^14
for exp in range(1, 15):
    P = 2**exp
    if P * P > 2e9:  # tape * steps too big; skip
        print(f"  P={P}: SKIPPING (too expensive in Python)")
        continue
    spike_ok, ts_ok = check_shrink_period(34, 22, P)
    print(f"  P={P:6d}: spike(34)={'PASS' if spike_ok else 'FAIL'}  twoSpike(34,22)={'PASS' if ts_ok else 'FAIL'}")
    if spike_ok and ts_ok:
        print(f"  *** FOUND: P={P} is a valid period! ***")

# ── Section 2: Same for w=40 ──
print("\n--- Section 2: Small period divisors ≤ 16384 for w=40, m=22 ---")
for exp in range(1, 15):
    P = 2**exp
    if P * P > 2e9:
        print(f"  P={P}: SKIPPING")
        continue
    spike_ok, ts_ok = check_shrink_period(40, 22, P)
    print(f"  P={P:6d}: spike(40)={'PASS' if spike_ok else 'FAIL'}  twoSpike(40,22)={'PASS' if ts_ok else 'FAIL'}")

# ── Section 3: BM on periodic tape (N=512, 3000 steps) ──
print("\n--- Section 3: BM on center-cell sequence (N=512 periodic tape, 3000 steps) ---")
N_bm = 512; steps_bm = 3000
for (w, m, label) in [(34, 0, "spike(34)"), (34, 22, "twoSpike(34,22)"),
                       (40, 0, "spike(40)"), (40, 22, "twoSpike(40,22)")]:
    seq = center_seq_periodic(w, m, N_bm, steps_bm)
    L, C = berlekamp_massey(seq)
    # Analyze polynomial
    exp_terms = [i for i,c in enumerate(C) if c]
    print(f"  {label:20s}: LFSR_len={L:4d}  poly_degree={len(C)-1}  terms={exp_terms[:8]}{'...' if len(exp_terms)>8 else ''}")

# ── Section 4: BM with larger N to get cleaner structure ──
print("\n--- Section 4: BM with N=2048 periodic tape, 5000 steps ---")
N_bm2 = 2048; steps_bm2 = 5000
for (w, m, label) in [(34, 0, "spike(34)"), (34, 22, "twoSpike(34,22)"),
                       (40, 0, "spike(40)"), (40, 22, "twoSpike(40,22)")]:
    seq = center_seq_periodic(w, m, N_bm2, steps_bm2)
    L, C = berlekamp_massey(seq)
    exp_terms = [i for i,c in enumerate(C) if c]
    print(f"  {label:20s}: LFSR_len={L:4d}  poly_degree={len(C)-1}  terms={exp_terms[:8]}{'...' if len(exp_terms)>8 else ''}")

# ── Section 5: Sensitivity at small n' ≡ 14 mod 256 for m=22 ──
print("\n--- Section 5: Sensitivity at small n' ≡ 14 mod 256, w=34 ---")
for np in [14, 270, 526, 782, 1038, 1294, 1550, 1806, 2062, 2318, 2574, 2830, 3086, 3342]:
    if np < 22:  # m=22 requires n' ≥ m
        continue
    F, H, sens = check_sensitivity(34, 22, np)
    marker = "*** SENS ***" if sens else ""
    print(f"  n'={np:5d}: F={F}, H={H} {'SENSITIVE' if sens else 'not sens'} {marker}")

# ── Section 6: Check n'=270 with w=6 (should NOT be sensitive per loop76) ──
print("\n--- Section 6: n'=270 w=6 sanity check (loop76 refutation) ---")
F, H, sens = check_sensitivity(6, 22, 270)
print(f"  n'=270, w=6: F={F}, H={H}, sensitive={sens} (expected False — loop63 was wrong)")

print("\n=== Done ===")
