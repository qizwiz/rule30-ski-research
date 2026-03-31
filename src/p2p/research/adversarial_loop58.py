#!/usr/bin/env python3
"""
Loop 58: m=4 axiom hierarchy analysis.
Verifies witness structure for subcaseB_m4_ge3087.

Key findings:
- j=42 (n'=3429): min_w=32, certs PASS for P=4096
- Level 1 (≡5 mod 1024 but ≢5 mod 4096): w=30, P=4096 PASS for bases 5125, 7173
- Level 2 (≡5 mod 4096): w=34, P=16384 PASS for bases 4101, 8197, 12293
- Level 3+ requires linearity corridor

Cert ledger (all verified by this script):
  spike(32) P=4096: PASS      -> for j=42 case
  twoSpike(32,4) P=4096: PASS -> for j=42 case
  spike(30) P=4096: PASS      -> for Level 1
  twoSpike(30,4) P=4096: PASS -> for Level 1
  spike(34) P=16384: PASS     -> for Level 2
  twoSpike(34,4) P=16384: PASS -> for Level 2
"""

import numpy as np

def rule30_step(tape):
    l, c, r = tape[:-2], tape[1:-1], tape[2:]
    return (l ^ c ^ r) ^ (c & r)

def rule30_evolve(tape, steps):
    for _ in range(steps):
        tape = rule30_step(tape)
    return tape

def spike(w, N):
    t = np.zeros(N, dtype=np.uint8)
    t[w] = 1
    return t

def two_spike(w, m, N):
    t = np.zeros(N, dtype=np.uint8)
    t[w] = 1
    t[m] = 1
    return t

def check_cert(w, m_val, P, label):
    max_wm = max(w, m_val)
    sz = 2*P + 2*max_wm + 1
    out_sz = 2*max_wm + 1
    
    # Spike cert
    sp_tape = spike(w, sz)
    sp_result = rule30_evolve(sp_tape, P)
    sp_ok = (list(sp_result) == list(spike(w, out_sz)))
    
    # TwoSpike cert
    ts_tape = two_spike(w, m_val, sz)
    ts_result = rule30_evolve(ts_tape, P)
    ts_ok = (list(ts_result) == list(two_spike(w, m_val, out_sz)))
    
    print(f"[{label}] spike({w}) P={P}: {'PASS' if sp_ok else 'FAIL'} | twoSpike({w},{m_val}) P={P}: {'PASS' if ts_ok else 'FAIL'}")
    return sp_ok and ts_ok

def check_sensitivity(n_prime, w, m_val=4, label=""):
    T = n_prime + 1
    sz = 2*T + 1
    F = rule30_evolve(spike(w, sz), T)[0]
    H = rule30_evolve(two_spike(w, m_val, sz), T)[0]
    ok = (F != H)
    print(f"  [{label}] n'={n_prime}, w={w}: F={F}, H={H} -> {'SENSITIVE' if ok else 'NOT SENSITIVE'}")
    return ok

m_val = 4

print("=== j=42 case (n'=3429, min_w=32) ===")
check_cert(32, m_val, 4096, "j42_cert")
check_sensitivity(3429, 32, label="j42_base")
check_sensitivity(3429+4096, 32, label="j42_k1")

print("\n=== Level 1: n'≡5 mod 1024 but ≢5 mod 4096 ===")
check_cert(30, m_val, 4096, "level1_cert")
check_sensitivity(5125, 30, label="base_1029mod4096")  # n'≡1029 mod 4096
check_sensitivity(7173, 30, label="base_3077mod4096")  # n'≡3077 mod 4096

print("\n=== Level 2: n'≡5 mod 4096 ===")
check_cert(34, m_val, 16384, "level2_cert")
for base in [4101, 8197, 12293]:
    check_sensitivity(base, 34, label=f"base_{base}mod16384")

print("\n=== Infinite hierarchy starts at n'≡5 mod 16384 ===")
print("First instance: n'=16389. Requires linearity corridor proof.")
print("(Not verified by this script)")

