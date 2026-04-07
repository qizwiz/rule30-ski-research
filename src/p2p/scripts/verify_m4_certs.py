#!/usr/bin/env python3
"""Verify m=4 SubcaseB period certs for CA_Array.lean Level 0-2.

Checks:
  Level 0 (j=42): w=32, P=4096, base n'=3429
  Level 1 (≡5 mod 1024): w=30, P=4096, bases n'=5125, 7173
  Level 2 (≡5 mod 4096): w=34, P=16384, bases n'=4101, 8197, 12293
"""
import sys

def rule30_step_shrink(row):
    """One step of Rule 30 with shrinking boundary (drops first and last cell)."""
    n = len(row)
    new = []
    for i in range(1, n - 1):
        L = row[i - 1]
        C = row[i]
        R = row[i + 1]
        new.append(L ^ (C or R))
    return new

def ca_evolve_shrink(steps, initial):
    """Evolve with shrinking tape."""
    row = list(initial)
    for _ in range(steps):
        if len(row) < 3:
            return row
        row = rule30_step_shrink(row)
    return row

def spike_list(w, N):
    """spikeAtList w N: list of length N, 1 at position w."""
    tape = [False] * N
    if w < N:
        tape[w] = True
    return tape

def two_spike_list(w, m, N):
    """twoSpikeList w m N: 1 at position w and position 2*(N//2) = N-1."""
    tape = [False] * N
    if w < N:
        tape[w] = True
    last = N - 1  # position 2*(N//2) when N=2k+1 odd
    if last < N:
        tape[last] = True
    return tape

def check_period_cert(w, P, m_val=None):
    """Check: caEvolve P (spikeAtList w (2*P+2*w+1)) == spikeAtList w (2*w+1)
    and optionally twoSpike(w, m_val).
    """
    N_in = 2 * P + 2 * w + 1
    N_out = 2 * w + 1
    expected = spike_list(w, N_out)

    sp_in = spike_list(w, N_in)
    sp_out = ca_evolve_shrink(P, sp_in)
    spike_ok = (sp_out == expected)

    ts_ok = None
    if m_val is not None:
        # twoSpikeList w m_val (2*P + 2*max(w,m_val) + 1) should equal twoSpikeList w m_val (2*max(w,m_val)+1)
        mx = max(w, m_val)
        N_ts_in = 2 * P + 2 * mx + 1
        N_ts_out = 2 * mx + 1
        ts_in = two_spike_list(w, m_val, N_ts_in)
        ts_out = ca_evolve_shrink(P, ts_in)
        ts_expected = two_spike_list(w, m_val, N_ts_out)
        ts_ok = (ts_out == ts_expected)

    return spike_ok, ts_ok

def check_base_sensitivity(w, n_prime, m_val=4):
    """Check: caEvolve(n'+1)(spike_w) center != caEvolve(n'+1)(twoSpike(w,m)) center."""
    n_steps = n_prime + 1
    N = 2 * n_steps + 1

    sp = spike_list(w, N)
    sp_out = ca_evolve_shrink(n_steps, sp)
    f = sp_out[0] if sp_out else False

    ts = two_spike_list(w, m_val, N)
    ts_out = ca_evolve_shrink(n_steps, ts)
    h = ts_out[0] if ts_out else False

    return f != h, f, h

print("=== m=4 SubcaseB Cert Verification ===\n")

# LEVEL 0: j=42, n'=3429, w=32, P=4096
print("--- Level 0: j=42, n'=3429, w=32, P=4096 ---")
print("  Checking spike(32) period=4096 ...", end=' ', flush=True)
sp_ok, ts_ok = check_period_cert(32, 4096, m_val=4)
print("PASS" if sp_ok else "FAIL")
print("  Checking twoSpike(32,4) period=4096 ...", end=' ', flush=True)
print("PASS" if ts_ok else "FAIL")
print("  Checking base sensitivity n'=3429, w=32 ...", end=' ', flush=True)
sens_ok, f, h = check_base_sensitivity(32, 3429, m_val=4)
print(f"PASS (F={f}, H={h})" if sens_ok else f"FAIL (F={f}, H={h})")
print()

# LEVEL 1: w=30, P=4096, bases n'=5125 and n'=7173
print("--- Level 1: w=30, P=4096 ---")
print("  Checking spike(30) period=4096 ...", end=' ', flush=True)
sp_ok, ts_ok = check_period_cert(30, 4096, m_val=4)
print("PASS" if sp_ok else "FAIL")
print("  Checking twoSpike(30,4) period=4096 ...", end=' ', flush=True)
print("PASS" if ts_ok else "FAIL")
print("  Checking base sensitivity n'=5125, w=30 ...", end=' ', flush=True)
sens_ok, f, h = check_base_sensitivity(30, 5125, m_val=4)
print(f"PASS (F={f}, H={h})" if sens_ok else f"FAIL (F={f}, H={h})")
print("  Checking base sensitivity n'=7173, w=30 ...", end=' ', flush=True)
sens_ok, f, h = check_base_sensitivity(30, 7173, m_val=4)
print(f"PASS (F={f}, H={h})" if sens_ok else f"FAIL (F={f}, H={h})")
print()

# LEVEL 2: w=34, P=16384, bases n'=4101, 8197, 12293
print("--- Level 2: w=34, P=16384 ---")
print("  Checking spike(34) period=16384 ...", end=' ', flush=True)
sp_ok, ts_ok = check_period_cert(34, 16384, m_val=4)
print("PASS" if sp_ok else "FAIL")
print("  Checking twoSpike(34,4) period=16384 ...", end=' ', flush=True)
print("PASS" if ts_ok else "FAIL")
print("  Checking base sensitivity n'=4101, w=34 ...", end=' ', flush=True)
sens_ok, f, h = check_base_sensitivity(34, 4101, m_val=4)
print(f"PASS (F={f}, H={h})" if sens_ok else f"FAIL (F={f}, H={h})")
print("  Checking base sensitivity n'=8197, w=34 ...", end=' ', flush=True)
sens_ok, f, h = check_base_sensitivity(34, 8197, m_val=4)
print(f"PASS (F={f}, H={h})" if sens_ok else f"FAIL (F={f}, H={h})")
print("  Checking base sensitivity n'=12293, w=34 ...", end=' ', flush=True)
sens_ok, f, h = check_base_sensitivity(34, 12293, m_val=4)
print(f"PASS (F={f}, H={h})" if sens_ok else f"FAIL (F={f}, H={h})")
print()

print("=== Done ===")
