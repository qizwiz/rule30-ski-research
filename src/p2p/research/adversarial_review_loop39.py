#!/usr/bin/env python3
"""
Adversarial Review Loop 39 — F-certificate minimality for m=34,36 (and m=38 if time permits)
Run date: 2026-03-24

TARGET CLAIM (paper, Part B, lines ~444-446):
  "period minimality confirmed for all m ≤ 38: m ≤ 28 by full F-sequence comparison (loop-20);
   m ∈ {30,34,36,38} by triangle method showing P/2 fails at n'=3087 (loop-25, 2026-03-24)"

THE GAP:
  Loop 25 verified minimality using the TRIANGLE METHOD: it showed F(3087,m) ≠ F(3087+P/2,m),
  i.e., a single-point mismatch. This proves period does NOT divide P/2 — which IS sufficient
  for period minimality. However, the paper's companion claim (lines ~583-589) uses F-CERTIFICATES:
      caEvolve P_m (spikeAtList m (2*P_m + 2*m + 1)) = spikeAtList m (2*m + 1)
  These certificates are the Lean-style proof objects. For m≤30 (P≤4096) these are verified
  and Lean-proved. For m=34,36,38 the paper says the certificates HOLD (Python-verified) but
  MINIMALITY via the cert method has NOT been separately verified.

  The question: does caEvolve(P/2)(spike_m(2*(P/2)+2*m+1)) give spike_m(2*m+1)?
  If YES → P/2 is ALSO a valid F-cert → period divides P/2 → claimed period WRONG.
  If NO  → P/2 cert fails → P is the true minimal period (via cert method).

  This is a STRONGER test than the triangle-method P/2 failure, because:
  - Triangle method: one-point mismatch F(3087,m) ≠ F(3087+P/2,m) — proves period > P/2
  - F-cert failure: the entire state after P/2 steps ≠ initial spike — proves period does not
    divide P/2 starting from the certified initial state

  Both methods should agree; the F-cert method is what the Lean proof requires.

ATTACKS:
1. For m=34 (P=8192): verify F-cert(P=8192) holds AND F-cert(P=4096) FAILS
2. For m=36 (P=16384): verify F-cert(P=16384) holds AND F-cert(P=8192) FAILS
3. For m=38 (P=32768): verify F-cert(P=32768) holds AND F-cert(P=16384) FAILS
   [m=38 takes ~315s; run only if m=34,36 complete quickly]

Also cross-check: resonance test for m=40 at n'=16403 (paper says (0,0), "decisive").
"""
import numpy as np
import time
import sys


def make_spike(m, L):
    """Array of length L with 1 at position m, 0 elsewhere."""
    a = np.zeros(L, dtype=np.uint8)
    a[m] = 1
    return a


def caEvolve(n_steps, a):
    """Apply Rule 30 (open boundary) for n_steps steps: a[i] = a[i-1] XOR (a[i] OR a[i+1]).
    Each step shrinks the array by 2.
    """
    a = a.copy()
    for _ in range(n_steps):
        if len(a) < 3:
            break
        a = a[:-2] ^ (a[1:-1] | a[2:])
    return a


def check_f_cert(m, P, verbose=True):
    """Check: caEvolve(P)(spike_m(2P+2m+1)) == spike_m(2m+1).
    Returns True if certificate holds.

    Meaning: F(n', m) has period P for all n' ≥ m (period divides P).
    """
    L = 2 * P + 2 * m + 1
    start = make_spike(m, L)
    t0 = time.time()
    end = caEvolve(P, start)
    elapsed = time.time() - t0

    # After P steps, array has size L - 2P = 2m+1
    assert len(end) == 2 * m + 1, f"Size mismatch: got {len(end)}, expected {2*m+1}"

    expected = make_spike(m, 2 * m + 1)
    holds = np.array_equal(end, expected)

    if verbose:
        print(f"    m={m}, P={P}: L={L} cells, {P} steps → {elapsed:.1f}s → cert holds: {holds}")
        if not holds:
            # Find where it fails
            diff_positions = np.where(end != expected)[0]
            print(f"      First mismatch at position {diff_positions[0]}: got {end[diff_positions[0]]}, expected {expected[diff_positions[0]]}")
            print(f"      end[:10]={list(end[:10])}, expected[:10]={list(expected[:10])}")

    return holds, elapsed


def check_f_cert_minimality(m, P, verbose=True):
    """Check both F-cert(P) and F-cert(P/2).
    Returns (P_cert_holds, P_half_cert_holds).
    If P_cert_holds=True and P_half_cert_holds=False → P is the minimal period.
    """
    if verbose:
        print(f"\n  --- F-cert minimality check for m={m}, P={P} ---")
        print(f"  Step 1: Verify F-cert(P={P}) holds...")
    P_holds, t1 = check_f_cert(m, P, verbose=verbose)

    if P % 2 != 0:
        return P_holds, None

    if verbose:
        print(f"  Step 2: Verify F-cert(P/2={P//2}) FAILS (minimality)...")
    P_half_holds, t2 = check_f_cert(m, P // 2, verbose=verbose)

    if verbose:
        if P_holds and not P_half_holds:
            print(f"  --> MINIMAL PERIOD CONFIRMED: P={P} is minimal (cert holds, P/2 cert fails)")
        elif P_holds and P_half_holds:
            print(f"  --> WARNING: BOTH P and P/2 certs hold! Period could be {P//2} or smaller!")
        elif not P_holds:
            print(f"  --> WARNING: P-cert FAILS! Claimed period {P} is WRONG!")

    return P_holds, P_half_holds


# ============================================================
# ATTACK 1: m=34, P=8192
# Array size: 2*8192 + 2*34 + 1 = 16453 cells
# Steps: 8192
# Cost: O(P^2) ≈ 8192^2 ≈ 67M array-cell operations
# Expected time: ~30-60s in numpy
# ============================================================
print("=" * 70)
print("LOOP 39: F-certificate minimality for m=34,36,38")
print("=" * 70)
print()
print("TARGET: paper claims period minimality for m=34 (P=8192), m=36 (P=16384),")
print("  m=38 (P=32768) verified by 'triangle method showing P/2 fails at n'=3087'.")
print("  This loop upgrades to F-CERTIFICATE method (what Lean proof actually needs).")
print()

print("=" * 60)
print("ATTACK 1: m=34, P=8192")
print("=" * 60)
t_start = time.time()
m34_P_holds, m34_Phalf_holds = check_f_cert_minimality(34, 8192, verbose=True)
t_total = time.time() - t_start

print(f"\n  SUMMARY m=34:")
print(f"    F-cert(P=8192) holds: {m34_P_holds}")
print(f"    F-cert(P/2=4096) holds: {m34_Phalf_holds}")
if m34_P_holds and not m34_Phalf_holds:
    print(f"    ✓ MINIMALITY CONFIRMED: P=8192 is the minimal period for m=34")
elif m34_P_holds and m34_Phalf_holds:
    print(f"    *** PERIOD ERROR: P/2 also works — claimed period 8192 may be wrong! ***")
elif not m34_P_holds:
    print(f"    *** PERIOD ERROR: claimed period 8192 does NOT satisfy F-cert! ***")
print(f"  Total wall time: {t_total:.1f}s")
print()
sys.stdout.flush()

# ============================================================
# ATTACK 2: m=36, P=16384
# Array size: 2*16384 + 2*36 + 1 = 32845 cells
# Steps: 16384
# Cost: O(P^2) ≈ 16384^2 ≈ 268M operations
# Expected time: ~60-120s in numpy
# ============================================================
print("=" * 60)
print("ATTACK 2: m=36, P=16384")
print("=" * 60)
t_start = time.time()
m36_P_holds, m36_Phalf_holds = check_f_cert_minimality(36, 16384, verbose=True)
t_total = time.time() - t_start

print(f"\n  SUMMARY m=36:")
print(f"    F-cert(P=16384) holds: {m36_P_holds}")
print(f"    F-cert(P/2=8192) holds: {m36_Phalf_holds}")
if m36_P_holds and not m36_Phalf_holds:
    print(f"    ✓ MINIMALITY CONFIRMED: P=16384 is the minimal period for m=36")
elif m36_P_holds and m36_Phalf_holds:
    print(f"    *** PERIOD ERROR: P/2 also works — claimed period 16384 may be wrong! ***")
elif not m36_P_holds:
    print(f"    *** PERIOD ERROR: claimed period 16384 does NOT satisfy F-cert! ***")
print(f"  Total wall time: {t_total:.1f}s")
print()
sys.stdout.flush()

# ============================================================
# ATTACK 3: m=38, P=32768
# Array size: 2*32768 + 2*38 + 1 = 65613 cells
# Steps: 32768
# Cost: O(P^2) ≈ 32768^2 ≈ 1.07B operations
# Expected time: ~315s per the paper; may be ~120-200s in numpy (vectorized)
# ONLY RUN IF previous attacks completed quickly
# ============================================================
m38_P_holds = None
m38_Phalf_holds = None

T_budget = 400  # seconds budget for m=38 (each cert)
print("=" * 60)
print(f"ATTACK 3: m=38, P=32768  (budget: {T_budget}s per cert)")
print("=" * 60)
print("  NOTE: m=38 costs ~1.07B operations per cert. Paper says 315s in Python.")
print("  Running with numpy vectorization — should be faster.")
print()

t_start = time.time()

print(f"  Step 1: F-cert(P=32768)...")
sys.stdout.flush()
m38_P_holds, t38_P = check_f_cert(38, 32768, verbose=True)
t_step1 = time.time() - t_start

if t_step1 < T_budget:
    print(f"  Step 2: F-cert(P/2=16384)...")
    sys.stdout.flush()
    m38_Phalf_holds, t38_Phalf = check_f_cert(38, 16384, verbose=True)

    print(f"\n  SUMMARY m=38:")
    print(f"    F-cert(P=32768) holds: {m38_P_holds}")
    print(f"    F-cert(P/2=16384) holds: {m38_Phalf_holds}")
    if m38_P_holds and not m38_Phalf_holds:
        print(f"    ✓ MINIMALITY CONFIRMED: P=32768 is the minimal period for m=38")
    elif m38_P_holds and m38_Phalf_holds:
        print(f"    *** PERIOD ERROR: P/2 also works — claimed period 32768 may be wrong! ***")
    elif not m38_P_holds:
        print(f"    *** PERIOD ERROR: claimed period 32768 does NOT satisfy F-cert! ***")
else:
    print(f"  Step 1 took {t_step1:.1f}s; skipping P/2 check for m=38 (budget constraint).")
    print(f"  m=38 P-cert result: {m38_P_holds}")

print(f"  Total wall time: {time.time() - t_start:.1f}s")
print()
sys.stdout.flush()

# ============================================================
# CROSS-CHECK: m=40 resonance test at n'=16403
# Paper claims: "resonance test at n'=16403 gives (0,0) — decisive"
# i.e., F(16403,40)=0 AND G(16403,40)=0 (NOT SubcaseB)
# Under the doubling law, if m=40 were active its first (0,1) would be at n'=16403
# (last - m = 2*16403 + 2 - 40 = 32808 - 40 = 32768 = 2^15)
# ============================================================
print("=" * 60)
print("CROSS-CHECK: m=40 resonance test at n'=16403")
print("=" * 60)
print("  Paper: 'resonance test at n'=16403 gives (0,0) — decisive'")
print("  Under doubling law: if m=40 active, first hit should be at last-m=2^15=32768,")
print("  i.e., n'=(32768+40-2)/2=16403. (0,0) would disprove this.")
print()

n_test = 16403
m_test = 40

# The CORRECT SubcaseB definition (matching loop16_compute.py and the Lean formalization):
# F(n', m) = center cell after n'+1 steps from spike at m in tape of SIZE 2*(n'+1)+1 = 2n'+3
# G(n', m) = center cell after n'+1 steps from two-spike tape (spike at m AND spike at last=2*(n'+1))
#            in same tape of size 2n'+3
# Center position = n'+1 (the middle of a tape of size 2n'+3)
# NOTE: Using 2n'+3 with n'+1 steps, the tape shrinks to size 1 at the end.
# An equivalent formulation: size 2n'+3, n'+1 steps, check leftmost cell of the result.
# This is the form used in loop16_compute.py and confirmed correct against known SubcaseB events.

# Compute F(n'=16403, m=40)
L_F = 2 * (n_test + 1) + 1  # = 2n'+3 = 32809
a_F = make_spike(m_test, L_F)
t0 = time.time()
result_F = caEvolve(n_test + 1, a_F)  # n'+1 steps
F_val = int(result_F[0]) if len(result_F) > 0 else 0
t_F = time.time() - t0
print(f"  F({n_test}, {m_test}) = {F_val}  ({t_F:.1f}s)  [tape size {L_F}, {n_test+1} steps]")

# Compute G(n'=16403, m=40)
# spike at m AND spike at last = L_F-1 = 2*(n'+1)
L_G = L_F  # same tape size
a_G = np.zeros(L_G, dtype=np.uint8)
a_G[m_test] = 1
a_G[L_G - 1] = 1
t0 = time.time()
result_G = caEvolve(n_test + 1, a_G)  # n'+1 steps
G_val = int(result_G[0]) if len(result_G) > 0 else 0
t_G = time.time() - t0
print(f"  G({n_test}, {m_test}) = {G_val}  ({t_G:.1f}s)")

subcaseB_m40 = (F_val == 0 and G_val == 1)
print(f"  SubcaseB({n_test}, {m_test}) = {subcaseB_m40}")
print(f"  Paper's expected result: (F,G) = (0,0) — 'decisive' evidence of inactivity")

if F_val == 0 and G_val == 0:
    print(f"  ✓ CONFIRMED: (0,0) at resonance point. Not SubcaseB. Consistent with inactivity.")
    print(f"  Paper's claim matches: '{{8211,16403,32787}} give (1,1),(0,0),(1,1)'  [line ~470]")
elif F_val == 0 and G_val == 1:
    print(f"  *** SURPRISE: m=40 IS active! SubcaseB at n'=16403! Paper claim WRONG! ***")
elif F_val == 1 and G_val == 0:
    print(f"  (1,0): Not SubcaseB but also not matching paper's '(0,0)' claim.")
    print(f"  *** DISCREPANCY with paper line ~470 which says (0,0) ***")
elif F_val == 1 and G_val == 1:
    print(f"  (1,1): Not SubcaseB, consistent with paper claim '(1,1)' for n'=8211,32787.")
    print(f"  *** DISCREPANCY: paper says n'=16403 gives (0,0), not (1,1) ***")
print()
sys.stdout.flush()

# ============================================================
# FINAL SUMMARY
# ============================================================
print("=" * 70)
print("LOOP 39 FINAL SUMMARY")
print("=" * 70)
print()
print("F-CERTIFICATE MINIMALITY RESULTS:")
print(f"  m=34: P=8192  cert holds={m34_P_holds}, P/2 cert holds={m34_Phalf_holds}", end="")
if m34_P_holds is True and m34_Phalf_holds is False:
    print("  ✓ MINIMAL")
elif m34_P_holds is True and m34_Phalf_holds is True:
    print("  *** OVERCLAIM ***")
else:
    print("  *** ERROR ***")

print(f"  m=36: P=16384 cert holds={m36_P_holds}, P/2 cert holds={m36_Phalf_holds}", end="")
if m36_P_holds is True and m36_Phalf_holds is False:
    print("  ✓ MINIMAL")
elif m36_P_holds is True and m36_Phalf_holds is True:
    print("  *** OVERCLAIM ***")
else:
    print("  *** ERROR ***")

if m38_P_holds is not None:
    print(f"  m=38: P=32768 cert holds={m38_P_holds}, P/2 cert holds={m38_Phalf_holds}", end="")
    if m38_P_holds is True and m38_Phalf_holds is False:
        print("  ✓ MINIMAL")
    elif m38_P_holds is True and m38_Phalf_holds is True:
        print("  *** OVERCLAIM ***")
    elif not m38_P_holds:
        print("  *** ERROR ***")
    else:
        print("  (P/2 not checked)")
else:
    print(f"  m=38: P=32768 cert holds={m38_P_holds} (P/2 not attempted)")

print()
print("RESONANCE TEST:")
print(f"  m=40 at n'=16403: F={F_val}, G={G_val} → SubcaseB={subcaseB_m40}")
if not subcaseB_m40:
    print("  ✓ Paper's 'decisive' resonance claim CONFIRMED")
else:
    print("  *** Paper claim REFUTED ***")

print()
print("VERDICT:")
if (m34_P_holds is True and m34_Phalf_holds is False and
    m36_P_holds is True and m36_Phalf_holds is False and
    not subcaseB_m40):
    print("  ✓ All checked claims VERIFIED via F-certificate method.")
    print("  Paper's period minimality for m=34,36 is now confirmed by BOTH methods:")
    print("    (1) triangle method P/2-fails-at-n'=3087 (loop-25)")
    print("    (2) F-certificate P/2 fails (loop-39, this run)")
    print("  The F-certificate method is what the Lean proof requires.")
    print("  This closes the gap between loop-25 evidence and the proof plan.")
else:
    print("  *** WARNINGS: see individual results above ***")
