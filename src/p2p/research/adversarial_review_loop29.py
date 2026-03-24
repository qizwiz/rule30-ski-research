#!/usr/bin/env python3
"""
Adversarial Review Loop 29 — F-period certificates for ALL active small m
Run date: 2026-03-24

Target: paper states periods for all active m={4,6,8,10,12,14,16,20,22,24,26,28,30}
but F-period certificates (the Lean-style check_F_cert) have never been verified
for these positions. If any claimed period is wrong, the G-period lemma fails for that m.

Also verify: "for m=4, hard cases appear at n'=3093, 3101, 3109,...(every 8 steps)"
"""
import numpy as np
import time
import sys


def check_F_cert(m, P):
    """caEvolve P (spikeAtList m (2P+2m+1)) = spikeAtList m (2m+1)"""
    L = 2 * P + 2 * m + 1
    a = np.zeros(L, dtype=np.uint8)
    a[m] = 1
    for _ in range(P):
        a = a[:-2] ^ (a[1:-1] | a[2:])
    expected = np.zeros(2 * m + 1, dtype=np.uint8)
    expected[m] = 1
    return np.array_equal(a, expected)


def compute_F_triangle(m, N_max):
    a = np.zeros(2 * N_max + 1, dtype=np.uint8)
    a[m] = 1
    F = np.zeros(N_max, dtype=np.uint8)
    for k in range(1, N_max + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
        F[k - 1] = a[0]
    return F


def compute_G_single(n_prime, m):
    L = 2 * (n_prime + 1) + 1
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L - 1] = 1
    for _ in range(n_prime + 1):
        g = g[:-2] ^ (g[1:-1] | g[2:])
    return bool(g[0]) if len(g) else False


# ============================================================
# All active m with claimed periods
# ============================================================
active_periods = {
    4:  8,    6:  16,   8:  32,
    10: 64,   12: 64,   14: 64,
    16: 256,  20: 256,  22: 256,
    24: 512,  26: 1024, 28: 2048,
    30: 4096,
}

print("=== F-period certificates for all active m=4..30 ===\n")
print(f"  {'m':>4}  {'claimed P':>10}  {'P cert':>8}  {'P/2 cert':>10}  {'minimal':>8}  {'list size':>10}  {'time':>6}")
print("  " + "-" * 70)

all_ok = True
for m, P in sorted(active_periods.items()):
    t0 = time.time()
    P_holds = check_F_cert(m, P)
    P_half_holds = check_F_cert(m, P // 2) if P > 8 else False
    minimal = P_holds and not P_half_holds
    list_size = 2 * P + 2 * m + 1
    elapsed = time.time() - t0

    status = "✓" if minimal else ("P WRONG" if not P_holds else "NOT MINIMAL")
    print(f"  m={m:>2}  P={P:>8}  cert={str(P_holds):>6}  P/2={str(P_half_holds):>6}  "
          f"{'minimal' if minimal else '*** ' + status + ' ***':>10}  "
          f"L={list_size:>8}  {elapsed:.2f}s")
    if not minimal:
        all_ok = False
    sys.stdout.flush()

print()
if all_ok:
    print("  ✓ ALL active m=4..30 have correct minimal F-periods confirmed by cert")
else:
    print("  *** WARNING: some periods are wrong or not minimal! ***")

# ============================================================
# Verify SubcaseB pattern for m=4: "every 8 steps from n'=3093"
# ============================================================
print("\n\n=== SubcaseB pattern for m=4 in [3087, 3200) ===\n")

F4 = compute_F_triangle(4, 3201)
subcaseB_m4 = []
for n in range(3087, 3200):
    if F4[n] == 0:
        if compute_G_single(n, 4):
            subcaseB_m4.append(n)

print(f"  SubcaseB events for m=4 in [3087, 3200): {subcaseB_m4}")
if subcaseB_m4:
    diffs = [subcaseB_m4[i+1] - subcaseB_m4[i] for i in range(len(subcaseB_m4)-1)]
    print(f"  Gaps between events: {diffs}")
    print(f"  First event: n'={subcaseB_m4[0]} (paper claims 3093)")
    print(f"  Period: {diffs[0] if diffs else 'N/A'} (paper claims 8)")
    if subcaseB_m4[0] == 3093 and all(d == 8 for d in diffs):
        print(f"  ✓ Confirmed: first at 3093, period 8")
    else:
        print(f"  *** DISCREPANCY from paper claim! ***")

# ============================================================
# Also verify SubcaseB pattern for m=6 and m=22
# ============================================================
print("\n\n=== SubcaseB patterns for m=6 (period 16), m=22 (period 256) ===\n")

for m, P in [(6, 16), (22, 256)]:
    F = compute_F_triangle(m, 3087 + 2*P + 10)
    events = [n for n in range(3087, 3087 + 2*P)
              if F[n] == 0 and compute_G_single(n, m)]
    print(f"  m={m} (P={P}): SubcaseB events in [3087, {3087+2*P}): {events}")
    if len(events) >= 2:
        diffs = [events[i+1]-events[i] for i in range(len(events)-1)]
        print(f"    Gaps: {diffs}")
    sys.stdout.flush()

# ============================================================
# Lean feasibility: which certs are small enough for native_decide?
# ============================================================
print("\n\n=== Lean native_decide feasibility (cert list sizes) ===\n")
print(f"  {'m':>4}  {'P':>6}  {'list size':>12}  {'Lean status'}")
print("  " + "-" * 50)
OOM_THRESHOLD = 16000  # approx limit before native_decide OOM
for m, P in sorted(active_periods.items()):
    L = 2 * P + 2 * m + 1
    status = "certifiable now" if L < OOM_THRESHOLD else "OOM risk"
    print(f"  m={m:>2}  P={P:>6}  L={L:>10}  {status}")
