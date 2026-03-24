#!/usr/bin/env python3
"""
Adversarial Review Loop 30 — Two targets
Run date: 2026-03-24

Target 1: Paper line 560 claims "m=38 hits at 4118, 8210, 8214"
  Loop-28 known_events table says m=38: [8210, 8214, 40978, 40982] — no 4118.
  Is SubcaseB(4118, 38) true? If not, the paper has an error.
  Exhaustive check m=38 in [3087, 9000) to find ALL events.

Target 2: Near-boundary positions last-16k for k=6..10 only verified to n'=3500 (413 values).
  Paper says "last-48 through last-80 are similarly inert in [3087, 3500)".
  Extend these to [3087, 8000) — matching the coverage we have for last-16 and last-24.
"""
import numpy as np
import time
import sys


def compute_F_single(n_prime, m):
    L = 2 * (n_prime + 1) + 1
    a = np.zeros(L, dtype=np.uint8)
    a[m] = 1
    for _ in range(n_prime + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
    return bool(a[0]) if len(a) else False


def compute_G_single(n_prime, m):
    L = 2 * (n_prime + 1) + 1
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L - 1] = 1
    for _ in range(n_prime + 1):
        g = g[:-2] ^ (g[1:-1] | g[2:])
    return bool(g[0]) if len(g) else False


def compute_F_triangle(m, N_max):
    a = np.zeros(2 * N_max + 1, dtype=np.uint8)
    a[m] = 1
    F = np.zeros(N_max, dtype=np.uint8)
    for k in range(1, N_max + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
        F[k - 1] = a[0]
    return F


# ============================================================
# Target 1: m=38 — is 4118 really a SubcaseB event?
# ============================================================
print("=== Target 1: m=38 SubcaseB events in [3087, 9000) ===\n")

t0 = time.time()
# Spot-check n'=4118 first
F_4118 = compute_F_single(4118, 38)
G_4118 = compute_G_single(4118, 38)
print(f"  Spot check n'=4118, m=38: F={int(F_4118)}, G={int(G_4118)}, SubcaseB={not F_4118 and G_4118}")
print(f"  Paper claims this is a hit — {'CONFIRMED' if (not F_4118 and G_4118) else 'WRONG — not a SubcaseB event'}")
print()

# Now exhaustively find all SubcaseB events for m=38 in [3087, 9000)
print("  Computing F triangle for m=38 up to n'=8999...")
F38 = compute_F_triangle(38, 9000)
print(f"  Triangle done in {time.time()-t0:.1f}s")

events_38 = []
print("  G-checking all F=0 candidates...")
t1 = time.time()
f0_candidates = list(np.where(F38[3087:9000] == 0)[0] + 3087)
print(f"  F=0 candidates in [3087,9000): {len(f0_candidates)}")
for n_p in f0_candidates:
    if compute_G_single(int(n_p), 38):
        events_38.append(int(n_p))
        print(f"    *** SubcaseB at n'={n_p} ***")

elapsed = time.time() - t1
print(f"\n  All F=0 candidates G-checked in {elapsed:.1f}s")
print(f"  SubcaseB events for m=38 in [3087,9000): {events_38}")

if not events_38:
    print("  *** PROBLEM: paper claims hits at 4118,8210,8214 but none found to 9000 ***")
elif events_38 == [8210, 8214]:
    print("  ✓ Confirmed: first hits at 8210, 8214 — NO hit at 4118")
    print("  Paper line 560 contains an error: '4118' should be removed")
else:
    print(f"  Events found: {events_38}")

# Also spot-check 8210 and 8214
print()
for n_p in [8210, 8214]:
    F_val = compute_F_single(n_p, 38)
    G_val = compute_G_single(n_p, 38)
    print(f"  Spot check n'={n_p}, m=38: F={int(F_val)}, G={int(G_val)}, SubcaseB={not F_val and G_val}")

sys.stdout.flush()

# ============================================================
# Target 2: Near-boundary positions last-48..last-80 extended to n'=8000
# m = 2n'-k for k=48,56,64,72,80 (i.e., last-48 through last-80 in steps of 8)
# ============================================================
print("\n\n=== Target 2: Near-boundary positions last-48..last-80 to n'=8000 ===\n")
print("  Paper claim: 'last-48 through last-80 are similarly inert in [3087, 3500)'")
print("  We extend to [3087, 8000) to match last-16 and last-24 coverage\n")

near_boundary_offsets = [48, 56, 64, 72, 80]

for offset in near_boundary_offsets:
    t_start = time.time()
    # For each n', m = 2n' - offset
    # We need to compute SubcaseB for these (n', m) pairs
    # Since m grows with n', we can't use the triangle method directly
    # We compute each individually
    events = []
    errors = []
    for n_p in range(3087, 8001):
        m_val = 2 * n_p - offset
        if m_val <= 0:
            continue
        F_val = compute_F_single(n_p, m_val)
        G_val = compute_G_single(n_p, m_val)
        if not F_val and G_val:
            events.append(n_p)
        # Also note anti-correlation violations
        if F_val and G_val:  # (1,1) shouldn't happen if F+G=1
            pass  # not checking this here

    elapsed = time.time() - t_start
    if events:
        print(f"  last-{offset}: *** ACTIVE *** SubcaseB at n'={events} ({elapsed:.1f}s)")
    else:
        print(f"  last-{offset} (m=2n'-{offset}): 0 SubcaseB in [3087,8000) ({elapsed:.1f}s)")
    sys.stdout.flush()

print()
print("  Note: last-8 (m=2n'-8) is the main Part C family — not checked here")
print("  last-16, last-24 were already extended to n'=8000 in loop-26")

# ============================================================
# Target 3: Verify the P/2 minimality witnesses in paper
# Paper lines 547-551 claim specific F-values:
#   m=30: F(3087,30)=1, F(5135,30)=0
#   m=34: F(3087,34)=1, F(7183,34)=0
#   m=36: F(3087,36)=0, F(11279,36)=1
#   m=38: F(3087,38)=1, F(19471,38)=0
# ============================================================
print("\n\n=== Target 3: Verify P/2 minimality witnesses ===\n")
witnesses = [
    (30, 4096, 3087, 5135,  1, 0),
    (34, 8192, 3087, 7183,  1, 0),
    (36, 16384, 3087, 11279, 0, 1),
    (38, 32768, 3087, 19471, 1, 0),
]
print(f"  {'m':>4}  {'P':>6}  {'n1':>6}  {'n2=n1+P/2':>10}  {'F(n1)claimed':>14}  {'F(n2)claimed':>14}  {'status'}")
print("  " + "-" * 75)
all_ok = True
for m, P, n1, n2, f1_claimed, f2_claimed in witnesses:
    f1_actual = int(compute_F_single(n1, m))
    f2_actual = int(compute_F_single(n2, m))
    n2_check = n1 + P // 2
    ok = (f1_actual == f1_claimed) and (f2_actual == f2_claimed) and (n2 == n2_check)
    status = "✓" if ok else "*** WRONG ***"
    if not ok:
        all_ok = False
    print(f"  m={m:>2}  P={P:>6}  n1={n1}  n2={n2} (={n1}+{P//2})  "
          f"F(n1)={f1_actual}(claimed {f1_claimed})  F(n2)={f2_actual}(claimed {f2_claimed})  {status}")
    sys.stdout.flush()

print()
if all_ok:
    print("  ✓ ALL P/2 minimality witnesses verified correct")
else:
    print("  *** SOME WITNESSES ARE WRONG — paper needs correction ***")
