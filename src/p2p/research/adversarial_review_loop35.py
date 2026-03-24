#!/usr/bin/env python3
"""
Adversarial Review Loop 35 — last-32 and last-40 coverage gap
Run date: 2026-03-24

Target: Paper lines 724-727 say:
  "last-32 and last-40 confirmed in [3087, 5500) by prior scans"
  while last-16, last-24 are confirmed to n'=8000, and
  last-48 through last-80 are confirmed to [3087, 8000) by loop-30.

last-32 and last-40 are the ONLY two positions left with coverage only to 5500.
This is an asymmetric gap: they're surrounded by positions checked to 8000.

Fix: extend last-32 (m = 2n'-30) and last-40 (m = 2n'-38) from [3087,5500)
to [3087,8000). If both still 0 SubcaseB, update paper to say "all last-9
through last-80 confirmed to [3087,8000)".

Also: check last-26, last-28, last-34, last-36 (even offsets between
last-24 and last-40 that aren't explicitly mentioned in the paper).
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
    return bool(a[0])


def compute_G_single(n_prime, m):
    L = 2 * (n_prime + 1) + 1
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[L - 1] = 1
    for _ in range(n_prime + 1):
        g = g[:-2] ^ (g[1:-1] | g[2:])
    return bool(g[0])


def scan_near_boundary(offset, n_start=3087, n_end=8001):
    """
    Check SubcaseB for m = 2n' - offset over n' in [n_start, n_end).
    last-k label = offset + 2.
    """
    events = []
    for n_p in range(n_start, n_end):
        m_val = 2 * n_p - offset
        if m_val <= 0 or m_val >= 2 * n_p + 1:
            continue
        F = compute_F_single(n_p, m_val)
        G = compute_G_single(n_p, m_val)
        if not F and G:
            events.append(n_p)
    return events


print("=== Loop 35: last-32 and last-40 coverage gap fill ===\n")
print("  Paper: last-32, last-40 only confirmed to n'=5500.")
print("  All other last-9..last-80 confirmed to n'=8000.")
print("  Extending last-32, last-40 from [5500,8000) and re-scanning [3087,8000).")
print("  Also checking last-26,28,34,36 which aren't explicitly mentioned.\n")

# last-k → offset = k-2 (since last = 2n'+2, m = last-k = 2n'+2-k = 2n'-(k-2))
positions_to_check = [
    (26, 24),  # last-26: m = 2n'-24
    (28, 26),  # last-28: m = 2n'-26
    (32, 30),  # last-32: m = 2n'-30  *** PAPER SAYS ONLY TO 5500 ***
    (34, 32),  # last-34: m = 2n'-32
    (36, 34),  # last-36: m = 2n'-34
    (38, 36),  # last-38: m = 2n'-36  (between last-36 and last-40)
    (40, 38),  # last-40: m = 2n'-38  *** PAPER SAYS ONLY TO 5500 ***
    (42, 40),  # last-42: m = 2n'-40  (between last-40 and last-48)
    (44, 42),  # last-44: m = 2n'-42
    (46, 44),  # last-46: m = 2n'-44  (just before last-48 which is confirmed)
]

print(f"  {'position':>10}  {'formula':>12}  {'n range':>14}  {'SubcaseB':>30}  {'time':>6}")
print("  " + "-" * 80)

any_active = False
for last_k, offset in positions_to_check:
    t0 = time.time()
    # Full scan [3087, 8000)
    events = scan_near_boundary(offset, 3087, 8001)
    elapsed = time.time() - t0
    status = "*** ACTIVE ***" if events else "0 SubcaseB"
    if events:
        any_active = True
        print(f"  last-{last_k:<4}  m=2n'-{offset:<4}  [3087,8000)  {status} {events}  {elapsed:.0f}s")
    else:
        print(f"  last-{last_k:<4}  m=2n'-{offset:<4}  [3087,8000)  {status}             {elapsed:.0f}s")
    sys.stdout.flush()

print()
if any_active:
    print("  *** ACTIVE NEAR-BOUNDARY POSITIONS FOUND — 'single exceptional' claim wrong ***")
else:
    print("  ✓ All checked positions (last-26..last-46) confirmed 0 SubcaseB in [3087,8000)")
    print("  ✓ last-32 and last-40 gap filled: now all last-9..last-46 confirmed to n'=8000")
    print("  Paper correction: update 'last-32 and last-40 confirmed in [3087,5500)' to")
    print("  'all last-9 through last-80 confirmed in [3087,8000)'")
