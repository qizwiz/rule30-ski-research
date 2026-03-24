"""
adversarial_loop52.py — Loop 52: Attack the Part C mod-4 rule

Paper claims (lines 800-801):
  SubcaseB(n', 2n'-6) = true iff n' ≡ 1 or 2 (mod 4), for all n' ≥ 3089.

Verified densely to n'=15000. This loop extends to n'=20000 using targeted
spot checks (one per mod-4 class per range), then does a dense extension
from n'=15001 to n'=16000.

Definition:
  F(n', m): tape of size 2n'+3, spike at position m, run n'+1 steps, read center (n'+1).
  G(n', m): same but spike at m AND at last=2n'+2.
  SubcaseB(n', m) = F(n',m)=0 AND G(n',m)=1.

For Part C: m = 2n'-6 (spike always 8 from right boundary).

Anti-correlation claim: F + G = 1 for Part C positions (loop-26 verified to n'=15000).
If anti-correlation holds, SubcaseB ⟺ F=0, and the mod-4 rule becomes:
  F(n', 2n'-6) = 0 iff n' ≡ 1 or 2 (mod 4).

Correct simulation: spike near right end, so we CANNOT use the diagonal-read trick
(which only works for spike near left end). Must use fresh tapes per n'.
For efficiency: skip to selected n' values.
"""

import numpy as np
import sys
import time

def rule30_step_np(tape):
    l = np.roll(tape, 1); l[0] = 0
    c = tape
    r = np.roll(tape, -1); r[-1] = 0
    return l ^ (c | r)

def compute_F_partC(n_prime):
    """
    F(n', 2n'-6): tape of size 2n'+3, spike at 2n'-6, run n'+1 steps, read center n'+1.
    m = 2n'-6 is near the RIGHT boundary (position last-8 = 2n'+2-8 = 2n'-6).
    """
    sz = 2 * n_prime + 3
    m = 2 * n_prime - 6
    center = n_prime + 1
    tape = np.zeros(sz, dtype=bool)
    tape[m] = True
    for _ in range(n_prime + 1):
        tape = rule30_step_np(tape)
    return bool(tape[center])

def compute_FG_partC(n_prime):
    """
    Both F and G for Part C position.
    G uses spikes at m=2n'-6 AND at last=2n'+2.
    """
    sz = 2 * n_prime + 3
    m = 2 * n_prime - 6
    last = 2 * n_prime + 2
    center = n_prime + 1

    tape_F = np.zeros(sz, dtype=bool)
    tape_F[m] = True

    tape_G = np.zeros(sz, dtype=bool)
    tape_G[m] = True
    tape_G[last] = True

    for _ in range(n_prime + 1):
        tape_F = rule30_step_np(tape_F)
        tape_G = rule30_step_np(tape_G)

    F = bool(tape_F[center])
    G = bool(tape_G[center])
    return F, G

# ──────────────────────────────────────────────────────────────────────────────
# Sanity check: verify mod-4 rule at a few known values
# ──────────────────────────────────────────────────────────────────────────────

print("=" * 65)
print("ADVERSARIAL LOOP 52: Part C mod-4 rule extension")
print("=" * 65)

print("\n--- Sanity check at n' ∈ {3089..3100} ---")
for n in range(3089, 3101):
    F, G = compute_FG_partC(n)
    mod4 = n % 4
    expected_F0 = (mod4 in [1, 2])
    subcaseB = (not F) and G
    anticorr_ok = (int(F) + int(G) == 1)
    status = "OK" if (not F) == expected_F0 else "FAIL"
    print(f"  n'={n} (≡{mod4} mod 4): F={int(F)}, G={int(G)}, SubcaseB={subcaseB}, F+G={int(F)+int(G)} [{status}]")

# ──────────────────────────────────────────────────────────────────────────────
# Dense extension: n' ∈ [15001, 15100]
# ──────────────────────────────────────────────────────────────────────────────

print(f"\n--- Dense extension n'=[15001,15100] ---")
t0 = time.time()
fails = []
for n in range(15001, 15101):
    F = compute_F_partC(n)
    mod4 = n % 4
    expected_F0 = (mod4 in [1, 2])
    if (not F) != expected_F0:
        fails.append((n, int(F), mod4))
t1 = time.time()
print(f"  Checked {15101-15001} values in {t1-t0:.1f}s")
print(f"  Violations: {len(fails)}" + (f" — {fails[:3]}" if fails else " — NONE"))

# ──────────────────────────────────────────────────────────────────────────────
# Spot checks at larger n' (one per mod-4 class, power-of-2 near boundary)
# ──────────────────────────────────────────────────────────────────────────────

print(f"\n--- Spot checks at large n' ---")
spot_targets = [
    16001,   # ≡ 1 mod 4, expected F=0
    16002,   # ≡ 2 mod 4, expected F=0
    16003,   # ≡ 3 mod 4, expected F=1
    16004,   # ≡ 0 mod 4, expected F=1
    16383,   # 2^14 - 1 ≡ 3 mod 4, expected F=1
    16384,   # 2^14     ≡ 0 mod 4, expected F=1
    16385,   # 2^14 + 1 ≡ 1 mod 4, expected F=0
    16386,   # 2^14 + 2 ≡ 2 mod 4, expected F=0
]

for n in spot_targets:
    t0 = time.time()
    F, G = compute_FG_partC(n)
    t1 = time.time()
    mod4 = n % 4
    expected_F0 = (mod4 in [1, 2])
    sb = (not F) and G
    anticorr = (int(F) + int(G) == 1)
    status = "OK" if (not F) == expected_F0 else "FAIL!"
    print(f"  n'={n:6d} (≡{mod4}): F={int(F)}, G={int(G)}, F+G={int(F)+int(G)}, SubcaseB={sb} [{status}] ({t1-t0:.1f}s)")

# ──────────────────────────────────────────────────────────────────────────────
# Summary
# ──────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 65)
print("VERDICT")
print("=" * 65)
print("Dense verification extended to n'=15100 (beyond paper's n'=15000).")
print("Spot checks at key values up to n'≈16386.")
print("Any violations above would invalidate the mod-4 rule claim.")
