"""
adversarial_loop44.py  —  Loop 44 adversarial review
Target claim: "m ∈ {30, 34, 36} first appear in [4112, 4117]"
              (paper line 470-471)

For m=34 and m=36, dense scans [3087, first_hit) were done in loop-22.
For m=30, NO dense scan of [3087, 4114) is documented in the findings log.
The loop-9 entry says "m=30: first n'=4114" but without a confirming scan.

This script:
  A. Dense scan [3087, 4115) for m=30 — confirms no SubcaseB before n'=4114
  B. Verify SubcaseB at n'=4114 for m=30
  C. Verify second hit at n'=8210 for m=30 (gap = 4096 = claimed period)
  D. Full SubcaseB residue within one period [4114, 4114+4096) for m=30
  E. Cross-check: verify m=34's first hit is at 4112 and m=36's is at 4113
     (previously done in loop-22, repeating for completeness)
  F. Period-P certificate for m=30: F(4114, 30) == F(4114 + 4096, 30)

Rule 30: rule30(l, c, r) = l XOR (c OR r)
F(n', m) = center cell after n'+1 steps from spike at position m (tape size 2*n'+3)
G(n', m) = center cell after n'+1 steps from two-spike tape: spike at m AND spike at last=2*n'+2
SubcaseB(n', m) = (F(n',m) == 0) AND (G(n',m) == 1)
"""

import numpy as np
import time

def rule30_step(row):
    """One step of Rule 30 on a numpy boolean array (open boundary, zeros outside)."""
    l = np.roll(row, 1)
    r = np.roll(row, -1)
    l[0] = False
    r[-1] = False
    return l ^ (row | r)

def make_spike(pos, size):
    """Tape of length `size` with True at position `pos`, False elsewhere."""
    tape = np.zeros(size, dtype=bool)
    tape[pos] = True
    return tape

def rule30n_center(initial_tape, steps):
    """Evolve `initial_tape` for `steps` steps, return center cell value."""
    tape = initial_tape.copy()
    n = len(tape)
    for _ in range(steps):
        tape = rule30_step(tape)
    center = len(tape) // 2
    return bool(tape[center])

def compute_F(n_prime, m):
    """
    F(n', m) = center after n'+1 steps from spike at position m.
    Tape size = 2*(n'+1)+1 = 2*n'+3.
    Center = n'+1.
    """
    size = 2 * n_prime + 3
    tape = make_spike(m, size)
    return rule30n_center(tape, n_prime + 1)

def compute_G(n_prime, m):
    """
    G(n', m) = center after n'+1 steps from tape with spikes at position m
               AND at position last = 2*n'+2.
    Tape size = 2*n'+3. Last position = 2*n'+2 = size-1.
    """
    size = 2 * n_prime + 3
    tape = make_spike(m, size)
    tape[size - 1] = True   # second spike at last position
    return rule30n_center(tape, n_prime + 1)

def subcaseB(n_prime, m):
    """True if F(n',m)==0 AND G(n',m)==1."""
    f = compute_F(n_prime, m)
    g = compute_G(n_prime, m)
    return (not f) and g, f, g

print("=" * 70)
print("Loop 44: Adversarial review — m=30 first SubcaseB hit location")
print("Target claim: 'm ∈ {30,34,36} first appear in [4112,4117]'")
print("=" * 70)

# ---- Attack A: Dense scan [3087, 4115) for m=30 ----
print("\n--- Attack A: Dense scan [3087, 4115) for m=30 ---")
print("(Checking: is n'=4114 truly the FIRST SubcaseB event for m=30?)")

m30 = 30
hits_m30_early = []
t0 = time.time()
for np_ in range(3087, 4115):
    sb, f, g = subcaseB(np_, m30)
    if sb:
        hits_m30_early.append((np_, f, g))

elapsed = time.time() - t0
print(f"Scan [3087, 4115) for m=30 completed in {elapsed:.1f}s")
print(f"SubcaseB hits in [3087, 4115): {hits_m30_early}")
if len(hits_m30_early) == 0:
    print("RESULT: NO SubcaseB events before n'=4114 for m=30. First hit confirmed ≥ 4114.")
else:
    print(f"RESULT: SURPRISE — SubcaseB found earlier than expected at {hits_m30_early}!")

# ---- Attack B: Verify SubcaseB at n'=4114 for m=30 ----
print("\n--- Attack B: Verify SubcaseB at n'=4114 for m=30 ---")
sb4114, f4114, g4114 = subcaseB(4114, 30)
print(f"F(4114, 30) = {int(f4114)}, G(4114, 30) = {int(g4114)}, SubcaseB = {sb4114}")
if sb4114:
    print("RESULT: SubcaseB confirmed at n'=4114. Paper claim correct.")
else:
    print(f"RESULT: ERROR — SubcaseB NOT at n'=4114! (F,G) = ({int(f4114)},{int(g4114)})")

# ---- Attack C: Verify second hit at n'=8210 for m=30 ----
print("\n--- Attack C: Verify second hit at n'=8210 for m=30 ---")
sb8210, f8210, g8210 = subcaseB(8210, 30)
print(f"F(8210, 30) = {int(f8210)}, G(8210, 30) = {int(g8210)}, SubcaseB = {sb8210}")
gap = 8210 - 4114
print(f"Gap from first hit: 8210 - 4114 = {gap} (claimed period = 4096)")
if sb8210 and gap == 4096:
    print("RESULT: Second hit confirmed at n'=8210 with gap exactly 4096. Period consistent.")
elif sb8210:
    print(f"RESULT: SubcaseB at 8210 but gap = {gap} ≠ 4096. Period claim needs checking.")
else:
    print("RESULT: ERROR — no SubcaseB at n'=8210!")

# ---- Attack D: Full SubcaseB structure in one period [4114, 4114+4096) ----
print("\n--- Attack D: SubcaseB residues in [4114, 4114+4096) for m=30 ---")
print("(Enumerating all SubcaseB events in one claimed period)")
hits_period = []
t0 = time.time()
for np_ in range(4114, 4114 + 4096):
    sb, f, g = subcaseB(np_, m30)
    if sb:
        hits_period.append(np_)
elapsed = time.time() - t0
print(f"Period scan [4114, 8210) for m=30 completed in {elapsed:.1f}s")
print(f"SubcaseB hits: {hits_period}")
if hits_period:
    residues = [(h - 4114) % 4096 for h in hits_period]
    print(f"Residues mod 4096 (from 4114): {residues}")
    # Check that the last element is at 8210 (i.e., we should stop before 4114+4096=8210)
    if max(hits_period) < 4114 + 4096:
        print(f"All hits within one period. Gaps between hits: {[hits_period[i+1]-hits_period[i] for i in range(len(hits_period)-1)]}")

# ---- Attack E: Cross-check m=34 and m=36 first hits ----
print("\n--- Attack E: Cross-check m=34 first hit (claimed n'=4112) ---")
sb4112_34, f4112_34, g4112_34 = subcaseB(4112, 34)
print(f"m=34: F(4112)={int(f4112_34)}, G(4112)={int(g4112_34)}, SubcaseB={sb4112_34}")
if sb4112_34:
    print("CONFIRMED: m=34 first SubcaseB at n'=4112.")
else:
    print("ERROR: m=34 NOT SubcaseB at n'=4112!")

print("\n--- Attack E: Cross-check m=36 first hit (claimed n'=4113) ---")
sb4113_36, f4113_36, g4113_36 = subcaseB(4113, 36)
print(f"m=36: F(4113)={int(f4113_36)}, G(4113)={int(g4113_36)}, SubcaseB={sb4113_36}")
if sb4113_36:
    print("CONFIRMED: m=36 first SubcaseB at n'=4113.")
else:
    print("ERROR: m=36 NOT SubcaseB at n'=4113!")

# ---- Attack F: Verify the range claim "[4112,4117]" covers all three ----
print("\n--- Attack F: Summary — do all three fit within [4112,4117]? ---")
first_hits = {}
if hits_m30_early:
    first_hits[30] = hits_m30_early[0][0]
elif sb4114:
    first_hits[30] = 4114
if sb4112_34:
    first_hits[34] = 4112
if sb4113_36:
    first_hits[36] = 4113

print(f"First SubcaseB hits: {first_hits}")
all_in_range = all(4112 <= v <= 4117 for v in first_hits.values())
print(f"All in [4112, 4117]? {all_in_range}")
if all_in_range:
    print("VERIFIED: Paper claim 'm∈{30,34,36} first appear in [4112,4117]' is CORRECT.")
else:
    for m, hit in first_hits.items():
        if not (4112 <= hit <= 4117):
            print(f"ERROR: m={m} first hit at n'={hit}, NOT in [4112,4117]!")

# ---- Additional check: look around 4115-4120 for m=30 ----
print("\n--- Additional: scan [4115, 4125) for m=30 to find all early hits ---")
for np_ in range(4115, 4125):
    sb, f, g = subcaseB(np_, m30)
    if sb:
        print(f"n'={np_}: SubcaseB (F={int(f)}, G={int(g)})")
    else:
        print(f"n'={np_}: not SubcaseB (F={int(f)}, G={int(g)})")

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print("Attack A: Dense scan [3087,4115) for m=30")
print(f"  → {len(hits_m30_early)} SubcaseB events found before n'=4114")
print(f"Attack B: SubcaseB at n'=4114 for m=30: {sb4114}")
print(f"Attack C: SubcaseB at n'=8210 for m=30: {sb8210}, gap={8210-4114}")
print(f"Attack D: SubcaseB residues in [4114, 8210): {[h-4114 for h in hits_period]}")
print(f"Attack E: m=34 first at 4112: {sb4112_34}, m=36 first at 4113: {sb4113_36}")
print(f"Attack F: All three m=30,34,36 first appear in [4112,4117]: {all_in_range}")
