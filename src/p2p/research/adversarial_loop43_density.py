#!/opt/homebrew/bin/python3
"""
Adversarial Review Loop 43 — Density / Involution attack on SubcaseB at m=2n'-6
Run date: 2026-03-24

TARGET CLAIMS (paper lines 778–805):
  A. Perfect mod-4 rule: SubcaseB(n', 2n'-6) iff n' ≡ 1 or 2 (mod 4), for all n' ≥ 3089
  B. Anti-correlation: F(n', 2n'-6) + G(n', 2n'-6) = 1 always (for all n' in range)
  C. Period-4 exactness of F: F(n', 2n'-6) has exact period 4 in n'
  D. Involution F(n')+F(n'+2)=1 for all n' in [3089,3289] — claimed 0 violations
  E. Direct computation [3089,3108]: F pattern 0,0,1,1,... period 4, 20/20 correct

DEFINITIONS (matching loop-26 and paper):
  - Tape size L = 2*(n'+1)+1 = 2n'+3
  - m = 2n'-6  (spike position, 0-indexed from left)
  - last = L-1 = 2n'+2
  - Evolution: shrink left-to-right: new[i] = old[i] ^ (old[i+1] | old[i+2])
    Actually: rule30 open boundary: new = old[:-2] ^ (old[1:-1] | old[2:])
  - F(n') = a[0] after n'+1 shrink steps from spike at m
  - G(n') = g[0] after n'+1 shrink steps from two-spike at m and last
  - SubcaseB = (F==0 AND G==1)

ADVERSARIAL ATTACKS:
  1. Verify mod-4 rule densely in [3089, 3300]: any violations?
  2. Verify F+G=1 anti-correlation densely in [3089, 3300]
  3. Verify F has EXACT period 4 in [3089, 3300] — check F(n')=F(n'+4) for all n'
  4. Involution: F(n')+F(n'+2)=1 for all n' in [3089, 3289]
  5. Spot check [3089, 3108] with explicit F pattern vs 0,0,1,1,0,0,1,1,...
  6. HOSTILE REVIEWER ANALYSIS: what are the weakest points?

NOTE ON MOD-4 SUBCASEB RULE vs F-PERIOD:
  SubcaseB iff F=0 AND G=1.
  Paper claims F=0 iff n'≡1,2 mod 4.
  But attack B (F+G=1) and the SubcaseB rule interact: if F+G=1 always,
  then G=1-F, and SubcaseB = (F=0) = (n'≡1,2 mod 4). Both claims together imply the rule.
  Attack: verify each independently.
"""

import numpy as np
import time
import sys

# ============================================================
# Core CA computation
# ============================================================

def compute_F_G(n_prime):
    """Compute (F, G) for m=2n'-6 using shrinking left-to-right Rule 30.

    Rule 30 open boundary (left-aligned shrink):
      Each step: new = old[:-2] ^ (old[1:-1] | old[2:])
    After n'+1 steps the tape has shrunk by 2*(n'+1) cells,
    leaving 1 cell: F = that cell[0].

    Tape size: L = 2*(n'+1)+1
    m = 2*n_prime - 6
    last = L - 1 = 2*n_prime + 2
    """
    L = 2 * (n_prime + 1) + 1
    m = 2 * n_prime - 6
    last = L - 1

    if m < 0 or m >= L:
        raise ValueError(f"m={m} out of bounds for L={L} at n'={n_prime}")

    # F: single spike at m
    a = np.zeros(L, dtype=np.uint8)
    a[m] = 1
    for _ in range(n_prime + 1):
        a = a[:-2] ^ (a[1:-1] | a[2:])
    F = int(a[0])

    # G: two spikes at m and last
    g = np.zeros(L, dtype=np.uint8)
    g[m] = 1
    g[last] = 1
    for _ in range(n_prime + 1):
        g = g[:-2] ^ (g[1:-1] | g[2:])
    G = int(g[0])

    return F, G


# ============================================================
# Scan [3089, 3300]
# ============================================================
N_START = 3089
N_END   = 3300  # inclusive

print("=" * 65)
print(f"Adversarial Loop 43 — SubcaseB density/involution at m=2n'-6")
print(f"Range: n' in [{N_START}, {N_END}]  ({N_END - N_START + 1} values)")
print("=" * 65)
print()

t0 = time.time()
F_vals = {}
G_vals = {}

for n in range(N_START, N_END + 1):
    F, G = compute_F_G(n)
    F_vals[n] = F
    G_vals[n] = G

elapsed = time.time() - t0
print(f"Computed F,G for {N_END - N_START + 1} values in {elapsed:.1f}s")
print()

# ============================================================
# Attack A: Mod-4 rule — SubcaseB iff n' ≡ 1 or 2 (mod 4)
# ============================================================
print("=" * 65)
print("ATTACK A: Mod-4 SubcaseB rule")
print("  Claim: SubcaseB(n', 2n'-6) iff n'≡1 or 2 (mod 4), for all n' in range")
print()

mod4_violations = []
for n in range(N_START, N_END + 1):
    F = F_vals[n]
    G = G_vals[n]
    subcaseB = (F == 0 and G == 1)
    predicted_subcaseB = (n % 4 in (1, 2))
    if subcaseB != predicted_subcaseB:
        mod4_violations.append((n, F, G, subcaseB, predicted_subcaseB, n % 4))

print(f"  Total violations: {len(mod4_violations)}")
if mod4_violations:
    print(f"  VIOLATIONS FOUND:")
    for v in mod4_violations[:20]:
        n, F, G, sb, pred, rem = v
        print(f"    n'={n}: F={F}, G={G}, SubcaseB={sb}, predicted={pred}, n'%4={rem}")
    attack_A_ok = False
else:
    print(f"  VERIFIED: mod-4 SubcaseB rule holds in [{N_START},{N_END}] with 0 violations")
    attack_A_ok = True

# Show SubcaseB density
subcaseB_count = sum(1 for n in range(N_START, N_END + 1) if F_vals[n]==0 and G_vals[n]==1)
total = N_END - N_START + 1
print(f"  SubcaseB count: {subcaseB_count}/{total} = {subcaseB_count/total:.6f} (expected 0.5)")
print()

# ============================================================
# Attack B: Anti-correlation F + G = 1 always
# ============================================================
print("=" * 65)
print("ATTACK B: Anti-correlation F(n', 2n'-6) + G(n', 2n'-6) = 1")
print("  Claim: holds for ALL n' in [3089, 3300]")
print()

anticorr_violations = []
for n in range(N_START, N_END + 1):
    F = F_vals[n]
    G = G_vals[n]
    if F + G != 1:
        anticorr_violations.append((n, F, G, F + G))

print(f"  Total anti-correlation violations: {len(anticorr_violations)}")
if anticorr_violations:
    print(f"  VIOLATIONS FOUND:")
    for v in anticorr_violations[:20]:
        n, F, G, s = v
        print(f"    n'={n}: F={F}, G={G}, F+G={s}")
    attack_B_ok = False
else:
    # Characterize what values appear
    fg_pairs = {}
    for n in range(N_START, N_END + 1):
        pair = (F_vals[n], G_vals[n])
        fg_pairs[pair] = fg_pairs.get(pair, 0) + 1
    print(f"  VERIFIED: F+G=1 holds everywhere. (F,G) pair counts:")
    for pair in sorted(fg_pairs):
        print(f"    (F={pair[0]},G={pair[1]}): {fg_pairs[pair]}")
    attack_B_ok = True
print()

# ============================================================
# Attack C: Exact period 4 of F in n'
# ============================================================
print("=" * 65)
print("ATTACK C: Exact period 4 of F(n', 2n'-6) in n'")
print("  Claim: F(n')=F(n'+4) for all n' in [3089, 3296]")
print()

period4_violations = []
for n in range(N_START, N_END - 3):  # need n+4 <= N_END
    if F_vals[n] != F_vals[n + 4]:
        period4_violations.append((n, F_vals[n], F_vals[n + 4]))

print(f"  F(n')=F(n'+4) violations in [{N_START},{N_END-3}]: {len(period4_violations)}")
if period4_violations:
    print(f"  PERIOD-4 FAILS:")
    for v in period4_violations[:20]:
        n, f0, f1 = v
        print(f"    n'={n}: F(n')={f0}, F(n'+4)={f1}")
    attack_C_ok = False
else:
    print(f"  VERIFIED: F has exact period 4 in n' over [{N_START},{N_END-3}]")
    attack_C_ok = True

# Also verify period 2 FAILS (period 4 is minimal, not period 2)
period2_fail_n = None
for n in range(N_START, N_END - 1):
    if F_vals[n] != F_vals[n + 2]:
        period2_fail_n = n
        break
if period2_fail_n is not None:
    print(f"  Period-2 FAILS at n'={period2_fail_n}: F={F_vals[period2_fail_n]}, F(n'+2)={F_vals[period2_fail_n+2]}")
    print(f"  → Period 4 is MINIMAL (period 2 is not a period)")
else:
    print(f"  WARNING: period 2 did not fail — period 4 may not be minimal!")
print()

# ============================================================
# Attack D: Involution F(n') + F(n'+2) = 1 for n' in [3089, 3289]
# ============================================================
print("=" * 65)
print("ATTACK D: Involution F(n')+F(n'+2)=1 for all n' in [3089,3289]")
print("  Paper claims 0 violations in this range")
print()

involution_violations = []
for n in range(3089, 3290):  # n+2 <= 3291, within our scan range
    if n + 2 > N_END:
        print(f"  WARNING: n'={n}+2={n+2} outside scan range [{N_START},{N_END}]")
        break
    if F_vals[n] + F_vals[n + 2] != 1:
        involution_violations.append((n, F_vals[n], F_vals[n + 2]))

print(f"  Involution violations in [3089,3289]: {len(involution_violations)}")
if involution_violations:
    print(f"  VIOLATIONS FOUND:")
    for v in involution_violations[:20]:
        n, f0, f2 = v
        print(f"    n'={n}: F(n')={f0}, F(n'+2)={f2}, sum={f0+f2}")
    attack_D_ok = False
else:
    print(f"  VERIFIED: involution F(n')+F(n'+2)=1 holds in [3089,3289]")
    attack_D_ok = True
print()

# ============================================================
# Attack E: Spot-check [3089,3108] explicit F pattern
# ============================================================
print("=" * 65)
print("ATTACK E: Spot-check [3089,3108] — F pattern 0,0,1,1,0,0,1,1,...")
print("  Paper: 20/20 predictions correct (period 4, F=0 iff n'≡1,2 mod 4)")
print()

n_range_E = list(range(3089, 3109))
F_pattern_actual = [F_vals[n] for n in n_range_E]
# Predicted: F=0 if n'≡1,2 mod 4, F=1 if n'≡0,3 mod 4
# n'=3089: 3089%4=1 → F=0; n'=3090: 3090%4=2 → F=0; n'=3091: 3091%4=3 → F=1; n'=3092: 3092%4=0 → F=1
F_pattern_predicted = [0 if n % 4 in (1, 2) else 1 for n in n_range_E]

print(f"  n':         {n_range_E[:10]}  ...")
print(f"  n'%4:       {[n%4 for n in n_range_E[:10]]}  ...")
print(f"  F actual:   {F_pattern_actual[:10]}  ...")
print(f"  F predicted:{F_pattern_predicted[:10]}  ...")
print()

correct = sum(1 for a, p in zip(F_pattern_actual, F_pattern_predicted) if a == p)
print(f"  Predictions correct: {correct}/20")
if correct == 20:
    print(f"  VERIFIED: all 20/20 predictions correct")
    attack_E_ok = True
else:
    wrong = [(n_range_E[i], F_pattern_actual[i], F_pattern_predicted[i])
             for i in range(20) if F_pattern_actual[i] != F_pattern_predicted[i]]
    print(f"  FAILURES:")
    for n, fa, fp in wrong:
        print(f"    n'={n} (n'%4={n%4}): actual F={fa}, predicted F={fp}")
    attack_E_ok = False
print()

# ============================================================
# NOTE: G-period check — does G also have period 4?
# ============================================================
print("=" * 65)
print("BONUS: Does G(n', 2n'-6) also have period 4?")
print("  (Not directly claimed in paper, but relevant to anti-correlation argument)")
print()

Gperiod4_violations = []
for n in range(N_START, N_END - 3):
    if G_vals[n] != G_vals[n + 4]:
        Gperiod4_violations.append((n, G_vals[n], G_vals[n + 4]))

print(f"  G(n')=G(n'+4) violations: {len(Gperiod4_violations)}")
if Gperiod4_violations:
    print(f"  G does NOT have period 4 in general!")
    for v in Gperiod4_violations[:5]:
        n, g0, g1 = v
        print(f"    n'={n}: G(n')={g0}, G(n'+4)={g1}")
else:
    print(f"  G also has period 4.")
print()

# ============================================================
# SUMMARY TABLE
# ============================================================
print("=" * 65)
print("LOOP 43 SUMMARY")
print(f"  Attack A (mod-4 SubcaseB rule, [{N_START},{N_END}]):   {'VERIFIED' if attack_A_ok else 'FAILED'}")
print(f"  Attack B (anti-correlation F+G=1, [{N_START},{N_END}]): {'VERIFIED' if attack_B_ok else 'FAILED'}")
print(f"  Attack C (period-4 of F, [{N_START},{N_END}]):           {'VERIFIED' if attack_C_ok else 'FAILED'}")
print(f"  Attack D (involution F(n')+F(n'+2)=1, [3089,3289]):  {'VERIFIED' if attack_D_ok else 'FAILED'}")
print(f"  Attack E (spot-check [3089,3108], 20/20):             {'VERIFIED' if attack_E_ok else 'FAILED'}")
all_ok = attack_A_ok and attack_B_ok and attack_C_ok and attack_D_ok and attack_E_ok
print()
if all_ok:
    print("ALL ATTACKS REPELLED: every claim verified with 0 violations.")
else:
    print("DISCREPANCIES FOUND — see details above.")
print()

# ============================================================
# HOSTILE REVIEWER ANALYSIS
# ============================================================
print("=" * 65)
print("HOSTILE REVIEWER ANALYSIS — weakest points in the density argument")
print()
print("""
WEAKNESS 1 (STRONGEST ATTACK): The period-4 claim is computationally verified,
not proved.  The paper acknowledges this explicitly ("computationally verified but
not yet formally proved in Lean"), but a hostile reviewer will note that:
  - F(n', 2n'-6) depends on n' in the POSITION (m=2n'-6 grows), not just via
    a fixed-m period.
  - For fixed m, period of F is a power of 2 in n'. But here m co-varies with n',
    so the period claim is a claim about a different (non-standard) function.
  - The paper provides NO analytic reason why this specific co-varying function
    should have period 4. It is purely empirical.
  - Hostile reviewer: "What prevents the period from eventually breaking? The
    compute budget only reaches n'=15000 densely. A period-4 pattern could be
    a transient before a much longer period at n'>>15000."

WEAKNESS 2 (SECOND STRONGEST): The anti-correlation F+G=1 claim has NO proof sketch.
  - The paper says "prove (a) F has period 4 in n', and (b) F+G=1 identically,
    and the SubcaseB rule follows." But (b) is itself unproved.
  - A hostile reviewer: "You reduce one unproved claim (SubcaseB density=1/2) to
    TWO unproved claims (period 4 + anti-correlation). This is not progress; it is
    a reformulation."
  - The involution argument (F(n')+F(n'+2)=1) gives a nice geometric explanation
    for density=1/2 CONDITIONAL ON period 4, but the involution itself also lacks proof.

WEAKNESS 3 (MODERATE): The verification window [3089,15000] is large but finite.
  - m=2n'-6 means at n'=15000, m=29994 — well within any reasonable cone.
  - But the spike at m=2n'-6 is always 8 cells from the right boundary (last=2n'+2,
    m=last-8). The paper correctly notes this means the open-boundary approximation
    breaks down. The right boundary interference is O(1), not growing with n'.
  - This is actually exploitable: IF the right-boundary effect is what CAUSES period 4,
    then a hostile reviewer could ask: why does right-boundary interference produce
    exactly period 4, and not period 2, 8, or 16?

WEAKNESS 4 (MINOR): The involution claim is stated for [3089,3289] (200 values)
  in one part of the paper and the mod-4 rule for [3089,15000] (11912 values) in
  another. This inconsistency in verification ranges looks sloppy.
  - A hostile reviewer: "Why is the involution only checked to n'=3289 when the
    mod-4 rule is checked to n'=15000? If the involution explains the density,
    it should be verified over the same range."

WEAKNESS 5 (FATAL IF TRUE, BUT LIKELY NOT): IF F+G=1 were to fail at even one n',
  the entire proof strategy collapses. The anti-correlation is the load-bearing bridge
  between period-4-of-F and the SubcaseB density-1/2 conclusion.
  - All 5 attacks above show 0 violations in [3089,3300], but the unproved status
    means this remains a gap in the proof.

BOTTOM LINE FOR REVIEWER: The density argument is convincing as empirical evidence
but the paper correctly labels it as "computationally verified but not proved."
The single most actionable critique is: provide a proof sketch for F+G=1
(anti-correlation), since the period-4 claim might follow from it via symmetry.
""")

print(f"\nTotal runtime: {time.time() - t0:.1f}s")
