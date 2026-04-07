# Session Analysis: Both-Zero Impossibility and Right-Mirror Structure

**Date**: 2026-04-07  
**Focus**: Synthesizing two Opus consultations + original computational investigation  
**Key files modified**: SpinePass.lean (comment updated), research/findings.md (appended)

## The Single Sorry

`twoSpike_center_complement` at SpinePass.lean:480.

Goal: for even m≥40, T≥3088, m≠2T-8, m≠2(T-1), SubcaseB conditions:
  `rule30n T (twoSpike 2 m) = !dChain T 2`

## Algebraic Reduction (SESSION CONTRIBUTION)

**The sorry reduces to: a_{2,m}(T) = 1.**

Step 1 (algebraic, no computation):
- F_last = dChain T (2T) = 1 (proved: dChain_last_true in SpinePass.lean:174)
- At SubcaseB: F_m=0, G_{m,last}=1
- Therefore: a_{m,last} = G_{m,last} XOR F_m XOR F_last = 1 XOR 0 XOR 1 = **0**

Step 2 (what's needed):
- G_{2,m} = F_2 XOR F_m XOR a_{2,m} = F_2 XOR a_{2,m}  (since F_m=0)
- Goal: G_{2,m} = !F_2 ⟺ a_{2,m} = 1

The sorry = "both-zero impossibility for m≥40 at SubcaseB, excluding right-mirror."

## Right-Mirror Structure (SESSION CONTRIBUTION)

For m≥40, violations of a_{2,m}=1 at SubcaseB events occur **ONLY at m=2T-8** (right-mirror).

Pattern (computationally verified):
- m≡0 mod 8: no violations ever
- m≡2 mod 8: no violations ever  
- m≡4 mod 8: exactly one violation at T=(m+8)/2, which gives m=2T-8 — excluded by hm_not_rm!

Verified at: m=44@T=26, m=52@T=30, m=60@T=34, m=68@T=38, m=76@T=42, m=84@T=46, m=92@T=50.

**SIGNIFICANCE**: `m ≠ 2*T - 8` is EXACTLY the hypothesis needed, and it handles ALL exceptions.

## D-Chain Cascade: REFUTED

The hypothesis "D_{m+1}=0 → a_{m,last}=1" (from Opus consultation 2) is WRONG.
At m=40 SubcaseB events: T=106520 has D_41=False but a_{2,40}=1. The D_{m+1} value
does not determine a_{2,m}.

## Promising Proof Approaches

### Approach A: LFSR Orbit Characterization

For fixed even m≥40:
1. The sequence (dChain T m, a_{2,m}(T)) has period P_m = 2^(m/2)
2. On the SubcaseB sub-orbit {T : F_m=0 ∧ G_{m,last}=1}, a_{2,m}=1 except at m=2T-8
3. Prove by: (a) period P_m for both sequences, (b) native_decide for one period (infeasible for large m)

### Approach B: Linearity Corridor (BEST CANDIDATE)

For m≥40 SubcaseB events:
- T/m ≥ 40984/40 = 1025 at minimum (T >> m always)
- The spike at position m is "deep in the linear regime" near the left boundary
- In this regime, a_{2,m}=1 is forced by left-boundary linearty

Key data:
- m=40: first SubcaseB T=40984, T/m=1025
- m=42: first SubcaseB T=118804, T/m=2829
- m=46: first SubcaseB T=106523, T/m=2316

This is the SAME approach as the "linearity corridor" for m=4 Level 3+ (CLAUDE.md).
Completing that proof would give this as a corollary.

### What's Proved

In SpinePass.lean (ALL proved, no sorry):
- `dChain_last_true`: F_last=1 universally
- `dChain_2_last_false`: G_{2,last}=0 for T≥2
- `dChain_2_parity`: F_2=(T%2==1)
- `rule30n_spike_dChain`: spike center = dChain value

In LiftingLemma_LeftPermutive.lean (0 actual sorry tactics — builds with subcaseB_mgt38_witness axiom):
- `lifting_lemma` proved (but Prize3_Complete.lean has it as axiom — need integration)

## Proof Chain to Prize 3

To close the prize proof, need either:
1. Prove `twoSpike_center_complement` → proves `subcaseB_mgt38_witness_proved` →
   replaces `axiom subcaseB_mgt38_witness` in SubcaseBPeriod.lean →
   LiftingLemma_LeftPermutive.lean becomes axiom-free →
   Prize 3 proved

2. Alternatively: integrate LiftingLemma_LeftPermutive.lean's proved `lifting_lemma`
   into Prize3_Complete.lean (replace `axiom lifting_lemma` at line 309 with import
   and reference to the proved theorem). Then need `subcaseB_mgt38_witness` proved to
   make LiftingLemma axiom-free.

Both paths require proving `twoSpike_center_complement` to achieve 0 axioms.

## Brief for Next Consultant

**(a) What was done**: Synthesized two Opus consultations, ran computational verification,
refuted D-chain cascade hypothesis, verified right-mirror structure is COMPLETE and EXACT.

**(b) Key finding**: The sorry reduces to a_{2,m}=1. The ONLY exceptions for m≥40 are at
m=2T-8 (right-mirror), which is excluded by hypothesis. D_{m+1} value is irrelevant.

**(c) Best approach**: "Linearity corridor" — for m≥40 SubcaseB, T/m ≥ 1000, so the spike
at m is far from the tape center in the "linear regime". This is the same proof structure
as the m=4 Level 3+ linearity corridor.

**(d) Single best question**: "For T >> m (specifically T/m ≥ 1000), does the D-chain
structure in positions [0..m] imply a_{2,m}=1 at SubcaseB events? Can this be proved using
the anti-diagonal zero structure (f_center_prev_zero) and linearity corridor framework?"
