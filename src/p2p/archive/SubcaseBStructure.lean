/-
SubcaseBStructure.lean
=====================
Structural analysis of the SubcaseB sorry in LiftingLemma_LeftPermutive.lean.

The sorry at line 6950 of LiftingLemma_LeftPermutive.lean requires proving:
  For all n' ≥ 3085 and all even m in "subcaseB" at level n'+1,
  there exists a configuration c_n with all odd positions = false
  that is sensitive at position m.

SubcaseB conditions:
  hcase: rule30n(n'+1)(spike_m) = false
  hts:   rule30n(n'+1)(two_spike_{m, last}) = true

This file states the missing structural lemma and documents the computational evidence.

STATUS: Contains sorry (the missing structural proof).
This is research infrastructure, not meant to compile into the main proof yet.
-/

import P2p.CA_Basics

/-!
## Computational Findings

### F(n, j) = rule30n(n)(spike_j) is periodic in n:
- j=2: period 2 (proved in Spike2Parity.lean)
- j=4: period 8
- j=6: period 16
- j=8: period 32
- j=10: period 64
- j=12: period 64
- j=14: period 64
- j=16: period 256
- j=18: period 256
- j=20: period 256

F(n, j) is independent of tape size (padding with zeros doesn't change output).

### SubcaseB positions grow:
- Max m at n'=2829: m=20
- Max m at n'=3341: m=28
- Period of subcaseB(m=4): every 8 values of n'
- Period of subcaseB(m=8): every 32 values of n'

### Witnesses always exist:
For all subcaseB (n', m) with n' ∈ [2829, 4000], there exists an even j < 100
such that spike_j witnesses sensitivity at m. Exhaustively verified.

### Why the sorry cannot be closed by enumeration:
1. SubcaseB positions grow: new m values appear at larger n'
2. Witness map is not exactly periodic: the optimal j shifts between period blocks
3. No single period captures all (n' mod P, m, j) triples
-/

/-- spike_j output periodicity axiom: F(n, j) = rule30n(n)(spike_j)
    is periodic in n for each fixed even j.
    Computationally verified for j ≤ 20, n up to 10000.
    Period = 2^(j/2) for j ≤ 8, period = 2^(j/2 - 1) for j = 10..14, etc. -/
axiom spike_periodicity (j : Nat) (hj_even : j % 2 = 0) (hj_pos : 0 < j) :
    ∃ p : Nat, p > 0 ∧ ∀ n : Nat, n ≥ j + 1 →
      rule30n n (fun k : Fin (2 * n + 1) => decide (k.val = j)) =
      rule30n (n + p) (fun k : Fin (2 * (n + p) + 1) => decide (k.val = j))

/-- Tape-size independence for spike configurations:
    rule30n(n)(spike_j) on tape of size 2n+1 equals
    rule30n(n)(spike_j) on any larger tape (same number of steps).
    This follows from the causal cone: cell 0 after n steps depends only on
    cells [0, 2n], and spike_j with j < 2n+1 has its spike within this range. -/
axiom spike_tape_independence (n j : Nat) (hn : j < 2 * n + 1) (extra : Nat) :
    rule30n n (fun k : Fin (2 * n + 1) => decide (k.val = j)) =
    (caEvolve n (List.ofFn (fun k : Fin (2 * (n + extra) + 1) => decide (k.val = j)))).getD 0 false

/-- The key missing structural lemma for SubcaseB.

    Statement: For ALL n' ≥ 3085 and ALL even m satisfying the subcaseB conditions,
    there exists an all-odd-false configuration that is sensitive at m.

    This is computationally verified for n' ∈ [2829, 4000].
    Witnesses are always single-spike configurations at even positions j < 100.

    A structural proof would require either:
    (a) Proving spike_j sensitivity is periodic and verifying base cases, or
    (b) A fundamentally new argument about Rule 30 sensitivity propagation.

    NOTE: This lemma is ONLY needed for rule30_prize3_direct (axiom-free path).
    The main theorem rule30_prize3 uses the lifting_lemma axiom instead. -/
axiom subcaseB_witness_exists_structural (n' : Nat) (hn : 3085 ≤ n')
    (m : Fin (2 * (n' + 1) + 1))
    (hm_even : m.val % 2 = 0)
    (hm_low : 1 ≤ m.val)
    (hm_ne_r : m.val ≠ 2 * n')
    (hm_high : m.val + 1 < 2 * (n' + 1) + 1)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m)

/-!
## Key Discovery: Max m Appears Bounded

Over n' in [5, 6000], the maximum m appearing in subcaseB oscillates between
24 and 28. If max m is truly bounded (say m <= M), then subcaseB_resolution
can be proved by:

1. SubcaseB occurrence for fixed m is periodic in n' (confirmed: period 8 for m=4,
   period 256 for m=20).
2. Sensitivity(n, j, m) for fixed (j, m) is periodic in n (confirmed for all tested pairs).
3. For each m <= M, find witness j and verify over one full period of the subcaseB
   occurrence times the sensitivity period.

The periods found:
  F(n, j=4): period 8.   F(n, j=6): period 16.   F(n, j=8): period 32.
  sensitivity(j=6, m=4): period 16.   sensitivity(j=2, m=8): period 32.
  sensitivity(j=4, m=12): period 128.  sensitivity(j=16, m=4): period 512.

## Proof Strategy Discussion

### Path 1: Prove max m bounded + periodicity (MOST PROMISING)
1. Prove F(n, j) periodic for j <= 48 (generalize Spike2Parity)
2. Prove subcaseB occurrence periodic for fixed m
3. Prove sensitivity periodic for fixed (j, m)
4. Finite case analysis over all m <= bound and all subcaseB residues
Each step generalizes proven infrastructure (Spike2Parity pattern).

### Path 2: Prove lifting_lemma axiom directly (MEDIUM)
Bypass subcaseB entirely by proving the lifting_lemma from Prize3_Complete.lean.
Requires backward construction with blocker handling.
Edge case at k = 2n needs separate treatment.

### Path 3: Accept current state (PRAGMATIC)
rule30_prize3 is proved (via axiom). subcaseB_resolution is a second axiom
in LiftingLemma_LeftPermutive.lean used only by rule30_prize3_direct.
-/
