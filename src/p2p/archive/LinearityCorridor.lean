/-
LinearityCorridor.lean
======================
Algebraic lemmas for the D-field linearity corridor approach to SubcaseB m=4 Level 3+.

These lemmas formalize the observation that the nonlinearity term NL vanishes
on cells outside the causal cones of the B and A fields, allowing a linear analysis.

## Background

Rule 30 can be written as: next[i] = L XOR (C OR R)
                                    = (L XOR C XOR R) XOR (C AND R)

In the three-spike decomposition at position m with witness w:
  F = rule30^n (spike_w)       -- witness-only config
  H = rule30^n (twoSpike_{w,m})  -- witness + m config
  A = spike_w evolution
  B = spike_m evolution
  C = twoSpike evolution (should equal A XOR B outside interference zone)

The nonlinearity term for adjacent cells (l,c) and (l',c') is:
  NL(l, c, l', c') = (l OR c) XOR (l' OR c') XOR ((l XOR l') OR (c XOR c'))

Key property: NL(0, 0, a', b') = 0 for all a', b'.

This means that outside the support of both B and A fields, the nonlinearity vanishes,
and the evolution is linear — enabling the "linearity corridor" argument.

## The 4 Lean lemmas toward closing subcaseB_m4_ge3087 Level 3+

Lemma 1: nl_zero_when_both_zero — NL vanishes when left inputs are both 0 (PROVED)
Lemma 2: hcone_left_edge — the H-spike's causal cone doesn't reach n'+1 (PROVED)
Lemma 3: f_center_prev_zero — anti-diagonal i+t=7 in infinite-tape Rule 30 is 0 (PROVED t≤2000)
Lemma 4: d_leftbound — D[center+1]=0 at T-1: HOLDS for right-boundary, FAILS for m=4
-/
import P2p.Prize3_Complete
import P2p.CausalConeLemmas

namespace P2p

/-!
## Lemma 1: nl_zero_when_both_zero

The nonlinearity term NL(l, c, l', c') = (l OR c) XOR (l' OR c') XOR ((l XOR l') OR (c XOR c'))
vanishes when both left inputs l and c are false, for any a' b' : Bool.

This is the key property that makes the D-field analysis tractable:
outside the support of the initial spikes (where left-pair cells are 0),
the XOR linearity of Rule 30 is preserved.
-/

/-- NL(0, 0, a', b') = 0 for all a', b' : Bool.
    This is immediate from the truth table: (0|0) = 0, and XOR with (a'|b') and ((0^a')|(0^b'))=(a'|b') gives 0. -/
lemma nl_zero_when_both_zero (a' b' : Bool) :
    (false || false) ^^ (a' || b') ^^ ((false ^^ a') || (false ^^ b')) = false := by
  cases a' <;> cases b' <;> decide

/-!
## Lemma 2: hcone_left_edge

After n' steps from an H-spike at position 2*(n'+1) in a tape of length 2*(n'+1)+1,
position n'+1 is false (for n' ≥ 2).

Key: after n' steps the tape has length exactly 3, so index n'+1 ≥ 3 is out of bounds.
This formalizes "the H-spike's left causal boundary hasn't reached center-1 by step T-1."
-/

/-- After n' steps from spikeAtList (2*(n'+1)) (2*(n'+1)+1), position n'+1 is false (n' ≥ 2).
    Proof: the result tape has length exactly 3, so index n'+1 ≥ 3 is out of bounds. -/
lemma hcone_left_edge (n' : Nat) (hn' : 2 ≤ n') :
    (caEvolve n' (spikeAtList (2*(n'+1)) (2*(n'+1)+1))).getD (n'+1) false = false := by
  have hlen_init : (spikeAtList (2*(n'+1)) (2*(n'+1)+1)).length = 2*(n'+1)+1 :=
    spikeAtList_length _ _
  have hge : (spikeAtList (2*(n'+1)) (2*(n'+1)+1)).length ≥ 2 * n' := by omega
  have hlen_result : (caEvolve n' (spikeAtList (2*(n'+1)) (2*(n'+1)+1))).length = 3 := by
    rw [caEvolve_length_le n' _ hge, hlen_init]; omega
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

/-!
## Lemma 3: f_center_prev_zero (anti-diagonal k=7)

The anti-diagonal x + t = 7 in Rule 30 from a single spike is identically zero:
Cell(t, 7-t) = 0 for all t ≥ 0 (verified computationally for t = 0..2000).

In the finite-tape caEvolve model:
  Spike at position 2t in tape of width 4t+15, evolved t steps → position 7 is false.

Proof: evolved[j] represents Cell(t, j+t). With spike at position 2t:
  evolved[7] = Cell(t, 7+t) with spike offset 7+t - 2t = 7-t.
  Anti-diagonal check: offset + time = (7-t) + t = 7 ✓

For t ≤ 3, position 7-t > t so it's outside the right causal cone of the spike → trivially 0.
For t ≥ 4, this is non-trivial (the position enters the causal cone).
For t ≥ 8, 7-t < 0 so the position is to the left of the spike; the left causal cone
of the spike grows as t, so these positions are well inside the cone.

Currently proved for t ≤ 30 by native_decide. The full proof for all t requires an
inductive argument (see A3 in loop-prompt-A.md).
-/

/-- Anti-diagonal k=7 in Rule 30: Cell(t, 7-t) = 0 for t ≤ 2000.
    Finite-tape encoding: spike at position 2t in tape of width 4t+15, evolved t steps.
    evolved[7] = Cell(t, 7+t); spike offset = (7+t) - 2t = 7-t; sum = (7-t)+t = 7. ✓
    Machine-checked: native_decide over all 2001 values. -/
theorem f_center_prev_zero_le2000 :
    ∀ t : Fin 2001,
    (caEvolve t.val (spikeAtList (2*t.val) (4*t.val+15))).getD 7 false = false := by
  native_decide

/-!
## Lemma 4: d_leftbound — D-field analysis

For the **right-boundary family** (m = 2n'-6), D[center+1] = D[center+2] = 0 at step T-1.
Python-verified for n' = 8..99. This means the corridor argument works for right-boundary.

For **fixed m=4**, D[center+1] is NOT always 0 (counterexamples: n'=13, 37, 45, 53, 61, ...).
The corridor argument does NOT apply directly to m=4 SubcaseB.
A different approach is needed for the m=4 axiom.
-/

end P2p
