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
Lemma 2: hcone_left_edge — the H-spike's causal cone doesn't reach n'+1 (TODO)
Lemma 3: f_center_prev_zero — anti-diagonal i+t=7 in infinite-tape Rule 30 is 0 (TODO)
Lemma 4: d_leftbound — D-field min support ≥ center+2 at step T-1 (TODO)
-/
import P2p.Prize3_Complete

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

end P2p
