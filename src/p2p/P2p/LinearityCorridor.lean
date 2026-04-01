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

end P2p
