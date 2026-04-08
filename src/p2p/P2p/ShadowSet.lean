/-
ShadowSet.lean — Decidable shadow-region classifier for Rule 30 dChain
======================================================================

A position (n, j) is in the "shadow" if dChain is false at both levels n and n+1.
These are the positions where neither Case 1 nor Case 2 of the lifting proof applies,
requiring the algebraic argument (Case 3 in Lifting.lean).

This file provides:
  1. `isShadow` — computable Bool classifier
  2. `isShadow_iff` — spec lemma relating Bool to propositions
  3. `#eval` exploration of shadow positions
  4. Period conjecture (sorry'd)
-/

import P2p.SpinePass

set_option maxHeartbeats 400000

/-- Shadow classifier: true when dChain is false at both levels n+1 and n. -/
def isShadow (n j : Nat) : Bool :=
  !dChain (n + 1) j && !dChain n j

/-- Specification lemma: isShadow computes the conjunction of two dChain=false conditions. -/
lemma isShadow_iff (n j : Nat) :
    isShadow n j = true ↔ dChain (n + 1) j = false ∧ dChain n j = false := by
  simp only [isShadow, Bool.and_eq_true, Bool.not_eq_true']

-- Shadow positions for small n and j.
#eval (List.range 30).flatMap (fun n =>
  (List.range (2 * n + 3)).filterMap (fun j =>
    if isShadow n j then some (n, j) else none))

/-- Conjecture: isShadow is eventually periodic in n for each fixed j,
    with period related to 2^⌊j/2⌋ (from dChain LFSR structure). -/
theorem isShadow_periodic (j : Nat) :
    ∃ P : Nat, P > 0 ∧ ∀ n : Nat, isShadow (n + P) j = isShadow n j := by
  sorry

