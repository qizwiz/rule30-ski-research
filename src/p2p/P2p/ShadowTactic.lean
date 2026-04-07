/-
ShadowTactic.lean — decide_shadow tactic for Case 3 shadow goals
================================================================

When both dChain(n+1, j) and dChain(n, j) are false ("shadow" positions),
the all-zeros and all-ones witnesses used in Cases 1/2 fail. Instead,
we search computationally for a spike witness: a configuration with a
single true cell at position x such that flipping cell j changes the output.

Computational discovery: three spike positions cover ALL shadows for n ≤ 120:
  • rightmost = 2*(n+1)    (the rightmost cell)
  • x = 1                   (second cell from left)
  • x = 6                   (seventh cell from left)

The tactic `decide_shadow` tries each in turn, using native_decide to verify.
-/

import P2p.SpinePass

set_option maxHeartbeats 800000

namespace P2p

/-- Spike configuration at position x for level n+1: all false except position x. -/
def shadowSpike (x : Nat) (n : Nat) : Config (n + 1) :=
  fun k : Fin (2 * (n + 1) + 1) => decide (k.val = x)

/-- Try three spike witnesses for Essential goals at shadow positions.

    Usage: in a goal of the form `Essential (n+1) ⟨j, _⟩` where n and j are
    concrete numerals and both dChain values are false, this tactic finds a
    spike witness and closes the goal via native_decide. -/
macro "decide_shadow" : tactic => `(tactic|
  first
  | (refine ⟨shadowSpike (2 * (_ + 1)) _, ?_⟩; native_decide)
  | (refine ⟨shadowSpike 1 _, ?_⟩; native_decide)
  | (refine ⟨shadowSpike 6 _, ?_⟩; native_decide)
  | (refine ⟨fun _ => false, ?_⟩; native_decide)
  | fail "decide_shadow: no spike witness found at positions rightmost/1/6/all-false")

-- ============================================================================
-- Tests: known shadow positions
-- ============================================================================

-- n=4→5, j=3 is the first shadow (dChain 5 3 = false, dChain 4 3 = false)
-- Verify the shadow condition first:
example : dChain 5 3 = false := by native_decide
example : dChain 4 3 = false := by native_decide

-- The tactic should close it:
example : Essential 5 ⟨3, by omega⟩ := by decide_shadow

-- A non-shadow position for sanity (should also work via all-false witness):
example : Essential 5 ⟨5, by omega⟩ := by decide_shadow

-- More shadow tests at higher n
example : Essential 6 ⟨3, by omega⟩ := by decide_shadow
example : Essential 7 ⟨3, by omega⟩ := by decide_shadow

end P2p
