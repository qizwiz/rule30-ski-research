import Init.Data.Nat.Basic

/-
  Prize #3 formal track starter.
  This file contains minimal model primitives plus a first
  dependency-cone arithmetic lemma that we can build on.
-/

namespace Prize3

structure Model where
  work : Nat -> Nat

-- Width of the dependency cone at generation n
def coneWidth (n : Nat) : Nat := 2 * n + 1

-- First foundational fact: width is at least n+1.
-- This is intentionally simple, but nontrivial and reusable.
theorem coneWidth_ge_n_plus_one (n : Nat) : n + 1 ≤ coneWidth n := by
  unfold coneWidth
  have h : n ≤ 2 * n := by
    simpa [Nat.two_mul] using (Nat.le_add_right n n)
  exact Nat.succ_le_succ h

end Prize3
