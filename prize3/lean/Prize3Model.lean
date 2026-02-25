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
  have h0 : n ≤ n + n := Nat.le_add_right n n
  have h : n ≤ 2 * n := by
    simpa [Nat.two_mul] using h0
  simpa [Nat.succ_eq_add_one] using Nat.succ_le_succ h

-- Width increase per generation is exactly 2.
theorem coneWidth_succ (n : Nat) : coneWidth (n + 1) = coneWidth n + 2 := by
  unfold coneWidth
  simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

-- Width is monotone in n.
theorem coneWidth_monotone (n : Nat) : coneWidth n ≤ coneWidth (n + 1) := by
  rw [coneWidth_succ]
  exact Nat.le_add_right (coneWidth n) 2

end Prize3
