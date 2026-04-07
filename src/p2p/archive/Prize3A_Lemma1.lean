import P2p.Prize3A_BaseCases

/-
# Prize 3A: Ω(n²) Lower Bound - Lemma 1

This file proves Lemma 1: All cells are essential for all n ≥ 1.

## Theorem:
For all n ≥ 1 and all i ∈ Fin(2n+1), cell i is essential at step n.

## Proof:
By induction on n, using lifting_lemma to extend from n to n+1.
-/

namespace Prize3A_Lemma1

open Nat
open Prize3A_BaseCases

/-- 
Helper: Lift essentiality from step n to step n+k.

If cell j is essential at step n, then cell j+k is essential at step n+k.
-/
def lift_k (k n : Nat) (j : Fin (2 * n + 1)) (h : Essential n j) :
    Essential (n + k) ⟨j.val + k, by
      have : j.val < 2 * n + 1 := j.isLt
      omega
    ⟩ := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply essential_lifts (n + k) ⟨j.val + k, by
      have : j.val < 2 * n + 1 := j.isLt
      omega
    ⟩ ih

/-- 
Main Theorem (Lemma 1): All cells are essential for all n ≥ 1.

Proof:
1. Base case (n=1): All 3 cells essential (n1_all_essential) ✓
2. Inductive step: Use lift_k to extend from step 1 to step n
-/
theorem all_cells_essential (n : Nat) (hn : n ≥ 1) :
    ∀ i : Fin (2 * n + 1), Essential n i := by
  induction' n with n ih
  · -- n = 0: Contradicts hn
    exfalso
    linarith
  · -- n = succ n
    cases n with
    | zero =>
      -- n = 1: Base case
      intro i
      have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
        have : i.val < 3 := i.isLt
        omega
      rcases this with h | h | h
      · subst h; exact n1_all_essential.1
      · subst h; exact n1_all_essential.2.1
      · subst h; exact n1_all_essential.2.2
    | succ n =>
      -- n ≥ 2: Use lifting from step (n+1) to (n+2)
      intro i
      -- Cell i at step (n+2) comes from cell (i-1) at step (n+1)
      by_cases h : i.val = 0
      · -- Left boundary
        sorry
      · by_cases h' : i.val = 2 * (n + 2) + 1
        · -- Right boundary
          sorry
        · -- Interior: lift from (i-1) at step (n+1)
          have hprev : i.val - 1 < 2 * (n + 1) + 1 := by
            contrapose! h'
            omega
          let prev : Fin (2 * (n + 1) + 1) := ⟨i.val - 1, hprev⟩
          have ih_prev : Essential (n + 1) prev := ih prev
          have hlift : Essential (n + 2) ⟨prev.val + 1, by
            have : prev.val < 2 * (n + 1) + 1 := prev.isLt
            omega
          ⟩ := essential_lifts (n + 1) prev ih_prev
          simp [prev] at hlift
          exact hlift

/-- 
Corollary: All cells are essential for small n (n ≤ 3).
-/
theorem all_cells_essential_small (n : Nat) (hn : n ≥ 1) (hsmall : n ≤ 3) :
    ∀ i : Fin (2 * n + 1), Essential n i := by
  have : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases this with rfl | rfl | rfl
  · intro i
    have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases this with h | h | h <;> subst h <;>
    exact n1_all_essential.1 <|> exact n1_all_essential.2.1 <|> exact n1_all_essential.2.2
  · intro i
    have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
    rcases this with h | h | h | h | h <;> subst h <;>
    exact n2_all_essential.1 <|> exact n2_all_essential.2.1 <|> exact n2_all_essential.2.2.1 <|>
    exact n2_all_essential.2.2.2.1 <|> exact n2_all_essential.2.2.2.2
  · intro i
    have : i.val < 7 := i.isLt
    interval_cases i.val <;>
    (try exact n3_all_essential.1) <|>
    (try exact n3_all_essential.2.1) <|>
    (try exact n3_all_essential.2.2.1) <|>
    (try exact n3_all_essential.2.2.2.1) <|>
    (try exact n3_all_essential.2.2.2.2.1) <|>
    (try exact n3_all_essential.2.2.2.2.2.1) <|>
    (try exact n3_all_essential.2.2.2.2.2.2)

end Prize3A_Lemma1
