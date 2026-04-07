import P2p.Prize3A_BaseCases

/-
# Prize 3A: Ω(n²) Lower Bound - Lemma 1 (Decide Approach)

This file tries using `decide` tactic instead of `native_decide`.

The `decide` tactic can sometimes prove propositions that `native_decide` cannot.
-/

namespace Prize3A_Lemma1_Decide

open Nat
open Prize3A_BaseCases

/-- 
Theorem: All cells are essential for n = 4.

Trying decide tactic.
-/
theorem all_cells_essential_n4 :
    ∀ i : Fin (2 * 4 + 1), Essential 4 i := by
  intro i
  -- Try fin_cases instead of interval_cases
  have : i.val < 9 := i.isLt
  have : i.val ≥ 0 := by omega
  -- Enumerate all 9 cases
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ 
           i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by omega
  rcases h with h | h | h | h | h | h | h | h | h
  all_goals {
    -- For each case, try to prove essentiality
    -- Use the fact that we can compute this
    apply Eq.subst h
    intro j hj
    cases i <;> simp_all [Fin.ext_iff]
    -- Now try decide
    try decide
    -- If decide fails, try with explicit witness
    try {
      use fun _ => false
      simp [rule30n, caEvolve, flipCell]
      decide
    }
  }

/-- 
Alternative: State as a decidable proposition and use decide directly.
-/
def all_essential_at (n : Nat) : Prop :=
  ∀ i : Fin (2 * n + 1), Essential n i

/-- 
Theorem: All cells are essential for n = 4.

Stated as decidable proposition.
-/
theorem n4_all_essential_decide : all_essential_at 4 := by
  unfold all_essential_at
  intro i
  -- We need to show Essential 4 i for any i : Fin 9
  -- This requires case analysis on i
  have : i.val < 9 := i.isLt
  interval_cases i.val
  · -- i.val = 0
    apply Eq.subst (Fin.ext (by decide))
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    decide
  · -- i.val = 1
    apply Eq.subst (Fin.ext (by decide))
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    decide
  · -- i.val = 2
    apply Eq.subst (Fin.ext (by decide))
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    decide
  · -- i.val = 3
    apply Eq.subst (Fin.ext (by decide))
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    decide
  · -- i.val = 4
    apply Eq.subst (Fin.ext (by decide))
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    decide
  · -- i.val = 5
    apply Eq.subst (Fin.ext (by decide))
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    decide
  · -- i.val = 6
    apply Eq.subst (Fin.ext (by decide))
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    decide
  · -- i.val = 7
    apply Eq.subst (Fin.ext (by decide))
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    decide
  · -- i.val = 8
    apply Eq.subst (Fin.ext (by decide))
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    decide

/-- 
Corollary: All cells are essential for n ≤ 4.
-/
theorem all_cells_essential_upto_4 (n : Nat) (hn : n ≥ 1) (hsmall : n ≤ 4) :
    ∀ i : Fin (2 * n + 1), Essential n i := by
  have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · -- n = 1
    intro i
    have : i.val < 3 := i.isLt
    have : i.val ≥ 0 := by omega
    have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases h with h | h | h <;>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n1_all_essential.1) <|>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n1_all_essential.2.1) <|>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n1_all_essential.2.2)
  · -- n = 2
    intro i
    have : i.val < 5 := i.isLt
    have : i.val ≥ 0 := by omega
    have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
    rcases h with h | h | h | h | h <;>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n2_all_essential.1) <|>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n2_all_essential.2.1) <|>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n2_all_essential.2.2.1) <|>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n2_all_essential.2.2.2.1) <|>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n2_all_essential.2.2.2.2)
  · -- n = 3
    intro i
    have : i.val < 7 := i.isLt
    have : i.val ≥ 0 := by omega
    have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 := by omega
    rcases h with h | h | h | h | h | h | h <;>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n3_all_essential.1) <|>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n3_all_essential.2.1) <|>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n3_all_essential.2.2.1) <|>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n3_all_essential.2.2.2.1) <|>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n3_all_essential.2.2.2.2.1) <|>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n3_all_essential.2.2.2.2.2.1) <|>
    (apply Eq.subst h; intro j hj; cases i <;> simp_all [Fin.ext_iff]; exact n3_all_essential.2.2.2.2.2.2)
  · -- n = 4
    exact n4_all_essential_decide

end Prize3A_Lemma1_Decide
