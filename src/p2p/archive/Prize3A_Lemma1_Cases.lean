import P2p.Prize3A_BaseCases

/-
# Prize 3A: Ω(n²) Lower Bound - Lemma 1 (Cases Approach)

This file tries direct case analysis on Fin values.
-/

namespace Prize3A_Lemma1_Cases

open Nat
open Prize3A_BaseCases

/-- Helper: Check if a specific cell is essential at n=4 -/
def check_cell_n4 (i : Nat) : Prop :=
  i < 9 → Essential 4 ⟨i, by omega⟩

/-- 
Theorem: All cells are essential for n = 4.

Proved by explicit case analysis on each of the 9 cells.
-/
theorem all_cells_essential_n4 :
    ∀ i : Fin (2 * 4 + 1), Essential 4 i := by
  intro i
  -- We know i.val is between 0 and 8
  have hbound : i.val < 9 := i.isLt
  
  -- Do case analysis on the actual value
  have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ 
         i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by
    omega
  
  -- Handle each case
  rcases this with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  
  · -- Case i.val = 0
    have : i = ⟨0, by omega⟩ := by
      apply Fin.ext
      exact h0
    rw [this]
    -- Cell 0 at n=4: witness = all-zeros
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    native_decide
    
  · -- Case i.val = 1
    have : i = ⟨1, by omega⟩ := by
      apply Fin.ext
      exact h1
    rw [this]
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    native_decide
    
  · -- Case i.val = 2
    have : i = ⟨2, by omega⟩ := by
      apply Fin.ext
      exact h2
    rw [this]
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    native_decide
    
  · -- Case i.val = 3
    have : i = ⟨3, by omega⟩ := by
      apply Fin.ext
      exact h3
    rw [this]
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    native_decide
    
  · -- Case i.val = 4
    have : i = ⟨4, by omega⟩ := by
      apply Fin.ext
      exact h4
    rw [this]
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    native_decide
    
  · -- Case i.val = 5
    have : i = ⟨5, by omega⟩ := by
      apply Fin.ext
      exact h5
    rw [this]
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    native_decide
    
  · -- Case i.val = 6
    have : i = ⟨6, by omega⟩ := by
      apply Fin.ext
      exact h6
    rw [this]
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    native_decide
    
  · -- Case i.val = 7
    have : i = ⟨7, by omega⟩ := by
      apply Fin.ext
      exact h7
    rw [this]
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    native_decide
    
  · -- Case i.val = 8
    have : i = ⟨8, by omega⟩ := by
      apply Fin.ext
      exact h8
    rw [this]
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    native_decide

/-- 
Corollary: All cells are essential for n ≤ 4.
-/
theorem all_cells_essential_upto_4 (n : Nat) (hn : n ≥ 1) (hsmall : n ≤ 4) :
    ∀ i : Fin (2 * n + 1), Essential n i := by
  have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl
  
  · -- n = 1
    intro i
    have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases this with h | h | h
    · have : i = ⟨0, by omega⟩ := by apply Fin.ext; exact h
      rw [this]; exact n1_all_essential.1
    · have : i = ⟨1, by omega⟩ := by apply Fin.ext; exact h
      rw [this]; exact n1_all_essential.2.1
    · have : i = ⟨2, by omega⟩ := by apply Fin.ext; exact h
      rw [this]; exact n1_all_essential.2.2
  
  · -- n = 2
    intro i
    have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
    rcases this with h | h | h | h | h
    · have : i = ⟨0, by omega⟩ := by apply Fin.ext; exact h
      rw [this]; exact n2_all_essential.1
    · have : i = ⟨1, by omega⟩ := by apply Fin.ext; exact h
      rw [this]; exact n2_all_essential.2.1
    · have : i = ⟨2, by omega⟩ := by apply Fin.ext; exact h
      rw [this]; exact n2_all_essential.2.2.1
    · have : i = ⟨3, by omega⟩ := by apply Fin.ext; exact h
      rw [this]; exact n2_all_essential.2.2.2.1
    · have : i = ⟨4, by omega⟩ := by apply Fin.ext; exact h
      rw [this]; exact n2_all_essential.2.2.2.2
  
  · -- n = 3
    intro i
    have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 := by omega
    rcases this with h | h | h | h | h | h | h
    · have : i = ⟨0, by omega⟩ := by apply Fin.ext; exact h; rw [this]; exact n3_all_essential.1
    · have : i = ⟨1, by omega⟩ := by apply Fin.ext; exact h; rw [this]; exact n3_all_essential.2.1
    · have : i = ⟨2, by omega⟩ := by apply Fin.ext; exact h; rw [this]; exact n3_all_essential.2.2.1
    · have : i = ⟨3, by omega⟩ := by apply Fin.ext; exact h; rw [this]; exact n3_all_essential.2.2.2.1
    · have : i = ⟨4, by omega⟩ := by apply Fin.ext; exact h; rw [this]; exact n3_all_essential.2.2.2.2.1
    · have : i = ⟨5, by omega⟩ := by apply Fin.ext; exact h; rw [this]; exact n3_all_essential.2.2.2.2.2.1
    · have : i = ⟨6, by omega⟩ := by apply Fin.ext; exact h; rw [this]; exact n3_all_essential.2.2.2.2.2.2
  
  · -- n = 4
    exact all_cells_essential_n4

end Prize3A_Lemma1_Cases
