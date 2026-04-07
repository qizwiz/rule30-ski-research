import P2p.Prize3_Bridge_Verified

/-
# Prize 3A: Ω(n²) Lower Bound - Verified Base Cases

This file proves base cases for Lemma 1: All cells are essential.

## Theorems:
- n=1: All 3 cells essential ✓
- n=2: All 5 cells essential ✓  
- n=3: All 7 cells essential ✓
-/

namespace Prize3A_BaseCases

open Nat

/-- 
Theorem: For n=1, all 3 cells are essential.

Witness for all cells: all-zeros configuration.
-/
theorem n1_all_essential :
    Essential 1 ⟨0, by omega⟩ ∧
    Essential 1 ⟨1, by omega⟩ ∧
    Essential 1 ⟨2, by omega⟩ := by
  constructor
  · exact ⟨(fun _ => false), by simp [rule30n, caEvolve]; native_decide⟩
  constructor
  · exact ⟨(fun _ => false), by simp [rule30n, caEvolve]; native_decide⟩
  · exact ⟨(fun _ => false), by simp [rule30n, caEvolve]; native_decide⟩

/-- 
Theorem: For n=2, all 5 cells are essential.
-/
theorem n2_all_essential :
    Essential 2 ⟨0, by omega⟩ ∧
    Essential 2 ⟨1, by omega⟩ ∧
    Essential 2 ⟨2, by omega⟩ ∧
    Essential 2 ⟨3, by omega⟩ ∧
    Essential 2 ⟨4, by omega⟩ := by
  constructor
  · exact ⟨(fun _ => false), by simp [rule30n, caEvolve]; native_decide⟩
  constructor
  · exact ⟨(fun i => i.val = 3), by simp [rule30n, caEvolve]; native_decide⟩
  constructor
  · exact ⟨(fun i => i.val = 3), by simp [rule30n, caEvolve]; native_decide⟩
  constructor
  · exact ⟨(fun _ => false), by simp [rule30n, caEvolve]; native_decide⟩
  · exact ⟨(fun _ => false), by simp [rule30n, caEvolve]; native_decide⟩

/-- 
Theorem: For n=3, all 7 cells are essential.
-/
theorem n3_all_essential :
    Essential 3 ⟨0, by omega⟩ ∧
    Essential 3 ⟨1, by omega⟩ ∧
    Essential 3 ⟨2, by omega⟩ ∧
    Essential 3 ⟨3, by omega⟩ ∧
    Essential 3 ⟨4, by omega⟩ ∧
    Essential 3 ⟨5, by omega⟩ ∧
    Essential 3 ⟨6, by omega⟩ := by
  constructor
  · exact ⟨(fun _ => false), by simp [rule30n, caEvolve]; native_decide⟩
  constructor
  · exact ⟨(fun _ => false), by simp [rule30n, caEvolve]; native_decide⟩
  constructor
  · exact ⟨(fun _ => false), by simp [rule30n, caEvolve]; native_decide⟩
  constructor
  · exact ⟨(fun _ => false), by simp [rule30n, caEvolve]; native_decide⟩
  constructor
  · exact ⟨(fun i => i.val = 1), by simp [rule30n, caEvolve]; native_decide⟩
  constructor
  · exact ⟨(fun _ => false), by simp [rule30n, caEvolve]; native_decide⟩
  · exact ⟨(fun _ => false), by simp [rule30n, caEvolve]; native_decide⟩

/-- 
Corollary: Lifting preserves essentiality.
-/
theorem essential_lifts (n : Nat) (k : Fin (2 * n + 1)) :
    Essential n k → Essential (n + 1) ⟨k.val + 1, by
      have : k.val < 2 * n + 1 := k.isLt
      omega
    ⟩ :=
  lifting_lemma n k

end Prize3A_BaseCases
