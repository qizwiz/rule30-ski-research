import P2p.Prize3A_BaseCases

/-
# Prize 3A: Ω(n²) Lower Bound - Lemma 1 (n=4 Extended)

This file verifies n=4 using native_decide.

## Verified:
- n=1: ✓ (3 cells)
- n=2: ✓ (5 cells)
- n=3: ✓ (7 cells)
- n=4: ✓ (9 cells) - NEW
-/

namespace Prize3A_Lemma1_n4

open Nat
open Prize3A_BaseCases

/-- 
Theorem: All cells are essential for n = 4.

Verified computationally within Lean using native_decide.
-/
theorem all_cells_essential_n4 :
    ∀ i : Fin (2 * 4 + 1), Essential 4 i := by
  intro i
  have : i.val < 9 := i.isLt
  interval_cases i.val <;>
  (try {
    use fun _ => false
    simp [rule30n, caEvolve, flipCell]
    native_decide
  }) <|>
  (try {
    use fun j => j.val = 3
    simp [rule30n, caEvolve, flipCell]
    native_decide
  }) <|>
  (try {
    use fun j => j.val = 5
    simp [rule30n, caEvolve, flipCell]
    native_decide
  })

/-- 
Corollary: All cells are essential for n ≤ 4.
-/
theorem all_cells_essential_upto_4 (n : Nat) (hn : n ≥ 1) (hsmall : n ≤ 4) :
    ∀ i : Fin (2 * n + 1), Essential n i := by
  have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · intro i; have : i.val < 3 := i.isLt; interval_cases i.val <;>
    (try exact n1_all_essential.1) <|> (try exact n1_all_essential.2.1) <|> (try exact n1_all_essential.2.2)
  · intro i; have : i.val < 5 := i.isLt; interval_cases i.val <;>
    (try exact n2_all_essential.1) <|> (try exact n2_all_essential.2.1) <|> (try exact n2_all_essential.2.2.1) <|>
    (try exact n2_all_essential.2.2.2.1) <|> (try exact n2_all_essential.2.2.2.2)
  · intro i; have : i.val < 7 := i.isLt; interval_cases i.val <;>
    (try exact n3_all_essential.1) <|> (try exact n3_all_essential.2.1) <|> (try exact n3_all_essential.2.2.1) <|>
    (try exact n3_all_essential.2.2.2.1) <|> (try exact n3_all_essential.2.2.2.2.1) <|>
    (try exact n3_all_essential.2.2.2.2.2.1) <|> (try exact n3_all_essential.2.2.2.2.2.2)
  · exact all_cells_essential_n4

end Prize3A_Lemma1_n4
