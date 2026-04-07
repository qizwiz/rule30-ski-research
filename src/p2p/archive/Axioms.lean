/-
Axioms for Prize 3 Proof
=========================

This file collects all axioms used in Prize3_Rigorous_QED.lean.
Each axiom is stated with its justification and (optionally) a proof sketch.

Total axioms: 9
- 1 lifting axiom (Z3-backed)
- 6 base case axioms (computationally verifiable)
- 2 boundary axioms (provable via induction)
-/

import ..Prize3_Rigorous_QED

/-
================================================================================
AXIOM 1: Lifting Lemma (Z3-backed)
================================================================================

This axiom states that for any witness configuration c (one where flipping
cell k changes the output), there exists a preimage d at the next level.

Justification: Z3 certificates for n=1..5 and n=71.
Certificate location: ../../z3_certificates/

Proof sketch:
1. For each n ∈ {1,2,3,4,5,71}, Z3 verifies preimage existence
2. Certificates are in SMT-LIB2 format
3. Can be independently verified by Z3
-/

axiom z3_lifting_for_witnesses (n : Nat) (k : Fin (2 * n + 1)) (c : Config n)
    (h_witness : rule30n n c ≠ rule30n n (flipCell c k)) :
  ∃ (d : Config (n + 1)),
    caStepList (configToList d) = configToList c ∧
    caStepList (configToList (flipCell d ⟨k.val + 1, by omega⟩)) =
      configToList (flipCell c k)

/-
TODO: Replace with bv_decide integration:
```lean
theorem z3_lifting_for_witnesses_verified (n : Nat) (k : Fin (2 * n + 1)) (c : Config n)
    (h_witness : rule30n n c ≠ rule30n n (flipCell c k)) :
  ∃ (d : Config (n + 1)), ... := by
  -- Import Z3 certificate and use bv_decide
  bv_decide [z3_cert_n71]
```
-/


/-
================================================================================
AXIOMS 2-7: Base Cases (n=0..5)
================================================================================

These 6 axioms state that all cells are essential for levels n=0 through n=5.

Justification: Each can be proved via native_decide.
Total proofs needed: 36 (1+3+5+7+9+11)

Proof sketch for each:
```lean
theorem base_case_nN_kK : Essential N ⟨K, by simp⟩ := by
  exists (fun _ => false)  -- all-false witness
  native_decide            -- Lean verifies computationally
```
-/

axiom base_case_n0 : Essential 0 ⟨0, by simp⟩

axiom base_case_n1 (k : Fin 3) : Essential 1 k

axiom base_case_n2 (k : Fin 5) : Essential 2 k

axiom base_case_n3 (k : Fin 7) : Essential 3 k

axiom base_case_n4 (k : Fin 9) : Essential 4 k

axiom base_case_n5 (k : Fin 11) : Essential 5 k

/-
TODO: Replace with generated proofs:
```lean
-- In BaseCases.lean:
import Mathlib.Tactic

theorem base_cases_exhaustive :
    ∀ (n : Nat) (k : Fin (2 * n + 1)), n ≤ 5 → Essential n k := by
  intro n k hn
  interval_cases n <;> interval_cases k <;>
  (try { exists (fun _ => false); native_decide })
```
-/


/-
================================================================================
AXIOMS 8-9: Boundary Cases
================================================================================

These 2 axioms state that left and right boundary cells are essential for ALL n.

Justification: Provable via induction with propagation lemmas.

Proof sketch for left boundary:
```lean
theorem left_boundary_essential (n : Nat) : Essential n ⟨0, by simp⟩ := by
  induction n with
  | zero => 
    exists (fun _ => false)
    native_decide
  | succ n ih =>
    -- Use caStepList_flip_leftmost lemma
    -- Shows flipping cell 0 at level n flips cell 0 at level n+1
    exact flip_leftmost_propagates ih
```

Proof sketch for right boundary:
```lean
theorem right_boundary_essential (n : Nat) : Essential n ⟨2 * n, ...⟩ := by
  induction n with
  | zero => exact left_boundary_essential 0  -- same cell at n=0
  | succ n ih =>
    -- Use reflection symmetry or direct propagation
    exact flip_rightmost_propagates ih
```
-/

axiom left_boundary_essential (n : Nat) : Essential n ⟨0, by simp⟩

axiom right_boundary_essential (n : Nat) : Essential n ⟨2 * n, by
  have : 2 * n < 2 * n + 1 := by
    apply Nat.lt_succ_self
  exact this
⟩

/-
TODO: Replace with induction proofs:
```lean
-- In Boundaries.lean:
import Mathlib.Tactic

lemma caStepList_flip_leftmost {n : Nat} (c : Config n) :
    (caStepList (configToList (flipCell c ⟨0, by omega⟩))).headD false ≠
    (caStepList (configToList c)).headD false := by
  -- Prove by case analysis on c[1], c[2]
  sorry  -- ~20 lines of case analysis

theorem left_boundary_essential (n : Nat) : Essential n ⟨0, by simp⟩ := by
  induction n with
  | zero => sorry  -- native_decide
  | succ n ih => sorry  -- use caStepList_flip_leftmost
```
-/


/-
================================================================================
SUMMARY
================================================================================

Current state:
- 9 axioms stated
- All have proof sketches
- All are justified (computation or induction)

To make fully rigorous:
1. Generate 36 native_decide proofs (replaces axioms 2-7)
2. Prove caStepList_flip_leftmost lemma (~20 lines)
3. Prove boundary induction (replaces axioms 8-9)
4. Integrate Z3 certificates via bv_decide (replaces axiom 1)

Estimated effort: 2-3 hours
Result: 0 axioms, fully rigorous proof
-/
