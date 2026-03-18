/-
  LiftingLemma_Period3.lean
  
  Proves Essential(n, 2n-2) for all n ≥ 2 using a universal witness.
  
  The witness pattern:
  - For n=2: Config with single True at position 3 (k+1)
  - For n≥3: Config with single True at position 1
  
  This is called "period-3" because it relates to the period-3 behavior
  observed in suffix analysis for position k=2n-2.
-/

import P2p.Prize3_Complete
import P2p.LiftingLemma_LeftPermutive

namespace Rule30

/-- Witness config for n=2, k=2: single True at position 3 -/
def witness_n2 : Config 2 :=
  fun i => i.val == 3

/-- Witness config for n≥3: single True at position 1 -/
def witnessPosition1 (n : Nat) : Config n :=
  fun i => i.val == 1

/-
================================================================================
SECTION: HELPER LEMMAS FOR 2-STEP PERIODICITY
================================================================================
-/

/-- configToList of witnessPosition1 n = [false, true, false, ..., false] (2n+1 cells) -/
lemma configToList_witnessPosition1 (n : Nat) (hn : n ≥ 1) :
    configToList (witnessPosition1 n) = [false, true] ++ List.replicate (2 * n - 1) false := by
  unfold configToList witnessPosition1
  apply List.ext_getElem
  · -- Lengths match: List.ofFn has length 2*n+1, RHS has length 2 + (2*n-1) = 2*n+1
    simp [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · -- Elements match
    intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_append, List.length_cons, List.length_nil,
               Nat.add_zero, List.length_replicate]
    -- Split on whether i < 2
    by_cases hi0 : i = 0
    · subst hi0
      simp
    · by_cases hi1 : i = 1
      · subst hi1
        simp
      · -- i ≥ 2, so we're in the replicate part
        have hi_ge : i ≥ 2 := by omega
        simp only [show ¬(i < 2) by omega, ↓reduceIte]
        simp [List.getElem_replicate]
        intro heq
        omega

/-- Helper: caStepList unfolds on 3+ element list -/
lemma caStepList_cons3 (a b c : Bool) (rest : List Bool) :
    caStepList (a :: b :: c :: rest) = rule30Local a b c :: caStepList (b :: c :: rest) := rfl

/-- Helper: List.replicate (n+2) false = false :: false :: replicate n false -/
lemma replicate_succ2 (n : Nat) :
    List.replicate (n + 2) false = false :: false :: List.replicate n false := by
  rw [List.replicate_succ, List.replicate_succ]

/-- Helper: [a, b] ++ (c :: d :: rest) = [a, b, c, d] ++ rest -/
lemma append_pair_cons2 {α : Type*} (a b c d : α) (rest : List α) :
    [a, b] ++ (c :: d :: rest) = a :: b :: c :: d :: rest := rfl

/-- caStepList on [false, true, false, false, ..., false] (at least 4 cells) gives [true, true, ...] -/
lemma caStepList_false_true_false (n : Nat) :
    caStepList ([false, true] ++ List.replicate (n + 2) false) =
    [true, true] ++ List.replicate n false := by
  -- [false, true, false, false, ..., false] with n+4 total cells
  -- Use native_decide for base cases and small n
  match n with
  | 0 => native_decide
  | 1 => native_decide
  | 2 => native_decide
  | 3 => native_decide
  | 4 => native_decide
  | 5 => native_decide
  | 6 => native_decide
  | 7 => native_decide
  | 8 => native_decide
  | 9 => native_decide
  | 10 => native_decide
  | n + 11 =>
    conv_lhs => rw [replicate_succ2 (n + 11)]
    rw [append_pair_cons2]
    rw [caStepList_cons3, caStepList_cons3]
    have hb1 : rule30Local false true false = true := by decide
    have hb2 : rule30Local true false false = true := by decide
    rw [hb1, hb2]
    conv_lhs =>
      arg 2; arg 2
      rw [← List.replicate_succ, ← List.replicate_succ]
    rw [caStepList_all_false]
    rfl

/-- caStepList on [true, true, false, false, ..., false] (at least 4 cells) gives [false, true, ...] -/
lemma caStepList_true_true_false (n : Nat) :
    caStepList ([true, true] ++ List.replicate (n + 2) false) =
    [false, true] ++ List.replicate n false := by
  match n with
  | 0 => native_decide
  | 1 => native_decide
  | 2 => native_decide
  | 3 => native_decide
  | 4 => native_decide
  | 5 => native_decide
  | 6 => native_decide
  | 7 => native_decide
  | 8 => native_decide
  | 9 => native_decide
  | 10 => native_decide
  | n + 11 =>
    conv_lhs => rw [replicate_succ2 (n + 11)]
    rw [append_pair_cons2]
    rw [caStepList_cons3, caStepList_cons3]
    have hb1 : rule30Local true true false = false := by decide
    have hb2 : rule30Local true false false = true := by decide
    rw [hb1, hb2]
    conv_lhs =>
      arg 2; arg 2
      rw [← List.replicate_succ, ← List.replicate_succ]
    rw [caStepList_all_false]
    rfl

/-
================================================================================
SECTION: 2-STEP PERIODICITY OF witnessPosition1
================================================================================
-/

/-- caEvolve commutes with caStepList: n steps then 1 step = 1 step then n steps -/
lemma caEvolve_step_comm (n : Nat) (l : List Bool) :
    caEvolve n (caStepList l) = caStepList (caEvolve n l) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    simp only [caEvolve]
    exact ih (caStepList l)

/-- caEvolve is additive: (m+n) steps = n steps then m steps -/
lemma caEvolve_add (m n : Nat) (l : List Bool) :
    caEvolve (m + n) l = caEvolve m (caEvolve n l) := by
  induction m generalizing l with
  | zero => simp [caEvolve]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [caEvolve]
    rw [← caEvolve_step_comm n l]
    exact ih (caStepList l)

/-- 2-step periodicity: evolving witnessPosition1 (n+2) by 2 steps gives witnessPosition1 n -/
lemma witnessPosition1_two_steps (n : Nat) (hn : n ≥ 1) :
    caEvolve 2 (configToList (witnessPosition1 (n + 2))) = configToList (witnessPosition1 n) := by
  simp only [caEvolve]
  rw [configToList_witnessPosition1 (n + 2) (by omega)]
  have h1 : 2 * (n + 2) - 1 = (2 * n + 1) + 2 := by omega
  rw [h1, caStepList_false_true_false (2 * n + 1)]
  have h2 : 2 * n + 1 = (2 * n - 1) + 2 := by omega
  rw [h2, caStepList_true_true_false (2 * n - 1)]
  rw [← configToList_witnessPosition1 n hn]

/-- Consequence: rule30n output of witnessPosition1 is the same at n+2 and n -/
lemma rule30n_witnessPosition1_step (n : Nat) (hn : n ≥ 1) :
    rule30n (n + 2) (witnessPosition1 (n + 2)) = rule30n n (witnessPosition1 n) := by
  unfold rule30n
  rw [caEvolve_add n 2 (configToList (witnessPosition1 (n + 2)))]
  rw [witnessPosition1_two_steps n hn]

/-- Essential(2, 2) via native_decide -/
theorem essential_2_2 : Essential 2 ⟨2, by omega⟩ := by
  unfold Essential
  use witness_n2
  native_decide

/-- Essential(3, 4) via native_decide -/
theorem essential_3_4 : Essential 3 ⟨4, by omega⟩ := by
  unfold Essential
  use witnessPosition1 3
  native_decide

/-- Essential(4, 6) via native_decide -/
theorem essential_4_6 : Essential 4 ⟨6, by omega⟩ := by
  unfold Essential
  use witnessPosition1 4
  native_decide

/-- Essential(5, 8) via native_decide -/
theorem essential_5_8 : Essential 5 ⟨8, by omega⟩ := by
  unfold Essential
  use witnessPosition1 5
  native_decide

/--
  General theorem: For all n ≥ 2, Essential(n, 2n-2).

  Proof: write n = n'+1. Position 2n-2 = 2n'. Witness = delta at last position 2n'+2.
  - rule30n (n'+1) (delta_{2n'+2}) = true          [rule30n_deltaEvenRight (n'+1)]
  - flipCell(delta_{2n'+2}, 2n') = two_spike{2n', 2n'+2} [flipCell_deltaEvenRight_penultimate n']
  - rule30n (n'+1) (two_spike{2n', 2n'+2}) = false  [rule30n_twoSpikeEvenRight n']
  Hence true ≠ false, giving sensitivity at position 2n'.
-/
theorem essential_k2n2 (n : Nat) (hn : n ≥ 2) :
    Essential n ⟨2*n - 2, by omega⟩ := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  -- n = n'+1, hn : n'+1 ≥ 2, so n' ≥ 1. Position 2*(n'+1)-2 = 2*n'.
  -- The Fin position ⟨2*(n'+1)-2, _⟩ = ⟨2*n', _⟩ as a Fin value.
  -- The Fin position 2*(n'+1)-2 = 2*n' in Nat arithmetic
  have hlt : 2 * n' < 2 * (n' + 1) + 1 := by omega
  have harith : 2 * (n' + 1) - 2 = 2 * n' := by omega
  have hfin_eq : (⟨2 * (n' + 1) - 2, by omega⟩ : Fin (2 * (n' + 1) + 1)) =
      ⟨2 * n', hlt⟩ := Fin.ext harith
  rw [hfin_eq]
  -- Now the goal is: Essential (n'+1) ⟨2*n', _⟩
  -- Witness: delta at last even position 2*(n'+1)
  let witness : Config (n' + 1) := fun k => decide (k.val = 2 * (n' + 1))
  refine ⟨witness, ?_⟩
  -- Step 1: rule30n (n'+1) witness = true
  have h_true : rule30n (n' + 1) witness = true := rule30n_deltaEvenRight (n' + 1)
  -- Step 2: flipCell witness ⟨2*n', _⟩ = two_spike{2n', 2n'+2}
  have hflip : flipCell witness ⟨2 * n', by omega⟩ =
      fun k : Fin (2 * (n' + 1) + 1) => decide (k.val = 2 * n' ∨ k.val = 2 * n' + 2) :=
    flipCell_deltaEvenRight_penultimate n'
  -- Step 3: rule30n of the flipped config = false
  have h_false : rule30n (n' + 1) (flipCell witness ⟨2 * n', by omega⟩) = false := by
    rw [hflip]
    exact rule30n_twoSpikeEvenRight n'
  -- Conclude: true ≠ false
  rw [h_true, h_false]
  decide

/-- Alternative statement with explicit k -/
theorem essential_second_from_right (n : Nat) (hn : n ≥ 2) :
  let k := 2 * n - 2
  have hk : k < 2 * n + 1 := by omega
  Essential n ⟨k, hk⟩ := by
  exact essential_k2n2 n hn

end Rule30
