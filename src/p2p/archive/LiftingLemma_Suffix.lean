/-
LiftingLemma_Suffix.lean - Suffix-based Lifting Lemma for Wolfram Prize 3
===========================================================================

KEY DISCOVERY: all_zeros witnesses Essential n ⟨2*n-1, _⟩ for ALL n ≥ 1.

Proof strategy:
1. suffix10(n) = [F,...,F,T,F] (true at position 2n-1 only)
2. suffix11(n) = [F,...,F,T,T] (true at positions 2n-1 and 2n)
3. caStep(suffix10(n)) = suffix11(n-1)  (computation verified)
4. caStep(suffix11(n)) = suffix11(n-1)  (fixed point pattern, shrinks)
5. rule30n(n, suffix11(n)) = true for all n ≥ 1
6. rule30n(n, all_zeros) = false (fixed point)
7. flip(all_zeros, 2n-1) = suffix10(n)
8. Therefore: Essential n ⟨2*n-1, _⟩ witnessed by all_zeros

Author: Jonathan Hill
Date: 2026-03-16
Status: DEVELOPMENT
-/

import P2p.Prize3_Complete

/-
================================================================================
SECTION 1: CORE SUFFIX CONFIGURATIONS
================================================================================
-/

/-- All-zeros configuration -/
def all_zeros (n : Nat) : Config n := fun _ => false

/-- suffix10(n): true only at position 2n-1 (second-to-last) -/
def suffix10 (n : Nat) : Config n :=
  fun i : Fin (2 * n + 1) => decide (i.val = 2 * n - 1)

/-- suffix11(n): true at positions 2n-1 and 2n (last two positions) -/
def suffix11 (n : Nat) : Config n :=
  fun i : Fin (2 * n + 1) => decide (i.val = 2 * n - 1 ∨ i.val = 2 * n)

/-
================================================================================
SECTION 2: LIST REPRESENTATIONS
================================================================================
-/

/-- Helper: list length for suffix10 -/
lemma suffix10_list_length (n : Nat) (hn : n ≥ 1) :
    (List.replicate (2 * n - 1) false ++ [true, false]).length = 2 * n + 1 := by
  simp [List.length_append, List.length_replicate]
  omega

/-- configToList of suffix10 is [F,...,F,T,F] -/
theorem configToList_suffix10 (n : Nat) (hn : n ≥ 1) :
    configToList (suffix10 n) = List.replicate (2 * n - 1) false ++ [true, false] := by
  simp only [configToList]
  apply List.ext_getElem
  · -- Lengths match
    simp [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · -- Elements match
    intro i h1 h2
    simp only [List.getElem_ofFn, suffix10]
    simp only [List.getElem_append, List.length_replicate]
    split_ifs with hi
    · -- i < 2*n-1: need decide (i = 2*n-1) = false and list[i] = false
      simp [List.getElem_replicate]
      have : i ≠ 2 * n - 1 := Nat.ne_of_lt hi
      simp [this]
    · -- i ≥ 2*n-1: i must be 2*n-1 or 2*n (since i < 2*n+1)
      push_neg at hi
      have hib : i < 2 * n + 1 := by simp [List.length_ofFn] at h1; exact h1
      -- i is either 2*n-1 or 2*n
      have : i = 2 * n - 1 ∨ i = 2 * n := by omega
      rcases this with (heq1 | heq2)
      · -- i = 2*n-1
        subst heq1
        simp
      · -- i = 2*n
        subst heq2
        have hne : 2 * n ≠ 2 * n - 1 := by omega
        simp [hne]
        have hidx : 2 * n - (2 * n - 1) = 1 := by omega
        simp [hidx]

/-- configToList of suffix11 is [F,...,F,T,T] -/
theorem configToList_suffix11 (n : Nat) (hn : n ≥ 1) :
    configToList (suffix11 n) = List.replicate (2 * n - 1) false ++ [true, true] := by
  simp only [configToList]
  apply List.ext_getElem
  · -- Lengths match
    simp [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · -- Elements match
    intro i h1 h2
    simp only [List.getElem_ofFn, suffix11]
    simp only [List.getElem_append, List.length_replicate]
    split_ifs with hi
    · -- i < 2*n-1: need decide (i = 2*n-1 ∨ i = 2*n) = false and list[i] = false
      simp [List.getElem_replicate]
      have hne1 : i ≠ 2 * n - 1 := Nat.ne_of_lt hi
      have hne2 : i ≠ 2 * n := by omega
      simp [hne1, hne2]
    · -- i ≥ 2*n-1: i must be 2*n-1 or 2*n (since i < 2*n+1)
      push_neg at hi
      have hib : i < 2 * n + 1 := by simp [List.length_ofFn] at h1; exact h1
      -- i is either 2*n-1 or 2*n
      have : i = 2 * n - 1 ∨ i = 2 * n := by omega
      rcases this with (heq1 | heq2)
      · -- i = 2*n-1: decide(i = 2*n-1 ∨ i = 2*n) = true, [true,true][0] = true
        subst heq1
        simp
      · -- i = 2*n: decide(i = 2*n-1 ∨ i = 2*n) = true, [true,true][1] = true
        subst heq2
        simp
        have hidx : 2 * n - (2 * n - 1) = 1 := by omega
        simp [hidx]

/-- configToList of all_zeros is all false -/
lemma configToList_all_zeros (n : Nat) :
    configToList (all_zeros n) = List.replicate (2 * n + 1) false := by
  exact configToList_const_false n

/-
================================================================================
SECTION 3: CAUSAL STEP LEMMAS
================================================================================
-/

/-- Helper lemma for caStepList_false_true_false using m = 2*(n-2) -/
lemma caStepList_false_true_false_helper (m : Nat) :
    caStepList (List.replicate (m + 3) false ++ [true, false]) =
    List.replicate (m + 1) false ++ [true, true] := by
  induction m with
  | zero =>
    -- caStepList [F,F,F,T,F] = [F,T,T]
    rfl
  | succ m ih =>
    calc caStepList (List.replicate (m + 1 + 3) false ++ [true, false])
        = caStepList (List.replicate (m + 4) false ++ [true, false]) := rfl
      _ = caStepList (false :: List.replicate (m + 3) false ++ [true, false]) := rfl
      _ = caStepList (false :: false :: List.replicate (m + 2) false ++ [true, false]) := rfl
      _ = rule30Local false false false :: caStepList (false :: List.replicate (m + 2) false ++ [true, false]) := rfl
      _ = false :: caStepList (List.replicate (m + 3) false ++ [true, false]) := by simp [rule30Local]; rfl
      _ = false :: (List.replicate (m + 1) false ++ [true, true]) := by rw [ih]
      _ = List.replicate (m + 2) false ++ [true, true] := rfl

/-- Helper: caStepList of [F,...,F,T,F] (length 2n+1) = [F,...,F,T,T] (length 2n-1) -/
theorem caStepList_false_true_false (n : Nat) (hn : n ≥ 2) :
    caStepList (List.replicate (2 * n - 1) false ++ [true, false]) =
    List.replicate (2 * (n - 1) - 1) false ++ [true, true] := by
  have h1 : 2 * n - 1 = (2 * (n - 2)) + 3 := by omega
  have h2 : 2 * (n - 1) - 1 = (2 * (n - 2)) + 1 := by omega
  rw [h1, h2]
  exact caStepList_false_true_false_helper (2 * (n - 2))
  -- Computation verified for n=2..10:
  -- n=2: caStepList [F,F,F,T,F] = [F,T,T], RHS = [F,T,T] ✓
  -- n=3: caStepList [F,F,F,F,F,T,F] = [F,F,F,T,T], RHS = [F,F,F,T,T] ✓
  -- Pattern: rule30(F,F,F) = F (leading cells), rule30(F,F,T) = T, rule30(F,T,F) = T
  -- NOTE: For n=1 this axiom does NOT hold (RHS would be [T,T] but LHS is [T])
  -- The n=1 case is handled separately with native_decide

/-- caStepList of suffix10 yields suffix11 (one level down) -/
theorem caStepList_suffix10 (n : Nat) (hn : n ≥ 1) :
    caStepList (configToList (suffix10 n)) = configToList (suffix11 (n - 1)) := by
  rw [configToList_suffix10 n hn]
  by_cases h : n - 1 ≥ 1
  · -- n ≥ 2: use axiom caStepList_false_true_false
    rw [configToList_suffix11 (n - 1) h]
    have hn2 : n ≥ 2 := by omega
    exact caStepList_false_true_false n hn2
  · -- n = 1 case
    have : n = 1 := by omega
    subst this
    -- suffix10(1) = [F,T,F], suffix11(0) = [T]
    -- caStepList [F,T,F] = [rule30Local F T F] = [T]
    -- configToList (suffix11 0) = [T]
    native_decide

/-- Helper lemma for caStepList_false_true_true using m = 2*(n-2) -/
lemma caStepList_false_true_true_helper (m : Nat) :
    caStepList (List.replicate (m + 3) false ++ [true, true]) =
    List.replicate (m + 1) false ++ [true, true] := by
  induction m with
  | zero =>
    -- caStepList [F,F,F,T,T] = [F,T,T]
    rfl
  | succ m ih =>
    calc caStepList (List.replicate (m + 1 + 3) false ++ [true, true])
        = caStepList (List.replicate (m + 4) false ++ [true, true]) := rfl
      _ = caStepList (false :: List.replicate (m + 3) false ++ [true, true]) := rfl
      _ = caStepList (false :: false :: List.replicate (m + 2) false ++ [true, true]) := rfl
      _ = rule30Local false false false :: caStepList (false :: List.replicate (m + 2) false ++ [true, true]) := rfl
      _ = false :: caStepList (List.replicate (m + 3) false ++ [true, true]) := by simp [rule30Local]; rfl
      _ = false :: (List.replicate (m + 1) false ++ [true, true]) := by rw [ih]
      _ = List.replicate (m + 2) false ++ [true, true] := rfl

/-- Helper: caStepList of [F,...,F,T,T] (length 2n+1) = [F,...,F,T,T] (length 2n-1) -/
theorem caStepList_false_true_true (n : Nat) (hn : n ≥ 2) :
    caStepList (List.replicate (2 * n - 1) false ++ [true, true]) =
    List.replicate (2 * (n - 1) - 1) false ++ [true, true] := by
  have h1 : 2 * n - 1 = (2 * (n - 2)) + 3 := by omega
  have h2 : 2 * (n - 1) - 1 = (2 * (n - 2)) + 1 := by omega
  rw [h1, h2]
  exact caStepList_false_true_true_helper (2 * (n - 2))

/-- caStepList of suffix11 yields suffix11 (one level down) - fixed point pattern -/
theorem caStepList_suffix11 (n : Nat) (hn : n ≥ 1) :
    caStepList (configToList (suffix11 n)) = configToList (suffix11 (n - 1)) := by
  rw [configToList_suffix11 n hn]
  by_cases h : n - 1 ≥ 1
  · -- n ≥ 2: use axiom caStepList_false_true_true
    rw [configToList_suffix11 (n - 1) h]
    have hn2 : n ≥ 2 := by omega
    exact caStepList_false_true_true n hn2
  · -- n = 1 case: suffix11(1) = [F,T,T], caStepList [F,T,T] = [T]
    -- configToList (suffix11 0) = [T]
    have : n = 1 := by omega
    subst this
    native_decide

/-
================================================================================
SECTION 4: EVOLUTION LEMMAS
================================================================================
-/

/-- Evolving all-zeros gives [false] -/
theorem rule30n_all_zeros (n : Nat) :
    rule30n n (all_zeros n) = false := by
  simp only [rule30n]
  unfold all_zeros
  rw [configToList_const_false]
  rw [caEvolve_all_false]
  decide

/-- Base case: rule30n(1, suffix11(1)) = true -/
theorem rule30n_suffix11_base :
    rule30n 1 (suffix11 1) = true := by
  -- suffix11(1) = [F,T,T] on config [0,1,2]
  -- caStep([F,T,T]) = [rule30(F,T,T)] = [F XOR (T OR T)] = [F XOR T] = [T]
  -- So rule30n(1, ...) = [T].getD 0 false = T
  native_decide

/-- Inductive step: if rule30n(n, suffix11(n)) = true, then rule30n(n+1, suffix11(n+1)) = true -/
theorem rule30n_suffix11_succ (n : Nat) (hn : n ≥ 1)
    (ih : rule30n n (suffix11 n) = true) :
    rule30n (n + 1) (suffix11 (n + 1)) = true := by
  -- rule30n (n+1) c = (caEvolve (n+1) (configToList c)).getD 0 false
  --                 = (caEvolve n (caStepList (configToList c))).getD 0 false
  simp only [rule30n]
  rw [caEvolve_succ]
  have h1 : n + 1 ≥ 1 := by omega
  rw [caStepList_suffix11 (n + 1) h1]
  -- Now need: (caEvolve n (configToList (suffix11 n))).getD 0 false = true
  -- But that's exactly rule30n n (suffix11 n) = true, which is ih
  have : n + 1 - 1 = n := by omega
  rw [this]
  exact ih

/-- Main theorem: rule30n(n, suffix11(n)) = true for all n ≥ 1 -/
theorem rule30n_suffix11 (n : Nat) (hn : n ≥ 1) :
    rule30n n (suffix11 n) = true := by
  -- Induction on n
  induction n with
  | zero => omega  -- contradicts hn
  | succ n ih =>
    by_cases h : n = 0
    · -- Base case: n+1 = 1
      subst h
      exact rule30n_suffix11_base
    · -- Inductive case: n+1 ≥ 2, so n ≥ 1
      have hn' : n ≥ 1 := by omega
      have ih' := ih hn'
      exact rule30n_suffix11_succ n hn' ih'

/-- rule30n(n, suffix10(n)) = true for all n ≥ 1 -/
theorem rule30n_suffix10 (n : Nat) (hn : n ≥ 1) :
    rule30n n (suffix10 n) = true := by
  -- suffix10 evolves to suffix11 in one step
  simp only [rule30n]
  match n with
  | 0 => omega  -- contradicts hn
  | n' + 1 =>
    rw [caEvolve_succ]
    have h1 : n' + 1 ≥ 1 := by omega
    rw [caStepList_suffix10 (n' + 1) h1]
    have : n' + 1 - 1 = n' := by omega
    rw [this]
    -- Now: (caEvolve n' (configToList (suffix11 n'))).getD 0 false = true
    by_cases h : n' ≥ 1
    · -- n' ≥ 1: use rule30n_suffix11
      have : (caEvolve n' (configToList (suffix11 n'))).getD 0 false =
             rule30n n' (suffix11 n') := rfl
      rw [this]
      exact rule30n_suffix11 n' h
    · -- n' = 0: caEvolve 0 x = x, suffix11(0) = [T]
      have : n' = 0 := by omega
      subst this
      native_decide

/-
================================================================================
SECTION 5: FLIP RELATIONSHIP
================================================================================
-/

/-- Flipping all_zeros at position 2n-1 gives suffix10 -/
theorem flip_all_zeros_eq_suffix10 (n : Nat) (hn : n ≥ 1) :
    flipCell (all_zeros n) ⟨2 * n - 1, by omega⟩ = suffix10 n := by
  -- Both are functions, so prove extensionally
  funext i
  simp only [flipCell, all_zeros, suffix10]
  split_ifs with h
  · -- i = ⟨2*n-1, _⟩, so i.val = 2*n-1
    have : i.val = 2 * n - 1 := by
      have := Fin.ext_iff.mp h
      simp at this
      exact this
    simp [this]
  · -- i ≠ ⟨2*n-1, _⟩, so i.val ≠ 2*n-1
    have hne : i.val ≠ 2 * n - 1 := by
      intro heq
      apply h
      ext
      exact heq
    -- Goal: false = decide (i.val = 2*n-1)
    have : decide (i.val = 2 * n - 1) = false := decide_eq_false hne
    exact this.symm

/-
================================================================================
SECTION 6: MAIN THEOREM - SECOND-TO-LAST POSITION IS ESSENTIAL
================================================================================
-/

/-- The second-to-last position (2n-1) is essential for all n ≥ 1.
    Witnessed by all_zeros configuration. -/
theorem essential_second_to_last (n : Nat) (hn : n ≥ 1) :
    Essential n ⟨2 * n - 1, by omega⟩ := by
  -- Witness: all_zeros
  use all_zeros n
  -- Show: rule30n n (all_zeros n) ≠ rule30n n (flipCell (all_zeros n) ⟨2*n-1, _⟩)
  -- LHS: rule30n n (all_zeros n) = false
  have h_zeros : rule30n n (all_zeros n) = false := rule30n_all_zeros n
  -- RHS: flipCell (all_zeros n) ⟨2*n-1, _⟩ = suffix10 n
  have h_flip : flipCell (all_zeros n) ⟨2 * n - 1, by omega⟩ = suffix10 n :=
    flip_all_zeros_eq_suffix10 n hn
  rw [h_zeros, h_flip]
  -- Need: false ≠ rule30n n (suffix10 n)
  have h_suffix10 : rule30n n (suffix10 n) = true := rule30n_suffix10 n hn
  rw [h_suffix10]
  decide

/-
================================================================================
SUMMARY
================================================================================

This file proves that position 2n-1 (second-to-last) is essential for all n ≥ 1,
witnessed by the all-zeros configuration.

STATUS (2026-03-16 UPDATE):
  ✓ COMPILES with 0 errors, 0 sorries
  ✓ MAIN THEOREM `essential_second_to_last` PROVED (modulo computational axioms)
  ✓ ALL 3 SORRIES CLOSED using native_decide

AXIOMS (4 computational facts - all verified computationally):
  1. configToList_suffix10 (n ≥ 1):       [F,...,F,T,F] representation
  2. configToList_suffix11 (n ≥ 1):       [F,...,F,T,T] representation
  3. caStepList_false_true_false (n ≥ 2): caStep([F,...,F,T,F]) = [F,...,F,T,T]
  4. caStepList_false_true_true (n ≥ 2):  caStep([F,...,F,T,T]) = [F,...,F,T,T]

  IMPORTANT: Axioms 3 and 4 require n ≥ 2 (not n ≥ 1) because for n=1, the
  suffix11(0) configuration has only 1 cell, breaking the list formula pattern.
  The n=1 base cases are handled separately via native_decide.

  All axioms verified computationally for n=2..10 (see TestCa.lean).

SORRIES RESOLVED:
  ✓ caStepList_suffix10 (n=1):  PROVED via native_decide
  ✓ caStepList_suffix11 (n=1):  PROVED via native_decide
  ✓ rule30n_suffix10 (n'=0):    PROVED via native_decide

PROVED THEOREMS:
  ✓ rule30n_all_zeros:              all-zeros is a fixed point
  ✓ flip_all_zeros_eq_suffix10:     flipping all-zeros at 2n-1 gives suffix10
  ✓ rule30n_suffix11_base:          rule30n(1, suffix11(1)) = true (via native_decide)
  ✓ rule30n_suffix11_succ:          inductive step for suffix11
  ✓ rule30n_suffix11:               rule30n(n, suffix11(n)) = true for all n ≥ 1
  ✓ rule30n_suffix10:               rule30n(n, suffix10(n)) = true for all n ≥ 1
  ✓ essential_second_to_last:       position 2n-1 is essential (MAIN RESULT)

KEY DISCOVERY:
  The all-zeros configuration witnesses Essential n ⟨2*n-1, _⟩ for ALL n ≥ 1.
  This is because:
    - rule30n n (all_zeros n) = false (fixed point)
    - flip(all_zeros, 2n-1) = suffix10(n)
    - rule30n n (suffix10 n) = true (proved by induction via suffix11 pattern)
    - Therefore Essential n ⟨2*n-1, _⟩ with witness all_zeros

SIGNIFICANCE:
  This provides an alternative proof that the second-to-last position is always
  essential, complementing the lifting lemma approach. The suffix pattern provides
  an explicit witness configuration (all-zeros) that works uniformly for all n.

================================================================================
-/
