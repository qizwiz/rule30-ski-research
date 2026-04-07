/-
LiftingLemma_AllOnes.lean
=========================
Alternative approach to the lifting lemma via the all-ones / all-zeros observation.

KEY INSIGHT (sidesteps the k+1 obstruction):
  In the standard lifting attempt, flipping position k+1 in an arbitrary config c
  unavoidably changes caStep at both position k (wanted) AND k+1 (left-permutive).
  This is why all 7+ previous attempts failed.

  With all_ones as the preimage config:
    caStep(all_ones_{n+1}) = all_zeros_n      [since rule30Local(1,1,1) = 1 XOR 1 = 0]

    For position j with j.val ≤ 2n, flipping j in all_ones_{n+1} changes ONLY caStep[j]:
      - caStep[j-2]: rule30Local(1,1,0) = 1 XOR (1 OR 0) = 0  [UNCHANGED — OR absorbs right flip]
      - caStep[j-1]: rule30Local(1,0,1) = 1 XOR (0 OR 1) = 0  [UNCHANGED — OR absorbs middle flip]
      - caStep[j]:   rule30Local(0,1,1) = 0 XOR (1 OR 1) = 1  [CHANGES — left-permutive]
    (positions j = 2n+1 and j = 2n+2 have no caStep[j], so flip propagates differently)

  Therefore for j.val ≤ 2n:
    caStep(flipCell(all_ones_{n+1}, j)) = flipCell(all_zeros_n, j)

  Consequence:
    all_zeros_n witnesses Essential(n, j) → all_ones_{n+1} witnesses Essential(n+1, j)
    (same position j, not shifted)

SCOPE AND LIMITATIONS:
  - Covers positions j.val = 0..2n at level n+1 (where caStep[j] exists)
  - Only applies when all_zeros_n specifically witnesses Essential(n, j)
  - Computationally: all_zeros does NOT witness all positions at all n
    (example: position 1 at n=2 not witnessed by all_zeros — verified by native_decide)
  - Therefore NOT a complete proof of the general lifting lemma — but a new structural tool

INDEX NOTE: In the axiom, n refers to the LOWER level. allOnes (n+1) has 2n+3 cells.
  After caStep: 2n+1 cells = Config n. Positions j in the INPUT (level n+1) with j.val ≤ 2n
  have a valid corresponding OUTPUT position j.val in level n (since j.val < 2n+1).

STATUS: Algebraic identities proved via decide.
        caStepList_allOnes_eq_allZeros_list PROVED via induction (2026-03-14).
        Only caStepList_flip_allOnes remains axiomatized.
-/

import P2p.Prize3_Complete

/-
================================================================================
SECTION 1: CONSTANT CONFIGURATIONS
================================================================================
-/

/-- Configuration with all cells set to true -/
def allOnes (n : Nat) : Config n := fun _ => true

/-- Configuration with all cells set to false -/
def allZeros (n : Nat) : Config n := fun _ => false

/-
================================================================================
SECTION 2: CORE ALGEBRAIC IDENTITIES (all proved via decide)
================================================================================
-/

/-- rule30(1,1,1) = 0: when all three inputs are true, output is false -/
lemma rule30Local_ones_ones_ones : rule30Local true true true = false := by decide

/-- rule30(0,1,1) = 1: flipping left input always changes output (left-permutive) -/
lemma rule30Local_zero_one_one : rule30Local false true true = true := by decide

/-- rule30(1,0,1) = 0: flipping middle input is absorbed by OR when right=1 -/
lemma rule30Local_one_zero_one : rule30Local true false true = false := by decide

/-- rule30(1,1,0) = 0: flipping right input is absorbed by OR when middle=1 -/
lemma rule30Local_one_one_zero : rule30Local true true false = false := by decide

/-
================================================================================
SECTION 3: configToList IDENTITIES
================================================================================
-/

/-- configToList of allOnes n is a list of (2n+1) trues -/
lemma configToList_allOnes (n : Nat) :
    configToList (allOnes n) = List.replicate (2 * n + 1) true := by
  unfold configToList allOnes
  exact List.ofFn_const (2 * n + 1) true

/-- configToList of allZeros n is a list of (2n+1) falses -/
lemma configToList_allZeros (n : Nat) :
    configToList (allZeros n) = List.replicate (2 * n + 1) false := by
  unfold configToList allZeros
  exact List.ofFn_const (2 * n + 1) false

/-
================================================================================
SECTION 4: caStepList IDENTITIES

INDEX CONVENTION: In the theorems below, n refers to the OUTPUT level.
  - Input config: allOnes (n+1), which has 2*(n+1)+1 = 2n+3 cells
  - Output list: allZeros n, which has 2*n+1 cells
  - Valid input positions j with j.val ≤ 2n map to valid output positions

STATUS: ALL THEOREMS PROVED (2026-03-17 UPDATE):
        - caStepList_allOnes_eq_allZeros_list: PROVED via induction
        - caStepList_flip_allOnes: PROVED via caStepList_prefix_flip
        - caStepList_prefix_flip: PROVED via induction on i
        No custom axioms used (only standard Lean axioms: propext, Classical.choice, Quot.sound)
================================================================================
-/

/-- Core lemma: caStepList of (k+3) trues gives (k+1) falses.
    Proof by induction on k. -/
lemma caStepList_allTrue (k : Nat) :
    caStepList (List.replicate (k + 3) true) = List.replicate (k + 1) false := by
  induction k with
  | zero =>
    -- Base case: k=0, caStepList [true, true, true] = [false]
    decide
  | succ k ih =>
    -- Inductive step: k+1
    -- Goal: caStepList (replicate (k+4) true) = replicate (k+2) false
    -- Expand (k+4) trues as true :: replicate (k+3) true
    rw [show k + 1 + 3 = k + 4 from by omega]
    rw [show k + 1 + 1 = k + 2 from by omega]
    -- Rewrite replicate (k+4) true as true :: true :: true :: replicate (k+1) true
    have h_rep : List.replicate (k + 4) true =
                 true :: true :: true :: List.replicate (k + 1) true := by
      rw [List.replicate_succ, List.replicate_succ, List.replicate_succ]
    rw [h_rep]
    -- Apply caStepList definition
    simp only [caStepList, rule30Local_ones_ones_ones]
    -- Now goal is: false :: caStepList (true :: true :: replicate (k+1) true) = replicate (k+2) false
    -- Collapse back: true :: true :: replicate (k+1) true = replicate (k+3) true
    have h_collapse : true :: true :: List.replicate (k + 1) true = List.replicate (k + 3) true := by
      rw [← List.replicate_succ, ← List.replicate_succ]
    rw [h_collapse, ih]
    -- Now: false :: replicate (k+1) false = replicate (k+2) false
    rw [← List.replicate_succ]

/-- Variant with different offset (k+2 trues gives k falses) -/
lemma caStepList_allTrue2 (k : Nat) :
    caStepList (List.replicate (k + 2) true) = List.replicate k false := by
  cases k with
  | zero =>
    -- k=0: replicate 2 true has length < 3, so caStepList returns []
    decide
  | succ k =>
    -- k ≥ 1: k+2 = (k-1)+3, so use caStepList_allTrue with (k-1)
    have : k + 1 + 2 = k + 3 := by omega
    rw [this]
    have h := caStepList_allTrue k
    have : k + 3 = k + 3 := rfl
    have : k + 1 = k + 1 := rfl
    exact h

/-- caStepList of all-true list of length 2n+3 gives all-false list of length 2n+1.
    Proof: direct application of caStepList_allTrue with k = 2n. -/
theorem caStepList_allOnes_eq_allZeros_list (n : Nat) :
    caStepList (List.replicate (2 * (n + 1) + 1) true) = List.replicate (2 * n + 1) false := by
  have h1 : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
  have h2 : 2 * n + 1 = 2 * n + 1 := rfl
  rw [h1, h2]
  exact caStepList_allTrue (2 * n)

/-
================================================================================
SECTION 4.5: HELPER LEMMAS FOR caStepList_flip_allOnes
================================================================================
-/

/-- Explicit equation lemma for 3-cons case of caStepList (holds by rfl) -/
private lemma caStepList_cons3 (p q r : Bool) (rest : List Bool) :
    caStepList (p :: q :: r :: rest) = rule30Local p q r :: caStepList (q :: r :: rest) := rfl

/-- Helper: rule30Local(true, true, x) = false for all x -/
private lemma rule30Local_true_true (x : Bool) : rule30Local true true x = false := by
  cases x <;> decide

/-- Peeling lemma: if we have true-prefix before the flip, caStepList gives false-prefix. -/
private lemma caStepList_cons_true_prefix (i k : Nat) :
    caStepList (true :: List.replicate i true ++ [false] ++ List.replicate (k + 2) true) =
    false :: List.replicate i false ++ [true] ++ List.replicate k false := by
  induction i with
  | zero =>
    simp only [List.replicate_zero, List.singleton_append]
    -- Goal: caStepList(T :: F :: replicate (k+2) true) = F :: T :: replicate k false
    -- Expose 3rd element (head of replicate (k+2) true = T)
    rw [show List.replicate (k + 2) true = true :: List.replicate (k + 1) true from by
      rw [List.replicate_succ]]
    change false :: caStepList (false :: true :: List.replicate (k + 1) true) = false :: true :: List.replicate k false
    congr 1
    -- Need: caStepList(F :: T :: replicate (k+1) true) = T :: replicate k false
    -- Expose third element: replicate (k+1) true = T :: replicate k true
    rw [show List.replicate (k + 1) true = true :: List.replicate k true from by
      rw [List.replicate_succ]]
    change true :: caStepList (true :: true :: List.replicate k true) = true :: List.replicate k false
    congr 1
    -- Goal: caStepList (T :: T :: replicate k true) = replicate k false
    -- Need to convert to form for caStepList_allTrue2: caStepList (replicate (k+2) true) = replicate k false
    conv_lhs => rw [show true :: true :: List.replicate k true = List.replicate (k + 2) true from by
      rw [List.replicate_succ, List.replicate_succ]]
    exact caStepList_allTrue2 k
  | succ i' ih =>
    rw [List.replicate_succ, List.cons_append]
    -- Goal: caStepList(T :: T :: (replicate i' true ++ [F] ++ replicate (k+2) true)) = F :: replicate (i'+1) false ++ T :: replicate k false
    -- Simplify LHS
    simp only [List.cons_append]
    -- Key: expose the 3rd element using set + cases
    set L := List.replicate i' true ++ [false] ++ List.replicate (k + 2) true with hL_def
    have hL_ne : L ≠ [] := by
      rw [hL_def]
      intro h
      simp at h
    cases hL : L with
    | nil => exact absurd hL hL_ne
    | cons c rest =>
      -- Now: caStepList(T :: T :: c :: rest) = F :: replicate (i'+1) false ++ T :: replicate k false
      -- Use change to expose rule30Local true true c = false
      change false :: caStepList (true :: c :: rest) = false :: List.replicate (i' + 1) false ++ [true] ++ List.replicate k false
      congr 1
      -- Goal: caStepList(T :: c :: rest) = replicate (i'+1) false ++ T :: replicate k false
      -- Expand RHS: replicate (i'+1) false = F :: replicate i' false
      rw [show List.replicate (i' + 1) false = false :: List.replicate i' false from by
        rw [List.replicate_succ]]
      -- Goal: caStepList(T :: c :: rest) = F :: replicate i' false ++ T :: replicate k false
      -- Rewrite c :: rest back to L using hL
      rw [← hL]
      -- Now: caStepList(T :: L) = F :: replicate i' false ++ T :: replicate k false
      rw [hL_def]
      -- = caStepList(T :: replicate i' true ++ [F] ++ replicate (k+2) true) = F :: replicate i' false ++ T :: replicate k false
      exact ih

/-- Main structural lemma: i-true-prefix before false, becomes i-false-prefix after flip. -/
private lemma caStepList_prefix_flip (i k : Nat) :
    caStepList (List.replicate i true ++ [false] ++ List.replicate (k + 2) true) =
    List.replicate i false ++ [true] ++ List.replicate k false := by
  cases i with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    -- caStepList(F :: replicate (k+2) true) = T :: replicate k false
    -- Expose first 3 elements
    rw [show List.replicate (k + 2) true = true :: true :: List.replicate k true from by
      simp [List.replicate_succ]]
    change true :: caStepList (true :: true :: List.replicate k true) = true :: List.replicate k false
    congr 1
    rw [show true :: true :: List.replicate k true = List.replicate (k + 2) true from by
      simp [List.replicate_succ]]
    exact caStepList_allTrue2 k
  | succ i' =>
    rw [List.replicate_succ, List.cons_append]
    -- caStepList(T :: replicate i' true ++ [F] ++ ...) = F :: replicate i' false ++ ...
    exact caStepList_cons_true_prefix i' k

/-- configToList of flipCell for constant true config.
    Note: j : Fin (2*n+1), so the config has size n. -/
private lemma configToList_flipCell_true (n : Nat) (j : Fin (2 * n + 1)) :
    configToList (flipCell (fun (_ : Fin (2 * n + 1)) => true) j) =
    List.replicate j.val true ++ [false] ++ List.replicate (2 * n + 1 - j.val - 1) true := by
  unfold configToList flipCell
  simp only [Bool.not_true]
  apply List.ext_getElem
  · simp [List.length_ofFn, List.length_append, List.length_replicate]
    have := j.isLt
    omega
  · intro p hp _
    simp only [List.getElem_ofFn]
    have hj : j.val < 2 * n + 1 := j.isLt
    have hp' : p < 2 * n + 1 := by simpa using hp
    rcases Nat.lt_trichotomy p j.val with hp_lt | hp_eq | hp_gt
    · -- p < j.val: in left replicate
      have hne : (⟨p, hp'⟩ : Fin (2 * n + 1)) ≠ j := by simp [Fin.ext_iff]; omega
      simp only [if_neg hne, List.getElem_append, List.length_replicate, List.length_append]
      simp [hp_lt, List.getElem_replicate]
    · -- p = j.val: the singleton
      have heq : (⟨p, hp'⟩ : Fin (2 * n + 1)) = j := by simp [hp_eq]
      simp only [if_pos heq, List.getElem_append, List.length_replicate, List.length_append]
      subst hp_eq
      simp [Nat.sub_self]
    · -- p > j.val: in right replicate
      have hne : (⟨p, hp'⟩ : Fin (2 * n + 1)) ≠ j := by simp [Fin.ext_iff]; omega
      simp only [if_neg hne, List.getElem_append, List.length_replicate, List.length_append]
      have hjp : j.val + 1 ≤ p := Nat.succ_le_of_lt hp_gt
      simp [hp_gt, hjp, List.getElem_replicate, Nat.not_lt_of_lt]

/-- configToList of flipCell for constant false config.
    Note: j : Fin (2*n+1), so the config has size n. -/
private lemma configToList_flipCell_false (n : Nat) (j : Fin (2 * n + 1)) :
    configToList (flipCell (fun (_ : Fin (2 * n + 1)) => false) j) =
    List.replicate j.val false ++ [true] ++ List.replicate (2 * n + 1 - j.val - 1) false := by
  unfold configToList flipCell
  simp only [Bool.not_false]
  apply List.ext_getElem
  · simp [List.length_ofFn, List.length_append, List.length_replicate]
    have := j.isLt
    omega
  · intro p hp _
    simp only [List.getElem_ofFn]
    have hj : j.val < 2 * n + 1 := j.isLt
    have hp' : p < 2 * n + 1 := by simpa using hp
    rcases Nat.lt_trichotomy p j.val with hp_lt | hp_eq | hp_gt
    · -- p < j.val: in left replicate
      have hne : (⟨p, hp'⟩ : Fin (2 * n + 1)) ≠ j := by simp [Fin.ext_iff]; omega
      simp only [if_neg hne, List.getElem_append, List.length_replicate, List.length_append]
      simp [hp_lt, List.getElem_replicate]
    · -- p = j.val: the singleton
      have heq : (⟨p, hp'⟩ : Fin (2 * n + 1)) = j := by simp [hp_eq]
      simp only [if_pos heq, List.getElem_append, List.length_replicate, List.length_append]
      subst hp_eq
      simp [Nat.sub_self]
    · -- p > j.val: in right replicate
      have hne : (⟨p, hp'⟩ : Fin (2 * n + 1)) ≠ j := by simp [Fin.ext_iff]; omega
      simp only [if_neg hne, List.getElem_append, List.length_replicate, List.length_append]
      have hjp : j.val + 1 ≤ p := Nat.succ_le_of_lt hp_gt
      simp [hp_gt, hjp, List.getElem_replicate, Nat.not_lt_of_lt]

/-- Flipping input position j (with j.val ≤ 2n) in all-true list of length 2n+3
    produces the all-false output list with exactly output position j.val flipped.
    Proof sketch: OR gate absorbs flips at positions j-1 and j-2 (neighbors still 1);
    only position j itself changes via left-permutivity. -/
theorem caStepList_flip_allOnes (n : Nat) (j : Fin (2 * (n + 1) + 1)) (hj : j.val ≤ 2 * n) :
    caStepList (configToList (flipCell (allOnes (n + 1)) j)) =
    configToList (flipCell (allZeros n) ⟨j.val, Nat.lt_succ_of_le hj⟩) := by
  unfold allOnes allZeros
  rw [configToList_flipCell_true, configToList_flipCell_false]
  -- LHS has: j.val trues ++ [false] ++ (2n+3 - j.val - 1) trues
  --        = j.val trues ++ [false] ++ (2n+2 - j.val) trues
  -- RHS has: j.val falses ++ [true] ++ (2n+1 - j.val - 1) falses
  --        = j.val falses ++ [true] ++ (2n - j.val) falses
  -- Apply caStepList_prefix_flip with i = j.val, k = 2*n - j.val
  -- Need: 2n+2 - j.val = k + 2 = 2n - j.val + 2 ✓ (given j.val ≤ 2n)
  have hk : 2 * (n + 1) + 1 - j.val - 1 = 2 * n - j.val + 2 := by omega
  rw [hk]
  have hrhs : 2 * n + 1 - j.val - 1 = 2 * n - j.val := by omega
  rw [hrhs]
  exact caStepList_prefix_flip j.val (2 * n - j.val)

/-
Small-case verification: these examples confirm the axioms above.

INDEX NOTE: For allOnes 1 (n+1=1 → n=0), output level is 0 (Fin 1).
            For allOnes 2 (n+1=2 → n=1), output level is 1 (Fin 3).
            Valid input positions j for flipping: j.val ≤ 2*n (output level n).
-/

/-- Verify axiom 1 for n=0: caStep([true,true,true]) = [false] -/
example : caStepList (List.replicate 3 true) = List.replicate 1 false := by decide

/-- Verify axiom 1 for n=1: caStep(5 trues) = 3 falses -/
example : caStepList (List.replicate 5 true) = List.replicate 3 false := by decide

/-- Verify axiom 2: allOnes 1 → allZeros 0, flip j=0 (only valid interior position) -/
example :
    caStepList (configToList (flipCell (allOnes 1) ⟨0, by omega⟩)) =
    configToList (flipCell (allZeros 0) ⟨0, by omega⟩) := by native_decide

/-- Verify axiom 2: allOnes 2 → allZeros 1, flip j=0 -/
example :
    caStepList (configToList (flipCell (allOnes 2) ⟨0, by omega⟩)) =
    configToList (flipCell (allZeros 1) ⟨0, by omega⟩) := by native_decide

/-- Verify axiom 2: allOnes 2 → allZeros 1, flip j=1 -/
example :
    caStepList (configToList (flipCell (allOnes 2) ⟨1, by omega⟩)) =
    configToList (flipCell (allZeros 1) ⟨1, by omega⟩) := by native_decide

/-- Verify axiom 2: allOnes 2 → allZeros 1, flip j=2 (= 2*n for n=1, max valid) -/
example :
    caStepList (configToList (flipCell (allOnes 2) ⟨2, by omega⟩)) =
    configToList (flipCell (allZeros 1) ⟨2, by omega⟩) := by native_decide

/-- Verify axiom 2: allOnes 3 → allZeros 2, flip j=4 (= 2*n for n=2, max valid) -/
example :
    caStepList (configToList (flipCell (allOnes 3) ⟨4, by omega⟩)) =
    configToList (flipCell (allZeros 2) ⟨4, by omega⟩) := by native_decide

/-
================================================================================
SECTION 5: KEY THEOREMS
================================================================================
-/

/-- rule30n of all_ones at level n+1 equals rule30n of all_zeros at level n.
    Proof: unfold both sides, caEvolve_succ on the left, then reduce caStepList. -/
theorem rule30n_allOnes_eq_allZeros (n : Nat) :
    rule30n (n + 1) (allOnes (n + 1)) = rule30n n (allZeros n) := by
  show (caEvolve (n + 1) (configToList (allOnes (n + 1)))).getD 0 false =
       (caEvolve n (configToList (allZeros n))).getD 0 false
  rw [caEvolve_succ, configToList_allOnes, configToList_allZeros,
      caStepList_allOnes_eq_allZeros_list]

/-- Main theorem: all_zeros witnesses Essential(n, j) → all_ones witnesses Essential(n+1, j).
    Same position j (not shifted). The all-ones lifting, distinct from the standard
    lifting_lemma which shifts position by 1. -/
theorem essential_lift_via_allOnes (n : Nat) (j : Fin (2 * n + 1))
    (h : rule30n n (allZeros n) ≠ rule30n n (flipCell (allZeros n) j)) :
    rule30n (n + 1) (allOnes (n + 1)) ≠
    rule30n (n + 1) (flipCell (allOnes (n + 1)) ⟨j.val, by have := j.is_lt; omega⟩) := by
  -- Abbreviate the lifted index
  set j' : Fin (2 * (n + 1) + 1) := ⟨j.val, by have := j.is_lt; omega⟩ with hj'_def
  -- Observe that j'.val ≤ 2 * n (since j.val < 2*n+1 means j.val ≤ 2*n)
  have hj_le : j'.val ≤ 2 * n := by simp only [j']; omega
  -- Key: rule30n (n+1) (allOnes (n+1)) = rule30n n (allZeros n)
  rw [rule30n_allOnes_eq_allZeros]
  -- Key: rule30n (n+1) (flipCell (allOnes (n+1)) j') = rule30n n (flipCell (allZeros n) j)
  have hflip : rule30n (n + 1) (flipCell (allOnes (n + 1)) j') =
               rule30n n (flipCell (allZeros n) j) := by
    -- Unfold rule30n and peel off one caEvolve step
    show (caEvolve (n + 1) (configToList (flipCell (allOnes (n + 1)) j'))).getD 0 false =
         (caEvolve n (configToList (flipCell (allZeros n) j))).getD 0 false
    rw [caEvolve_succ]
    -- Now reduce caStepList of the flipped all-ones config
    have hcstep : caStepList (configToList (flipCell (allOnes (n + 1)) j')) =
                  configToList (flipCell (allZeros n) j) := by
      -- After rewriting, goal closes by proof irrelevance (j'.val = j.val definitionally via set)
      rw [caStepList_flip_allOnes n j' hj_le]
    rw [hcstep]
  rw [hflip]
  exact h

/-
================================================================================
SECTION 6: WHAT THIS GIVES AND WHAT'S STILL MISSING
================================================================================

PROVED (machine-checked):
  ✓ rule30Local_ones_ones_ones, _zero_one_one, _one_zero_one, _one_one_zero (decide)
  ✓ configToList_allOnes, configToList_allZeros (unfold + ofFn_const)
  ✓ Small-case verification n=0,1,2 (native_decide)
  ✓ caStepList_allTrue (k : Nat) — induction on k (PROVED 2026-03-14)
  ✓ caStepList_allTrue2 (k : Nat) — variant with k+2 offset (PROVED 2026-03-14)
  ✓ caStepList_allOnes_eq_allZeros_list — now a THEOREM (was axiom, PROVED 2026-03-14)
  ✓ caStepList_prefix_flip (i k : Nat) — induction on i (PROVED 2026-03-17)
  ✓ caStepList_flip_allOnes — uses caStepList_prefix_flip (PROVED 2026-03-17)
  ✓ rule30n_allOnes_eq_allZeros (using theorem caStepList_allOnes_eq_allZeros_list)
  ✓ essential_lift_via_allOnes (using theorem caStepList_flip_allOnes)

NO CUSTOM AXIOMS: All theorems proved using only standard Lean axioms.

NOT PROVED BY THIS FILE:
  ✗ General lifting_lemma for ARBITRARY witnesses (not just all_zeros)
  ✗ Coverage of rightmost positions (j.val = 2n+1, 2n+2) at level n+1
  ✗ That all_zeros witnesses Essential(n, j) for all n, j — FALSE for n=2, j=1

COMPLEMENTARY TOOLS:
  Standard lifting_lemma:  Essential n k → Essential (n+1) (k+1)  [position shifts by 1]
  All-ones lifting:        all_zeros witnesses Essential n k
                          → all_ones witnesses Essential (n+1) k  [same position]

These are different; neither implies the other in general.
================================================================================
-/

#check @rule30n_allOnes_eq_allZeros
-- rule30n_allOnes_eq_allZeros : ∀ (n : ℕ), rule30n (n + 1) (allOnes (n + 1)) = rule30n n (allZeros n)

#check @essential_lift_via_allOnes
-- essential_lift_via_allOnes : ∀ (n : ℕ) (j : Fin (2 * n + 1)),
--   rule30n n (allZeros n) ≠ rule30n n (flipCell (allZeros n) j) →
--   rule30n (n + 1) (allOnes (n + 1)) ≠ rule30n (n + 1) (flipCell (allOnes (n + 1)) ⟨↑j, _⟩)
