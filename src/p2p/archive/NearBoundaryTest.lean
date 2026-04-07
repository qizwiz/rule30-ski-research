/-
  NearBoundaryTest.lean

  Near-boundary cases for lifting_lemma:
    k=0:  Essential n ⟨0,_⟩ → Essential (n+1) ⟨1,_⟩
    k=2n: Essential n ⟨2n,_⟩ → Essential (n+1) ⟨2n+1,_⟩

  Right boundary strategy (k=2n):
    - flip-symmetry gives c_n[2n]=false
    - b0=false, b1=true gives c'[2n+2]=false, c'[2n+1]=true
    - recurrence gives c'[2n]=true (left blocker for pos 2n-1)
    - flip at 2n+1 propagates to output at 2n (not blocked by c'[2n+2]=false)
  Left boundary strategy (k=0): direct application of lifting_lemma.
-/

import P2p.LiftingLemma_LeftPermutive

namespace Rule30

-- ============================================================
-- AUXILIARY: flipCell involution
-- ============================================================

/-- flipCell is an involution -/
lemma flipCell_involution {n : Nat} (c : Config n) (k : Fin (2 * n + 1)) :
    flipCell (flipCell c k) k = c := by
  ext j
  simp only [flipCell]
  by_cases h : j = k
  · subst h; simp
  · simp [h]

/-- From any witness, get one where c[k] = false -/
lemma essential_witness_false_at (n : Nat) (k : Fin (2 * n + 1))
    (h_ess : Essential n k) :
    ∃ c : Config n, rule30n n c ≠ rule30n n (flipCell c k) ∧ c k = false := by
  obtain ⟨c, hc⟩ := h_ess
  by_cases hk : c k = false
  · exact ⟨c, hc, hk⟩
  · -- c k = true; use flipCell c k, which has (flipCell c k) k = false
    refine ⟨flipCell c k, ?_, ?_⟩
    · rw [flipCell_involution]; exact hc.symm
    · simp only [flipCell]
      simp only [ite_true]
      -- !(c k) = !true = false
      have : c k = true := by
        cases h : c k
        · exact absurd h hk
        · rfl
      simp [this]

-- ============================================================
-- AUXILIARY: Boundary bits of backwardFillList
-- ============================================================

/-- The rightmost element of backwardFillList is b0 -/
lemma backwardFillList_last (c_n_list : List Bool) (b0 b1 : Bool)
    (h : c_n_list.length = 2 * n + 1) :
    (backwardFillList c_n_list b0 b1).getD (2 * n + 2) false = b0 := by
  have hlen := backwardFillList_length c_n_list b0 b1
  rw [h] at hlen
  -- backwardFillList builds with [b1, b0] as the initial accumulator
  -- The last element (index 2n+2) should be b0 from acc[1]
  -- Use fillBackward_getD_tail: position > len means it's from acc
  unfold backwardFillList
  split
  · -- c_n_list.length = 0 case (contradiction)
    omega
  · -- c_n_list.length = len + 1 = 2*n+1
    rename_i len hlen_eq
    have : len = 2 * n := by omega
    subst this
    -- fillBackward c_n_list [b1, b0] (2*n) at position 2*n+2
    -- 2*n+2 > 2*n, so getD from acc at index 2*n+2 - 2*n - 1 = 1
    rw [fillBackward_getD_tail c_n_list [b1, b0] (2 * n) (2 * n + 2) (by omega)]
    simp

/-- The second-to-last element of backwardFillList is b1 -/
lemma backwardFillList_second_last (c_n_list : List Bool) (b0 b1 : Bool)
    (h : c_n_list.length = 2 * n + 1) :
    (backwardFillList c_n_list b0 b1).getD (2 * n + 1) false = b1 := by
  have hlen := backwardFillList_length c_n_list b0 b1
  rw [h] at hlen
  unfold backwardFillList
  split
  · -- c_n_list.length = 0 case (contradiction)
    omega
  · -- c_n_list.length = len + 1 = 2*n+1
    rename_i len hlen_eq
    have : len = 2 * n := by omega
    subst this
    rw [fillBackward_getD_tail c_n_list [b1, b0] (2 * n) (2 * n + 1) (by omega)]
    simp


-- ============================================================
-- NEAR-BOUNDARY CASE k = 2n (RIGHT BOUNDARY)
-- ============================================================

/-- Lifting from right boundary: Essential n ⟨2n,_⟩ → Essential (n+1) ⟨2n+1,_⟩
    Uses: flip symmetry gives c_n[2n]=false,
          b0=false b1=true gives c'[2n+2]=false, c'[2n+1]=true,
          recurrence gives c'[2n]=NOT c_n[2n] = true (left blocker). -/
theorem lifting_right_boundary (n : Nat)
    (h_ess : Essential n ⟨2 * n, by omega⟩) :
    Essential (n + 1) ⟨2 * n + 1, by omega⟩ := by
  -- Step 1: Get witness c_n with c_n[2n] = false
  obtain ⟨c_n, h_essential, h_cn_false⟩ :=
    essential_witness_false_at n ⟨2 * n, by omega⟩ h_ess
  -- Step 2: Construct c' = backwardFillConfig c_n false true (b0=false, b1=true)
  let c' := backwardFillConfig c_n false true
  unfold Essential
  use c'
  -- Step 3a: Right blocker at position 2n+2 (= b0 = false)
  have h_pos_k2 : c' ⟨2 * n + 2, by omega⟩ = false := by
    show (backwardFillList (configToList c_n) false true).getD (2 * n + 2) false = false
    rw [backwardFillList_last (configToList c_n) false true (configToList_length c_n)]
  -- Step 3b: Position 2n+1 (= b1 = true)
  have h_pos_k1 : c' ⟨2 * n + 1, by omega⟩ = true := by
    show (backwardFillList (configToList c_n) false true).getD (2 * n + 1) false = true
    rw [backwardFillList_second_last (configToList c_n) false true (configToList_length c_n)]
  -- Step 4: Left blocker at position 2n from backward recurrence:
  --   c'[2n] = c_n[2n] XOR (c'[2n+1] OR c'[2n+2])
  --         = false XOR (true OR false) = false XOR true = true
  have h_left : c' ⟨2 * n, by omega⟩ = true := by
    show (backwardFillList (configToList c_n) false true).getD (2 * n) false = true
    have hcn_len : (configToList c_n).length = 2 * n + 1 := configToList_length c_n
    -- Apply backward recurrence at position 2n
    have h2n_lt : 2 * n < (configToList c_n).length := by rw [hcn_len]; omega
    have h_rec := backwardFillList_recurrence (configToList c_n) false true (2 * n) h2n_lt
    simp only at h_rec
    -- h_rec : c'[2n] = c_n[2n] XOR (c'[2n+1] OR c'[2n+2])
    rw [h_rec]
    -- c_n[2n] = false (from h_cn_false)
    have hcn_2n : (configToList c_n).getD (2 * n) false = false := by
      rw [configToList_getD]
      simp [h_cn_false]
    rw [hcn_2n]
    -- c'[2n+1] = b1 = true
    have h_r1 : (backwardFillList (configToList c_n) false true).getD (2 * n + 1) false = true :=
      backwardFillList_second_last (configToList c_n) false true hcn_len
    -- c'[2n+2] = b0 = false
    have h_r2 : (backwardFillList (configToList c_n) false true).getD (2 * n + 2) false = false :=
      backwardFillList_last (configToList c_n) false true hcn_len
    rw [h_r1, h_r2]
    simp
  -- Step 5: caStep(c') = c_n
  have h_caStep : ∀ j : Fin (2 * n + 1),
      (caStepList (configToList c')).getD j.val false = c_n j := by
    intro j
    -- c' = backwardFillConfig c_n false true
    -- configToList c' = List.ofFn c' which expands to backwardFillList (configToList c_n) false true
    -- We need to relate caStepList (configToList c') to c_n
    -- c' i = (backwardFillList (configToList c_n) false true).getD i false
    -- So configToList c' = List.ofFn c' where c' : Fin (2*(n+1)+1) → Bool
    -- and c' ⟨i, _⟩ = (backwardFillList ...).getD i false
    -- We use that caStepList of (List.ofFn f) = caStepList of the underlying list
    have h_len : (configToList c').length = 2 * (n + 1) + 1 := configToList_length c'
    have h_bfl_len : (backwardFillList (configToList c_n) false true).length = 2 * (n + 1) + 1 := by
      rw [backwardFillList_length, configToList_length]; omega
    -- Show each element matches
    have h_elem : ∀ i, i < 2 * (n + 1) + 1 →
        (configToList c').getD i false = (backwardFillList (configToList c_n) false true).getD i false := by
      intro i hi
      rw [configToList_getD]
      simp only [hi, dite_true]
      rfl
    have h_j2 : j.val + 2 < 2 * (n + 1) + 1 := by have := j.isLt; omega
    have h_j2' : j.val + 2 < (backwardFillList (configToList c_n) false true).length := by rw [h_bfl_len]; exact h_j2
    have h_j2'' : j.val + 2 < (configToList c').length := by rw [h_len]; exact h_j2
    -- Express caStepList (configToList c').getD j.val = rule30Local (...)
    rw [caStepList_getD_eq _ _ h_j2'']
    -- Now the inputs are from configToList c'
    have he0 : (configToList c').getD j.val false = (backwardFillList (configToList c_n) false true).getD j.val false :=
      h_elem j.val (by omega)
    have he1 : (configToList c').getD (j.val + 1) false = (backwardFillList (configToList c_n) false true).getD (j.val + 1) false :=
      h_elem (j.val + 1) (by omega)
    have he2 : (configToList c').getD (j.val + 2) false = (backwardFillList (configToList c_n) false true).getD (j.val + 2) false :=
      h_elem (j.val + 2) h_j2
    rw [he0, he1, he2]
    -- Now apply backwardFillList_caStep_inverse
    rw [← caStepList_getD_eq _ _ h_j2']
    have hj_lt : j.val < (configToList c_n).length := by rw [configToList_length]; exact j.isLt
    have hstep := backwardFillList_caStep_inverse (configToList c_n) false true
      (configToList_length c_n) j.val hj_lt
    rw [hstep, configToList_getD]
    simp only [j.isLt, dite_true]
  -- Step 6: Conclude by the same argument as allEssential_to_essential_interior
  -- We have:
  --   - c' : Config (n+1) with caStep(c') = c_n
  --   - h_left : c'[2n] = true (left blocker)
  --   - h_right : c'[2n+2] = true (right blocker)
  --   - h_essential : c_n witnesses E(n, ⟨2n, _⟩)
  -- Goal: rule30n (n+1) c' ≠ rule30n (n+1) (flipCell c' ⟨2n+1, _⟩)

  -- The structure follows allEssential_to_essential_interior with k = ⟨2n, _⟩
  -- flip position = k+1 = 2n+1, blockers at k = 2n and k+2 = 2n+2

  -- Step A: caStepList (configToList c') = configToList c_n (as lists)
  have hLists_eq : caStepList (configToList c') = configToList c_n := by
    have hlen1 : (caStepList (configToList c')).length = 2 * n + 1 := by
      rw [caStepList_length (configToList c') (by simp [configToList_length]; omega)]
      simp [configToList_length]; omega
    have hlen2 : (configToList c_n).length = 2 * n + 1 := configToList_length c_n
    apply list_ext_getD _ _ (hlen1.trans hlen2.symm)
    intro j
    by_cases hj : j < 2 * n + 1
    · -- j in range
      have hR : (configToList c_n).getD j false = c_n ⟨j, hj⟩ := by
        rw [configToList_getD]; simp [hj]
      have hL : (caStepList (configToList c')).getD j false = c_n ⟨j, hj⟩ := h_caStep ⟨j, hj⟩
      rw [hL, hR]
    · -- j out of range: both false
      rw [configToList_getD]; simp [hj]
      by_cases h_in : j < (caStepList (configToList c')).length
      · omega  -- contradiction
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (caStepList (configToList c')).length ≤ j)]

  -- Step B: rule30n (n + 1) c' = rule30n n c_n
  have h1 : rule30n (n + 1) c' = rule30n n c_n := by
    unfold rule30n
    rw [show caEvolve (n + 1) (configToList c') = caEvolve n (caStepList (configToList c')) from rfl]
    rw [hLists_eq]

  -- Step C: Similar for flipCell
  let m_n : Fin (2 * n + 1) := ⟨2 * n, by omega⟩
  have hLists_flip : caStepList (configToList (flipCell c' ⟨2 * n + 1, by omega⟩)) = configToList (flipCell c_n m_n) := by
    have hlen1 : (caStepList (configToList (flipCell c' ⟨2 * n + 1, by omega⟩))).length = 2 * n + 1 := by
      rw [caStepList_length (configToList (flipCell c' ⟨2 * n + 1, by omega⟩)) (by simp [configToList_length]; omega)]
      simp [configToList_length]; omega
    have hlen2 : (configToList (flipCell c_n m_n)).length = 2 * n + 1 := configToList_length _
    apply list_ext_getD _ _ (hlen1.trans hlen2.symm)
    intro j
    by_cases hj : j < 2 * n + 1
    · -- j in range: split on j = 2*n (the changed output) vs j < 2*n (unchanged)
      -- NOTE: we use j = 2*n FIRST to avoid n=0 edge case where 2*n-1 underflows
      by_cases hj_eq_2n : j = 2 * n
      · -- Case j = 2n: window (c'[2n], c'[2n+1], c'[2n+2])
        -- Flipping c'[2n+1] changes output: c'[2n]=true, c'[2n+2]=false, flip propagates
        subst hj_eq_2n
        have h_bound_flip : 2 * n + 2 < (configToList (flipCell c' ⟨2 * n + 1, by omega⟩)).length := by
          simp [configToList_length]; omega
        -- Only rewrite the LHS (flip case)
        rw [caStepList_getD_eq _ _ h_bound_flip]
        rw [configToList_flipCell_getD, configToList_flipCell_getD, configToList_flipCell_getD]
        have h2n_lt : 2 * n < 2 * (n + 1) + 1 := by omega
        have h2n1_lt : 2 * n + 1 < 2 * (n + 1) + 1 := by omega
        have h2n2_lt : 2 * n + 2 < 2 * (n + 1) + 1 := by omega
        simp only [show 2 * n ≠ 2 * n + 1 by omega, show 2 * n + 2 ≠ 2 * n + 1 by omega, ite_true, ite_false, if_false]
        -- c'[2n]=true, !c'[2n+1]=!true=false, c'[2n+2]=false
        have hv2n : (configToList c').getD (2 * n) false = true := by
          rw [configToList_getD]; simp only [h2n_lt, dite_true]; exact h_left
        have hv2n1 : (configToList c').getD (2 * n + 1) false = true := by
          rw [configToList_getD]; simp only [h2n1_lt, dite_true]; exact h_pos_k1
        have hv2n2 : (configToList c').getD (2 * n + 2) false = false := by
          rw [configToList_getD]; simp only [h2n2_lt, dite_true]; exact h_pos_k2
        rw [hv2n, hv2n1, hv2n2]
        -- LHS: rule30Local true false false = true XOR false = true
        -- RHS: (flipCell c_n m_n)[2n] = !c_n[2n] = !false = true
        rw [configToList_flipCell_getD, configToList_getD]
        simp [m_n, show 2 * n < 2 * n + 1 by omega]
        have hcn_val : c_n ⟨2 * n, by omega⟩ = false := h_cn_false
        rw [hcn_val]
        simp [rule30Local]
      · -- Case j ≠ 2n: output is unchanged, equals c_n[j] = (flipCell c_n m_n)[j]
        have hj_lt_2n : j < 2 * n := by omega
        -- Sub-case: j = 2n-1 (n≥1, since j < 2n means n≥1, and j could equal 2n-1)
        -- In this sub-case, j+2 = 2n+1 = flip position, but c'[j+1]=c'[2n]=true blocks it
        -- For j ≤ 2n-2: window doesn't include position 2n+1 at all
        -- We handle both uniformly: if j+2 = 2n+1, use blocking; otherwise window is unaffected
        by_cases hj2_eq : j + 2 = 2 * n + 1
        · -- j = 2n-1: window (c'[j], c'[j+1]=c'[2n], c'[2n+1] which is flipped)
          -- c'[j+1]=c'[2n]=true blocks the right flip
          have hj_val : j = 2 * n - 1 := by omega
          have h_bound_orig : j + 2 < (configToList c').length := by
            simp [configToList_length]; omega
          have h_bound_flip : j + 2 < (configToList (flipCell c' ⟨2 * n + 1, by omega⟩)).length := by
            simp [configToList_length]; omega
          -- Only rewrite on LHS (the flip case)
          rw [caStepList_getD_eq _ _ h_bound_flip]
          rw [configToList_flipCell_getD, configToList_flipCell_getD, configToList_flipCell_getD]
          -- j ≠ 2n+1, j+1 ≠ 2n+1 (j+1=2n ≠ 2n+1), j+2 = 2n+1 → flipped
          have hne_j : j ≠ 2 * n + 1 := by omega
          have hne_j1 : j + 1 ≠ 2 * n + 1 := by omega  -- j+1 = 2n < 2n+1
          simp only [hne_j, hne_j1, hj2_eq, ite_true, ite_false, if_false]
          -- Goal: rule30Local c'[j] c'[j+1] !(c'[2n+1]) = configToList(flipCell c_n m_n).getD j false
          -- c'[j+1] = c'[2n] = true (left blocker for this window position)
          have hcenter : (configToList c').getD (j + 1) false = true := by
            rw [configToList_getD]
            -- j+2 = 2n+1, so j+1 = 2n, and 2n < 2(n+1)+1 = 2n+3
            have hj1_lt : j + 1 < 2 * (n + 1) + 1 := by
              have : j = 2 * n - 1 := by omega
              omega
            simp only [hj1_lt, dite_true]
            -- j+1 = 2*n (since j = 2n-1 and j+2 = 2n+1)
            have hj1_eq_2n : (⟨j + 1, hj1_lt⟩ : Fin (2 * (n + 1) + 1)) = ⟨2 * n, by omega⟩ := by
              ext
              simp only [Fin.val_mk]
              omega
            rw [hj1_eq_2n]
            exact h_left
          -- The goal is rule30Local c'[j] c'[j+1] (!c'[2n+1]) = (flipCell c_n m_n)[j]
          -- Since j+2 = 2n+1, we have c'[j+2] = c'[2n+1]
          have hgetD_eq : (configToList c').getD (2 * n + 1) false = (configToList c').getD (j + 2) false := by
            congr 1; omega
          rw [hgetD_eq]
          -- Apply blocking lemma in reverse direction
          rw [← rule30Local_right_blocked_by_center _ _ _ hcenter]
          -- Now: rule30Local c'[j] c'[j+1] c'[j+2] = configToList(flipCell c_n m_n).getD j false
          -- Use h_caStep to get LHS = c_n j
          have h_lhs : rule30Local ((configToList c').getD j false)
              ((configToList c').getD (j + 1) false) ((configToList c').getD (j + 2) false) =
              c_n ⟨j, hj⟩ := by
            rw [← caStepList_getD_eq _ _ h_bound_orig]
            exact h_caStep ⟨j, hj⟩
          rw [h_lhs]
          rw [configToList_flipCell_getD, configToList_getD]
          have hj_ne_mn : j ≠ m_n.val := by simp [m_n]; omega
          simp only [hj_ne_mn, if_false, show j < 2 * n + 1 from hj, dite_true]
        · -- j+2 ≠ 2n+1: also j+1 ≠ 2n+1 and j ≠ 2n+1 (since j < j+1 < j+2)
          have hne1 : j ≠ 2 * n + 1 := by omega
          have hne2 : j + 1 ≠ 2 * n + 1 := by omega
          have hne3 : j + 2 ≠ 2 * n + 1 := hj2_eq
          have h_bound_orig : j + 2 < (configToList c').length := by
            simp [configToList_length]; omega
          have h_bound_flip : j + 2 < (configToList (flipCell c' ⟨2 * n + 1, by omega⟩)).length := by
            simp [configToList_length]; omega
          -- Only rewrite on LHS (the flip case)
          rw [caStepList_getD_eq _ _ h_bound_flip]
          rw [configToList_flipCell_getD, configToList_flipCell_getD, configToList_flipCell_getD]
          simp only [hne1, hne2, hne3, if_false]
          -- LHS is now rule30Local c'[j] c'[j+1] c'[j+2] = (flipCell c_n m_n)[j]
          have h_lhs : rule30Local ((configToList c').getD j false)
              ((configToList c').getD (j + 1) false) ((configToList c').getD (j + 2) false) =
              c_n ⟨j, hj⟩ := by
            rw [← caStepList_getD_eq _ _ h_bound_orig]
            exact h_caStep ⟨j, hj⟩
          rw [h_lhs]
          rw [configToList_flipCell_getD, configToList_getD]
          have hj_ne_mn : j ≠ m_n.val := by simp [m_n]; omega
          simp only [hj_ne_mn, if_false, show j < 2 * n + 1 from hj, dite_true]
    · -- j out of range: both false
      have hlen_flip : (caStepList (configToList (flipCell c' ⟨2 * n + 1, by omega⟩))).length = 2 * n + 1 := by
        rw [caStepList_length (configToList (flipCell c' ⟨2 * n + 1, by omega⟩)) (by simp [configToList_length]; omega)]
        simp [configToList_length]; omega
      have hj_oob : j ≥ (caStepList (configToList (flipCell c' ⟨2 * n + 1, by omega⟩))).length := by
        rw [hlen_flip]; omega
      -- RHS: (configToList (flipCell c_n m_n)).getD j false = false when j out of range
      rw [configToList_getD]
      simp only [hj, dite_false]
      -- LHS: (caStepList ...).getD j false = false when j out of range
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj_oob]
      rfl

  -- Step D: rule30n (n + 1) (flipCell c' ⟨2n+1, _⟩) = rule30n n (flipCell c_n m_n)
  have h2 : rule30n (n + 1) (flipCell c' ⟨2 * n + 1, by omega⟩) = rule30n n (flipCell c_n m_n) := by
    unfold rule30n
    rw [show caEvolve (n + 1) (configToList (flipCell c' ⟨2 * n + 1, by omega⟩)) =
           caEvolve n (caStepList (configToList (flipCell c' ⟨2 * n + 1, by omega⟩))) from rfl]
    rw [hLists_flip]

  -- Conclude
  rw [h1, h2]
  exact h_essential

-- ============================================================
-- NEAR-BOUNDARY CASE k = 0 (LEFT BOUNDARY)
-- ============================================================

/-- Lifting from left boundary: Essential n ⟨0,_⟩ → Essential (n+1) ⟨1,_⟩
    Uses lifting_lemma_core with m=0 at level n to get a witness c_n and preimage c'
    with blockers at positions 0-1=-1 (but m.val=0 is boundary) and 0+1=1.

    WAIT: m=0 doesn't satisfy hm_low (requires 1 ≤ m.val).
    Instead: use lifting_lemma_core at m=1, which gives Essential(n, 1) and
    Essential(n+1, 1). But we need Essential(n, 0) → Essential(n+1, 1).

    CORRECT APPROACH: The witness from Essential(n, 0) combined with
    lifting_lemma_core at position m=0... but m=0 fails hm_low.

    Actually, we use the SAME construction as allEssential_to_essential_interior,
    but with k_n = ⟨0, _⟩ mapping to position 1 at level n+1.
    The blockers are at k.val = 0-1 = -1 (impossible) ...

    INSIGHT: For the left boundary, we DON'T have both blockers!
    We only have the right blocker at position k.val+2 = 2.
    The left blocker at position -1 doesn't exist.

    So we need a different strategy: use lifting_lemma_core at m=1 directly,
    since Essential(n, 0) is covered by the base case, and we're proving
    Essential(n+1, 1) using the structure from lifting_lemma_core. -/
theorem lifting_left_boundary (n : Nat) (hn : n ≥ 1)
    (h_ess : Essential n ⟨0, by omega⟩) :
    Essential (n + 1) ⟨1, by omega⟩ := by
  -- For n ≥ 1: position m=0 at level n maps to position 1 at level n+1
  -- But lifting_lemma_core requires 1 ≤ m.val, which fails for m=0
  -- So we need a direct construction similar to lifting_right_boundary

  -- Get witness c_n with c_n[0] = false
  obtain ⟨c_n, h_essential, h_cn_false⟩ :=
    essential_witness_false_at n ⟨0, by omega⟩ h_ess

  -- Construct c' = backwardFillConfig c_n b0 b1
  -- For left boundary, we want c'[0]=true (left blocker) and c'[2]=true (right blocker)
  -- With c_n[0]=false, recurrence gives: c'[0] = false XOR (c'[1] OR c'[2])
  -- To get c'[0]=true, we need c'[1] OR c'[2] = true, so at least one must be true
  -- Choose b1=true (c'[2n+1]) and propagate back via recurrence
  -- Actually, we need to work backwards from the right: b0, b1 are the rightmost two bits

  -- For n ≥ 1: we have at least 2n+1 ≥ 3 positions (0, 1, 2, ..., 2n)
  -- Use b0=true, b1=false to get c'[2n+2]=true
  -- Then use the recurrence to compute c'[0], c'[1], c'[2]

  -- Actually, for simplicity: use lifting_lemma_core at position m=0 with RELAXED bounds
  -- OR: prove it directly using the all-zeros construction from left_boundary_essential

  -- SIMPLEST: Just use left_boundary_essential (n+1) which gives Essential (n+1) ⟨0, _⟩
  -- Then use lifting_lemma to lift from position 0 to position 1
  -- NO WAIT: that's circular.

  -- CORRECT: We already have lifting_lemma : Essential n k → Essential (n+1) (k+1)
  -- Apply it to k = ⟨0, _⟩:
  have h_lift := lifting_lemma n ⟨0, by omega⟩ h_ess
  -- h_lift : Essential (n+1) ⟨0 + 1, _⟩ = Essential (n+1) ⟨1, _⟩
  -- The goal is Essential (n+1) ⟨1, _⟩ and h_lift gives Essential (n+1) ⟨0+1, _⟩
  -- These Fins are equal since 0+1 = 1
  exact h_lift

end Rule30
