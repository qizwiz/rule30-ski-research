/-
SubcaseB_Firewall.lean
======================

Late-tail split for SubcaseB beyond m=38.

## Mathematical Argument (Full Penultimate Tape Equality)

Rule 30: f(a,b,c) = a XOR (b OR c).

The `twoSpikeLast` tape differs from the `spike` tape only at position 2*(n'+1)
(the rightmost cell of the initial tape). After n'+1 steps on a tape of size
2*(n'+1)+1, the penultimate-step tape (caEvolve n') has size 3: [a, b, c].

## Causal Cone Analysis

For even m ≥ 40 (inactive, not in {34,36,38}):

- Position 0 of penultimate tape: causal cone is [0, 2*n']. The difference is at
  N-1 = 2*(n'+1) = 2*n'+2 > 2*n'. So a1 = a2 by caEvolve_agree.

- Position 1 of penultimate tape: causal cone is [1, 2*n'+1]. The difference is at
  2*n'+2 > 2*n'+1. So b1 = b2 by caEvolve_agree (after drop).

- Position 2 of penultimate tape: causal cone is [2, 2*n'+2]. The difference is at
  2*n'+2 = N-1 — exactly at the boundary! Standard caEvolve_agree does NOT suffice.

  However, computational verification shows that for inactive even m ≥ 40 with
  m ≠ 2*(n'+1)-8 (right-mirror) and m ≠ 2*n' and n' ≥ 3087:
    (caEvolve n' spike_m).getD 2 = (caEvolve n' twoSpikeLast_m).getD 2

  This is the key mathematical sorry: position 2 of the penultimate tape agrees.
  Proof requires algebraic/LFSR analysis of Rule 30 for inactive m.

## Reduction Summary

Since all three cells [a,b,c] of the penultimate tape agree between spike_m and
twoSpikeLast_m, the final centers must agree: F_m = G_{m,last}.
SubcaseB (F_m=false ∧ G_{m,last}=true) is impossible for inactive m ≥ 40.

## Note on Previous Approach
An earlier version claimed `b = true` (position 1 always true for inactive m ≥ 40).
This is FALSE — computationally, b=false occurs for many inactive m values.
The correct claim is the FULL penultimate tape equality (all three cells agree).

Author: Jonathan Hill
Date: 2026-04-06
-/

import P2p.Prize3_Complete
import P2p.CausalConeLemmas

set_option maxHeartbeats 800000000

/-!
## Penultimate position-2 agreement (key sorry)

The hard part: for m > 30 (inactive tail), n' ≥ 3087, the third cell
of the 3-cell penultimate tape agrees between spike_m and twoSpikeLast_m.
-/

/-- Penultimate position-2 agreement: for inactive even m ≥ 40, the third cell
    of the 3-cell penultimate tape agrees between spike_m and twoSpikeLast_m.

    Via caEvolve_getD_shift, this reduces to showing that
    `(caEvolve n' (spikeAtList m N).drop 2).getD 0` equals the same for
    `(twoSpikeLastList m N).drop 2`. The drop-2 lists differ only at the last
    position 2*n' (the boundary of the causal cone), so caEvolve_agree does not
    directly apply.

    SORRY: Requires algebraic/LFSR analysis of Rule 30 inactive-m dynamics.
    Computationally verified for n' ∈ [3,5000], even m ∈ [32, 2*(n'+1)-3]
    (includes m=32 and m=34..38 which are excluded at the call site via separate theorems)
    with m ≠ 2*(n'+1)-8 and m ≠ 2*n'. The claim fails WITHOUT the exclusions
    (m = 2*(n'+1)-8 gives a counterexample). -/
private lemma penultimate_pos2_agree
    (n' : Nat) (hn' : 3087 ≤ n')
    (m : Nat)
    (hm_even : m % 2 = 0)
    (hm_gt30 : 30 < m)
    (hm_ne_r : m ≠ 2 * n')
    (hm_not_rm : m ≠ 2 * (n' + 1) - 8)
    (hm_high : m + 1 < 2 * (n' + 1) + 1) :
    (caEvolve n' (spikeAtList m (2 * (n' + 1) + 1))).getD 2 false =
    (caEvolve n' (twoSpikeLastList m (2 * (n' + 1) + 1))).getD 2 false := by
  sorry

/-!
## Main firewall theorem
-/

/-- Inactive-tail firewall for `m > 38`, non-right-mirror branch.

    When SubcaseB fires at `m > 38` (even, not right-mirror, not in {34,36,38}),
    all three cells of the penultimate tape agree between spike_m and twoSpikeLast.
    Therefore F_m = rule30Local a b c = G_{m,last}, contradicting F=false and G=true.

    Proof plan:
    1. Convert hcase/hts to caEvolve form
    2. Expand caEvolve (n'+1) = caStepList (caEvolve n') to get 3-cell penultimate tape
    3. Show positions 0 and 1 agree (standard causal cone, caEvolve_agree)
    4. Show position 2 agrees (penultimate_pos2_agree — the sorry)
    5. rule30Local a b c = rule30Local a b c → F_m = G_{m,last} → contradiction -/
theorem subcaseB_mgt30_split
    (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1))
    (hm_even : m.val % 2 = 0)
    (hm_low : 1 ≤ m.val)
    (hm_gt30 : 30 < m.val)
    (hm_ne_r : m.val ≠ 2 * n')
    (hm_not_rm : m.val ≠ 2 * (n' + 1) - 8)
    (hm_high : m.val + 1 < 2 * (n' + 1) + 1)
    (hm_ne34 : m.val ≠ 34)
    (hm_ne36 : m.val ≠ 36)
    (hm_ne38 : m.val ≠ 38)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    False := by
  -- Convert to caEvolve form
  have hF : (caEvolve (n' + 1) (spikeAtList m.val (2 * (n' + 1) + 1))).getD 0 false = false := by
    have h := hcase
    simp only [rule30n, configToList, spikeAtList] at h
    exact h
  have hG : (caEvolve (n' + 1) (twoSpikeLastList m.val (2 * (n' + 1) + 1))).getD 0 false = true := by
    have h := hts
    simp only [rule30n] at h
    rw [show configToList (fun k : Fin (2 * (n' + 1) + 1) =>
            decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) =
          twoSpikeLastList m.val (2 * (n' + 1) + 1) from by
      simp [configToList, twoSpikeLastList,
            show 2 * (n' + 1) + 1 - 1 = 2 * (n' + 1) from by omega]] at h
    exact h
  -- All three cells of the penultimate tape agree between spike_m and twoSpikeLast.
  -- Positions 0,1 by causal cone; position 2 by penultimate_pos2_agree (sorry).
  have hFG_eq : (caEvolve (n' + 1) (spikeAtList m.val (2 * (n' + 1) + 1))).getD 0 false =
                (caEvolve (n' + 1) (twoSpikeLastList m.val (2 * (n' + 1) + 1))).getD 0 false := by
    -- Step 1: caEvolve (n'+1) l = caStepList (caEvolve n' l)
    have ce1_eq : ∀ (l : List Bool),
        caEvolve (n' + 1) l = caStepList (caEvolve n' l) := by
      intro l
      conv_lhs => rw [show n' + 1 = 1 + n' from by omega, caEvolve_add]
      have : caEvolve 1 (caEvolve n' l) = caStepList (caEvolve n' l) := by
        have h := caEvolve_succ 0 (caEvolve n' l)
        simp [caEvolve_zero] at h
        exact h
      exact this
    rw [ce1_eq (spikeAtList m.val (2 * (n' + 1) + 1)),
        ce1_eq (twoSpikeLastList m.val (2 * (n' + 1) + 1))]
    -- Step 2: Lengths
    have hL1_len : (spikeAtList m.val (2 * (n' + 1) + 1)).length = 2 * (n' + 1) + 1 :=
      spikeAtList_length m.val (2 * (n' + 1) + 1)
    have hL2_len : (twoSpikeLastList m.val (2 * (n' + 1) + 1)).length = 2 * (n' + 1) + 1 :=
      twoSpikeLastList_length m.val (2 * (n' + 1) + 1)
    have hce_len1 : (caEvolve n' (spikeAtList m.val (2 * (n' + 1) + 1))).length = 3 := by
      rw [caEvolve_length_le n' _ (by rw [hL1_len]; omega), hL1_len]; omega
    have hce_len2 : (caEvolve n' (twoSpikeLastList m.val (2 * (n' + 1) + 1))).length = 3 := by
      rw [caEvolve_length_le n' _ (by rw [hL2_len]; omega), hL2_len]; omega
    -- Step 3: Expand caStepList at position 0
    rw [caStepList_getD_eq _ 0 (by omega),
        caStepList_getD_eq _ 0 (by omega)]
    -- Step 4: Both tapes agree on positions 0..2*n'+1 (differ only at position 2*(n'+1) = N-1)
    -- This gives positions 0 and 1 of penultimate tape; position 2 needs separate argument.
    have hagree : ∀ i : Nat, i ≤ 2 * n' + 1 →
        (spikeAtList m.val (2 * (n' + 1) + 1)).getD i false =
        (twoSpikeLastList m.val (2 * (n' + 1) + 1)).getD i false := by
      intro i hi
      have hi_lt : i < 2 * (n' + 1) + 1 := by omega
      rw [spikeAtList_getD m.val (2 * (n' + 1) + 1) i hi_lt]
      rw [twoSpikeLastList_getD m.val (2 * (n' + 1) + 1) i hi_lt]
      have hi_ne_last : i ≠ 2 * (n' + 1) + 1 - 1 := by omega
      simp only [decide_eq_decide]
      constructor
      · intro h; exact Or.inl h
      · intro h; cases h with
        | inl h => exact h
        | inr h => exact absurd h hi_ne_last
    -- Step 5: a1 = a2 (position 0 of penultimate tape)
    have ha_eq : (caEvolve n' (spikeAtList m.val (2 * (n' + 1) + 1))).getD 0 false =
                 (caEvolve n' (twoSpikeLastList m.val (2 * (n' + 1) + 1))).getD 0 false :=
      caEvolve_agree n' _ _
        (by rw [hL1_len]; omega)
        (by rw [hL2_len]; omega)
        (fun i hi => hagree i (by omega))
    -- Step 6: b1 = b2 (position 1 of penultimate tape)
    have hb_eq : (caEvolve n' (spikeAtList m.val (2 * (n' + 1) + 1))).getD 1 false =
                 (caEvolve n' (twoSpikeLastList m.val (2 * (n' + 1) + 1))).getD 1 false := by
      rw [caEvolve_getD_shift n' (spikeAtList m.val (2 * (n' + 1) + 1)) 1,
          caEvolve_getD_shift n' (twoSpikeLastList m.val (2 * (n' + 1) + 1)) 1]
      apply caEvolve_agree n'
      · rw [List.length_drop, hL1_len]; omega
      · rw [List.length_drop, hL2_len]; omega
      · intro i hi
        rw [show ((spikeAtList m.val (2 * (n' + 1) + 1)).drop 1).getD i false =
              (spikeAtList m.val (2 * (n' + 1) + 1)).getD (1 + i) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop, add_comm 1 i]]
        rw [show ((twoSpikeLastList m.val (2 * (n' + 1) + 1)).drop 1).getD i false =
              (twoSpikeLastList m.val (2 * (n' + 1) + 1)).getD (1 + i) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop, add_comm 1 i]]
        exact hagree (1 + i) (by omega)
    -- Step 7: c1 = c2 (position 2 of penultimate tape) — the key sorry
    have hc_eq : (caEvolve n' (spikeAtList m.val (2 * (n' + 1) + 1))).getD 2 false =
                 (caEvolve n' (twoSpikeLastList m.val (2 * (n' + 1) + 1))).getD 2 false :=
      penultimate_pos2_agree n' hn' m.val hm_even hm_gt30 hm_ne_r hm_not_rm hm_high
    -- Step 8: Since all three cells [a,b,c] agree, rule30Local gives the same output
    rw [ha_eq, hb_eq, hc_eq]
  -- Contradiction: F_m = false but G_{m,last} = true, yet F_m = G_{m,last}
  exact absurd (hF.symm.trans (hFG_eq.trans hG)) (by decide)
