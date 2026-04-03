/-
SubcaseB_m22_RightEdge.lean
===========================
Closes subcaseB_m22_l0_sorry (line 2747 SubcaseBPeriod.lean) using RIGHT-EDGE WITNESSES.

Discovery (Opus consult 2026-04-02):
Instead of fixed-position witnesses (which lead to period-131072 algebraic barrier),
use witnesses at fixed offsets FROM THE RIGHT EDGE:
  w = 2*(n'+1) - k, for k = 6

These witnesses have PERIOD 256 in T (= n'+1), matching the spike-at-22 LFSR period.
The period-131072 barrier completely disappears — it was an artifact of the fixed-position
viewpoint. Total new native_decide computation: ~1 second.

STRUCTURE:
  SubcaseB m=22 fires at n' ≡ 14 mod 256 for n' ≥ 3087:
    n' ≡ 14 mod 256 → witness k=6

  Period-256 facts:
    rightEdgeF_period256_k6  (F period 256, via period-2 and period-2|256)
    rightEdgeG_period256_k6  (G period 256, via caEvolve_cert_m22_p256)

  Base case (1 native_decide): T = 271 (n'=270)

  Uses:
    - SubcaseB_m4_RightEdge.lean: rightEdgeF, rightEdgeG, rightEdgeSens, spikeConfigAt,
      and all bridge lemmas (reused directly)
    - CausalConeLemmas.lean: rule30n_spikeAt22_period256, caEvolve_cert_m22_p256,
      caEvolve_agree, caEvolve_getD_shift, caEvolve_spikeAt_agree

Self-contained modulo imports above; no new mathematical ideas beyond m=4 template.
-/

import P2p.Prize3_Complete
import P2p.CausalConeLemmas
import P2p.SubcaseB_m4_RightEdge

namespace P2p

/-!
## F period 2 for k=6 (right-edge spike only)

rightEdgeF 6 T = (caEvolve T (spikeAtList (2T-6) (2T+1))).getD 0 false

Strategy: The spike at 2T-6 is 6 cells from the right boundary (position 2T).
After k/2 = 3 steps the spike reaches the boundary and boundary absorption
forces the output to depend only on T mod 2.

Split: T = (S-1) + 1 + 3, T+2 = (S-1) + 1 + 5, where S = T-3.
Both inner tapes have length 2S+1 after evolution.
Positions 0..2S-1: both false (spike at 2S, causal cone of pos i≤2S-4 doesn't reach 2S).
Positions 2S-4..2S-1: need careful case analysis (spike nearby).
Position 2S-1: true in both (cert: caEvolve_3_spikeAtRelPos1_8_pos0 below).

NOTE: This proof has the same structure as rightEdgeF_period8_k10 but comparing
steps 3 and 5 (= 3+2) instead of 5 and 13 (= 5+8).
-/

/-- Cert: caEvolve 3 (spikeAtList 1 8) at position 0 = true.
    This is drop(2S-1) of (caEvolve 3 (spikeAtList (2S) (2S+7))) reduced to canonical form.
    Spike at 2S in tape 2S+7: drop(2S-1) gives spike at 1 in tape 8. -/
private lemma rightEdgeF6_ev3_pos2Sm1_cert :
    (caEvolve 3 (spikeAtList 1 8)).getD 0 false = true := by native_decide

private lemma rightEdgeF6_ev3_pos2Sm1 (S : ℕ) (hS : 4 ≤ S) :
    (caEvolve 3 (spikeAtList (2 * S) (2 * S + 7))).getD (2 * S - 1) false = true := by
  rw [caEvolve_getD_shift 3 _ (2 * S - 1)]
  apply (caEvolve_agree 3 _ (spikeAtList 1 8) (by
    rw [List.length_drop, spikeAtList_length]; omega) (by
    rw [spikeAtList_length]; omega) (fun j hj => ?_)).trans rightEdgeF6_ev3_pos2Sm1_cert
  rw [show ((spikeAtList (2 * S) (2 * S + 7)).drop (2 * S - 1)).getD j false =
       (spikeAtList (2 * S) (2 * S + 7)).getD (2 * S - 1 + j) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  rw [spikeAtList_getD (2 * S) (2 * S + 7) (2 * S - 1 + j) (by omega)]
  rw [spikeAtList_getD 1 8 j (by omega)]
  simp; omega

/-- Cert: caEvolve 5 (spikeAtList 5 12) at position 0 = true.
    This is drop(2S-1) of (caEvolve 5 (spikeAtList (2S+4) (2S+11))) at position 0.
    Spike at 2S+4 in tape 2S+11: drop(2S-1) gives spike at 5 in tape 12. -/
private lemma rightEdgeF6_ev5_pos2Sm1_cert :
    (caEvolve 5 (spikeAtList 5 12)).getD 0 false = true := by native_decide

private lemma rightEdgeF6_ev5_pos2Sm1 (S : ℕ) (hS : 4 ≤ S) :
    (caEvolve 5 (spikeAtList (2 * S + 4) (2 * S + 11))).getD (2 * S - 1) false = true := by
  rw [caEvolve_getD_shift 5 _ (2 * S - 1)]
  apply (caEvolve_agree 5 _ (spikeAtList 5 12) (by
    rw [List.length_drop, spikeAtList_length]; omega) (by
    rw [spikeAtList_length]; omega) (fun j hj => ?_)).trans rightEdgeF6_ev5_pos2Sm1_cert
  rw [show ((spikeAtList (2 * S + 4) (2 * S + 11)).drop (2 * S - 1)).getD j false =
       (spikeAtList (2 * S + 4) (2 * S + 11)).getD (2 * S - 1 + j) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  rw [spikeAtList_getD (2 * S + 4) (2 * S + 11) (2 * S - 1 + j) (by omega)]
  rw [spikeAtList_getD 5 12 j (by omega)]
  simp; omega

-- spikeAtList_caEvolve_far_false is now defined in SubcaseB_m4_RightEdge (imported above)

private lemma rightEdgeF6_ev3_spike_far_false (S i : ℕ) (hi : i + 6 < 2 * S) (hS : 1 ≤ S) :
    (caEvolve 3 (spikeAtList (2 * S) (2 * S + 7))).getD i false = false :=
  spikeAtList_caEvolve_far_false 3 (2 * S) (2 * S + 7) i (by omega) (by omega)

private lemma rightEdgeF6_ev5_spike_far_false (S i : ℕ) (hi : i + 10 < 2 * S + 4) (hS : 1 ≤ S) :
    (caEvolve 5 (spikeAtList (2 * S + 4) (2 * S + 11))).getD i false = false :=
  spikeAtList_caEvolve_far_false 5 (2 * S + 4) (2 * S + 11) i (by omega) (by omega)

/-- Certs for positions 2S-3..2S-2 of the inner tapes.
    These are within the causal cone of the spike, so we need small native_decide certs. -/

-- Near-zone certs for j=1..6 (j = 2*S - i).
-- LHS (ev3): caEvolve 3 (spikeAtList j (j+7)) = dropping spikeAtList(2*S)(2*S+7) by i=2*S-j
-- RHS (ev5): caEvolve 5 (spikeAtList (j+4) (j+11)) = dropping spikeAtList(2*S+4)(2*S+11) by i=2*S-j
private lemma rightEdgeF6_ev3_pos_near_cert_j1 :
    (caEvolve 3 (spikeAtList 1 8)).getD 0 false = true := by native_decide
private lemma rightEdgeF6_ev3_pos_near_cert_j2 :
    (caEvolve 3 (spikeAtList 2 9)).getD 0 false = true := by native_decide
private lemma rightEdgeF6_ev3_pos_near_cert_j3 :
    (caEvolve 3 (spikeAtList 3 10)).getD 0 false = true := by native_decide
private lemma rightEdgeF6_ev3_pos_near_cert_j4 :
    (caEvolve 3 (spikeAtList 4 11)).getD 0 false = false := by native_decide
private lemma rightEdgeF6_ev3_pos_near_cert_j5 :
    (caEvolve 3 (spikeAtList 5 12)).getD 0 false = true := by native_decide
private lemma rightEdgeF6_ev3_pos_near_cert_j6 :
    (caEvolve 3 (spikeAtList 6 13)).getD 0 false = true := by native_decide

private lemma rightEdgeF6_ev5_pos_near_cert_j1 :
    (caEvolve 5 (spikeAtList 5 12)).getD 0 false = true := by native_decide
private lemma rightEdgeF6_ev5_pos_near_cert_j2 :
    (caEvolve 5 (spikeAtList 6 13)).getD 0 false = true := by native_decide
private lemma rightEdgeF6_ev5_pos_near_cert_j3 :
    (caEvolve 5 (spikeAtList 7 14)).getD 0 false = true := by native_decide
private lemma rightEdgeF6_ev5_pos_near_cert_j4 :
    (caEvolve 5 (spikeAtList 8 15)).getD 0 false = false := by native_decide
private lemma rightEdgeF6_ev5_pos_near_cert_j5 :
    (caEvolve 5 (spikeAtList 9 16)).getD 0 false = true := by native_decide
private lemma rightEdgeF6_ev5_pos_near_cert_j6 :
    (caEvolve 5 (spikeAtList 10 17)).getD 0 false = true := by native_decide

-- G period-256 near-zone certs (ev259 right spike):
-- (caEvolve 259 (spikeAtList (512+j) 520)).getD 0 false for j=1..6
private lemma rightEdgeG6_ev259_near_cert_j1 :
    (caEvolve 259 (spikeAtList 513 520)).getD 0 false = true := by native_decide
private lemma rightEdgeG6_ev259_near_cert_j2 :
    (caEvolve 259 (spikeAtList 514 520)).getD 0 false = true := by native_decide
private lemma rightEdgeG6_ev259_near_cert_j3 :
    (caEvolve 259 (spikeAtList 515 520)).getD 0 false = true := by native_decide
private lemma rightEdgeG6_ev259_near_cert_j4 :
    (caEvolve 259 (spikeAtList 516 520)).getD 0 false = false := by native_decide
private lemma rightEdgeG6_ev259_near_cert_j5 :
    (caEvolve 259 (spikeAtList 517 520)).getD 0 false = true := by native_decide
private lemma rightEdgeG6_ev259_near_cert_j6 :
    (caEvolve 259 (spikeAtList 518 520)).getD 0 false = true := by native_decide

/-- Reduce near-zone position to canonical cert form for ev3.
    For i = 2*S - j (j ∈ 1..6, S ≥ 7):
    (caEvolve 3 (spikeAtList (2*S) (2*S+7))).getD (2*S-j) false
    = (caEvolve 3 (spikeAtList j (j+7))).getD 0 false  -/
private lemma rightEdgeF6_ev3_near_reduce (S j : ℕ) (hS : 7 ≤ S) (hj1 : 1 ≤ j) (hj6 : j ≤ 6) :
    (caEvolve 3 (spikeAtList (2 * S) (2 * S + 7))).getD (2 * S - j) false =
    (caEvolve 3 (spikeAtList j (j + 7))).getD 0 false := by
  rw [caEvolve_getD_shift 3 _ (2 * S - j), caEvolve_getD_shift 3 _ 0]
  simp only [List.drop_zero]
  apply caEvolve_agree 3
  · rw [List.length_drop, spikeAtList_length]; omega
  · rw [spikeAtList_length]; omega
  · intro k hk
    have hb1 : 2 * S - j + k < 2 * S + 7 := by omega
    have hb2 : k < j + 7 := by omega
    rw [show ((spikeAtList (2 * S) (2 * S + 7)).drop (2 * S - j)).getD k false =
         (spikeAtList (2 * S) (2 * S + 7)).getD (2 * S - j + k) false from by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
    rw [spikeAtList_getD (2 * S) (2 * S + 7) (2 * S - j + k) (by omega)]
    rw [spikeAtList_getD j (j + 7) k (by omega)]
    simp [show 2 * S - j + k = 2 * S ↔ k = j from by omega]

/-- Same for ev5 inner tape (shifted by 4, evolved 5 steps). -/
private lemma rightEdgeF6_ev5_near_reduce (S j : ℕ) (hS : 7 ≤ S) (hj1 : 1 ≤ j) (hj6 : j ≤ 6) :
    (caEvolve 5 (spikeAtList (2 * S + 4) (2 * S + 11))).getD (2 * S - j) false =
    (caEvolve 5 (spikeAtList (j + 4) (j + 11))).getD 0 false := by
  rw [caEvolve_getD_shift 5 _ (2 * S - j), caEvolve_getD_shift 5 _ 0]
  simp only [List.drop_zero]
  apply caEvolve_agree 5
  · rw [List.length_drop, spikeAtList_length]; omega
  · rw [spikeAtList_length]; omega
  · intro k hk
    have hb1 : 2 * S - j + k < 2 * S + 11 := by omega
    have hb2 : k < j + 11 := by omega
    rw [show ((spikeAtList (2 * S + 4) (2 * S + 11)).drop (2 * S - j)).getD k false =
         (spikeAtList (2 * S + 4) (2 * S + 11)).getD (2 * S - j + k) false from by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
    rw [spikeAtList_getD (2 * S + 4) (2 * S + 11) (2 * S - j + k) (by omega)]
    rw [spikeAtList_getD (j + 4) (j + 11) k (by omega)]
    simp [show 2 * S - j + k = 2 * S + 4 ↔ k = j + 4 from by omega]

/-- Combined agreement: positions 0..2S-1 agree between ev3 and ev5 tapes. -/
private lemma rightEdgeF6_inner_agree (S : ℕ) (hS : 7 ≤ S) (i : ℕ) (hi : i ≤ 2 * S - 1) :
    (caEvolve 3 (spikeAtList (2 * S) (2 * S + 7))).getD i false =
    (caEvolve 5 (spikeAtList (2 * S + 4) (2 * S + 11))).getD i false := by
  -- Far zone: i + 6 < 2*S (spike outside causal cone → both false)
  by_cases hfar : i + 6 < 2 * S
  · rw [rightEdgeF6_ev3_spike_far_false S i hfar (by omega)]
    rw [rightEdgeF6_ev5_spike_far_false S i (by omega) (by omega)]
  · -- Near zone: 2*S - 6 ≤ i ≤ 2*S - 1, i.e. j := 2*S - i ∈ {1..6}
    push_neg at hfar
    have hj_lo : 1 ≤ 2 * S - i := by omega
    have hj_hi : 2 * S - i ≤ 6 := by omega
    set j := 2 * S - i with hj_def
    have hi_eq : i = 2 * S - j := by omega
    rw [hi_eq]
    rw [rightEdgeF6_ev3_near_reduce S j (by omega) hj_lo hj_hi]
    rw [rightEdgeF6_ev5_near_reduce S j (by omega) hj_lo hj_hi]
    -- Now: compare (caEvolve 3 (spikeAtList j (j+7)))[0] with (caEvolve 5 (spikeAtList (j+4) (j+11)))[0]
    -- These are the fixed certs j=1..6
    rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 from by omega)
      with hj|hj|hj|hj|hj|hj
    · simp only [hj]; exact rightEdgeF6_ev3_pos_near_cert_j1.trans rightEdgeF6_ev5_pos_near_cert_j1.symm
    · simp only [hj]; exact rightEdgeF6_ev3_pos_near_cert_j2.trans rightEdgeF6_ev5_pos_near_cert_j2.symm
    · simp only [hj]; exact rightEdgeF6_ev3_pos_near_cert_j3.trans rightEdgeF6_ev5_pos_near_cert_j3.symm
    · simp only [hj]; exact rightEdgeF6_ev3_pos_near_cert_j4.trans rightEdgeF6_ev5_pos_near_cert_j4.symm
    · simp only [hj]; exact rightEdgeF6_ev3_pos_near_cert_j5.trans rightEdgeF6_ev5_pos_near_cert_j5.symm
    · simp only [hj]; exact rightEdgeF6_ev3_pos_near_cert_j6.trans rightEdgeF6_ev5_pos_near_cert_j6.symm

/-- F period 2 for k=6. -/
theorem rightEdgeF_period2_k6 (T : ℕ) (hT : 10 ≤ T) :
    rightEdgeF 6 (T + 2) = rightEdgeF 6 T := by
  simp only [rightEdgeF]
  set S := T - 3 with hS_def
  have h1 : 2 * (T + 2) - 6 = 2 * S + 4 := by omega
  have h2 : 2 * (T + 2) + 1 = 2 * S + 11 := by omega
  have h3 : 2 * T - 6 = 2 * S := by omega
  have h4 : 2 * T + 1 = 2 * S + 7 := by omega
  rw [h1, h2, h3, h4]
  rw [show T + 2 = (S - 1) + 1 + 5 from by omega]
  rw [show T = (S - 1) + 1 + 3 from by omega]
  rw [caEvolve_add (S - 1 + 1) 5, caEvolve_add (S - 1 + 1) 3]
  rw [caEvolve_add (S - 1) 1, caEvolve_add (S - 1) 1]
  set tape1 := caEvolve 5 (spikeAtList (2 * S + 4) (2 * S + 11))
  set tape2 := caEvolve 3 (spikeAtList (2 * S) (2 * S + 7))
  simp only [caEvolve_succ, caEvolve_zero]
  have hlen1 : tape1.length = 2 * S + 1 := by
    simp only [tape1]
    have := caEvolve_length_le 5 (spikeAtList (2 * S + 4) (2 * S + 11))
              (by rw [spikeAtList_length]; omega)
    rw [spikeAtList_length] at this; omega
  have hlen2 : tape2.length = 2 * S + 1 := by
    simp only [tape2]
    have := caEvolve_length_le 3 (spikeAtList (2 * S) (2 * S + 7))
              (by rw [spikeAtList_length]; omega)
    rw [spikeAtList_length] at this; omega
  have hstep_agree : ∀ i, i < (caStepList tape1).length →
      (caStepList tape1).getD i false = (caStepList tape2).getD i false := by
    apply rightEdge_caStep_agree S (by omega) tape1 tape2 hlen1 hlen2
    · intro i hi
      simp only [tape1, tape2]
      exact (rightEdgeF6_inner_agree S (by omega) i hi).symm
    · exact rightEdgeF6_ev5_pos2Sm1 S (by omega)
    · exact rightEdgeF6_ev3_pos2Sm1 S (by omega)
  have hstep_len1 : (caStepList tape1).length = 2 * S - 1 := by
    have := caStep_length tape1 (by omega); omega
  have hstep_len2 : (caStepList tape2).length = 2 * S - 1 := by
    have := caStep_length tape2 (by omega); omega
  apply caEvolve_agree (S - 1)
  · rw [hstep_len1]; omega
  · rw [hstep_len2]; omega
  · intro i hi
    exact hstep_agree i (by rw [hstep_len1]; omega)

/-- F period 256 for k=6 (derived from period-2). -/
theorem rightEdgeF_period256_k6 (T : ℕ) (hT : 100 ≤ T) :
    rightEdgeF 6 (T + 256) = rightEdgeF 6 T := by
  -- 256 = 2 * 128; apply period-2 inductively 128 times
  have h : ∀ j : ℕ, T ≤ T + j * 2 → rightEdgeF 6 (T + j * 2) = rightEdgeF 6 T := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro _
      have step : rightEdgeF 6 (T + j * 2 + 2) = rightEdgeF 6 (T + j * 2) :=
        rightEdgeF_period2_k6 (T + j * 2) (by omega)
      rw [show T + (j + 1) * 2 = T + j * 2 + 2 from by omega]
      rw [step, ih (by omega)]
  have := h 128 (by omega)
  simp only [show 128 * 2 = 256 from by omega] at this
  exact this

/-!
## G period 256 for k=6, m=22

rightEdgeG 6 22 T = (caEvolve T (twoSpikeList 22 (2T-6) (2T+1))).getD 0 false

Strategy: Same as F but with an additional spike at fixed position 22.
  - Left zone (positions i ≤ 22): use rule30n_spikeAt22_period256 (existing)
  - Right zone (positions 23..2S-1): same as F (left spike outside causal cone)
  - Boundary (position 2S-1): true (same cert as F, since right-spike dominates)

The key: positions i ≤ 22 of ev3(twoSpikeList 22 (2S) (2S+7)) agree with
ev3(spikeAtList 22 (2S+7)) because the right spike at 2S is outside the 3-step
causal cone of position i ≤ 22 (for S ≥ 22+3 = 25, position 2S-3 ≥ 47 > 22).
Then rule30n_spikeAt22_period256 gives the T ↦ T+256 agreement.
-/

/-- For positions i ≤ 22 of ev3(twoSpikeList 22 (2S) (2S+7)):
    the right spike at 2S is outside the 3-step causal cone when S ≥ 25. -/
private lemma rightEdgeG6_ev3_left_eq_spike22 (S i : ℕ) (hS : 25 ≤ S) (hi : i ≤ 22) :
    (caEvolve 3 (twoSpikeList 22 (2 * S) (2 * S + 7))).getD i false =
    (caEvolve 3 (spikeAtList 22 (2 * S + 7))).getD i false := by
  rw [caEvolve_getD_shift 3 _ i, caEvolve_getD_shift 3 _ i]
  apply caEvolve_agree 3
  · simp only [List.length_drop]
    have : (twoSpikeList 22 (2 * S) (2 * S + 7)).length = 2 * S + 7 := by
      rw [twoSpikeList_length]
    rw [this]; omega
  · rw [List.length_drop, spikeAtList_length]; omega
  · intro j hj
    have hbound : i + j < 2 * S + 7 := by omega
    rw [show ((twoSpikeList 22 (2 * S) (2 * S + 7)).drop i).getD j false =
         (twoSpikeList 22 (2 * S) (2 * S + 7)).getD (i + j) false from by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
    rw [show ((spikeAtList 22 (2 * S + 7)).drop i).getD j false =
         (spikeAtList 22 (2 * S + 7)).getD (i + j) false from by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
    rw [twoSpikeList_getD 22 (2 * S) (2 * S + 7) (i + j) (by omega)]
    rw [spikeAtList_getD 22 (2 * S + 7) (i + j) (by omega)]
    simp [show (i + j = 22 ∨ i + j = 2 * S) ↔ i + j = 22 from by omega]

/-- For positions i ≤ 22 of ev259(twoSpikeList 22 (2S+512) (2S+519)):
    the right spike at 2S+512 is outside the 259-step causal cone when S ≥ 130. -/
private lemma rightEdgeG6_ev259_left_eq_spike22 (S i : ℕ) (hS : 130 ≤ S) (hi : i ≤ 22) :
    (caEvolve 259 (twoSpikeList 22 (2 * S + 512) (2 * S + 519))).getD i false =
    (caEvolve 259 (spikeAtList 22 (2 * S + 519))).getD i false := by
  rw [caEvolve_getD_shift 259 _ i, caEvolve_getD_shift 259 _ i]
  apply caEvolve_agree 259
  · simp only [List.length_drop]
    have : (twoSpikeList 22 (2 * S + 512) (2 * S + 519)).length = 2 * S + 519 := by
      rw [twoSpikeList_length]
    rw [this]; omega
  · rw [List.length_drop, spikeAtList_length]; omega
  · intro j hj
    have hbound : i + j < 2 * S + 519 := by omega
    rw [show ((twoSpikeList 22 (2 * S + 512) (2 * S + 519)).drop i).getD j false =
         (twoSpikeList 22 (2 * S + 512) (2 * S + 519)).getD (i + j) false from by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
    rw [show ((spikeAtList 22 (2 * S + 519)).drop i).getD j false =
         (spikeAtList 22 (2 * S + 519)).getD (i + j) false from by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
    rw [twoSpikeList_getD 22 (2 * S + 512) (2 * S + 519) (i + j) (by omega)]
    rw [spikeAtList_getD 22 (2 * S + 519) (i + j) (by omega)]
    -- i + j ≤ i + 518 ≤ 22 + 518 = 540 < 2*130+512 = 772 ≤ 2*S+512
    simp [show (i + j = 22 ∨ i + j = 2 * S + 512) ↔ i + j = 22 from by omega]

/-- spike-at-22 period: ev3 at position i = ev259 at position i, for i ≤ 22 and S ≥ 130.
    Both sides reduce to (caEvolve 3 (spikeAtList 22 45)).getD i via
    caEvolve_spikeAt_agree + caEvolve_cert_m22_p256. -/
private lemma rightEdgeG6_spike22_period (S i : ℕ) (hS : 130 ≤ S) (hi : i ≤ 22) :
    (caEvolve 3 (spikeAtList 22 (2 * S + 7))).getD i false =
    (caEvolve 259 (spikeAtList 22 (2 * S + 519))).getD i false := by
  -- Reduce LHS to canonical size 45
  rw [caEvolve_spikeAt_agree 3 22 (2 * S + 7) 45 i (by omega) (by omega)]
  -- Reduce RHS: first reduce size, then split 259 = 256+3 and apply cert
  rw [caEvolve_spikeAt_agree 259 22 (2 * S + 519) 557 i (by omega) (by omega)]
  rw [show (259 : ℕ) = 3 + 256 from by omega, caEvolve_add 3 256]
  rw [caEvolve_cert_m22_p256]

/-- For positions 23..2S-1 of both G inner tapes: the left spike at 22 is outside
    the causal cone, so both reduce to the F case (both false). -/
private lemma rightEdgeG6_ev3_right_eq_F (S i : ℕ) (hS : 4 ≤ S) (hi23 : 23 ≤ i) (hiS : i ≤ 2 * S - 1) :
    (caEvolve 3 (twoSpikeList 22 (2 * S) (2 * S + 7))).getD i false =
    (caEvolve 3 (spikeAtList (2 * S) (2 * S + 7))).getD i false := by
  rw [caEvolve_getD_shift 3 _ i, caEvolve_getD_shift 3 _ i]
  apply caEvolve_agree 3
  · simp only [List.length_drop]
    have : (twoSpikeList 22 (2 * S) (2 * S + 7)).length = 2 * S + 7 := by
      rw [twoSpikeList_length]
    rw [this]; omega
  · rw [List.length_drop, spikeAtList_length]; omega
  · intro j hj
    have hbound : i + j < 2 * S + 7 := by omega
    rw [show ((twoSpikeList 22 (2 * S) (2 * S + 7)).drop i).getD j false =
         (twoSpikeList 22 (2 * S) (2 * S + 7)).getD (i + j) false from by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
    rw [show ((spikeAtList (2 * S) (2 * S + 7)).drop i).getD j false =
         (spikeAtList (2 * S) (2 * S + 7)).getD (i + j) false from by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
    rw [twoSpikeList_getD 22 (2 * S) (2 * S + 7) (i + j) (by omega)]
    rw [spikeAtList_getD (2 * S) (2 * S + 7) (i + j) (by omega)]
    -- i + j ≥ 23 > 22
    simp [show (i + j = 22 ∨ i + j = 2 * S) ↔ i + j = 2 * S from by omega]

private lemma rightEdgeG6_ev259_right_eq_F (S i : ℕ) (hS : 130 ≤ S) (hi23 : 23 ≤ i) (hiS : i ≤ 2 * S - 1) :
    (caEvolve 259 (twoSpikeList 22 (2 * S + 512) (2 * S + 519))).getD i false =
    (caEvolve 259 (spikeAtList (2 * S + 512) (2 * S + 519))).getD i false := by
  rw [caEvolve_getD_shift 259 _ i, caEvolve_getD_shift 259 _ i]
  apply caEvolve_agree 259
  · simp only [List.length_drop]
    have : (twoSpikeList 22 (2 * S + 512) (2 * S + 519)).length = 2 * S + 519 := by
      rw [twoSpikeList_length]
    rw [this]; omega
  · rw [List.length_drop, spikeAtList_length]; omega
  · intro j hj
    have hbound : i + j < 2 * S + 519 := by omega
    rw [show ((twoSpikeList 22 (2 * S + 512) (2 * S + 519)).drop i).getD j false =
         (twoSpikeList 22 (2 * S + 512) (2 * S + 519)).getD (i + j) false from by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
    rw [show ((spikeAtList (2 * S + 512) (2 * S + 519)).drop i).getD j false =
         (spikeAtList (2 * S + 512) (2 * S + 519)).getD (i + j) false from by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
    rw [twoSpikeList_getD 22 (2 * S + 512) (2 * S + 519) (i + j) (by omega)]
    rw [spikeAtList_getD (2 * S + 512) (2 * S + 519) (i + j) (by omega)]
    simp [show (i + j = 22 ∨ i + j = 2 * S + 512) ↔ i + j = 2 * S + 512 from by omega]

/-- G inner tapes agree on 0..2S-1 between T and T+256. -/
private lemma rightEdgeG6_inner_agree (S : ℕ) (hS : 130 ≤ S) (i : ℕ) (hi : i ≤ 2 * S - 1) :
    (caEvolve 3 (twoSpikeList 22 (2 * S) (2 * S + 7))).getD i false =
    (caEvolve 259 (twoSpikeList 22 (2 * S + 512) (2 * S + 519))).getD i false := by
  by_cases hi22 : i ≤ 22
  · -- Left zone: reduce to spikeAtList 22, use period-256
    rw [rightEdgeG6_ev3_left_eq_spike22 S i (by omega) hi22]
    rw [rightEdgeG6_ev259_left_eq_spike22 S i hS hi22]
    exact rightEdgeG6_spike22_period S i hS hi22
  · -- Right zone (23 ≤ i ≤ 2*S-1): strip left spike at 22, compare right spikes
    push_neg at hi22
    have hi23 : 23 ≤ i := by omega
    rw [rightEdgeG6_ev3_right_eq_F S i (by omega) hi23 hi]
    rw [rightEdgeG6_ev259_right_eq_F S i hS hi23 hi]
    -- Now compare caEvolve 3 (spikeAtList (2*S) (2*S+7)) with caEvolve 259 (spikeAtList (2*S+512) (2*S+519))
    -- Far zone: i + 518 < 2*S + 512 (equiv i + 6 < 2*S) → ev259 false; i + 6 < 2*S → ev3 false
    by_cases hfar : i + 6 < 2 * S
    · rw [rightEdgeF6_ev3_spike_far_false S i hfar (by omega)]
      exact (spikeAtList_caEvolve_far_false 259 (2 * S + 512) (2 * S + 519) i (by omega) (by omega)).symm
    · -- Near zone: 2*S - 6 ≤ i ≤ 2*S - 1, j := 2*S - i ∈ {1..6}
      push_neg at hfar
      have hj_lo : 1 ≤ 2 * S - i := by omega
      have hj_hi : 2 * S - i ≤ 6 := by omega
      set j := 2 * S - i with hj_def
      have hi_eq : i = 2 * S - j := by omega
      rw [hi_eq]
      -- Reduce LHS to cert
      rw [rightEdgeF6_ev3_near_reduce S j (by omega) hj_lo hj_hi]
      -- Reduce RHS (ev259 of right spike) to cert via spikeAt_agree
      rw [caEvolve_getD_shift 259 _ (2 * S - j)]
      -- After dropping: spike at 2*S+512-(2*S-j) = 512+j, tape length 519+j
      -- Reduce to canonical size 520 via caEvolve_spikeAt_agree
      have hrhs : (caEvolve 259 ((spikeAtList (2 * S + 512) (2 * S + 519)).drop (2 * S - j))).getD 0 false =
                  (caEvolve 259 (spikeAtList (512 + j) 520)).getD 0 false := by
        apply caEvolve_agree 259
        · rw [List.length_drop, spikeAtList_length]; omega
        · rw [spikeAtList_length]; omega
        · intro k hk
          have hb1 : 2 * S - j + k < 2 * S + 519 := by omega
          have hb2 : k < 520 := by omega
          rw [show ((spikeAtList (2 * S + 512) (2 * S + 519)).drop (2 * S - j)).getD k false =
               (spikeAtList (2 * S + 512) (2 * S + 519)).getD (2 * S - j + k) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
          rw [spikeAtList_getD (2 * S + 512) (2 * S + 519) (2 * S - j + k) (by omega)]
          rw [spikeAtList_getD (512 + j) 520 k (by omega)]
          simp [show (2 * S - j + k = 2 * S + 512) ↔ (k = 512 + j) from by omega]
      rw [hrhs]
      -- Now compare cert values for j=1..6
      rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 from by omega)
        with hj|hj|hj|hj|hj|hj
      · simp only [hj]; exact rightEdgeF6_ev3_pos_near_cert_j1.trans rightEdgeG6_ev259_near_cert_j1.symm
      · simp only [hj]; exact rightEdgeF6_ev3_pos_near_cert_j2.trans rightEdgeG6_ev259_near_cert_j2.symm
      · simp only [hj]; exact rightEdgeF6_ev3_pos_near_cert_j3.trans rightEdgeG6_ev259_near_cert_j3.symm
      · simp only [hj]; exact rightEdgeF6_ev3_pos_near_cert_j4.trans rightEdgeG6_ev259_near_cert_j4.symm
      · simp only [hj]; exact rightEdgeF6_ev3_pos_near_cert_j5.trans rightEdgeG6_ev259_near_cert_j5.symm
      · simp only [hj]; exact rightEdgeF6_ev3_pos_near_cert_j6.trans rightEdgeG6_ev259_near_cert_j6.symm

/-- G period-256 boundary cert: position 2S-1 of ev3(twoSpikeList 22 (2S) (2S+7)) = true. -/
private lemma rightEdgeG6_ev3_pos2Sm1 (S : ℕ) (hS : 12 ≤ S) :
    (caEvolve 3 (twoSpikeList 22 (2 * S) (2 * S + 7))).getD (2 * S - 1) false = true := by
  rw [caEvolve_getD_shift 3 _ (2 * S - 1)]
  apply (caEvolve_agree 3 _ (spikeAtList 1 8) (by
    simp only [List.length_drop]
    have : (twoSpikeList 22 (2 * S) (2 * S + 7)).length = 2 * S + 7 := by
      rw [twoSpikeList_length]
    rw [this]; omega) (by rw [spikeAtList_length]; omega) (fun j hj => ?_)).trans
    rightEdgeF6_ev3_pos2Sm1_cert
  have hbound : 2 * S - 1 + j < 2 * S + 7 := by omega
  -- For S ≥ 12 and j ≤ 6: 2*S-1+j ≥ 23 > 22, so left spike at 22 is irrelevant
  rw [show ((twoSpikeList 22 (2 * S) (2 * S + 7)).drop (2 * S - 1)).getD j false =
       (twoSpikeList 22 (2 * S) (2 * S + 7)).getD (2 * S - 1 + j) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  rw [twoSpikeList_getD 22 (2 * S) (2 * S + 7) (2 * S - 1 + j) (by omega)]
  rw [spikeAtList_getD 1 8 j (by omega)]
  simp [show (2 * S - 1 + j = 22 ∨ 2 * S - 1 + j = 2 * S) ↔ j = 1 from by omega]

/-- Cert: right spike j=1 for ev259. -/
private lemma rightEdgeG6_ev259_pos2Sm1_cert :
    (caEvolve 259 (spikeAtList 513 520)).getD 0 false = true := by native_decide

private lemma rightEdgeG6_ev259_pos2Sm1 (S : ℕ) (hS : 130 ≤ S) :
    (caEvolve 259 (twoSpikeList 22 (2 * S + 512) (2 * S + 519))).getD (2 * S - 1) false = true := by
  rw [caEvolve_getD_shift 259 _ (2 * S - 1)]
  apply (caEvolve_agree 259 _ (spikeAtList 513 520) (by
    simp only [List.length_drop]
    have : (twoSpikeList 22 (2 * S + 512) (2 * S + 519)).length = 2 * S + 519 := by
      rw [twoSpikeList_length]
    rw [this]; omega) (by rw [spikeAtList_length]; omega) (fun j hj => ?_)).trans
    rightEdgeG6_ev259_pos2Sm1_cert
  have hbound : 2 * S - 1 + j < 2 * S + 519 := by omega
  have hj_lt : j < 520 := by omega
  rw [show ((twoSpikeList 22 (2 * S + 512) (2 * S + 519)).drop (2 * S - 1)).getD j false =
       (twoSpikeList 22 (2 * S + 512) (2 * S + 519)).getD (2 * S - 1 + j) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  rw [twoSpikeList_getD 22 (2 * S + 512) (2 * S + 519) (2 * S - 1 + j) (by omega)]
  rw [spikeAtList_getD 513 520 j (by omega)]
  simp [show (2 * S - 1 + j = 22 ∨ 2 * S - 1 + j = 2 * S + 512) ↔ j = 513 from by omega]

/-- G period 256 for k=6, m=22. -/
theorem rightEdgeG_period256_k6 (T : ℕ) (hT : 200 ≤ T) :
    rightEdgeG 6 22 (T + 256) = rightEdgeG 6 22 T := by
  simp only [rightEdgeG]
  set S := T - 3 with hS_def
  have h1 : 2 * (T + 256) - 6 = 2 * S + 512 := by omega
  have h2 : 2 * (T + 256) + 1 = 2 * S + 519 := by omega
  have h3 : 2 * T - 6 = 2 * S := by omega
  have h4 : 2 * T + 1 = 2 * S + 7 := by omega
  rw [h1, h2, h3, h4]
  rw [show T + 256 = (S - 1) + 1 + 259 from by omega]
  rw [show T = (S - 1) + 1 + 3 from by omega]
  rw [caEvolve_add (S - 1 + 1) 259, caEvolve_add (S - 1 + 1) 3]
  rw [caEvolve_add (S - 1) 1, caEvolve_add (S - 1) 1]
  set tape1 := caEvolve 259 (twoSpikeList 22 (2 * S + 512) (2 * S + 519))
  set tape2 := caEvolve 3 (twoSpikeList 22 (2 * S) (2 * S + 7))
  simp only [caEvolve_succ, caEvolve_zero]
  have hlen1 : tape1.length = 2 * S + 1 := by
    simp only [tape1]
    have := caEvolve_length_le 259 (twoSpikeList 22 (2 * S + 512) (2 * S + 519))
              (by rw [twoSpikeList_length]; omega)
    rw [twoSpikeList_length] at this; omega
  have hlen2 : tape2.length = 2 * S + 1 := by
    simp only [tape2]
    have := caEvolve_length_le 3 (twoSpikeList 22 (2 * S) (2 * S + 7))
              (by rw [twoSpikeList_length]; omega)
    rw [twoSpikeList_length] at this; omega
  have hstep_agree : ∀ i, i < (caStepList tape1).length →
      (caStepList tape1).getD i false = (caStepList tape2).getD i false := by
    apply rightEdge_caStep_agree S (by omega) tape1 tape2 hlen1 hlen2
    · intro i hi
      simp only [tape1, tape2]
      exact (rightEdgeG6_inner_agree S (by omega) i hi).symm
    · exact rightEdgeG6_ev259_pos2Sm1 S (by omega)
    · exact rightEdgeG6_ev3_pos2Sm1 S (by omega)
  have hstep_len1 : (caStepList tape1).length = 2 * S - 1 := by
    have := caStep_length tape1 (by omega); omega
  have hstep_len2 : (caStepList tape2).length = 2 * S - 1 := by
    have := caStep_length tape2 (by omega); omega
  apply caEvolve_agree (S - 1)
  · rw [hstep_len1]; omega
  · rw [hstep_len2]; omega
  · intro i hi
    exact hstep_agree i (by rw [hstep_len1]; omega)

/-!
## Period propagation and base case
-/

lemma rightEdgeSens_step256_k6 (T : ℕ) (hT : 200 ≤ T) (h : rightEdgeSens 6 22 T) :
    rightEdgeSens 6 22 (T + 256) := by
  simp only [rightEdgeSens]
  rwa [rightEdgeF_period256_k6 T (by omega), rightEdgeG_period256_k6 T hT]

lemma rightEdgeSens_iterated256_k6 (T₀ j : ℕ) (hT₀ : 200 ≤ T₀)
    (h : rightEdgeSens 6 22 T₀) : rightEdgeSens 6 22 (T₀ + j * 256) := by
  induction j with
  | zero => simp [h]
  | succ j ih =>
    have : T₀ + (j + 1) * 256 = (T₀ + j * 256) + 256 := by omega
    rw [this]
    exact rightEdgeSens_step256_k6 _ (by omega) ih

/-- Base case: sensitivity at T=271 (n'=270, n'%256=14). -/
lemma rightEdgeSens_base_271_k6 : rightEdgeSens 6 22 271 := by
  simp only [rightEdgeSens, rightEdgeF, rightEdgeG]; native_decide

/-!
## hmod: SubcaseB m=22 fires only at n' ≡ 14 mod 256
-/

/-- Bridge: rule30n of spike-at-22 = caEvolve of spikeAtList. -/
private lemma rule30n_spikeAt22_bridge (n' : Nat) :
    rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) => decide (k.val = 22)) =
    (caEvolve (n' + 1) (spikeAtList 22 (2 * (n' + 1) + 1))).getD 0 false := by
  simp [rule30n, configToList, spikeAtList]

/-- Bridge: rule30n of twoSpike(22, last) = caEvolve of twoSpikeLastList. -/
private lemma rule30n_twoSpikeLast22_bridge (n' : Nat) :
    rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) => decide (k.val = 22 ∨ k.val = 2 * (n' + 1))) =
    (caEvolve (n' + 1) (twoSpikeLastList 22 (2 * (n' + 1) + 1))).getD 0 false := by
  simp [rule30n, configToList, twoSpikeLastList]

private lemma spikeAt22_period256_iter (n j : ℕ) :
    (caEvolve (n + 1) (spikeAtList 22 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + j * 256) + 1) (spikeAtList 22 (2 * ((n + j * 256) + 1) + 1))).getD 0 false := by
  induction j with
  | zero => simp
  | succ j ih =>
    have step := rule30n_spikeAt22_period256 (n + j * 256)
    rw [show n + (j + 1) * 256 = n + j * 256 + 256 from by omega]
    rw [show n + j * 256 + 256 + 1 = n + j * 256 + 1 + 256 from by omega]
    exact ih.trans step

private lemma twoSpikeLast22_period256_iter (n j : ℕ) (hn : n ≥ 22) :
    (caEvolve (n + 1) (twoSpikeLastList 22 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + j * 256) + 1) (twoSpikeLastList 22 (2 * ((n + j * 256) + 1) + 1))).getD 0 false := by
  induction j with
  | zero => simp
  | succ j ih =>
    have step := rule30n_twoSpikeLast22_period256 (n + j * 256) (by omega)
    rw [show n + (j + 1) * 256 = n + j * 256 + 256 from by omega]
    rw [show n + j * 256 + 256 + 1 = n + j * 256 + 1 + 256 from by omega]
    exact ih.trans step

-- SubcaseB for m=22 fires only at n' ≡ 14 mod 256 for n' in base range [270, 525].
-- Since 271 ≡ 15 mod 256, T = 271 + r covers all residues.
-- T = 271 + 255 = 526 corresponds to n'=525, 525 mod 256 = 13... wait, 270 mod 256 = 14, T=271≡15.
-- The ONLY firing case in T ∈ [271, 526] is T = 271 (n'=270, n'≡14 mod 256).
-- This corresponds to r = 0 (T = 271 + 0).
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m22_not_fires_other_residues_base :
    ∀ r : Fin 256, r.val ≠ 0 →
    ¬ ((caEvolve (271 + r.val) (spikeAtList 22 (2 * (271 + r.val) + 1))).getD 0 false = false ∧
       (caEvolve (271 + r.val) (twoSpikeLastList 22 (2 * (271 + r.val) + 1))).getD 0 false = true) := by
  native_decide

private lemma subcaseB_m22_hmod (n' : ℕ) (hn' : 3087 ≤ n')
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) => decide (k.val = 22)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = 22 ∨ k.val = 2 * (n' + 1))) = true) :
    n' % 256 = 14 := by
  rw [rule30n_spikeAt22_bridge] at hcase
  rw [rule30n_twoSpikeLast22_bridge] at hts
  -- Reduce to base range [270, 525] (T ∈ [271, 526])
  -- n'+1 = (271 + r_base) + j * 256 for some j and r_base ∈ [0, 255]
  set r_base := (n' + 1 - 271) % 256 with hr_base_def
  set j := (n' + 1 - 271) / 256 with hj_def
  have hn'1_eq : n' + 1 = 271 + r_base + j * 256 := by omega
  have hr_lt : r_base < 256 := Nat.mod_lt _ (by omega)
  -- Reduce F at n'+1 to base T = 271 + r_base using period-256
  have hF_base : (caEvolve (271 + r_base) (spikeAtList 22 (2 * (271 + r_base) + 1))).getD 0 false = false := by
    have eq := spikeAt22_period256_iter (271 + r_base - 1) j
    rw [show 271 + r_base - 1 + 1 = 271 + r_base from by omega] at eq
    rw [show 271 + r_base - 1 + j * 256 + 1 = n' + 1 from by omega] at eq
    rw [eq]; exact hcase
  have hG_base : (caEvolve (271 + r_base) (twoSpikeLastList 22 (2 * (271 + r_base) + 1))).getD 0 false = true := by
    have eq := twoSpikeLast22_period256_iter (271 + r_base - 1) j (by omega)
    rw [show 271 + r_base - 1 + 1 = 271 + r_base from by omega] at eq
    rw [show 271 + r_base - 1 + j * 256 + 1 = n' + 1 from by omega] at eq
    rw [eq]; exact hts
  have hr0 : r_base = 0 := by
    by_contra hr_ne
    exact subcaseB_m22_not_fires_other_residues_base ⟨r_base, by omega⟩ (by simpa) ⟨hF_base, hG_base⟩
  omega

/-!
## Main theorem
-/

theorem subcaseB_m22_ge3087_from_rightedge (n' : ℕ) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm22 : m.val = 22)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  have hcase22 : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) => decide (k.val = 22)) = false := by
    convert hcase using 2; ext k; rw [hm22]
  have hts22 : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = 22 ∨ k.val = 2 * (n' + 1))) = true := by
    convert hts using 2; ext k; rw [hm22]
  have hmod : n' % 256 = 14 := subcaseB_m22_hmod n' hn' hcase22 hts22
  obtain ⟨j, hj⟩ : ∃ j, n' + 1 = 271 + j * 256 := ⟨(n' + 1 - 271) / 256, by omega⟩
  have hsens : rightEdgeSens 6 22 (n' + 1) := by
    nth_rewrite 1 [hj]
    exact rightEdgeSens_iterated256_k6 271 j (by omega) rightEdgeSens_base_271_k6
  exact rightEdge_witness_gen n' 6 22 (by decide) (by omega) m hm22 hsens

end P2p
