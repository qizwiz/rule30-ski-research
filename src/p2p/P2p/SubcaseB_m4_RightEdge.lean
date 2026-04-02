/-
SubcaseB_m4_RightEdge.lean
==========================
Closes subcaseB_m4_ge3087 using RIGHT-EDGE WITNESSES.

Discovery (consult_20260402_m4_rightedge.md):
Instead of fixed-position witnesses (which lead to an infinite self-similar hierarchy),
use witnesses at fixed offsets FROM THE RIGHT EDGE of the causal cone:
  w = 2*(n'+1) - k, for k = 10

These witnesses have PERIOD 8 in n', with small certs (≤41 cells). The infinite
tower collapses because the reference frame changes.

STRUCTURE:
  SubcaseB fires at n' ≡ 5 mod 8 for n' ≥ 3087 (Python-verified):
    n' ≡ 5 mod 8 → witness k=10

  Period-8 axioms:
    rightEdgeF_period8_k10
    rightEdgeG_period8_k10

  Base case (1 native_decide): T = 3094

Self-contained: imports only Prize3_Complete and CausalConeLemmas.
-/

import P2p.Prize3_Complete
import P2p.CausalConeLemmas

namespace P2p

/-!
## Right-edge witness config and odd-free property
-/

/-- Config with a spike at position w in tape 2*(n+1)+1.
    This is the canonical "single spike" witness for SubcaseB. -/
def spikeConfigAt (w n : ℕ) : Config (n + 1) :=
  fun i => decide (i.val = w)

/-- spikeConfigAt at even position w has all odd positions = false. -/
lemma spikeConfigAt_odd_false (w n : ℕ) (hw : w % 2 = 0) :
    ∀ k : Fin (n + 1), spikeConfigAt w n ⟨2 * k.val + 1, by omega⟩ = false := by
  intro k
  simp only [spikeConfigAt, decide_eq_false_iff_not]
  omega

/-- rule30n of spikeConfigAt = caEvolve on spikeAtList. -/
lemma rule30n_spikeConfigAt_eq (w n : ℕ) :
    rule30n (n + 1) (spikeConfigAt w n) =
    (caEvolve (n + 1) (spikeAtList w (2 * (n + 1) + 1))).getD 0 false := by
  simp [rule30n, spikeConfigAt, configToList, spikeAtList]

/-- rule30n of flipCell(spikeConfigAt w n, m) = caEvolve of twoSpikeList. -/
lemma rule30n_flipCell_spikeConfigAt_eq (w n : ℕ) (m : Fin (2 * (n + 1) + 1))
    (hwm : w ≠ m.val) (hwb : w < 2 * (n + 1) + 1) :
    rule30n (n + 1) (flipCell (spikeConfigAt w n) m) =
    (caEvolve (n + 1) (twoSpikeList w m.val (2 * (n + 1) + 1))).getD 0 false := by
  simp only [rule30n]
  have hlist : configToList (flipCell (spikeConfigAt w n) m) =
               twoSpikeList w m.val (2 * (n + 1) + 1) := by
    apply List.ofFn_inj.mpr
    funext i
    show (if i = m then !decide (i.val = w) else decide (i.val = w)) =
         decide (i.val = w ∨ i.val = m.val)
    by_cases him : i = m
    · subst him
      simp [show i.val ≠ w from Ne.symm hwm]
    · have hine : i.val ≠ m.val := fun h => him (Fin.ext h)
      simp [him, hine]
  rw [hlist]

/-!
## Right-edge F/G definitions
-/

/-- F value for right-edge spike at offset k from right edge, at tape step T = n'+1. -/
def rightEdgeF (k T : ℕ) : Bool :=
  (caEvolve T (spikeAtList (2 * T - k) (2 * T + 1))).getD 0 false

/-- G value for twoSpike(m, right-edge-k) at tape step T. -/
def rightEdgeG (k m T : ℕ) : Bool :=
  (caEvolve T (twoSpikeList m (2 * T - k) (2 * T + 1))).getD 0 false

/-- Sensitivity: F ≠ G at step T for right-edge k witness vs m. -/
def rightEdgeSens (k m T : ℕ) : Prop :=
  rightEdgeF k T ≠ rightEdgeG k m T

/-!
## Period-8 proof via caEvolve_agree + caStep absorption

Strategy: Split T = (T-5) + 5 and T+8 = (T-5) + 13.
- rightEdgeF 10 T   = caEvolve (S-1) (caStep (caEvolve 5 (spikeAtList (2S) (2S+11))))[0]
- rightEdgeF 10 (T+8) = caEvolve (S-1) (caStep (caEvolve 13 (spikeAtList (2S+16) (2S+27))))[0]
where S = T-5.

After 5 (resp. 13) steps, the two intermediate tapes of length 2S+1 agree on
positions 0..2S-1 and differ only at position 2S. But position 2S-1 is true in both
(native_decide certs). Since R30(a, true, c) = !a regardless of c, one caStep
absorbs the difference, and the tapes agree everywhere after that.
-/

/-- Cert: position 2S-1 of caEvolve 5 (spikeAtList (2S) (2S+11)) = true.
    By caEvolve_getD_shift, this = caEvolve 5 (spikeAtList 1 12) at position 0.
    The drop-by-(2S-1) of spikeAtList (2S) (2S+11) has spike at position 1, length 12. -/
private lemma rightEdge_ev5_pos2Sm1_cert :
    (caEvolve 5 (spikeAtList 1 12)).getD 0 false = true := by native_decide

private lemma rightEdge_ev5_pos2Sm1 (S : ℕ) (hS : 6 ≤ S) :
    (caEvolve 5 (spikeAtList (2 * S) (2 * S + 11))).getD (2 * S - 1) false = true := by
  rw [caEvolve_getD_shift 5 _ (2 * S - 1)]
  apply (caEvolve_agree 5 _ (spikeAtList 1 12) (by
    rw [List.length_drop, spikeAtList_length]; omega) (by
    rw [spikeAtList_length]; omega) (fun j hj => ?_)).trans rightEdge_ev5_pos2Sm1_cert
  rw [show ((spikeAtList (2 * S) (2 * S + 11)).drop (2 * S - 1)).getD j false =
       (spikeAtList (2 * S) (2 * S + 11)).getD (2 * S - 1 + j) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  rw [spikeAtList_getD (2 * S) (2 * S + 11) (2 * S - 1 + j) (by omega)]
  rw [spikeAtList_getD 1 12 j (by omega)]
  simp; omega

/-- Cert: position 2S-1 of caEvolve 13 (spikeAtList (2S+16) (2S+27)) = true.
    By caEvolve_getD_shift, this = caEvolve 13 (spikeAtList 17 28) at position 0. -/
private lemma rightEdge_ev13_pos2Sm1_cert :
    (caEvolve 13 (spikeAtList 17 28)).getD 0 false = true := by native_decide

private lemma rightEdge_ev13_pos2Sm1 (S : ℕ) (hS : 6 ≤ S) :
    (caEvolve 13 (spikeAtList (2 * S + 16) (2 * S + 27))).getD (2 * S - 1) false = true := by
  rw [caEvolve_getD_shift 13 _ (2 * S - 1)]
  have h := caEvolve_spikeAt_agree 13 (2 * S + 16) (2 * S + 27) 28 (2 * S - 1)
    (by omega) (by omega)
  rw [h]
  exact rightEdge_ev13_pos2Sm1_cert

/-- Helper: caEvolve k of a spike at position 2S+2k in a (2S+2k+11)-cell tape is false
    at positions 0..2S-1. -/
private lemma rightEdge_spike_evolve_false (k S i : ℕ) (hi : i ≤ 2 * S - 1) (hS : 1 ≤ S) :
    (caEvolve k (spikeAtList (2 * S + 2 * k) (2 * S + 2 * k + 11))).getD i false = false := by
  rw [caEvolve_getD_shift k _ i]
  apply caEvolve_allFalse
  exact spikeAtList_drop_allFalse (2 * S + 2 * k) (2 * S + 2 * k + 11) i (by omega)

set_option maxHeartbeats 800000 in
private lemma rightEdge_spike_evolve_pos2S_cert5 :
    (caEvolve 5 (spikeAtList 10 21)).getD 0 false = true := by native_decide

set_option maxHeartbeats 800000 in
private lemma rightEdge_spike_evolve_pos2S_cert13 :
    (caEvolve 13 (spikeAtList 26 37)).getD 0 false = true := by native_decide

private lemma rightEdge_spike_evolve_pos2S_5 (S : ℕ) (hS : 6 ≤ S) :
    (caEvolve 5 (spikeAtList (2 * S) (2 * S + 11))).getD (2 * S) false = true := by
  rw [caEvolve_getD_shift 5 _ (2 * S)]
  have h := caEvolve_spikeAt_agree 5 (2 * S) (2 * S + 11) 21 (2 * S) (by omega) (by omega)
  rw [h]; exact rightEdge_spike_evolve_pos2S_cert5

private lemma rightEdge_spike_evolve_pos2S_13 (S : ℕ) (hS : 6 ≤ S) :
    (caEvolve 13 (spikeAtList (2 * S + 16) (2 * S + 27))).getD (2 * S) false = true := by
  rw [caEvolve_getD_shift 13 _ (2 * S)]
  have h := caEvolve_spikeAt_agree 13 (2 * S + 16) (2 * S + 27) 37 (2 * S) (by omega) (by omega)
  rw [h]; exact rightEdge_spike_evolve_pos2S_cert13

/-- Key: after one caStep, the intermediate tapes from T and T+8 agree everywhere.
    Both length-2S+1 tapes agree on 0..2S-1. Position 2S-1 = true in both.
    So R30(a, true, c) = !a is independent of c (position 2S), giving agreement at 2S-2.
    Positions 0..2S-3 of caStep depend only on positions ≤ 2S-1 where tapes already agree. -/
private lemma rightEdge_caStep_agree (S : ℕ) (hS : 6 ≤ S)
    (l1 l2 : List Bool) (hlen1 : l1.length = 2 * S + 1) (hlen2 : l2.length = 2 * S + 1)
    (hagree_low : ∀ i, i ≤ 2 * S - 1 → l1.getD i false = l2.getD i false)
    (hb_true1 : l1.getD (2 * S - 1) false = true)
    (hb_true2 : l2.getD (2 * S - 1) false = true) :
    ∀ i, i < (caStepList l1).length → (caStepList l1).getD i false = (caStepList l2).getD i false := by
  intro i hi
  have hlen_step : (caStepList l1).length = 2 * S - 1 := by
    rw [show (caStepList l1).length = l1.length - 2 from caStep_length l1 (by omega)]
    omega
  rw [hlen_step] at hi
  rw [caStepList_getD_eq l1 i (by omega), caStepList_getD_eq l2 i (by omega)]
  by_cases hi2 : i ≤ 2 * S - 3
  · -- positions 0..2S-3: all three inputs i, i+1, i+2 are ≤ 2S-1
    rw [hagree_low i (by omega), hagree_low (i + 1) (by omega), hagree_low (i + 2) (by omega)]
  · -- position 2S-2: inputs are 2S-2, 2S-1, 2S
    -- i = 2S-2
    have hi_eq : i = 2 * S - 2 := by omega
    rw [hi_eq]
    -- R30(a, b, c) = a XOR (b OR c). With b = true: R30(a, true, c) = a XOR true = !a
    rw [hagree_low (2 * S - 2) (by omega)]
    -- b positions: both true
    simp only [rule30Local]
    rw [hb_true1, hb_true2]
    -- Now: (l1[2S-2] XOR (true OR l1[2S])) = (l2[2S-2] XOR (true OR l2[2S]))
    -- Since (true OR x) = true for any x:
    simp [Bool.true_or]

theorem rightEdgeF_period8_k10 (T : ℕ) (hT : 100 ≤ T) :
    rightEdgeF 10 (T + 8) = rightEdgeF 10 T := by
  simp only [rightEdgeF]
  set S := T - 5 with hS_def
  -- Rewrite tape parameters in terms of S
  have h1 : 2 * (T + 8) - 10 = 2 * S + 16 := by omega
  have h2 : 2 * (T + 8) + 1 = 2 * S + 27 := by omega
  have h3 : 2 * T - 10 = 2 * S := by omega
  have h4 : 2 * T + 1 = 2 * S + 11 := by omega
  rw [h1, h2, h3, h4]
  -- Split T+8 = (S+5) + 8 = S + 13 = (S-1) + 1 + 13 and T = S + 5 = (S-1) + 1 + 5
  rw [show T + 8 = (S - 1) + 1 + 13 from by omega]
  rw [show T = (S - 1) + 1 + 5 from by omega]
  rw [caEvolve_add (S - 1 + 1) 13, caEvolve_add (S - 1 + 1) 5]
  rw [show S - 1 + 1 = S - 1 + 1 from rfl]
  rw [caEvolve_add (S - 1) 1, caEvolve_add (S - 1) 1]
  -- Now both sides are caEvolve (S-1) (caEvolve 1 (caEvolve K tape_K))[0]
  -- where K=13,tape_K for LHS and K=5,tape_T for RHS
  -- caEvolve 1 = caStepList
  simp only [caEvolve_succ, caEvolve_zero]
  -- Apply caEvolve_agree (S-1) on the two caStep'd tapes
  set tape1 := caEvolve 13 (spikeAtList (2 * S + 16) (2 * S + 27))
  set tape2 := caEvolve 5 (spikeAtList (2 * S) (2 * S + 11))
  have hlen1 : tape1.length = 2 * S + 1 := by
    simp only [tape1]
    have := caEvolve_length_le 13 (spikeAtList (2 * S + 16) (2 * S + 27))
              (by rw [spikeAtList_length]; omega)
    rw [spikeAtList_length] at this; omega
  have hlen2 : tape2.length = 2 * S + 1 := by
    simp only [tape2]
    have := caEvolve_length_le 5 (spikeAtList (2 * S) (2 * S + 11))
              (by rw [spikeAtList_length]; omega)
    rw [spikeAtList_length] at this; omega
  -- The caStep'd tapes agree everywhere
  have hstep_agree : ∀ i, i < (caStepList tape1).length →
      (caStepList tape1).getD i false = (caStepList tape2).getD i false := by
    apply rightEdge_caStep_agree S (by omega) tape1 tape2 hlen1 hlen2
    · -- Agreement on 0..2S-1
      intro i hi
      simp only [tape1, tape2]
      by_cases hiS : i ≤ 2 * S - 1
      · -- Both false at positions 0..2S-1
        rw [rightEdge_spike_evolve_false 13 S i hiS (by omega)]
        rw [rightEdge_spike_evolve_false 5 S i hiS (by omega)]
      · omega
    · exact rightEdge_ev13_pos2Sm1 S (by omega)
    · exact rightEdge_ev5_pos2Sm1 S (by omega)
  -- caStep'd tapes have length 2S-1
  have hstep_len1 : (caStepList tape1).length = 2 * S - 1 := by
    rw [show (caStepList tape1).length = tape1.length - 2 from caStep_length tape1 (by omega)]
    omega
  have hstep_len2 : (caStepList tape2).length = 2 * S - 1 := by
    rw [show (caStepList tape2).length = tape2.length - 2 from caStep_length tape2 (by omega)]
    omega
  apply caEvolve_agree (S - 1)
  · rw [hstep_len1]; omega
  · rw [hstep_len2]; omega
  · intro i hi
    exact hstep_agree i (by rw [hstep_len1]; omega)

/-!
## G period-8 helpers
-/

/-- For positions i ≤ 2S-1 of the G-ev5 tape (caEvolve 5 of twoSpikeList 4 (2S) (2S+11)):
    position i equals caEvolve 5 (spikeAtList (4-i) fixed) at 0, where the right spike
    (at 2S-i > 10) is outside the 5-step causal cone. -/
private lemma rightEdgeG_ev5_small_eq (S i : ℕ) (hS : 8 ≤ S) (hi : i ≤ 4) :
    (caEvolve 5 (twoSpikeList 4 (2 * S) (2 * S + 11))).getD i false =
    (caEvolve 5 (spikeAtList (4 - i) 11)).getD 0 false := by
  rw [caEvolve_getD_shift 5 _ i]
  apply caEvolve_agree 5
  · simp only [List.length_drop]
    have : (twoSpikeList 4 (2 * S) (2 * S + 11)).length = 2 * S + 11 := by
      simp [twoSpikeList, List.length_ofFn]
    rw [this]; omega
  · rw [spikeAtList_length]; omega
  · intro j hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [show (twoSpikeList 4 (2 * S) (2 * S + 11)).getElem? (i + j) =
           some (decide (i + j = 4 ∨ i + j = 2 * S)) from by
      simp [twoSpikeList, List.getElem?_ofFn]; omega]
    rw [show (spikeAtList (4 - i) 11).getElem? j =
           some (decide (j = 4 - i)) from by
      simp [spikeAtList, List.getElem?_ofFn]; omega]
    simp
    constructor
    · intro h; omega
    · intro h; omega

/-- For positions i ≤ 2S-1 of the G-ev13 tape (caEvolve 13 of twoSpikeList 4 (2S+16) (2S+27)):
    position i equals caEvolve 13 (spikeAtList (4-i) 27) at 0, where the right spike
    (at 2S+16-i > 26) is outside the 13-step causal cone. -/
private lemma rightEdgeG_ev13_small_eq (S i : ℕ) (hS : 8 ≤ S) (hi : i ≤ 4) :
    (caEvolve 13 (twoSpikeList 4 (2 * S + 16) (2 * S + 27))).getD i false =
    (caEvolve 13 (spikeAtList (4 - i) 27)).getD 0 false := by
  rw [caEvolve_getD_shift 13 _ i]
  apply caEvolve_agree 13
  · simp only [List.length_drop]
    have : (twoSpikeList 4 (2 * S + 16) (2 * S + 27)).length = 2 * S + 27 := by
      simp [twoSpikeList, List.length_ofFn]
    rw [this]; omega
  · rw [spikeAtList_length]; omega
  · intro j hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [show (twoSpikeList 4 (2 * S + 16) (2 * S + 27)).getElem? (i + j) =
           some (decide (i + j = 4 ∨ i + j = 2 * S + 16)) from by
      simp [twoSpikeList, List.getElem?_ofFn]; omega]
    rw [show (spikeAtList (4 - i) 27).getElem? j =
           some (decide (j = 4 - i)) from by
      simp [spikeAtList, List.getElem?_ofFn]; omega]
    simp
    constructor
    · intro h; omega
    · intro h; omega

/-- For positions 5 ≤ i ≤ 2S-1 of G-ev5: the value is the same as for F-ev5 (both
    reduce to caEvolve 5 on a tape with the right spike only). -/
private lemma rightEdgeG_ev5_ge5_eq_F (S i : ℕ) (hS : 8 ≤ S) (hi5 : 5 ≤ i) (hiS : i ≤ 2 * S - 1) :
    (caEvolve 5 (twoSpikeList 4 (2 * S) (2 * S + 11))).getD i false =
    (caEvolve 5 (spikeAtList (2 * S) (2 * S + 11))).getD i false := by
  rw [caEvolve_getD_shift 5 _ i, caEvolve_getD_shift 5 _ i]
  apply caEvolve_agree 5
  · simp only [List.length_drop]
    have : (twoSpikeList 4 (2 * S) (2 * S + 11)).length = 2 * S + 11 := by
      simp [twoSpikeList, List.length_ofFn]
    rw [this]; omega
  · rw [List.length_drop, spikeAtList_length]; omega
  · intro j hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    have hij_bound : i + j < 2 * S + 11 := by omega
    rw [show (twoSpikeList 4 (2 * S) (2 * S + 11)).getElem? (i + j) =
           some (decide (i + j = 4 ∨ i + j = 2 * S)) from by
      simp [twoSpikeList, List.getElem?_ofFn, hij_bound]]
    rw [show (spikeAtList (2 * S) (2 * S + 11)).getElem? (i + j) =
           some (decide (i + j = 2 * S)) from by
      simp [spikeAtList, List.getElem?_ofFn, hij_bound]]
    simp
    omega

/-- For positions 5 ≤ i ≤ 2S-1 of G-ev13: the value is the same as for F-ev13. -/
private lemma rightEdgeG_ev13_ge5_eq_F (S i : ℕ) (hS : 8 ≤ S) (hi5 : 5 ≤ i) (hiS : i ≤ 2 * S - 1) :
    (caEvolve 13 (twoSpikeList 4 (2 * S + 16) (2 * S + 27))).getD i false =
    (caEvolve 13 (spikeAtList (2 * S + 16) (2 * S + 27))).getD i false := by
  rw [caEvolve_getD_shift 13 _ i, caEvolve_getD_shift 13 _ i]
  apply caEvolve_agree 13
  · simp only [List.length_drop]
    have : (twoSpikeList 4 (2 * S + 16) (2 * S + 27)).length = 2 * S + 27 := by
      simp [twoSpikeList, List.length_ofFn]
    rw [this]; omega
  · rw [List.length_drop, spikeAtList_length]; omega
  · intro j hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    have hij_bound : i + j < 2 * S + 27 := by omega
    rw [show (twoSpikeList 4 (2 * S + 16) (2 * S + 27)).getElem? (i + j) =
           some (decide (i + j = 4 ∨ i + j = 2 * S + 16)) from by
      simp [twoSpikeList, List.getElem?_ofFn, hij_bound]]
    rw [show (spikeAtList (2 * S + 16) (2 * S + 27)).getElem? (i + j) =
           some (decide (i + j = 2 * S + 16)) from by
      simp [spikeAtList, List.getElem?_ofFn, hij_bound]]
    simp
    omega

/-- Native_decide certs: caEvolve 5 (spikeAtList j 11) at 0 = caEvolve 13 (spikeAtList j 27) at 0
    for j ∈ {0,1,2,3,4}. These hold because 13 = 5+8 and period-8 holds for each spike position. -/
private lemma leftSpike_ev5_eq_ev13_j4 :
    (caEvolve 5 (spikeAtList 4 11)).getD 0 false =
    (caEvolve 13 (spikeAtList 4 27)).getD 0 false := by native_decide

private lemma leftSpike_ev5_eq_ev13_j3 :
    (caEvolve 5 (spikeAtList 3 9)).getD 0 false =
    (caEvolve 13 (spikeAtList 3 25)).getD 0 false := by native_decide

private lemma leftSpike_ev5_eq_ev13_j2 :
    (caEvolve 5 (spikeAtList 2 7)).getD 0 false =
    (caEvolve 13 (spikeAtList 2 23)).getD 0 false := by native_decide

private lemma leftSpike_ev5_eq_ev13_j1 :
    (caEvolve 5 (spikeAtList 1 5)).getD 0 false =
    (caEvolve 13 (spikeAtList 1 21)).getD 0 false := by native_decide

private lemma leftSpike_ev5_eq_ev13_j0 :
    (caEvolve 5 (spikeAtList 0 3)).getD 0 false =
    (caEvolve 13 (spikeAtList 0 19)).getD 0 false := by native_decide

/-- Combined: for i ≤ 4, G-ev5 at i = G-ev13 at i. Uses the small reduction + native_decide certs. -/
private lemma rightEdgeG_agree_le4 (S i : ℕ) (hS : 8 ≤ S) (hi : i ≤ 4) :
    (caEvolve 5 (twoSpikeList 4 (2 * S) (2 * S + 11))).getD i false =
    (caEvolve 13 (twoSpikeList 4 (2 * S + 16) (2 * S + 27))).getD i false := by
  rw [rightEdgeG_ev5_small_eq S i hS hi, rightEdgeG_ev13_small_eq S i hS hi]
  -- Both sides now: caEvolve k (spikeAtList (4-i) size) at 0
  -- Use caEvolve_spikeAt_agree to reduce to canonical small tapes
  rw [caEvolve_spikeAt_agree 5 (4 - i) 11 (2 * (4 - i) + 3) 0 (by omega) (by omega)]
  rw [caEvolve_spikeAt_agree 13 (4 - i) 27 (2 * (4 - i) + 27) 0 (by omega) (by omega)]
  -- Now dispatch by case on i
  interval_cases i
  · exact leftSpike_ev5_eq_ev13_j4
  · exact leftSpike_ev5_eq_ev13_j3
  · exact leftSpike_ev5_eq_ev13_j2
  · exact leftSpike_ev5_eq_ev13_j1
  · exact leftSpike_ev5_eq_ev13_j0

/-- Cert: position 2S-1 of caEvolve 5 (twoSpikeList 4 (2S) (2S+11)) = true.
    The drop by (2S-1) gives spike at position 1 (from the right spike at 2S), same as
    spikeAtList 1 12. Same cert as the F case. -/
private lemma rightEdgeG_ev5_pos2Sm1 (S : ℕ) (hS : 6 ≤ S) :
    (caEvolve 5 (twoSpikeList 4 (2 * S) (2 * S + 11))).getD (2 * S - 1) false = true := by
  rw [caEvolve_getD_shift 5 _ (2 * S - 1)]
  -- drop (2S-1) of twoSpikeList 4 (2S) (2S+11) agrees with spikeAtList 1 12 on 0..10
  -- because: position j of drop is decide(2S-1+j = 4 ∨ 2S-1+j = 2S).
  -- For j ≤ 10: 2S-1+j = 4 iff j = 5-2S < 0 (false for S≥3); 2S-1+j = 2S iff j = 1.
  -- So drop agrees with spikeAtList 1 12 on positions 0..10.
  apply (caEvolve_agree 5 _ (spikeAtList 1 12) (by
    simp only [List.length_drop]
    have : (twoSpikeList 4 (2 * S) (2 * S + 11)).length = 2 * S + 11 := by
      simp [twoSpikeList, List.length_ofFn]
    rw [this]; omega) (by rw [spikeAtList_length]; omega) (fun j hj => ?_)).trans
    rightEdge_ev5_pos2Sm1_cert
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hbound : 2 * S - 1 + j < 2 * S + 11 := by omega
  rw [show (twoSpikeList 4 (2 * S) (2 * S + 11)).getElem? (2 * S - 1 + j) =
         some (decide (2 * S - 1 + j = 4 ∨ 2 * S - 1 + j = 2 * S)) from by
    simp [twoSpikeList, List.getElem?_ofFn, hbound]]
  rw [show (spikeAtList 1 12).getElem? j =
         some (decide (j = 1)) from by
    simp [spikeAtList, List.getElem?_ofFn]; omega]
  simp; omega

/-- Cert: position 2S-1 of caEvolve 13 (twoSpikeList 4 (2S+16) (2S+27)) = true.
    The drop by (2S-1) gives spike at position 17 (from right spike at 2S+16). -/
private lemma rightEdgeG_ev13_pos2Sm1 (S : ℕ) (hS : 6 ≤ S) :
    (caEvolve 13 (twoSpikeList 4 (2 * S + 16) (2 * S + 27))).getD (2 * S - 1) false = true := by
  rw [caEvolve_getD_shift 13 _ (2 * S - 1)]
  apply (caEvolve_agree 13 _ (spikeAtList 17 28) (by
    simp only [List.length_drop]
    have : (twoSpikeList 4 (2 * S + 16) (2 * S + 27)).length = 2 * S + 27 := by
      simp [twoSpikeList, List.length_ofFn]
    rw [this]; omega) (by rw [spikeAtList_length]; omega) (fun j hj => ?_)).trans
    rightEdge_ev13_pos2Sm1_cert
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hbound : 2 * S - 1 + j < 2 * S + 27 := by omega
  rw [show (twoSpikeList 4 (2 * S + 16) (2 * S + 27)).getElem? (2 * S - 1 + j) =
         some (decide (2 * S - 1 + j = 4 ∨ 2 * S - 1 + j = 2 * S + 16)) from by
    simp [twoSpikeList, List.getElem?_ofFn, hbound]]
  rw [show (spikeAtList 17 28).getElem? j =
         some (decide (j = 17)) from by
    simp [spikeAtList, List.getElem?_ofFn]; omega]
  simp; omega

-- G period-8: same structure, but with twoSpike (spikes at 4 and 2T-10)
theorem rightEdgeG_period8_k10 (T : ℕ) (hT : 100 ≤ T) :
    rightEdgeG 10 4 (T + 8) = rightEdgeG 10 4 T := by
  simp only [rightEdgeG]
  set S := T - 5 with hS_def
  have h1 : 2 * (T + 8) - 10 = 2 * S + 16 := by omega
  have h2 : 2 * (T + 8) + 1 = 2 * S + 27 := by omega
  have h3 : 2 * T - 10 = 2 * S := by omega
  have h4 : 2 * T + 1 = 2 * S + 11 := by omega
  rw [h1, h2, h3, h4]
  rw [show T + 8 = (S - 1) + 1 + 13 from by omega]
  rw [show T = (S - 1) + 1 + 5 from by omega]
  rw [caEvolve_add (S - 1 + 1) 13, caEvolve_add (S - 1 + 1) 5]
  rw [caEvolve_add (S - 1) 1, caEvolve_add (S - 1) 1]
  simp only [caEvolve_succ, caEvolve_zero]
  set tape1 := caEvolve 13 (twoSpikeList 4 (2 * S + 16) (2 * S + 27))
  set tape2 := caEvolve 5 (twoSpikeList 4 (2 * S) (2 * S + 11))
  have hlen1 : tape1.length = 2 * S + 1 := by
    simp only [tape1]
    have := caEvolve_length_le 13 (twoSpikeList 4 (2 * S + 16) (2 * S + 27))
              (by simp [twoSpikeList, List.length_ofFn]; omega)
    simp [twoSpikeList, List.length_ofFn] at this; omega
  have hlen2 : tape2.length = 2 * S + 1 := by
    simp only [tape2]
    have := caEvolve_length_le 5 (twoSpikeList 4 (2 * S) (2 * S + 11))
              (by simp [twoSpikeList, List.length_ofFn]; omega)
    simp [twoSpikeList, List.length_ofFn] at this; omega
  have hstep_agree : ∀ i, i < (caStepList tape1).length →
      (caStepList tape1).getD i false = (caStepList tape2).getD i false := by
    apply rightEdge_caStep_agree S (by omega) tape1 tape2 hlen1 hlen2
    · -- Agreement on 0..2S-1
      intro i hi
      simp only [tape1, tape2]
      by_cases hi4 : i ≤ 4
      · -- Left spike zone: use rightEdgeG_agree_le4
        exact rightEdgeG_agree_le4 S i (by omega) hi4
      · -- Right-spike-only zone: reduce to F tapes, which both give false
        push_neg at hi4
        have hi5 : 5 ≤ i := by omega
        rw [rightEdgeG_ev5_ge5_eq_F S i (by omega) hi5 hi]
        rw [rightEdgeG_ev13_ge5_eq_F S i (by omega) hi5 hi]
        rw [rightEdge_spike_evolve_false 13 S i hi (by omega)]
        rw [rightEdge_spike_evolve_false 5 S i hi (by omega)]
    · exact rightEdgeG_ev13_pos2Sm1 S (by omega)
    · exact rightEdgeG_ev5_pos2Sm1 S (by omega)
  have hstep_len1 : (caStepList tape1).length = 2 * S - 1 := by
    rw [show (caStepList tape1).length = tape1.length - 2 from caStep_length tape1 (by omega)]
    omega
  have hstep_len2 : (caStepList tape2).length = 2 * S - 1 := by
    rw [show (caStepList tape2).length = tape2.length - 2 from caStep_length tape2 (by omega)]
    omega
  apply caEvolve_agree (S - 1)
  · rw [hstep_len1]; omega
  · rw [hstep_len2]; omega
  · intro i hi
    exact hstep_agree i (by rw [hstep_len1]; omega)

/-!
## Period-8 sensitivity propagation
-/

lemma rightEdgeSens_step8_k10 (T : ℕ) (hT : 100 ≤ T) (h : rightEdgeSens 10 4 T) :
    rightEdgeSens 10 4 (T + 8) := by
  simp only [rightEdgeSens]
  rwa [rightEdgeF_period8_k10 T hT, rightEdgeG_period8_k10 T hT]

lemma rightEdgeSens_iterated_k10 (T₀ j : ℕ) (hT₀ : 100 ≤ T₀)
    (h : rightEdgeSens 10 4 T₀) : rightEdgeSens 10 4 (T₀ + j * 8) := by
  induction j with
  | zero => simp [h]
  | succ j ih =>
    have : T₀ + (j + 1) * 8 = (T₀ + j * 8) + 8 := by omega
    rw [this]
    exact rightEdgeSens_step8_k10 _ (by omega) ih

/-!
## Base case
SubcaseB fires at n' ≡ 5 mod 8 for n' ≥ 3087 (Python-verified).
Only T=3094 (n'=3093, n'%8=5) is needed as the base.
-/

lemma rightEdgeSens_base_3094_k10 : rightEdgeSens 10 4 3094 := by
  simp only [rightEdgeSens, rightEdgeF, rightEdgeG]; native_decide

/-!
## Bridge: rightEdgeSens → SubcaseB ∃ witness
-/

/-- twoSpikeList is symmetric in its first two arguments. -/
lemma twoSpikeList_comm (p q N : ℕ) : twoSpikeList p q N = twoSpikeList q p N := by
  simp only [twoSpikeList]
  congr 1
  ext i
  simp [or_comm]

/-- Given sensitivity at T = n'+1 with right-edge k witness,
    produce the SubcaseB witness config. -/
lemma rightEdge_witness (n' k : ℕ) (hk_even : k % 2 = 0)
    (hk_lt : k + 5 ≤ 2 * (n' + 1))
    (m : Fin (2 * (n' + 1) + 1)) (hm4 : m.val = 4)
    (hsens : rightEdgeSens k 4 (n' + 1)) :
    ∃ c_n : Config (n' + 1),
      (∀ j : Fin (n' + 1), c_n ⟨2 * j.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  set w := 2 * (n' + 1) - k with hw
  have hw_even : w % 2 = 0 := by omega
  have hw_ne_m : w ≠ m.val := by rw [hm4]; omega
  have hw_lt : w < 2 * (n' + 1) + 1 := by omega
  refine ⟨spikeConfigAt w n', spikeConfigAt_odd_false w n' hw_even, ?_⟩
  rw [rule30n_spikeConfigAt_eq, rule30n_flipCell_spikeConfigAt_eq w n' m hw_ne_m hw_lt]
  -- Goal: caEvolve on spikeAtList(w) ≠ caEvolve on twoSpikeList(w, m.val)
  -- These equal rightEdgeF k T and rightEdgeG k m.val T respectively
  simp only [rightEdgeSens] at hsens
  have hF : (caEvolve (n' + 1) (spikeAtList w (2 * (n' + 1) + 1))).getD 0 false =
            rightEdgeF k (n' + 1) := by
    simp [rightEdgeF, hw]
  have hG : (caEvolve (n' + 1) (twoSpikeList w m.val (2 * (n' + 1) + 1))).getD 0 false =
            rightEdgeG k 4 (n' + 1) := by
    simp only [rightEdgeG]
    rw [hm4, ← hw, twoSpikeList_comm]
  rw [hF, hG]
  exact hsens

/-!
## Helper lemmas for hmod
-/

/-- Bridge: rule30n of spike-at-4 config = caEvolve of spikeAtList. -/
private lemma rule30n_spikeAt4_bridge (n' : Nat) :
    rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) => decide (k.val = 4)) =
    (caEvolve (n' + 1) (spikeAtList 4 (2 * (n' + 1) + 1))).getD 0 false := by
  simp [rule30n, configToList, spikeAtList]

/-- Bridge: rule30n of twoSpike(4, last) config = caEvolve of twoSpikeLastList. -/
private lemma rule30n_twoSpikeLast4_bridge (n' : Nat) :
    rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) => decide (k.val = 4 ∨ k.val = 2 * (n' + 1))) =
    (caEvolve (n' + 1) (twoSpikeLastList 4 (2 * (n' + 1) + 1))).getD 0 false := by
  simp [rule30n, configToList, twoSpikeLastList]

/-- Period-8 iteration for spikeAt4 center value. -/
private lemma spikeAt4_period8_iter (n j : ℕ) :
    (caEvolve (n + 1) (spikeAtList 4 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + j * 8) + 1) (spikeAtList 4 (2 * ((n + j * 8) + 1) + 1))).getD 0 false := by
  induction j with
  | zero => simp
  | succ j ih =>
    have step := rule30n_spikeAt4_period8 (n + j * 8)
    rw [show n + (j + 1) * 8 = n + j * 8 + 8 from by omega]
    rw [show n + j * 8 + 8 + 1 = n + j * 8 + 1 + 8 from by omega]
    exact ih.trans step

/-- Period-8 iteration for twoSpikeLast4 center value. -/
private lemma twoSpikeLast4_period8_iter (n j : ℕ) (hn : n ≥ 4) :
    (caEvolve (n + 1) (twoSpikeLastList 4 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + j * 8) + 1) (twoSpikeLastList 4 (2 * ((n + j * 8) + 1) + 1))).getD 0 false := by
  induction j with
  | zero => simp
  | succ j ih =>
    have step := rule30n_twoSpikeLast4_period8 (n + j * 8) (by omega)
    rw [show n + (j + 1) * 8 = n + j * 8 + 8 from by omega]
    rw [show n + j * 8 + 8 + 1 = n + j * 8 + 1 + 8 from by omega]
    exact ih.trans step

-- SubcaseB for m=4 fires only at n' ≡ 5 mod 8 for n' ≥ 3087.
-- Verified: for all 7 other residues r ∈ {0,1,2,3,4,6,7} in [3087,3094],
-- either F(n')≠false or G(n')≠true, so both conditions cannot hold simultaneously.
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_not_fires_other_residues :
    ∀ r : Fin 8, r.val ≠ 6 →
    ¬ ((caEvolve (3087 + r.val + 1) (spikeAtList 4 (2 * (3087 + r.val + 1) + 1))).getD 0 false = false ∧
       (caEvolve (3087 + r.val + 1) (twoSpikeLastList 4 (2 * (3087 + r.val + 1) + 1))).getD 0 false = true) := by
  native_decide

/-- SubcaseB for m=4, given firing conditions, forces n' ≡ 5 mod 8. -/
private lemma subcaseB_m4_hmod (n' : ℕ) (hn' : 3087 ≤ n')
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) => decide (k.val = 4)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = 4 ∨ k.val = 2 * (n' + 1))) = true) :
    n' % 8 = 5 := by
  rw [rule30n_spikeAt4_bridge] at hcase
  rw [rule30n_twoSpikeLast4_bridge] at hts
  set r := (n' - 3087) % 8
  set q := (n' - 3087) / 8
  have hn'_eq : n' = 3087 + r + q * 8 := by omega
  have hr_lt : r < 8 := Nat.mod_lt _ (by omega)
  have hF' : (caEvolve (3087 + r + 1) (spikeAtList 4 (2 * (3087 + r + 1) + 1))).getD 0 false = false := by
    have eq := spikeAt4_period8_iter (3087 + r) q
    rw [show 3087 + r + q * 8 = n' from by omega] at eq
    rw [eq]; exact hcase
  have hG' : (caEvolve (3087 + r + 1) (twoSpikeLastList 4 (2 * (3087 + r + 1) + 1))).getD 0 false = true := by
    have eq := twoSpikeLast4_period8_iter (3087 + r) q (by omega)
    rw [show 3087 + r + q * 8 = n' from by omega] at eq
    rw [eq]; exact hts
  have hr6 : r = 6 := by
    by_contra hr_ne
    exact subcaseB_m4_not_fires_other_residues ⟨r, by omega⟩ (by simpa) ⟨hF', hG'⟩
  omega

/-!
## Main theorem
-/

theorem subcaseB_m4_ge3087_from_rightedge (n' : ℕ) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm4 : m.val = 4)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  -- Rewrite m.val to 4 using hm4
  have hcase4 : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) => decide (k.val = 4)) = false := by
    convert hcase using 2; ext k; rw [hm4]
  have hts4 : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = 4 ∨ k.val = 2 * (n' + 1))) = true := by
    convert hts using 2; ext k; rw [hm4]
  have hmod : n' % 8 = 5 := subcaseB_m4_hmod n' hn' hcase4 hts4
  obtain ⟨j, hj⟩ : ∃ j, n' + 1 = 3094 + j * 8 := ⟨(n' + 1 - 3094) / 8, by omega⟩
  have hsens : rightEdgeSens 10 4 (n' + 1) := by
    nth_rewrite 1 [hj]
    exact rightEdgeSens_iterated_k10 3094 j (by omega) rightEdgeSens_base_3094_k10
  exact rightEdge_witness n' 10 (by decide) (by omega) m hm4 hsens

end P2p
