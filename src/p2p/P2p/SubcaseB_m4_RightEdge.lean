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
## Period-8 axioms

PROOF PATH: combined-pattern cert on ≤41 cell tapes (see consult output).
-/

axiom rightEdgeF_period8_k10 (T : ℕ) (hT : 100 ≤ T) :
    rightEdgeF 10 (T + 8) = rightEdgeF 10 T

axiom rightEdgeG_period8_k10 (T : ℕ) (hT : 100 ≤ T) :
    rightEdgeG 10 4 (T + 8) = rightEdgeG 10 4 T

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
