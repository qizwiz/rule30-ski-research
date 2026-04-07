/-
SubcaseBPeriod.lean
===================
Structural resolution of the SubcaseB axiom in LiftingLemma_LeftPermutive.lean.

The SubcaseB arises when:
  (hcase) rule30n (n'+1) (spike_m) = false
  (hts)   rule30n (n'+1) (two_spike_{m, 2*(n'+1)}) = true
for even m with 1 ≤ m < 2*(n'+1), m ≠ 2*n'.

We need: ∃ c with odd-false constraint, sensitive at m.

Strategy: Periodicity reduction.

For fixed small m (the left SubcaseBs at m ∈ {4, 12, 14, 20, 22}):
- F_m(n'+1) = rule30n (n'+1) (spike_m) is periodic in n' with period P_m
- G_{m,last}(n'+1) = rule30n (n'+1) (twoSpikeLast_m) is periodic with period P_m
- These are proved in CausalConeLemmas.lean via native_decide certificates.

For fixed witness w (appearing at base n'' ∈ {3085, 3086}):
- The sensitivity F_w(n'+1) ≠ H_{w,m}(n'+1) is periodic with period LCM(P_w, P_{w,m})
- Where H_{w,m} = rule30n on two-spike {w, m_val} (interior-interior)
- This uses a two-spike period certificate proved by native_decide.

For the right-mirror SubcaseBs (m = 2*(n'+1) - 8):
- The witness alternates between spike_12 (odd n') and spike_2 (even n')
- This is established via right-boundary period-2 argument.

Status: THEOREM SKELETON with documented sorry obligations:
  - subcaseB_m4, m12, m14, m20, m22 (ge3087): multi-witness required (no single spike_w
    works for all firing positions in a full period); deferred
  - subcaseB_only_active_m: period analysis over n'≥3087; deferred
  - subcaseB_right_mirror_ge3087: right-boundary independence; deferred
  - subcaseB_resolution (n' ∈ [5,3086]): never called in practice
  Infrastructure proved: period reduction, iterated periods, sensitivity transfer,
  flipCell–twoSpikeList connection, native_decide base certificates.
-/

import P2p.Prize3_Complete
import P2p.CausalConeLemmas
import P2p.CA_Array
import Mathlib.Tactic.Ring

set_option maxHeartbeats 800000000

/-!
## Connection between rule30n and spikeAtList

The key identity: `rule30n (n+1) (fun k => decide (k.val = m))` equals
`(caEvolve (n+1) (spikeAtList m (2*(n+1)+1))).getD 0 false`
by definitional equality (both unfold to the same caEvolve call via configToList).
-/

/-- configToList of spike-at-m equals spikeAtList m. -/
lemma configToList_spikeAt (m n : Nat) :
    configToList (fun k : Fin (2*n+1) => decide (k.val = m)) = spikeAtList m (2*n+1) := by
  simp [configToList, spikeAtList]

/-- rule30n of spike-at-m = caEvolve of spikeAtList. -/
lemma rule30n_spikeAt_eq (n m : Nat) :
    rule30n (n + 1) (fun k : Fin (2 * (n + 1) + 1) => decide (k.val = m)) =
    (caEvolve (n + 1) (spikeAtList m (2 * (n + 1) + 1))).getD 0 false := by
  simp only [rule30n, configToList_spikeAt]

/-- rule30n of two-spike at {m, last} = caEvolve of twoSpikeLastList. -/
lemma rule30n_twoSpikeLast_eq (n m : Nat) :
    rule30n (n + 1) (fun k : Fin (2 * (n + 1) + 1) => decide (k.val = m ∨ k.val = 2 * (n + 1))) =
    (caEvolve (n + 1) (twoSpikeLastList m (2 * (n + 1) + 1))).getD 0 false := by
  simp only [rule30n]
  congr 1
  simp [configToList, twoSpikeLastList]

/-!
## Two-interior-spike infrastructure

For witness w and target position m (both small interior positions), we need period
lemmas for `rule30n (n+1) (twoSpikeList w m ...)` where twoSpikeList has spikes at
positions w and m_val.
-/

-- twoSpikeList is defined in CausalConeLemmas.lean (imported via P2p.CausalConeLemmas)

lemma twoSpikeList_length (p q N : Nat) : (twoSpikeList p q N).length = N := by
  simp [twoSpikeList, List.length_ofFn]

/-- twoSpikeList is symmetric in p and q. -/
lemma twoSpikeList_comm (p q N : Nat) : twoSpikeList p q N = twoSpikeList q p N := by
  apply List.ext_getElem
  · simp [twoSpikeList, List.length_ofFn]
  · intro i h1 h2
    simp only [twoSpikeList, List.getElem_ofFn]
    simp only [decide_eq_decide]
    tauto

lemma twoSpikeList_getD (p q N i : Nat) (hi : i < N) :
    (twoSpikeList p q N).getD i false = decide (i = p ∨ i = q) := by
  simp [twoSpikeList, List.getD_eq_getElem?_getD, hi]

/-- Two twoSpikeLists of different sizes agree at same interior positions. -/
lemma drop_twoSpike_agree (p q N1 N2 i j : Nat)
    (h1 : i + j < N1) (h2 : i + j < N2) :
    (List.drop i (twoSpikeList p q N1)).getD j false =
    (List.drop i (twoSpikeList p q N2)).getD j false := by
  simp only [twoSpikeList, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_ofFn]
  simp [h1, h2]

/-- Drop past max(p,q) gives all-false. -/
lemma twoSpikeList_drop_allFalse (p q N i : Nat) (hi : i > p) (hiq : i > q) :
    ∀ j, j < (List.drop i (twoSpikeList p q N)).length →
         (List.drop i (twoSpikeList p q N)).getD j false = false := by
  intro j hj
  simp only [List.length_drop, twoSpikeList_length] at hj
  rw [show ((twoSpikeList p q N).drop i).getD j false = (twoSpikeList p q N).getD (i + j) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  by_cases h : i + j < N
  · rw [twoSpikeList_getD p q N (i + j) h]; simp; omega
  · simp only [List.getD_eq_getElem?_getD, twoSpikeList, List.getElem?_ofFn]
    simp [show ¬(i + j < N) from h]

/-- Causal-cone independence for twoSpikeList. -/
lemma caEvolve_twoSpike_agree (P p q N1 N2 i : Nat)
    (h1 : i + 2 * P < N1) (h2 : i + 2 * P < N2) :
    (caEvolve P (twoSpikeList p q N1)).getD i false =
    (caEvolve P (twoSpikeList p q N2)).getD i false := by
  rw [caEvolve_getD_shift P (twoSpikeList p q N1) i,
      caEvolve_getD_shift P (twoSpikeList p q N2) i]
  apply caEvolve_agree P
  · rw [List.length_drop, twoSpikeList_length]; omega
  · rw [List.length_drop, twoSpikeList_length]; omega
  · intro j hj; exact drop_twoSpike_agree p q N1 N2 i j (by omega) (by omega)

/-- Parametric period lemma for two-spike-at-{p,q} interior config.

Given a `native_decide` certificate
  caEvolve P (twoSpikeList p q (2*P+2*(max p q)+1)) = twoSpikeList p q (2*(max p q)+1),
proves that the center value is periodic with period P. -/
lemma rule30n_twoSpike_period (p q P : Nat)
    (hcert : caEvolve P (twoSpikeList p q (2*P+2*(max p q)+1)) = twoSpikeList p q (2*(max p q)+1))
    (n : Nat) :
    (caEvolve (n + 1) (twoSpikeList p q (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n + 1) + P) (twoSpikeList p q (2*((n+1)+P)+1))).getD 0 false := by
  have rhs_len : 2*(n+1) < (caEvolve P (twoSpikeList p q (2*((n+1)+P)+1))).length := by
    have hlen := caEvolve_length_le P (twoSpikeList p q (2*((n+1)+P)+1))
                (by rw [twoSpikeList_length]; omega)
    rw [twoSpikeList_length] at hlen; omega
  conv_rhs => rw [caEvolve_add (n+1) P]
  apply caEvolve_agree (n+1)
  · rw [twoSpikeList_length]; omega
  · exact rhs_len
  · intro i hi
    suffices h : (twoSpikeList p q (2*(n+1)+1)).getD i false =
                 (caEvolve P (twoSpikeList p q (2*(n+1+P)+1))).getD i false by exact h
    by_cases hm : i ≤ max p q
    · rw [twoSpikeList_getD p q (2*(n+1)+1) i (by omega)]
      rw [caEvolve_twoSpike_agree P p q (2*(n+1+P)+1) (2*P+2*(max p q)+1) i (by omega) (by omega)]
      rw [hcert]
      rw [twoSpikeList_getD p q (2*(max p q)+1) i (by omega)]
    · have lhs_false : (twoSpikeList p q (2*(n+1)+1)).getD i false = false := by
        rw [twoSpikeList_getD p q (2*(n+1)+1) i (by omega)]; simp; omega
      have rhs_false : (caEvolve P (twoSpikeList p q (2*(n+1+P)+1))).getD i false = false := by
        rw [caEvolve_getD_shift P _ i]
        apply caEvolve_allFalse
        exact twoSpikeList_drop_allFalse p q (2*(n+1+P)+1) i (by omega) (by omega)
      rw [lhs_false, rhs_false]

/-!
## Native_decide period certificates for two-spike {w, m} pairs

For the SubcaseB witnesses: (w, m) pairs that arise at n' ∈ {3085, 3086}.
n'=3085: (w=6, m=4) period=LCM(16,8)=16; (w=4, m=12) period=LCM(8,64)=64;
          (w=16, m=20) period=LCM(256,256)=256; (w=12, m_right); (w=2, m_right)
n'=3086: (w=4, m=14) period=LCM(8,64)=64; (w=2, m=22) period=LCM(?,256)=256

Certificate form: caEvolve P (twoSpikeList w m (2*P+2*(max w m)+1)) = twoSpikeList w m (2*(max w m)+1)
-/

-- (w=6, m=4): period P=16, max=6, input=2*16+2*6+1=45, output=twoSpike(4,6,13)
lemma caEvolve_cert_ts46_p16 :
    caEvolve 16 (twoSpikeList 4 6 45) = twoSpikeList 4 6 13 := by native_decide

lemma rule30n_twoSpike46_period16 (n : Nat) :
    (caEvolve (n+1) (twoSpikeList 4 6 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+16) (twoSpikeList 4 6 (2*((n+1)+16)+1))).getD 0 false :=
  rule30n_twoSpike_period 4 6 16 (by
    have : max 4 6 = 6 := by decide
    rw [this]; exact caEvolve_cert_ts46_p16) n

-- (w=4, m=12): period P=128, max=12, input=2*128+2*12+1=281, output=twoSpike(4,12,25)
lemma caEvolve_cert_ts412_p128 :
    caEvolve 128 (twoSpikeList 4 12 281) = twoSpikeList 4 12 25 := by native_decide

lemma rule30n_twoSpike412_period128 (n : Nat) :
    (caEvolve (n+1) (twoSpikeList 4 12 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+128) (twoSpikeList 4 12 (2*((n+1)+128)+1))).getD 0 false :=
  rule30n_twoSpike_period 4 12 128 (by
    have : max 4 12 = 12 := by decide
    rw [this]; exact caEvolve_cert_ts412_p128) n

-- (w=16, m=20): period P=1024, max=20, input=2*1024+2*20+1=2089, output=twoSpike(16,20,41)
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts1620_p1024 :
    caEvolve 1024 (twoSpikeList 16 20 2089) = twoSpikeList 16 20 41 := by native_decide

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpike1620_period1024 (n : Nat) :
    (caEvolve (n+1) (twoSpikeList 16 20 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+1024) (twoSpikeList 16 20 (2*((n+1)+1024)+1))).getD 0 false :=
  rule30n_twoSpike_period 16 20 1024 (by
    have : max 16 20 = 20 := by decide
    rw [this]; exact caEvolve_cert_ts1620_p1024) n

-- (w=4, m=14): period P=256, max=14, input=2*256+2*14+1=541, output=twoSpike(4,14,29)
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts414_p256 :
    caEvolve 256 (twoSpikeList 4 14 541) = twoSpikeList 4 14 29 := by native_decide

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpike414_period256 (n : Nat) :
    (caEvolve (n+1) (twoSpikeList 4 14 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+256) (twoSpikeList 4 14 (2*((n+1)+256)+1))).getD 0 false :=
  rule30n_twoSpike_period 4 14 256 (by
    have : max 4 14 = 14 := by decide
    rw [this]; exact caEvolve_cert_ts414_p256) n

-- (w=2, m=22): period P=512, max=22, input=2*512+2*22+1=1069, output=twoSpike(2,22,45)
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts222_p512 :
    caEvolve 512 (twoSpikeList 2 22 1069) = twoSpikeList 2 22 45 := by native_decide

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpike222_period512 (n : Nat) :
    (caEvolve (n+1) (twoSpikeList 2 22 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+512) (twoSpikeList 2 22 (2*((n+1)+512)+1))).getD 0 false :=
  rule30n_twoSpike_period 2 22 512 (by
    have : max 2 22 = 22 := by decide
    rw [this]; exact caEvolve_cert_ts222_p512) n

-- (w=2, m=8): period P=32, max=8, input=2*32+2*8+1=81, output=twoSpike(2,8,17)
lemma caEvolve_cert_ts28_p32 :
    caEvolve 32 (twoSpikeList 2 8 81) = twoSpikeList 2 8 17 := by native_decide

lemma rule30n_twoSpike28_period32 (n : Nat) :
    (caEvolve (n+1) (twoSpikeList 2 8 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+32) (twoSpikeList 2 8 (2*((n+1)+32)+1))).getD 0 false :=
  rule30n_twoSpike_period 2 8 32 (by
    have : max 2 8 = 8 := by decide
    rw [this]; exact caEvolve_cert_ts28_p32) n

-- (w=2, m=10): period P=64, max=10, input=2*64+2*10+1=149, output=twoSpike(2,10,21)
lemma caEvolve_cert_ts210_p64 :
    caEvolve 64 (twoSpikeList 2 10 149) = twoSpikeList 2 10 21 := by native_decide

lemma rule30n_twoSpike210_period64 (n : Nat) :
    (caEvolve (n+1) (twoSpikeList 2 10 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+64) (twoSpikeList 2 10 (2*((n+1)+64)+1))).getD 0 false :=
  rule30n_twoSpike_period 2 10 64 (by
    have : max 2 10 = 10 := by decide
    rw [this]; exact caEvolve_cert_ts210_p64) n

-- spike_2 period-32 cert (F_2 period 2 divides 32)
-- N_in = 2*32+2*2+1=69, N_out = 2*2+1=5
lemma caEvolve_cert_ts2_p32 :
    caEvolve 32 (spikeAtList 2 69) = spikeAtList 2 5 := by native_decide

-- spike_2 period-64 cert
-- N_in = 2*64+2*2+1=133, N_out = 5
lemma caEvolve_cert_ts2_p64 :
    caEvolve 64 (spikeAtList 2 133) = spikeAtList 2 5 := by native_decide

-- spike_2 period-1024 cert
-- N_in = 2*1024+2*2+1=2053, N_out = 5
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts2_p1024 :
    caEvolve 1024 (spikeAtList 2 2053) = spikeAtList 2 5 := by native_decide

-- (w=2, m=26): period P=1024, max=26, input=2*1024+2*26+1=2101, output=twoSpike(2,26,53)
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts226_p1024 :
    caEvolve 1024 (twoSpikeList 2 26 2101) = twoSpikeList 2 26 53 := by native_decide

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpike226_period1024 (n : Nat) :
    (caEvolve (n+1) (twoSpikeList 2 26 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+1024) (twoSpikeList 2 26 (2*((n+1)+1024)+1))).getD 0 false :=
  rule30n_twoSpike_period 2 26 1024 (by
    have : max 2 26 = 26 := by decide
    rw [this]; exact caEvolve_cert_ts226_p1024) n

-- spike_2 period 2 certificate (not in CausalConeLemmas)
-- caEvolve 2 (spikeAtList 2 9) = spikeAtList 2 5
lemma caEvolve_cert_m2_p2 :
    caEvolve 2 (spikeAtList 2 9) = spikeAtList 2 5 := by native_decide

lemma rule30n_spikeAt2_period2 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 2 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+2) (spikeAtList 2 (2*((n+1)+2)+1))).getD 0 false :=
  rule30n_spikeAt_period 2 2 caEvolve_cert_m2_p2 n

/-!
## Connecting flipCell to twoSpikeList

`flipCell (fun k => decide (k.val = w)) m` where m.val ≠ w equals
`fun k => decide (k.val = w ∨ k.val = m.val)` = twoSpikeList at {w, m.val}.
-/

lemma flipCell_spike_eq_twoSpike (w : Nat) (n : Nat) (m : Fin (2*(n+1)+1))
    (hwm : w ≠ m.val) (hwb : w < 2*(n+1)+1) :
    flipCell (fun k : Fin (2*(n+1)+1) => decide (k.val = w)) m =
    fun k : Fin (2*(n+1)+1) => decide (k.val = w ∨ k.val = m.val) := by
  funext k
  simp only [flipCell]
  split_ifs with hk
  · have hiv : k = m := hk
    subst hiv
    simp [hwm.symm]
  · have him : k.val ≠ m.val := fun h => hk (Fin.ext h)
    simp [him]

-- rule30n_flipCell_spike_eq: superseded by rule30n_flipCell_spikeConfig_eq' below.

/-!
## Period-reduction helper

Given period P for both spike_m (F) and twoSpike_{w,m} (G), we can reduce
the sensitivity statement from n' to n' - P (and by induction, to any n'' ≡ n' (mod P)).
-/

/-- Apply the spike_m period to reduce n' by P (F-part). -/
lemma hcase_period_step (m P : Nat)
    (hF_cert : caEvolve P (spikeAtList m (2*P+2*m+1)) = spikeAtList m (2*m+1))
    (n : Nat) :
    (caEvolve (n+1) (spikeAtList m (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+P) (spikeAtList m (2*((n+1)+P)+1))).getD 0 false :=
  rule30n_spikeAt_period m P hF_cert n

/-!
## Iterated period reduction

Apply period reduction k times to go from n'+1 to (n'+1) - k*P.
-/

/-- Iterated spikeAt period: F(n+1, m) = F(n+1-k*P, m) for any k,
    expressed as F(n+1) = F((n+1) mod P + P) when we pick the right k.

    For our application: given n'+1 ≥ 3086+1, find k s.t. n'+1 - k*P ∈ [3086, 3086+P-1].
    Then F(n'+1, m) = F(n'+1-k*P, m).
-/

-- The key iterated lemma: F_m(n'+1) depends only on (n'+1) mod P (for n' large enough)
lemma spikeAt_iterated_period (m P : Nat) (hP : 0 < P)
    (hF_cert : caEvolve P (spikeAtList m (2*P+2*m+1)) = spikeAtList m (2*m+1))
    (n k : Nat) :
    (caEvolve (n + 1) (spikeAtList m (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * P) (spikeAtList m (2*(n+1+k*P)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * P = (n + k * P) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * P = (n + k * P) + 1 + P := by ring
    rw [hstep]
    exact rule30n_spikeAt_period m P hF_cert (n + k * P)

/-- Iterated twoSpike period. -/
lemma twoSpike_iterated_period (p q P : Nat) (hP : 0 < P)
    (hcert : caEvolve P (twoSpikeList p q (2*P+2*(max p q)+1)) = twoSpikeList p q (2*(max p q)+1))
    (n k : Nat) :
    (caEvolve (n + 1) (twoSpikeList p q (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * P) (twoSpikeList p q (2*(n+1+k*P)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * P = (n + k * P) + 1 from by omega]
    have hstep2 : n + 1 + (k + 1) * P = (n + k * P) + 1 + P := by ring
    rw [hstep2]
    exact rule30n_twoSpike_period p q P hcert (n + k * P)

/-!
## Sensitivity transfer lemma

Given that spike_w is sensitive at m at time n''+1 (F_w(n''+1) ≠ H_{w,m.val}(n''+1)),
and F_w and H_{w,m.val} are both periodic with period P, and
n' ≡ n'' (mod P), then spike_w is sensitive at m at time n'+1.
-/

/-- Transfer sensitivity from n'' to n' when both F_w and H_{w,m} have period P
    and n' = n'' + k*P. -/
lemma sensitivity_transfer (w m_val P n'' k : Nat) (hP : 0 < P)
    (hF_cert : caEvolve P (spikeAtList w (2*P+2*w+1)) = spikeAtList w (2*w+1))
    (hH_cert : caEvolve P (twoSpikeList w m_val (2*P+2*(max w m_val)+1)) =
               twoSpikeList w m_val (2*(max w m_val)+1))
    (h_sens : (caEvolve (n''+1) (spikeAtList w (2*(n''+1)+1))).getD 0 false ≠
              (caEvolve (n''+1) (twoSpikeList w m_val (2*(n''+1)+1))).getD 0 false) :
    (caEvolve (n''+1+k*P) (spikeAtList w (2*(n''+1+k*P)+1))).getD 0 false ≠
    (caEvolve (n''+1+k*P) (twoSpikeList w m_val (2*(n''+1+k*P)+1))).getD 0 false := by
  rw [← spikeAt_iterated_period w P hP hF_cert n'' k]
  rw [← twoSpike_iterated_period w m_val P hP hH_cert n'' k]
  exact h_sens

/-!
## Main SubcaseB resolution for small left m values

For each m ∈ {4, 12, 14, 20, 22}, the SubcaseB witness is spike_w for specific w.
The sensitivity at arbitrary n' ≥ 3087 follows from periodicity reduction to n'=3085 or 3086.
-/

-- Base sensitivity certificate for m=4, w=6 at n'=3085 (tape size 6173, level 3086)
lemma subcaseB_m4_base_sens :
    (caEvolve 3086 (spikeAtList 6 6173)).getD 0 false ≠
    (caEvolve 3086 (twoSpikeList 4 6 6173)).getD 0 false := by
  -- rule30n 3086 spike_6 ≠ rule30n 3086 (flipCell spike_6 (4:Fin 6173))
  -- = rule30n 3086 spike_6 ≠ rule30n 3086 twoSpike_{4,6}
  -- verified at n'=3085 (level 3086)
  native_decide

-- Base sensitivity for m=12, w=4 at n'=3085
lemma subcaseB_m12_base_sens :
    (caEvolve 3086 (spikeAtList 4 6173)).getD 0 false ≠
    (caEvolve 3086 (twoSpikeList 4 12 6173)).getD 0 false := by native_decide

-- Base sensitivity for m=20, w=16 at n'=3085
lemma subcaseB_m20_base_sens :
    (caEvolve 3086 (spikeAtList 16 6173)).getD 0 false ≠
    (caEvolve 3086 (twoSpikeList 16 20 6173)).getD 0 false := by native_decide

-- Base sensitivity for m=14, w=4 at n'=3086 (tape size 6175, level 3087)
lemma subcaseB_m14_base_sens :
    (caEvolve 3087 (spikeAtList 4 6175)).getD 0 false ≠
    (caEvolve 3087 (twoSpikeList 4 14 6175)).getD 0 false := by native_decide

-- Base sensitivity for m=22, w=2 at n'=3086
lemma subcaseB_m22_base_sens :
    (caEvolve 3087 (spikeAtList 2 6175)).getD 0 false ≠
    (caEvolve 3087 (twoSpikeList 2 22 6175)).getD 0 false := by native_decide

/-!
## Key connectivty: rule30n spike_w at n'' = caEvolve on spikeAtList

The sensitivity is stated in terms of rule30n (Config), so we need to convert
spikeAtList and twoSpikeList back to the Config type.
-/

-- The witness Config at level n+1: spike at position w
def spikeConfig (w : Nat) (n : Nat) : Config (n+1) :=
  fun k : Fin (2*(n+1)+1) => decide (k.val = w)

-- The odd-false property: for spike_w, all odd positions are false (w is even)
lemma spikeConfig_odd_false (w : Nat) (hw : w % 2 = 0) (n : Nat) :
    ∀ k : Fin (n+1), spikeConfig w n ⟨2 * k.val + 1, by omega⟩ = false := by
  intro k
  simp only [spikeConfig, decide_eq_false_iff_not]
  omega

/-- rule30n (spikeConfig w n) = caEvolve of spikeAtList. -/
lemma rule30n_spikeConfig_eq (w n : Nat) :
    rule30n (n+1) (spikeConfig w n) =
    (caEvolve (n+1) (spikeAtList w (2*(n+1)+1))).getD 0 false := by
  simp [rule30n, spikeConfig, configToList, spikeAtList]

-- rule30n_flipCell_spikeConfig_eq: superseded by the primed version below.

-- Better: avoid the side condition by computing directly
lemma rule30n_flipCell_spikeConfig_eq' (w n : Nat) (m : Fin (2*(n+1)+1))
    (hwm : w ≠ m.val) (hwb : w < 2*(n+1)+1) :
    rule30n (n+1) (flipCell (spikeConfig w n) m) =
    (caEvolve (n+1) (twoSpikeList w m.val (2*(n+1)+1))).getD 0 false := by
  simp only [rule30n]
  unfold spikeConfig
  congr 1
  rw [flipCell_spike_eq_twoSpike w n m hwm hwb]
  simp [configToList, twoSpikeList]

/-!
## SubcaseB resolution for specific left m values at n' ≥ 3087

For each m ∈ {4, 12, 14, 20, 22}:
1. From hcase: F_m(n'+1) = false
2. Find n'' ∈ {3085, 3086} with n'' ≡ n' (mod P_m): n'' = n' - k*P_m for some k
3. F_m(n''+1) = false (by period reduction)
4. Base case witness w: sensitivity at n''
5. Sensitivity at n' by period-sensitivity transfer
-/

-- Helper: period-fold for F_m from n'+1 down by multiples of P
-- Given n'+1 ≥ 3086+1 and period P: find k = (n' - base) / P, then n''+1 = n'+1-k*P
-- We state this as: n'' exists with n'+1 = n''+1 + k*P, n'' ∈ [base, base+P-1]

/-- Given n ≥ base + P, define the reduced value n - P * ((n - base) / P) ∈ [base, base+P-1]. -/
def periodReduce (base P n : Nat) : Nat := n - P * ((n - base) / P)

lemma periodReduce_range (base P n : Nat) (hP : 0 < P) (hn : base ≤ n) :
    base ≤ periodReduce base P n ∧ periodReduce base P n < base + P := by
  simp only [periodReduce]
  have hdiv_le : (n - base) / P * P ≤ n - base := Nat.div_mul_le_self _ _
  have hcomm : P * ((n - base) / P) = (n - base) / P * P := Nat.mul_comm _ _
  constructor
  · omega
  · have hdm := Nat.div_add_mod (n - base) P
    have hmod := Nat.mod_lt (n - base) hP
    omega

lemma periodReduce_diff (base P n : Nat) (hP : 0 < P) (hn : base ≤ n) :
    ∃ k : Nat, n = periodReduce base P n + k * P := by
  simp only [periodReduce]
  use (n - base) / P
  have hdiv_le : (n - base) / P * P ≤ n - base := Nat.div_mul_le_self _ _
  have hdm := Nat.div_add_mod (n - base) P
  have hcomm : P * ((n - base) / P) = (n - base) / P * P := Nat.mul_comm _ _
  omega

/-!
## SubcaseB resolution for m=8 (period 32) at n' ≥ 3087

Witness: spike_2 (w=2)
Period 32 = LCM(period of F_8 = 32, period of G_8_last = 32, period of F_2 = 2,
              period of H_{2,8} = 32).
SubcaseB fires only at n'≡3115 mod 32 in [3087,∞).
At those n': F_2=false, H_{2,8}=true → sensitive. ✓
-/

/-- Iterated G_{8,last} period for m=8. -/
lemma twoSpikeLast8_iterated_period32 (n k : Nat) (hn : n ≥ 8) :
    (caEvolve (n + 1) (twoSpikeLastList 8 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 32) (twoSpikeLastList 8 (2*(n+1+k*32)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 32 = (n + k * 32) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 32 = (n + k * 32) + 1 + 32 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast8_period32 (n + k * 32) (by omega)

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=8, w=2 at n'=3115 (level 3116, tape 6233). -/
lemma subcaseB_m8_base_sens :
    (caEvolve 3116 (spikeAtList 2 6233)).getD 0 false ≠
    (caEvolve 3116 (twoSpikeList 2 8 6233)).getD 0 false := by native_decide

/-- For j ∈ [8,40): F_8(j+1)=false AND G_{8,last}(j+1)=true iff j=11 or j=43 (but 43≥32 so j=11).
    Wait — we check [8,40) via Fin 32 offset by 8: j' = j - 8 ∈ [0,32) for j ∈ [8,40).
    This uses small tapes (size 19..81) and is fast. -/
lemma subcaseB_m8_residue_unique :
    ∀ j : Fin 32,
    (caEvolve (j.val + 8 + 1) (spikeAtList 8 (2*(j.val+8+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 8 + 1) (twoSpikeLastList 8 (2*(j.val+8+1)+1))).getD 0 false = true →
    j.val + 8 = 11 := by native_decide

/-- SubcaseB for m=8 fires only at n''=3115 in [3087, 3119).
    Proof: reduce n'' to j' = (n''-8) mod 32 + 8 ∈ [8,40) using periods,
    then use small native_decide to identify j'=11, hence n''=3115. -/
lemma subcaseB_m8_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 3119)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 8 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 8 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3115 := by
  -- Reduce to j' = (n''-8) mod 32 + 8 ∈ [8, 40), so j' ≥ 8 always holds.
  -- k = (n''-8) / 32 ≥ 0, and j' + k*32 = (n''-8) mod 32 + 8 + (n''-8)/32*32 = n''.
  set k := (n'' - 8) / 32
  set j' := (n'' - 8) % 32 + 8 with hj'_def
  have hj'_range : 8 ≤ j' ∧ j' < 40 := by
    simp only [hj'_def]
    constructor
    · omega
    · have := Nat.mod_lt (n'' - 8) (by omega : 0 < 32); omega
  have hj'lt : j' - 8 < 32 := by omega
  have hn''_decomp : n'' = j' + k * 32 := by
    have hk_def : k = (n'' - 8) / 32 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 8) 32
    omega
  -- Reduce F_8 from n'' to j'
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 8 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 8 32 (by omega) caEvolve_cert_m8_p32 j' k
    have heq : j' + 1 + k * 32 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase''
  -- Reduce G_{8,last} from n'' to j' (j' ≥ 8 holds by hj'_range.1)
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 8 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast8_iterated_period32 j' k hj'_range.1
    have heq : j' + 1 + k * 32 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts''
  -- Small native_decide: j' = 11 (j'.val - 8 = 3 for the Fin 32 encoding)
  have hj'11 : j' = 11 := by
    have hval : (⟨j' - 8, hj'lt⟩ : Fin 32).val = j' - 8 := rfl
    have := subcaseB_m8_residue_unique ⟨j' - 8, hj'lt⟩
      (by simp only [hval]; convert hF_j' using 2 <;> omega)
      (by simp only [hval]; convert hG_j' using 2 <;> omega)
    omega
  -- n'' = j' + k*32 = 11 + k*32; n''∈[3087,3119) → n''=3115
  omega

/-- SubcaseB resolution for m=8, n' ≥ 3087. Witness: spike_2 (w=2). -/
theorem subcaseB_m8_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm8 : m.val = 8)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 2 n'
  refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 2 n']
  rw [rule30n_flipCell_spikeConfig_eq' 2 n' m (by omega) (by omega)]
  -- After rw, goal has twoSpikeList 2 m.val ...; replace m.val with 8
  simp only [hm8]
  -- Convert hcase and hts to caEvolve form (with 8 substituted)
  have hcase8 : (caEvolve (n'+1) (spikeAtList 8 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm8] at hc
    rw [← rule30n_spikeAt_eq n' 8]; exact hc
  have hts8 : (caEvolve (n'+1) (twoSpikeLastList 8 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm8] at ht
    rw [← rule30n_twoSpikeLast_eq n' 8]; exact ht
  -- Period reduce n' to n''∈[3087, 3119)
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 32 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 32 n' (by omega) hn'
  set n'' := periodReduce 3087 32 n' with hn''_def
  -- n' = n'' + k * 32
  have hn'_n'' : n' + 1 = n'' + 1 + k * 32 := by omega
  -- Derive F_8(n''+1) = false
  have hcase'' : (caEvolve (n''+1) (spikeAtList 8 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 8 32 (by omega) caEvolve_cert_m8_p32 n'' k
    have heq : n'' + 1 + k * 32 = n' + 1 := by omega
    rw [heq] at hperiod
    rw [hperiod]; exact hcase8
  -- Derive G_{8,last}(n''+1) = true
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 8 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast8_iterated_period32 n'' k (by omega)
    have heq : n'' + 1 + k * 32 = n' + 1 := by omega
    rw [heq] at hperiod
    rw [hperiod]; exact hts8
  -- Identify n'' = 3115
  have hn''_3115 : n'' = 3115 :=
    subcaseB_m8_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  -- Now n' = 3115 + k * 32
  have hn'_3115k : n' + 1 = 3115 + 1 + k * 32 := by omega
  -- Apply sensitivity_transfer
  have h_base := subcaseB_m8_base_sens
  have h_F_cert : caEvolve 32 (spikeAtList 2 (2*32+2*2+1)) = spikeAtList 2 (2*2+1) :=
    caEvolve_cert_ts2_p32
  have h_H_cert : caEvolve 32 (twoSpikeList 2 8 (2*32+2*(max 2 8)+1)) =
                  twoSpikeList 2 8 (2*(max 2 8)+1) := by
    have : max 2 8 = 8 := by decide
    rw [this]; exact caEvolve_cert_ts28_p32
  have htransfer := sensitivity_transfer 2 8 32 3115 k (by omega) h_F_cert h_H_cert h_base
  -- htransfer : caEvolve (3115+1+k*32) (spikeAtList 2 ...) ≠ caEvolve (3115+1+k*32) (twoSpikeList 2 8 ...)
  -- Goal: caEvolve (n'+1) (spikeAtList 2 (2*(n'+1)+1)) ≠ caEvolve (n'+1) (twoSpikeList 2 8 (2*(n'+1)+1))
  -- n'+1 = 3115+1+k*32 by hn'_3115k
  have heq_np1 : n' + 1 = 3115 + 1 + k * 32 := hn'_3115k
  rw [heq_np1]; exact htransfer

/-!
## SubcaseB resolution for m=10 (period 64) at n' ≥ 3087

Witness: spike_2 (w=2)
Period 64 = LCM(period of F_10 = 64, period of G_10_last = 64, period of F_2 = 2,
              period of H_{2,10} = 64).
SubcaseB fires only at n'≡3120 mod 64 in [3087,∞).
At those n': F_2=false, H_{2,10}=true → sensitive. ✓
-/

/-- Iterated G_{10,last} period for m=10. -/
lemma twoSpikeLast10_iterated_period64 (n k : Nat) (hn : n ≥ 10) :
    (caEvolve (n + 1) (twoSpikeLastList 10 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 64) (twoSpikeLastList 10 (2*(n+1+k*64)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 64 = (n + k * 64) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 64 = (n + k * 64) + 1 + 64 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast10_period64 (n + k * 64) (by omega)

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=10, w=2 at n'=3120 (level 3121, tape 6243). -/
lemma subcaseB_m10_base_sens :
    (caEvolve 3121 (spikeAtList 2 6243)).getD 0 false ≠
    (caEvolve 3121 (twoSpikeList 2 10 6243)).getD 0 false := by native_decide

/-- F_10 and G_{10,last} residue pattern: for j ∈ [10,74) (i.e. j' = j-10 ∈ [0,64)),
    F_10(j+1)=false AND G_{10,last}(j+1)=true iff j=48. (Since (3120-10) mod 64 = 38,
    so j' = 38+10 = 48 in the offset encoding.)
    Small tapes (size 23..149), fast native_decide. -/
lemma subcaseB_m10_residue_unique :
    ∀ j : Fin 64,
    (caEvolve (j.val + 10 + 1) (spikeAtList 10 (2*(j.val+10+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 10 + 1) (twoSpikeLastList 10 (2*(j.val+10+1)+1))).getD 0 false = true →
    j.val + 10 = 48 := by native_decide

/-- SubcaseB for m=10 fires only at n''=3120 in [3087, 3151).
    Proof: reduce n'' to j' = (n''-10) mod 64 + 10 ∈ [10,74) using periods,
    then use small native_decide to identify j'=58, hence n''=3120. -/
lemma subcaseB_m10_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 3151)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 10 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 10 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3120 := by
  -- Reduce to j' = (n''-10) mod 64 + 10 ∈ [10, 74), guaranteeing j' ≥ 10
  set k := (n'' - 10) / 64
  set j' := (n'' - 10) % 64 + 10 with hj'_def
  have hj'_range : 10 ≤ j' ∧ j' < 74 := by
    simp only [hj'_def]
    constructor
    · omega
    · have := Nat.mod_lt (n'' - 10) (by omega : 0 < 64); omega
  have hj'lt : j' - 10 < 64 := by omega
  have hn''_decomp : n'' = j' + k * 64 := by
    have hk_def : k = (n'' - 10) / 64 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 10) 64
    omega
  -- Reduce F_10 from n'' to j'
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 10 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 10 64 (by omega) caEvolve_cert_m10_p64 j' k
    have heq : j' + 1 + k * 64 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase''
  -- Reduce G_{10,last} from n'' to j' (j' ≥ 10 holds by hj'_range.1)
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 10 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast10_iterated_period64 j' k hj'_range.1
    have heq : j' + 1 + k * 64 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts''
  -- Small native_decide: j' = 48 (j'.val - 10 = 38 for the Fin 64 encoding)
  have hj'48 : j' = 48 := by
    have hval : (⟨j' - 10, hj'lt⟩ : Fin 64).val = j' - 10 := rfl
    have := subcaseB_m10_residue_unique ⟨j' - 10, hj'lt⟩
      (by simp only [hval]; convert hF_j' using 2 <;> omega)
      (by simp only [hval]; convert hG_j' using 2 <;> omega)
    omega
  -- n'' = j' + k*64 = 48 + k*64; n''∈[3087,3151) → n''=3120
  omega

/-- SubcaseB resolution for m=10, n' ≥ 3087. Witness: spike_2 (w=2). -/
theorem subcaseB_m10_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm10 : m.val = 10)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 2 n'
  refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 2 n']
  rw [rule30n_flipCell_spikeConfig_eq' 2 n' m (by omega) (by omega)]
  simp only [hm10]
  -- Convert hcase and hts to caEvolve form (with 10 substituted)
  have hcase10 : (caEvolve (n'+1) (spikeAtList 10 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm10] at hc
    rw [← rule30n_spikeAt_eq n' 10]; exact hc
  have hts10 : (caEvolve (n'+1) (twoSpikeLastList 10 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm10] at ht
    rw [← rule30n_twoSpikeLast_eq n' 10]; exact ht
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 64 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 64 n' (by omega) hn'
  set n'' := periodReduce 3087 64 n' with hn''_def
  have hcase'' : (caEvolve (n''+1) (spikeAtList 10 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 10 64 (by omega) caEvolve_cert_m10_p64 n'' k
    have heq : n'' + 1 + k * 64 = n' + 1 := by omega
    rw [heq] at hperiod
    rw [hperiod]; exact hcase10
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 10 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast10_iterated_period64 n'' k (by omega)
    have heq : n'' + 1 + k * 64 = n' + 1 := by omega
    rw [heq] at hperiod
    rw [hperiod]; exact hts10
  have hn''_3120 : n'' = 3120 :=
    subcaseB_m10_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  have hn'_3120k : n' + 1 = 3120 + 1 + k * 64 := by omega
  have h_base := subcaseB_m10_base_sens
  have h_F_cert : caEvolve 64 (spikeAtList 2 (2*64+2*2+1)) = spikeAtList 2 (2*2+1) :=
    caEvolve_cert_ts2_p64
  have h_H_cert : caEvolve 64 (twoSpikeList 2 10 (2*64+2*(max 2 10)+1)) =
                  twoSpikeList 2 10 (2*(max 2 10)+1) := by
    have : max 2 10 = 10 := by decide
    rw [this]; exact caEvolve_cert_ts210_p64
  have htransfer := sensitivity_transfer 2 10 64 3120 k (by omega) h_F_cert h_H_cert h_base
  -- Goal: caEvolve (n'+1) (spikeAtList 2 (2*(n'+1)+1)) ≠ caEvolve (n'+1) (twoSpikeList 2 10 (2*(n'+1)+1))
  -- n'+1 = 3120+1+k*64 by hn'_3120k
  have heq_np1 : n' + 1 = 3120 + 1 + k * 64 := hn'_3120k
  rw [heq_np1]; exact htransfer

/-!
## SubcaseB resolution for m=4 (period 16) at n' ≥ 3087

Witness: spike_6 (w=6)
Period 16 = LCM(period of F_4 = 8, period of G_4_last = 8, period of F_6 = 16,
              period of H_{6,4} = 16).
For ALL j in [0,15]: if F_4(3085+j+1)=false AND G_last(3085+j+1)=true,
then F_6(3085+j+1) ≠ H_{6,4}(3085+j+1). [Verified by native_decide]
SubcaseB fires only at j=0 in [0,15], and at j=0: F_6≠H_{6,4}. ✓
-/

/-- Iterated twoSpikeLast period for m=4. -/
lemma twoSpikeLast4_iterated_period8 (n k : Nat) (hn : n ≥ 4) :
    (caEvolve (n + 1) (twoSpikeLastList 4 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 8) (twoSpikeLastList 4 (2*(n+1+k*8)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 8 = (n + k * 8) + 1 from by omega]
    have hstep3 : n + 1 + (k + 1) * 8 = (n + k * 8) + 1 + 8 := by ring
    rw [hstep3]
    exact rule30n_twoSpikeLast4_period8 (n + k * 8) (by omega)

-- Base sensitivity certs for m=4, w=6 at the two firing bases in [3087, 3103):
-- n'=3093 (≡5 mod 8), level=3094, tape=6189
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3093 :
    (caEvolve 3094 (spikeAtList 6 6189)).getD 0 false ≠
    (caEvolve 3094 (twoSpikeList 4 6 6189)).getD 0 false := by native_decide

-- n'=3101 (≡5 mod 8 as well, 8 steps later), level=3102, tape=6205
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3101 :
    (caEvolve 3102 (spikeAtList 6 6205)).getD 0 false ≠
    (caEvolve 3102 (twoSpikeList 4 6 6205)).getD 0 false := by native_decide

/-- SubcaseB for m=4 fires only at n''=3093 in [3087, 3095). -/
lemma subcaseB_m4_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 3095)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 4 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 4 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3093 := by
  have h : ∀ j : Fin 8,
      (caEvolve (3087 + j.val + 1) (spikeAtList 4 (2*(3087+j.val+1)+1))).getD 0 false = false →
      (caEvolve (3087 + j.val + 1) (twoSpikeLastList 4 (2*(3087+j.val+1)+1))).getD 0 false = true →
      3087 + j.val = 3093 := by native_decide
  have hj_bound : n'' - 3087 < 8 := by omega
  have hj_eq := h ⟨n'' - 3087, hj_bound⟩
    (by convert hcase'' using 2 <;> omega)
    (by convert hts'' using 2 <;> omega)
  omega

/-- SubcaseB resolution for m=4, n' ≥ 3087.
    Witness: w=6 (F_6 period 16, twoSpike(4,6) period 16).
    Two firing bases: n'=3093 and n'=3101 (one period-16 apart within k-parity split). -/
theorem subcaseB_m4_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm4 : m.val = 4)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  -- Convert hcase/hts to caEvolve form
  have hcase4 : (caEvolve (n'+1) (spikeAtList 4 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm4] at hc
    rw [← rule30n_spikeAt_eq n' 4]; exact hc
  have hts4 : (caEvolve (n'+1) (twoSpikeLastList 4 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm4] at ht
    rw [← rule30n_twoSpikeLast_eq n' 4]; exact ht
  -- Period reduce n' to n''∈[3087, 3095) using period 8
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 8 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 8 n' (by omega) hn'
  set n'' := periodReduce 3087 8 n' with hn''_def
  -- Reduce F_4 from n' to n''
  have hcase'' : (caEvolve (n''+1) (spikeAtList 4 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 4 8 (by omega) caEvolve_cert_m4_p8 n'' k
    have heq : n'' + 1 + k * 8 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase4
  -- Reduce G_{4,last} from n' to n''
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 4 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast4_iterated_period8 n'' k (by omega)
    have heq : n'' + 1 + k * 8 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts4
  -- Unique firing at n''=3093
  have hn''_3093 : n'' = 3093 :=
    subcaseB_m4_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  subst hn''_3093
  -- n' = 3093 + k*8; split k into even/odd to get period-16 sub-classes
  have hk_mod2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
  -- shared cert facts
  have h_F_cert : caEvolve 16 (spikeAtList 6 (2*16+2*6+1)) = spikeAtList 6 (2*6+1) :=
    caEvolve_cert_m6_p16
  have h_H_cert : caEvolve 16 (twoSpikeList 6 4 (2*16+2*(max 6 4)+1)) =
                  twoSpikeList 6 4 (2*(max 6 4)+1) := by
    have hmax : max 6 4 = 6 := by decide
    rw [hmax, twoSpikeList_comm 6 4, twoSpikeList_comm 6 4]
    exact caEvolve_cert_ts46_p16
  rcases hk_mod2 with hk0 | hk1
  · -- k = 2*j, n' = 3093 + 16*j; use base sensitivity at n'=3093
    obtain ⟨j, hkj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    use spikeConfig 6 n'
    refine ⟨spikeConfig_odd_false 6 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 6 n']
    rw [rule30n_flipCell_spikeConfig_eq' 6 n' m (by omega) (by omega)]
    simp only [hm4]
    rw [show n' + 1 = 3093 + 1 + j * 16 from by omega]
    have h_H_cert' : caEvolve 16 (twoSpikeList 6 4 (2*16+2*(max 6 4)+1)) =
                     twoSpikeList 6 4 (2*(max 6 4)+1) := h_H_cert
    have h_base : (caEvolve 3094 (spikeAtList 6 6189)).getD 0 false ≠
                  (caEvolve 3094 (twoSpikeList 6 4 6189)).getD 0 false := by
      rw [twoSpikeList_comm]; exact subcaseB_m4_base_sens_3093
    exact sensitivity_transfer 6 4 16 3093 j (by omega) h_F_cert h_H_cert' h_base
  · -- k = 2*j+1, n' = 3101 + 16*j; use base sensitivity at n'=3101
    obtain ⟨j, hkj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
    use spikeConfig 6 n'
    refine ⟨spikeConfig_odd_false 6 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 6 n']
    rw [rule30n_flipCell_spikeConfig_eq' 6 n' m (by omega) (by omega)]
    simp only [hm4]
    rw [show n' + 1 = 3101 + 1 + j * 16 from by omega]
    have h_H_cert' : caEvolve 16 (twoSpikeList 6 4 (2*16+2*(max 6 4)+1)) =
                     twoSpikeList 6 4 (2*(max 6 4)+1) := h_H_cert
    have h_base : (caEvolve 3102 (spikeAtList 6 6205)).getD 0 false ≠
                  (caEvolve 3102 (twoSpikeList 6 4 6205)).getD 0 false := by
      rw [twoSpikeList_comm]; exact subcaseB_m4_base_sens_3101
    exact sensitivity_transfer 6 4 16 3101 j (by omega) h_F_cert h_H_cert' h_base

/-!
## SubcaseB resolution for m=6 (period 16) at n' ≥ 3087

Eight witnesses via telescoping case split on (n' - 3098) / 16:
- n'≡3094 mod 16: witness w=2,  period P=16
- n'≡3098 mod 32: witness w=8,  period P=32
- n'≡3114 mod 64: witness w=10, period P=64
- n'≡3146 mod 256: witness w=14, period P=256
- n'≡3210 mod 256: witness w=20, period P=256
- n'≡3274 mod 256: witness w=14, period P=256
- n'≡3338 mod 512: witness w=16, period P=512
- n'≡3594 mod 512: witness w=16, period P=512
G_last6 period=16 (from CausalConeLemmas). SubcaseB fires at ≡6 and ≡10 mod 16.
-/

/-- Iterated G_{6,last} period for m=6 (period 16). -/
lemma twoSpikeLast6_iterated_period16 (n k : Nat) (hn : n ≥ 6) :
    (caEvolve (n + 1) (twoSpikeLastList 6 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 16) (twoSpikeLastList 6 (2*(n+1+k*16)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 16 = (n + k * 16) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 16 = (n + k * 16) + 1 + 16 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast6_period16 (n + k * 16) (by omega)

-- Period certs for m=6 witnesses: spike(w) and twoSpike(w,6) with native_decide
lemma caEvolve_cert_sp2_p16 :
    caEvolve 16 (spikeAtList 2 37) = spikeAtList 2 5 := by native_decide
lemma caEvolve_cert_ts26_p16 :
    caEvolve 16 (twoSpikeList 2 6 45) = twoSpikeList 2 6 13 := by native_decide
lemma caEvolve_cert_ts86_p32 :
    caEvolve 32 (twoSpikeList 8 6 81) = twoSpikeList 8 6 17 := by native_decide
lemma caEvolve_cert_ts106_p64 :
    caEvolve 64 (twoSpikeList 10 6 149) = twoSpikeList 10 6 21 := by native_decide
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_sp14_p256 :
    caEvolve 256 (spikeAtList 14 541) = spikeAtList 14 29 := by native_decide
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts146_p256 :
    caEvolve 256 (twoSpikeList 14 6 541) = twoSpikeList 14 6 29 := by native_decide
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts206_p256 :
    caEvolve 256 (twoSpikeList 20 6 553) = twoSpikeList 20 6 41 := by native_decide
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_sp16_p512 :
    caEvolve 512 (spikeAtList 16 1057) = spikeAtList 16 33 := by native_decide
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts166_p512 :
    caEvolve 512 (twoSpikeList 16 6 1057) = twoSpikeList 16 6 33 := by native_decide

-- Base sensitivity certs for m=6 (eight firing bases):
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m6_base_sens_3094 :
    (caEvolve 3095 (spikeAtList 2 6191)).getD 0 false ≠
    (caEvolve 3095 (twoSpikeList 2 6 6191)).getD 0 false := by native_decide
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m6_base_sens_3098 :
    (caEvolve 3099 (spikeAtList 8 6199)).getD 0 false ≠
    (caEvolve 3099 (twoSpikeList 8 6 6199)).getD 0 false := by native_decide
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m6_base_sens_3114 :
    (caEvolve 3115 (spikeAtList 10 6231)).getD 0 false ≠
    (caEvolve 3115 (twoSpikeList 10 6 6231)).getD 0 false := by native_decide
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m6_base_sens_3146 :
    (caEvolve 3147 (spikeAtList 14 6295)).getD 0 false ≠
    (caEvolve 3147 (twoSpikeList 14 6 6295)).getD 0 false := by native_decide
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m6_base_sens_3210 :
    (caEvolve 3211 (spikeAtList 20 6423)).getD 0 false ≠
    (caEvolve 3211 (twoSpikeList 20 6 6423)).getD 0 false := by native_decide
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m6_base_sens_3274 :
    (caEvolve 3275 (spikeAtList 14 6551)).getD 0 false ≠
    (caEvolve 3275 (twoSpikeList 14 6 6551)).getD 0 false := by native_decide
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m6_base_sens_3338 :
    (caEvolve 3339 (spikeAtList 16 6679)).getD 0 false ≠
    (caEvolve 3339 (twoSpikeList 16 6 6679)).getD 0 false := by native_decide
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m6_base_sens_3594 :
    (caEvolve 3595 (spikeAtList 16 7191)).getD 0 false ≠
    (caEvolve 3595 (twoSpikeList 16 6 7191)).getD 0 false := by native_decide

/-- Residue classification over Fin 16: SubcaseB for m=6 fires only at j+6∈{6,10}. -/
lemma subcaseB_m6_residue_2class :
    ∀ j : Fin 16,
    (caEvolve (j.val + 6 + 1) (spikeAtList 6 (2*(j.val+6+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 6 + 1) (twoSpikeLastList 6 (2*(j.val+6+1)+1))).getD 0 false = true →
    j.val + 6 = 6 ∨ j.val + 6 = 10 := by native_decide

/-- SubcaseB for m=6 fires only at n''∈{3094, 3098} in [3087, 3103). -/
lemma subcaseB_m6_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 3103)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 6 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 6 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3094 ∨ n'' = 3098 := by
  set k := (n'' - 6) / 16
  set j' := (n'' - 6) % 16 + 6 with hj'_def
  have hj'_range : 6 ≤ j' ∧ j' < 22 := by
    simp only [hj'_def]; constructor
    · omega
    · have := Nat.mod_lt (n'' - 6) (by omega : 0 < 16); omega
  have hj'lt : j' - 6 < 16 := by omega
  have hn''_decomp : n'' = j' + k * 16 := by
    have hk_def : k = (n'' - 6) / 16 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 6) 16; omega
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 6 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 6 16 (by omega) caEvolve_cert_m6_p16 j' k
    have heq : j' + 1 + k * 16 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase''
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 6 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast6_iterated_period16 j' k hj'_range.1
    have heq : j' + 1 + k * 16 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts''
  have hj'_cases : j' = 6 ∨ j' = 10 := by
    have hval : (⟨j' - 6, hj'lt⟩ : Fin 16).val = j' - 6 := rfl
    have h2 := subcaseB_m6_residue_2class ⟨j' - 6, hj'lt⟩
      (by simp only [hval]; convert hF_j' using 2 <;> omega)
      (by simp only [hval]; convert hG_j' using 2 <;> omega)
    rcases h2 with h | h <;> omega
  rcases hj'_cases with h1 | h2
  · left; omega
  · right; omega

/-- SubcaseB resolution for m=6, n' ≥ 3087. Eight witnesses via telescoping. -/
theorem subcaseB_m6_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm6 : m.val = 6)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  -- Convert hcase/hts to caEvolve form
  have hcase6 : (caEvolve (n'+1) (spikeAtList 6 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm6] at hc
    rw [← rule30n_spikeAt_eq n' 6]; exact hc
  have hts6 : (caEvolve (n'+1) (twoSpikeLastList 6 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm6] at ht
    rw [← rule30n_twoSpikeLast_eq n' 6]; exact ht
  -- Period reduce n' to n''∈[3087, 3103) using period 16
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 16 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 16 n' (by omega) hn'
  set n'' := periodReduce 3087 16 n' with hn''_def
  -- Reduce F_6 from n' to n''
  have hcase'' : (caEvolve (n''+1) (spikeAtList 6 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 6 16 (by omega) caEvolve_cert_m6_p16 n'' k
    have heq : n'' + 1 + k * 16 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase6
  -- Reduce G_{6,last} from n' to n''
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 6 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast6_iterated_period16 n'' k (by omega)
    have heq : n'' + 1 + k * 16 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts6
  -- Identify n''
  have hn''_cases : n'' = 3094 ∨ n'' = 3098 :=
    subcaseB_m6_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  rcases hn''_cases with h1 | h2
  · -- n''=3094, n'=3094+k*16, witness w=2, period 16
    use spikeConfig 2 n'
    refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 2 n']
    rw [rule30n_flipCell_spikeConfig_eq' 2 n' m (by omega) (by omega)]
    simp only [hm6]
    have h_F_cert : caEvolve 16 (spikeAtList 2 (2*16+2*2+1)) = spikeAtList 2 (2*2+1) :=
      caEvolve_cert_sp2_p16
    have h_H_cert : caEvolve 16 (twoSpikeList 2 6 (2*16+2*(max 2 6)+1)) =
                    twoSpikeList 2 6 (2*(max 2 6)+1) := by
      have : max 2 6 = 6 := by decide
      rw [this]; exact caEvolve_cert_ts26_p16
    rw [show n' + 1 = 3094 + 1 + k * 16 from by omega]
    exact sensitivity_transfer 2 6 16 3094 k (by omega) h_F_cert h_H_cert subcaseB_m6_base_sens_3094
  · -- n''=3098, n'=3098+k*16: telescope on k
    have hk_mod2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk_mod2 with hk0 | hk1
    · -- k=2*l, n'=3098+32*l, witness w=8, period 32
      obtain ⟨l, hkl⟩ : ∃ l, k = 2 * l := ⟨k / 2, by omega⟩
      use spikeConfig 8 n'
      refine ⟨spikeConfig_odd_false 8 (by decide) n', ?_⟩
      rw [rule30n_spikeConfig_eq 8 n']
      rw [rule30n_flipCell_spikeConfig_eq' 8 n' m (by omega) (by omega)]
      simp only [hm6]
      have h_F_cert : caEvolve 32 (spikeAtList 8 (2*32+2*8+1)) = spikeAtList 8 (2*8+1) :=
        caEvolve_cert_m8_p32
      have h_H_cert : caEvolve 32 (twoSpikeList 8 6 (2*32+2*(max 8 6)+1)) =
                      twoSpikeList 8 6 (2*(max 8 6)+1) := by
        have : max 8 6 = 8 := by decide
        rw [this]; exact caEvolve_cert_ts86_p32
      rw [show n' + 1 = 3098 + 1 + l * 32 from by omega]
      exact sensitivity_transfer 8 6 32 3098 l (by omega) h_F_cert h_H_cert subcaseB_m6_base_sens_3098
    · -- k=2*l+1, n'=3114+32*l: telescope on l
      obtain ⟨l, hkl⟩ : ∃ l, k = 2 * l + 1 := ⟨k / 2, by omega⟩
      have hl_mod2 : l % 2 = 0 ∨ l % 2 = 1 := by omega
      rcases hl_mod2 with hl0 | hl1
      · -- l=2*r, n'=3114+64*r, witness w=10, period 64
        obtain ⟨r, hlr⟩ : ∃ r, l = 2 * r := ⟨l / 2, by omega⟩
        use spikeConfig 10 n'
        refine ⟨spikeConfig_odd_false 10 (by decide) n', ?_⟩
        rw [rule30n_spikeConfig_eq 10 n']
        rw [rule30n_flipCell_spikeConfig_eq' 10 n' m (by omega) (by omega)]
        simp only [hm6]
        have h_F_cert : caEvolve 64 (spikeAtList 10 (2*64+2*10+1)) = spikeAtList 10 (2*10+1) :=
          caEvolve_cert_m10_p64
        have h_H_cert : caEvolve 64 (twoSpikeList 10 6 (2*64+2*(max 10 6)+1)) =
                        twoSpikeList 10 6 (2*(max 10 6)+1) := by
          have : max 10 6 = 10 := by decide
          rw [this]; exact caEvolve_cert_ts106_p64
        rw [show n' + 1 = 3114 + 1 + r * 64 from by omega]
        exact sensitivity_transfer 10 6 64 3114 r (by omega) h_F_cert h_H_cert subcaseB_m6_base_sens_3114
      · -- l=2*r+1, n'=3146+64*r: telescope on r mod 4
        obtain ⟨r, hlr⟩ : ∃ r, l = 2 * r + 1 := ⟨l / 2, by omega⟩
        have hr_mod4 : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
        rcases hr_mod4 with hr0 | hr1 | hr2 | hr3
        · -- r=4*s, n'=3146+256*s, witness w=14, period 256
          obtain ⟨s, hrs⟩ : ∃ s, r = 4 * s := ⟨r / 4, by omega⟩
          use spikeConfig 14 n'
          refine ⟨spikeConfig_odd_false 14 (by decide) n', ?_⟩
          rw [rule30n_spikeConfig_eq 14 n']
          rw [rule30n_flipCell_spikeConfig_eq' 14 n' m (by omega) (by omega)]
          simp only [hm6]
          have h_F_cert : caEvolve 256 (spikeAtList 14 (2*256+2*14+1)) = spikeAtList 14 (2*14+1) :=
            caEvolve_cert_sp14_p256
          have h_H_cert : caEvolve 256 (twoSpikeList 14 6 (2*256+2*(max 14 6)+1)) =
                          twoSpikeList 14 6 (2*(max 14 6)+1) := by
            have : max 14 6 = 14 := by decide
            rw [this]; exact caEvolve_cert_ts146_p256
          rw [show n' + 1 = 3146 + 1 + s * 256 from by omega]
          exact sensitivity_transfer 14 6 256 3146 s (by omega) h_F_cert h_H_cert subcaseB_m6_base_sens_3146
        · -- r=4*s+1, n'=3210+256*s, witness w=20, period 256
          obtain ⟨s, hrs⟩ : ∃ s, r = 4 * s + 1 := ⟨r / 4, by omega⟩
          use spikeConfig 20 n'
          refine ⟨spikeConfig_odd_false 20 (by decide) n', ?_⟩
          rw [rule30n_spikeConfig_eq 20 n']
          rw [rule30n_flipCell_spikeConfig_eq' 20 n' m (by omega) (by omega)]
          simp only [hm6]
          have h_F_cert : caEvolve 256 (spikeAtList 20 (2*256+2*20+1)) = spikeAtList 20 (2*20+1) :=
            caEvolve_cert_m20_p256
          have h_H_cert : caEvolve 256 (twoSpikeList 20 6 (2*256+2*(max 20 6)+1)) =
                          twoSpikeList 20 6 (2*(max 20 6)+1) := by
            have : max 20 6 = 20 := by decide
            rw [this]; exact caEvolve_cert_ts206_p256
          rw [show n' + 1 = 3210 + 1 + s * 256 from by omega]
          exact sensitivity_transfer 20 6 256 3210 s (by omega) h_F_cert h_H_cert subcaseB_m6_base_sens_3210
        · -- r=4*s+2, n'=3274+256*s, witness w=14, period 256
          obtain ⟨s, hrs⟩ : ∃ s, r = 4 * s + 2 := ⟨r / 4, by omega⟩
          use spikeConfig 14 n'
          refine ⟨spikeConfig_odd_false 14 (by decide) n', ?_⟩
          rw [rule30n_spikeConfig_eq 14 n']
          rw [rule30n_flipCell_spikeConfig_eq' 14 n' m (by omega) (by omega)]
          simp only [hm6]
          have h_F_cert : caEvolve 256 (spikeAtList 14 (2*256+2*14+1)) = spikeAtList 14 (2*14+1) :=
            caEvolve_cert_sp14_p256
          have h_H_cert : caEvolve 256 (twoSpikeList 14 6 (2*256+2*(max 14 6)+1)) =
                          twoSpikeList 14 6 (2*(max 14 6)+1) := by
            have : max 14 6 = 14 := by decide
            rw [this]; exact caEvolve_cert_ts146_p256
          rw [show n' + 1 = 3274 + 1 + s * 256 from by omega]
          exact sensitivity_transfer 14 6 256 3274 s (by omega) h_F_cert h_H_cert subcaseB_m6_base_sens_3274
        · -- r=4*s+3, n'=3338+256*s: telescope on s mod 2
          obtain ⟨s, hrs⟩ : ∃ s, r = 4 * s + 3 := ⟨r / 4, by omega⟩
          have hs_mod2 : s % 2 = 0 ∨ s % 2 = 1 := by omega
          rcases hs_mod2 with hs0 | hs1
          · -- s=2*u, n'=3338+512*u, witness w=16, period 512
            obtain ⟨u, hsu⟩ : ∃ u, s = 2 * u := ⟨s / 2, by omega⟩
            use spikeConfig 16 n'
            refine ⟨spikeConfig_odd_false 16 (by decide) n', ?_⟩
            rw [rule30n_spikeConfig_eq 16 n']
            rw [rule30n_flipCell_spikeConfig_eq' 16 n' m (by omega) (by omega)]
            simp only [hm6]
            have h_F_cert : caEvolve 512 (spikeAtList 16 (2*512+2*16+1)) = spikeAtList 16 (2*16+1) :=
              caEvolve_cert_sp16_p512
            have h_H_cert : caEvolve 512 (twoSpikeList 16 6 (2*512+2*(max 16 6)+1)) =
                            twoSpikeList 16 6 (2*(max 16 6)+1) := by
              have : max 16 6 = 16 := by decide
              rw [this]; exact caEvolve_cert_ts166_p512
            rw [show n' + 1 = 3338 + 1 + u * 512 from by omega]
            exact sensitivity_transfer 16 6 512 3338 u (by omega) h_F_cert h_H_cert subcaseB_m6_base_sens_3338
          · -- s=2*u+1, n'=3594+512*u, witness w=16, period 512
            obtain ⟨u, hsu⟩ : ∃ u, s = 2 * u + 1 := ⟨s / 2, by omega⟩
            use spikeConfig 16 n'
            refine ⟨spikeConfig_odd_false 16 (by decide) n', ?_⟩
            rw [rule30n_spikeConfig_eq 16 n']
            rw [rule30n_flipCell_spikeConfig_eq' 16 n' m (by omega) (by omega)]
            simp only [hm6]
            have h_F_cert : caEvolve 512 (spikeAtList 16 (2*512+2*16+1)) = spikeAtList 16 (2*16+1) :=
              caEvolve_cert_sp16_p512
            have h_H_cert : caEvolve 512 (twoSpikeList 16 6 (2*512+2*(max 16 6)+1)) =
                            twoSpikeList 16 6 (2*(max 16 6)+1) := by
              have : max 16 6 = 16 := by decide
              rw [this]; exact caEvolve_cert_ts166_p512
            rw [show n' + 1 = 3594 + 1 + u * 512 from by omega]
            exact sensitivity_transfer 16 6 512 3594 u (by omega) h_F_cert h_H_cert subcaseB_m6_base_sens_3594

/-!
## SubcaseB resolution for m=12 (period 128) at n' ≥ 3087

Two witnesses, four firing classes per 128-period:
- n''=3145 (mod128=73): witness w=4, period P=128
- n''=3149 (mod128=77): witness w=8, period P=128
- n''=3209 (mod128=9):  witness w=8, period P=128
- n''=3213 (mod128=13): witness w=4, period P=128
G_last12 period=64 (from CausalConeLemmas) divides 128; spike(12) period=64 divides 128.
-/

/-- Iterated G_{12,last} period for m=12 (period 64). -/
lemma twoSpikeLast12_iterated_period64 (n k : Nat) (hn : n ≥ 12) :
    (caEvolve (n + 1) (twoSpikeLastList 12 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 64) (twoSpikeLastList 12 (2*(n+1+k*64)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 64 = (n + k * 64) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 64 = (n + k * 64) + 1 + 64 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast12_period64 (n + k * 64) (by omega)

-- Period certs for m=12 witnesses (P=128): verified by native_decide
lemma caEvolve_cert_ts4_p128 :
    caEvolve 128 (spikeAtList 4 265) = spikeAtList 4 9 := by native_decide
lemma caEvolve_cert_ts8_p128 :
    caEvolve 128 (spikeAtList 8 273) = spikeAtList 8 17 := by native_decide
lemma caEvolve_cert_ts812_p128 :
    caEvolve 128 (twoSpikeList 8 12 281) = twoSpikeList 8 12 25 := by native_decide

-- Base sensitivity certs for m=12 (four firing bases):
lemma subcaseB_m12_base_sens_3145 :
    (caEvolve 3146 (spikeAtList 4 6293)).getD 0 false ≠
    (caEvolve 3146 (twoSpikeList 4 12 6293)).getD 0 false := by native_decide
lemma subcaseB_m12_base_sens_3149 :
    (caEvolve 3150 (spikeAtList 8 6301)).getD 0 false ≠
    (caEvolve 3150 (twoSpikeList 8 12 6301)).getD 0 false := by native_decide
lemma subcaseB_m12_base_sens_3209 :
    (caEvolve 3210 (spikeAtList 8 6421)).getD 0 false ≠
    (caEvolve 3210 (twoSpikeList 8 12 6421)).getD 0 false := by native_decide
lemma subcaseB_m12_base_sens_3213 :
    (caEvolve 3214 (spikeAtList 4 6429)).getD 0 false ≠
    (caEvolve 3214 (twoSpikeList 4 12 6429)).getD 0 false := by native_decide

-- Residue classification over Fin 128 (native_decide):
lemma subcaseB_m12_residue_4class :
    ∀ j : Fin 128,
    (caEvolve (j.val + 12 + 1) (spikeAtList 12 (2*(j.val+12+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 12 + 1) (twoSpikeLastList 12 (2*(j.val+12+1)+1))).getD 0 false = true →
    j.val + 12 = 13 ∨ j.val + 12 = 73 ∨ j.val + 12 = 77 ∨ j.val + 12 = 137 := by
  native_decide

/-- SubcaseB for m=12 fires only at n''∈{3145,3149,3209,3213} in [3087,3215). -/
lemma subcaseB_m12_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 3215)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 12 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 12 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3145 ∨ n'' = 3149 ∨ n'' = 3209 ∨ n'' = 3213 := by
  set k := (n'' - 12) / 128
  set j' := (n'' - 12) % 128 + 12 with hj'_def
  have hj'_range : 12 ≤ j' ∧ j' < 140 := by
    simp only [hj'_def]; constructor
    · omega
    · have := Nat.mod_lt (n'' - 12) (by omega : 0 < 128); omega
  have hj'lt : j' - 12 < 128 := by omega
  have hn''_decomp : n'' = j' + k * 128 := by
    have hk_def : k = (n'' - 12) / 128 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 12) 128
    omega
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 12 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 12 64 (by omega) caEvolve_cert_m12_p64 j' (2*k)
    have heq : j' + 1 + (2*k) * 64 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase''
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 12 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast12_iterated_period64 j' (2*k) hj'_range.1
    have heq : j' + 1 + (2*k) * 64 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts''
  have hj'_cases : j' = 13 ∨ j' = 73 ∨ j' = 77 ∨ j' = 137 := by
    have hval : (⟨j' - 12, hj'lt⟩ : Fin 128).val = j' - 12 := rfl
    have h4 := subcaseB_m12_residue_4class ⟨j' - 12, hj'lt⟩
      (by simp only [hval]; convert hF_j' using 2 <;> omega)
      (by simp only [hval]; convert hG_j' using 2 <;> omega)
    rcases h4 with h | h | h | h
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega
  rcases hj'_cases with h1 | h2 | h3 | h4
  · right; right; right; omega  -- h1: j'=13 → n''=3213
  · left; omega                  -- h2: j'=73 → n''=3145
  · right; left; omega           -- h3: j'=77 → n''=3149
  · right; right; left; omega    -- h4: j'=137 → n''=3209

/-- SubcaseB resolution for m=12, n' ≥ 3087. Two witnesses (w=4, w=8), period 128. -/
theorem subcaseB_m12_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm12 : m.val = 12)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  -- Convert hcase/hts to caEvolve form
  have hcase12 : (caEvolve (n'+1) (spikeAtList 12 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm12] at hc
    rw [← rule30n_spikeAt_eq n' 12]; exact hc
  have hts12 : (caEvolve (n'+1) (twoSpikeLastList 12 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm12] at ht
    rw [← rule30n_twoSpikeLast_eq n' 12]; exact ht
  -- Period reduce n' to n''∈[3087,3215) using period 128
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 128 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 128 n' (by omega) hn'
  set n'' := periodReduce 3087 128 n' with hn''_def
  -- Reduce F_12 from n' to n'' (spike(12) period 64, use 2*k steps)
  have hcase'' : (caEvolve (n''+1) (spikeAtList 12 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 12 64 (by omega) caEvolve_cert_m12_p64 n'' (2*k)
    have heq : n'' + 1 + (2*k) * 64 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase12
  -- Reduce G_{12,last} from n' to n''
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 12 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast12_iterated_period64 n'' (2*k) (by omega)
    have heq : n'' + 1 + (2*k) * 64 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts12
  -- Identify n''
  have hn''_cases : n'' = 3145 ∨ n'' = 3149 ∨ n'' = 3209 ∨ n'' = 3213 :=
    subcaseB_m12_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  rcases hn''_cases with h1 | h2 | h3 | h4
  · -- n''=3145, witness w=4, period 128
    use spikeConfig 4 n'
    refine ⟨spikeConfig_odd_false 4 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 4 n']
    rw [rule30n_flipCell_spikeConfig_eq' 4 n' m (by omega) (by omega)]
    simp only [hm12]
    have h_F_cert : caEvolve 128 (spikeAtList 4 (2*128+2*4+1)) = spikeAtList 4 (2*4+1) :=
      caEvolve_cert_ts4_p128
    have h_H_cert : caEvolve 128 (twoSpikeList 4 12 (2*128+2*(max 4 12)+1)) =
                    twoSpikeList 4 12 (2*(max 4 12)+1) := by
      have : max 4 12 = 12 := by decide
      rw [this]; exact caEvolve_cert_ts412_p128
    have htransfer := sensitivity_transfer 4 12 128 3145 k (by omega) h_F_cert h_H_cert
      subcaseB_m12_base_sens_3145
    rw [show n' + 1 = 3145 + 1 + k * 128 from by omega]; exact htransfer
  · -- n''=3149, witness w=8, period 128
    use spikeConfig 8 n'
    refine ⟨spikeConfig_odd_false 8 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 8 n']
    rw [rule30n_flipCell_spikeConfig_eq' 8 n' m (by omega) (by omega)]
    simp only [hm12]
    have h_F_cert : caEvolve 128 (spikeAtList 8 (2*128+2*8+1)) = spikeAtList 8 (2*8+1) :=
      caEvolve_cert_ts8_p128
    have h_H_cert : caEvolve 128 (twoSpikeList 8 12 (2*128+2*(max 8 12)+1)) =
                    twoSpikeList 8 12 (2*(max 8 12)+1) := by
      have : max 8 12 = 12 := by decide
      rw [this]; exact caEvolve_cert_ts812_p128
    have htransfer := sensitivity_transfer 8 12 128 3149 k (by omega) h_F_cert h_H_cert
      subcaseB_m12_base_sens_3149
    rw [show n' + 1 = 3149 + 1 + k * 128 from by omega]; exact htransfer
  · -- n''=3209, witness w=8, period 128
    use spikeConfig 8 n'
    refine ⟨spikeConfig_odd_false 8 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 8 n']
    rw [rule30n_flipCell_spikeConfig_eq' 8 n' m (by omega) (by omega)]
    simp only [hm12]
    have h_F_cert : caEvolve 128 (spikeAtList 8 (2*128+2*8+1)) = spikeAtList 8 (2*8+1) :=
      caEvolve_cert_ts8_p128
    have h_H_cert : caEvolve 128 (twoSpikeList 8 12 (2*128+2*(max 8 12)+1)) =
                    twoSpikeList 8 12 (2*(max 8 12)+1) := by
      have : max 8 12 = 12 := by decide
      rw [this]; exact caEvolve_cert_ts812_p128
    have htransfer := sensitivity_transfer 8 12 128 3209 k (by omega) h_F_cert h_H_cert
      subcaseB_m12_base_sens_3209
    rw [show n' + 1 = 3209 + 1 + k * 128 from by omega]; exact htransfer
  · -- n''=3213, witness w=4, period 128
    use spikeConfig 4 n'
    refine ⟨spikeConfig_odd_false 4 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 4 n']
    rw [rule30n_flipCell_spikeConfig_eq' 4 n' m (by omega) (by omega)]
    simp only [hm12]
    have h_F_cert : caEvolve 128 (spikeAtList 4 (2*128+2*4+1)) = spikeAtList 4 (2*4+1) :=
      caEvolve_cert_ts4_p128
    have h_H_cert : caEvolve 128 (twoSpikeList 4 12 (2*128+2*(max 4 12)+1)) =
                    twoSpikeList 4 12 (2*(max 4 12)+1) := by
      have : max 4 12 = 12 := by decide
      rw [this]; exact caEvolve_cert_ts412_p128
    have htransfer := sensitivity_transfer 4 12 128 3213 k (by omega) h_F_cert h_H_cert
      subcaseB_m12_base_sens_3213
    rw [show n' + 1 = 3213 + 1 + k * 128 from by omega]; exact htransfer

/-!
## SubcaseB resolution for m=14 (period 256) at n' ≥ 3087

Three witnesses, eight firing classes per 256-period:
- n''=3146 (mod256=74):  witness w=6,  period P=256
- n''=3150 (mod256=78):  witness w=6,  period P=256
- n''=3210 (mod256=138): witness w=10, period P=256
- n''=3214 (mod256=142): witness w=6,  period P=256
- n''=3274 (mod256=202): witness w=6,  period P=256
- n''=3278 (mod256=206): witness w=6,  period P=256
- n''=3338 (mod256=10):  witness w=16, period P=256
- n''=3342 (mod256=14):  witness w=6,  period P=256
G_last14 period=64, spike(14) period=64 (both divide 256). twoSpike({6,10,14}) period=256.
-/

/-- Iterated G_{14,last} period for m=14 (period 64). -/
lemma twoSpikeLast14_iterated_period64 (n k : Nat) (hn : n ≥ 14) :
    (caEvolve (n + 1) (twoSpikeLastList 14 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 64) (twoSpikeLastList 14 (2*(n+1+k*64)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 64 = (n + k * 64) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 64 = (n + k * 64) + 1 + 64 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast14_period64 (n + k * 64) (by omega)

-- Period certs for m=14 witnesses (P=256):
set_option maxHeartbeats 800000000 in
lemma caEvolve_cert_ts6_p256 :
    caEvolve 256 (spikeAtList 6 525) = spikeAtList 6 13 := by native_decide
set_option maxHeartbeats 800000000 in
lemma caEvolve_cert_ts614_p256 :
    caEvolve 256 (twoSpikeList 6 14 541) = twoSpikeList 6 14 29 := by native_decide
set_option maxHeartbeats 800000000 in
lemma caEvolve_cert_ts10_p256 :
    caEvolve 256 (spikeAtList 10 533) = spikeAtList 10 21 := by native_decide
set_option maxHeartbeats 800000000 in
lemma caEvolve_cert_ts1014_p256 :
    caEvolve 256 (twoSpikeList 10 14 541) = twoSpikeList 10 14 29 := by native_decide
set_option maxHeartbeats 800000000 in
lemma caEvolve_cert_ts1614_p256 :
    caEvolve 256 (twoSpikeList 16 14 545) = twoSpikeList 16 14 33 := by native_decide

-- Base sensitivity certs for m=14 (eight firing bases):
lemma subcaseB_m14_base_sens_3146 :
    (caEvolve 3147 (spikeAtList 6 6295)).getD 0 false ≠
    (caEvolve 3147 (twoSpikeList 6 14 6295)).getD 0 false := by native_decide
lemma subcaseB_m14_base_sens_3150 :
    (caEvolve 3151 (spikeAtList 6 6303)).getD 0 false ≠
    (caEvolve 3151 (twoSpikeList 6 14 6303)).getD 0 false := by native_decide
lemma subcaseB_m14_base_sens_3210 :
    (caEvolve 3211 (spikeAtList 10 6423)).getD 0 false ≠
    (caEvolve 3211 (twoSpikeList 10 14 6423)).getD 0 false := by native_decide
lemma subcaseB_m14_base_sens_3214 :
    (caEvolve 3215 (spikeAtList 6 6431)).getD 0 false ≠
    (caEvolve 3215 (twoSpikeList 6 14 6431)).getD 0 false := by native_decide
lemma subcaseB_m14_base_sens_3274 :
    (caEvolve 3275 (spikeAtList 6 6551)).getD 0 false ≠
    (caEvolve 3275 (twoSpikeList 6 14 6551)).getD 0 false := by native_decide
lemma subcaseB_m14_base_sens_3278 :
    (caEvolve 3279 (spikeAtList 6 6559)).getD 0 false ≠
    (caEvolve 3279 (twoSpikeList 6 14 6559)).getD 0 false := by native_decide
lemma subcaseB_m14_base_sens_3338 :
    (caEvolve 3339 (spikeAtList 16 6679)).getD 0 false ≠
    (caEvolve 3339 (twoSpikeList 16 14 6679)).getD 0 false := by native_decide
lemma subcaseB_m14_base_sens_3342 :
    (caEvolve 3343 (spikeAtList 6 6687)).getD 0 false ≠
    (caEvolve 3343 (twoSpikeList 6 14 6687)).getD 0 false := by native_decide

-- Residue classification over Fin 256 (native_decide):
lemma subcaseB_m14_residue_8class :
    ∀ j : Fin 256,
    (caEvolve (j.val + 14 + 1) (spikeAtList 14 (2*(j.val+14+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 14 + 1) (twoSpikeLastList 14 (2*(j.val+14+1)+1))).getD 0 false = true →
    j.val + 14 = 14 ∨ j.val + 14 = 74 ∨ j.val + 14 = 78 ∨ j.val + 14 = 138 ∨
    j.val + 14 = 142 ∨ j.val + 14 = 202 ∨ j.val + 14 = 206 ∨ j.val + 14 = 266 := by
  native_decide

/-- SubcaseB for m=14 fires only at n''∈{3146,3150,3210,3214,3274,3278,3338,3342} in [3087,3343). -/
lemma subcaseB_m14_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 3343)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 14 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 14 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3146 ∨ n'' = 3150 ∨ n'' = 3210 ∨ n'' = 3214 ∨
    n'' = 3274 ∨ n'' = 3278 ∨ n'' = 3338 ∨ n'' = 3342 := by
  set k := (n'' - 14) / 256
  set j' := (n'' - 14) % 256 + 14 with hj'_def
  have hj'_range : 14 ≤ j' ∧ j' < 270 := by
    simp only [hj'_def]; constructor
    · omega
    · have := Nat.mod_lt (n'' - 14) (by omega : 0 < 256); omega
  have hj'lt : j' - 14 < 256 := by omega
  have hn''_decomp : n'' = j' + k * 256 := by
    simp only [hj'_def]; have := Nat.div_add_mod (n'' - 14) 256; omega
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 14 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 14 64 (by omega) caEvolve_cert_m14_p64 j' (4*k)
    have heq : j' + 1 + (4*k) * 64 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase''
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 14 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast14_iterated_period64 j' (4*k) hj'_range.1
    have heq : j' + 1 + (4*k) * 64 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts''
  have hj'_cases : j' = 14 ∨ j' = 74 ∨ j' = 78 ∨ j' = 138 ∨
                   j' = 142 ∨ j' = 202 ∨ j' = 206 ∨ j' = 266 := by
    have hval : (⟨j' - 14, hj'lt⟩ : Fin 256).val = j' - 14 := rfl
    have h8 := subcaseB_m14_residue_8class ⟨j' - 14, hj'lt⟩
      (by simp only [hval]; convert hF_j' using 2 <;> omega)
      (by simp only [hval]; convert hG_j' using 2 <;> omega)
    rcases h8 with h|h|h|h|h|h|h|h
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; left; omega
    · right; right; right; right; left; omega
    · right; right; right; right; right; left; omega
    · right; right; right; right; right; right; left; omega
    · right; right; right; right; right; right; right; omega
  rcases hj'_cases with h1|h2|h3|h4|h5|h6|h7|h8
  · right; right; right; right; right; right; right; omega  -- h1: j'=14 → n''=3342
  · left; omega                                               -- h2: j'=74 → n''=3146
  · right; left; omega                                       -- h3: j'=78 → n''=3150
  · right; right; left; omega                               -- h4: j'=138 → n''=3210
  · right; right; right; left; omega                        -- h5: j'=142 → n''=3214
  · right; right; right; right; left; omega                 -- h6: j'=202 → n''=3274
  · right; right; right; right; right; left; omega          -- h7: j'=206 → n''=3278
  · right; right; right; right; right; right; left; omega   -- h8: j'=266 → n''=3338

/-- SubcaseB resolution for m=14, n' ≥ 3087. Witnesses w=6 (6 classes), w=10 (1), w=16 (1). -/
theorem subcaseB_m14_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm14 : m.val = 14)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  have hcase14 : (caEvolve (n'+1) (spikeAtList 14 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm14] at hc
    rw [← rule30n_spikeAt_eq n' 14]; exact hc
  have hts14 : (caEvolve (n'+1) (twoSpikeLastList 14 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm14] at ht
    rw [← rule30n_twoSpikeLast_eq n' 14]; exact ht
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 256 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 256 n' (by omega) hn'
  set n'' := periodReduce 3087 256 n' with hn''_def
  have hcase'' : (caEvolve (n''+1) (spikeAtList 14 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 14 64 (by omega) caEvolve_cert_m14_p64 n'' (4*k)
    have heq : n'' + 1 + (4*k) * 64 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase14
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 14 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast14_iterated_period64 n'' (4*k) (by omega)
    have heq : n'' + 1 + (4*k) * 64 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts14
  have hn''_cases := subcaseB_m14_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  -- Helper to build sensitivity proof for a given witness w and base n_base
  rcases hn''_cases with h1|h2|h3|h4|h5|h6|h7|h8
  · -- n''=3146, w=6
    use spikeConfig 6 n'
    refine ⟨spikeConfig_odd_false 6 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 6 n', rule30n_flipCell_spikeConfig_eq' 6 n' m (by omega) (by omega)]
    simp only [hm14]
    have h_F : caEvolve 256 (spikeAtList 6 (2*256+2*6+1)) = spikeAtList 6 (2*6+1) := caEvolve_cert_ts6_p256
    have h_H : caEvolve 256 (twoSpikeList 6 14 (2*256+2*(max 6 14)+1)) = twoSpikeList 6 14 (2*(max 6 14)+1) := by
      have : max 6 14 = 14 := by decide
      rw [this]; exact caEvolve_cert_ts614_p256
    rw [show n'+1 = 3146+1+k*256 from by omega]
    exact sensitivity_transfer 6 14 256 3146 k (by omega) h_F h_H subcaseB_m14_base_sens_3146
  · -- n''=3150, w=6
    use spikeConfig 6 n'
    refine ⟨spikeConfig_odd_false 6 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 6 n', rule30n_flipCell_spikeConfig_eq' 6 n' m (by omega) (by omega)]
    simp only [hm14]
    have h_F : caEvolve 256 (spikeAtList 6 (2*256+2*6+1)) = spikeAtList 6 (2*6+1) := caEvolve_cert_ts6_p256
    have h_H : caEvolve 256 (twoSpikeList 6 14 (2*256+2*(max 6 14)+1)) = twoSpikeList 6 14 (2*(max 6 14)+1) := by
      have : max 6 14 = 14 := by decide
      rw [this]; exact caEvolve_cert_ts614_p256
    rw [show n'+1 = 3150+1+k*256 from by omega]
    exact sensitivity_transfer 6 14 256 3150 k (by omega) h_F h_H subcaseB_m14_base_sens_3150
  · -- n''=3210, w=10
    use spikeConfig 10 n'
    refine ⟨spikeConfig_odd_false 10 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 10 n', rule30n_flipCell_spikeConfig_eq' 10 n' m (by omega) (by omega)]
    simp only [hm14]
    have h_F : caEvolve 256 (spikeAtList 10 (2*256+2*10+1)) = spikeAtList 10 (2*10+1) := caEvolve_cert_ts10_p256
    have h_H : caEvolve 256 (twoSpikeList 10 14 (2*256+2*(max 10 14)+1)) = twoSpikeList 10 14 (2*(max 10 14)+1) := by
      have : max 10 14 = 14 := by decide
      rw [this]; exact caEvolve_cert_ts1014_p256
    rw [show n'+1 = 3210+1+k*256 from by omega]
    exact sensitivity_transfer 10 14 256 3210 k (by omega) h_F h_H subcaseB_m14_base_sens_3210
  · -- n''=3214, w=6
    use spikeConfig 6 n'
    refine ⟨spikeConfig_odd_false 6 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 6 n', rule30n_flipCell_spikeConfig_eq' 6 n' m (by omega) (by omega)]
    simp only [hm14]
    have h_F : caEvolve 256 (spikeAtList 6 (2*256+2*6+1)) = spikeAtList 6 (2*6+1) := caEvolve_cert_ts6_p256
    have h_H : caEvolve 256 (twoSpikeList 6 14 (2*256+2*(max 6 14)+1)) = twoSpikeList 6 14 (2*(max 6 14)+1) := by
      have : max 6 14 = 14 := by decide
      rw [this]; exact caEvolve_cert_ts614_p256
    rw [show n'+1 = 3214+1+k*256 from by omega]
    exact sensitivity_transfer 6 14 256 3214 k (by omega) h_F h_H subcaseB_m14_base_sens_3214
  · -- n''=3274, w=6
    use spikeConfig 6 n'
    refine ⟨spikeConfig_odd_false 6 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 6 n', rule30n_flipCell_spikeConfig_eq' 6 n' m (by omega) (by omega)]
    simp only [hm14]
    have h_F : caEvolve 256 (spikeAtList 6 (2*256+2*6+1)) = spikeAtList 6 (2*6+1) := caEvolve_cert_ts6_p256
    have h_H : caEvolve 256 (twoSpikeList 6 14 (2*256+2*(max 6 14)+1)) = twoSpikeList 6 14 (2*(max 6 14)+1) := by
      have : max 6 14 = 14 := by decide
      rw [this]; exact caEvolve_cert_ts614_p256
    rw [show n'+1 = 3274+1+k*256 from by omega]
    exact sensitivity_transfer 6 14 256 3274 k (by omega) h_F h_H subcaseB_m14_base_sens_3274
  · -- n''=3278, w=6
    use spikeConfig 6 n'
    refine ⟨spikeConfig_odd_false 6 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 6 n', rule30n_flipCell_spikeConfig_eq' 6 n' m (by omega) (by omega)]
    simp only [hm14]
    have h_F : caEvolve 256 (spikeAtList 6 (2*256+2*6+1)) = spikeAtList 6 (2*6+1) := caEvolve_cert_ts6_p256
    have h_H : caEvolve 256 (twoSpikeList 6 14 (2*256+2*(max 6 14)+1)) = twoSpikeList 6 14 (2*(max 6 14)+1) := by
      have : max 6 14 = 14 := by decide
      rw [this]; exact caEvolve_cert_ts614_p256
    rw [show n'+1 = 3278+1+k*256 from by omega]
    exact sensitivity_transfer 6 14 256 3278 k (by omega) h_F h_H subcaseB_m14_base_sens_3278
  · -- n''=3338, w=16
    use spikeConfig 16 n'
    refine ⟨spikeConfig_odd_false 16 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 16 n', rule30n_flipCell_spikeConfig_eq' 16 n' m (by omega) (by omega)]
    simp only [hm14]
    have h_F : caEvolve 256 (spikeAtList 16 (2*256+2*16+1)) = spikeAtList 16 (2*16+1) := caEvolve_cert_m16_p256
    have h_H : caEvolve 256 (twoSpikeList 16 14 (2*256+2*(max 16 14)+1)) = twoSpikeList 16 14 (2*(max 16 14)+1) := by
      have : max 16 14 = 16 := by decide
      rw [this]; exact caEvolve_cert_ts1614_p256
    rw [show n'+1 = 3338+1+k*256 from by omega]
    exact sensitivity_transfer 16 14 256 3338 k (by omega) h_F h_H subcaseB_m14_base_sens_3338
  · -- n''=3342, w=6
    use spikeConfig 6 n'
    refine ⟨spikeConfig_odd_false 6 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 6 n', rule30n_flipCell_spikeConfig_eq' 6 n' m (by omega) (by omega)]
    simp only [hm14]
    have h_F : caEvolve 256 (spikeAtList 6 (2*256+2*6+1)) = spikeAtList 6 (2*6+1) := caEvolve_cert_ts6_p256
    have h_H : caEvolve 256 (twoSpikeList 6 14 (2*256+2*(max 6 14)+1)) = twoSpikeList 6 14 (2*(max 6 14)+1) := by
      have : max 6 14 = 14 := by decide
      rw [this]; exact caEvolve_cert_ts614_p256
    rw [show n'+1 = 3342+1+k*256 from by omega]
    exact sensitivity_transfer 6 14 256 3342 k (by omega) h_F h_H subcaseB_m14_base_sens_3342

/-!
## SubcaseB resolution for m=22 (period 256)
-/

/-!
## SubcaseB resolution for m=20 (fires every 256 steps) at n' ≥ 3087

Four firing classes per period-1024 (residues 269, 525, 781, 1037 mod 1024 from base 20):
- n''=3341 (j'=269): witness w=2,  cert (2,20) at P=512
- n''=3597 (j'=525): witness w=14, cert (14,20) at P=1024
- n''=3853 (j'=781): witness w=16, cert (16,20) at P=256
- n''=4109 (j'=1037): witness w=16, cert (16,20) at P=256
-/

/-- Iterated G_{20,last} period for m=20. -/
lemma twoSpikeLast20_iterated_period256 (n k : Nat) (hn : n ≥ 20) :
    (caEvolve (n + 1) (twoSpikeLastList 20 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 256) (twoSpikeLastList 20 (2*(n+1+k*256)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 256 = (n + k * 256) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 256 = (n + k * 256) + 1 + 256 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast20_period256 (n + k * 256) (by omega)

-- spike(2) period-512 cert: N_in=1029, N_out=5
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts2_p512 :
    caEvolve 512 (spikeAtList 2 1029) = spikeAtList 2 5 := by native_decide

-- twoSpike(2,20) period-512 cert: max=20, N_in=1065, N_out=41
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts220_p512 :
    caEvolve 512 (twoSpikeList 2 20 1065) = twoSpikeList 2 20 41 := by native_decide

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpike220_period512 (n : Nat) :
    (caEvolve (n+1) (twoSpikeList 2 20 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+512) (twoSpikeList 2 20 (2*((n+1)+512)+1))).getD 0 false :=
  rule30n_twoSpike_period 2 20 512 (by
    have : max 2 20 = 20 := by decide
    rw [this]; exact caEvolve_cert_ts220_p512) n

-- spike(14) period-1024 cert: N_in=2077, N_out=29
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts14_p1024 :
    caEvolve 1024 (spikeAtList 14 2077) = spikeAtList 14 29 := by native_decide

-- twoSpike(14,20) period-1024 cert: max=20, N_in=2089, N_out=41
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts1420_p1024 :
    caEvolve 1024 (twoSpikeList 14 20 2089) = twoSpikeList 14 20 41 := by native_decide

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpike1420_period1024 (n : Nat) :
    (caEvolve (n+1) (twoSpikeList 14 20 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+1024) (twoSpikeList 14 20 (2*((n+1)+1024)+1))).getD 0 false :=
  rule30n_twoSpike_period 14 20 1024 (by
    have : max 14 20 = 20 := by decide
    rw [this]; exact caEvolve_cert_ts1420_p1024) n

-- spike(16) period-1024 cert: N_in=2081, N_out=33
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts16_p1024 :
    caEvolve 1024 (spikeAtList 16 2081) = spikeAtList 16 33 := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=20, w=2 at n'=3341 (level 3342, tape 6685). -/
lemma subcaseB_m20_base_sens_3341 :
    (caEvolve 3342 (spikeAtList 2 6685)).getD 0 false ≠
    (caEvolve 3342 (twoSpikeList 2 20 6685)).getD 0 false := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=20, w=14 at n'=3597 (level 3598, tape 7197). -/
lemma subcaseB_m20_base_sens_3597 :
    (caEvolve 3598 (spikeAtList 14 7197)).getD 0 false ≠
    (caEvolve 3598 (twoSpikeList 14 20 7197)).getD 0 false := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=20, w=16 at n'=3853 (level 3854, tape 7709). -/
lemma subcaseB_m20_base_sens_3853 :
    (caEvolve 3854 (spikeAtList 16 7709)).getD 0 false ≠
    (caEvolve 3854 (twoSpikeList 16 20 7709)).getD 0 false := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=20, w=16 at n'=4109 (level 4110, tape 8221). -/
lemma subcaseB_m20_base_sens_4109 :
    (caEvolve 4110 (spikeAtList 16 8221)).getD 0 false ≠
    (caEvolve 4110 (twoSpikeList 16 20 8221)).getD 0 false := by native_decide

set_option maxHeartbeats 4000000000 in
/-- F_20 and G_{20,last} residue pattern: 4 firing positions in [20,1044).
    j.val+20 ∈ {269, 525, 781, 1037}. Tapes in [43,2089], feasible native_decide. -/
lemma subcaseB_m20_residue_4class :
    ∀ j : Fin 1024,
    (caEvolve (j.val + 20 + 1) (spikeAtList 20 (2*(j.val+20+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 20 + 1) (twoSpikeLastList 20 (2*(j.val+20+1)+1))).getD 0 false = true →
    j.val + 20 = 269 ∨ j.val + 20 = 525 ∨ j.val + 20 = 781 ∨ j.val + 20 = 1037 := by
  native_decide

/-- SubcaseB for m=20 fires only at n''∈{3341,3597,3853,4109} in [3087,4111). -/
lemma subcaseB_m20_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 4111)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 20 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 20 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3341 ∨ n'' = 3597 ∨ n'' = 3853 ∨ n'' = 4109 := by
  set k := (n'' - 20) / 1024
  set j' := (n'' - 20) % 1024 + 20 with hj'_def
  have hj'_range : 20 ≤ j' ∧ j' < 1044 := by
    simp only [hj'_def]
    constructor
    · omega
    · have := Nat.mod_lt (n'' - 20) (by omega : 0 < 1024); omega
  have hj'lt : j' - 20 < 1024 := by omega
  have hn''_decomp : n'' = j' + k * 1024 := by
    have hk_def : k = (n'' - 20) / 1024 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 20) 1024
    omega
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 20 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 20 256 (by omega) caEvolve_cert_m20_p256 j' (4*k)
    have heq : j' + 1 + (4*k) * 256 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase''
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 20 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast20_iterated_period256 j' (4*k) hj'_range.1
    have heq : j' + 1 + (4*k) * 256 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts''
  have hj'_cases : j' = 269 ∨ j' = 525 ∨ j' = 781 ∨ j' = 1037 := by
    have hval : (⟨j' - 20, hj'lt⟩ : Fin 1024).val = j' - 20 := rfl
    have h4 := subcaseB_m20_residue_4class ⟨j' - 20, hj'lt⟩
      (by simp only [hval]; convert hF_j' using 2 <;> omega)
      (by simp only [hval]; convert hG_j' using 2 <;> omega)
    rcases h4 with h | h | h | h
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega
  rcases hj'_cases with h1 | h2 | h3 | h4
  · left; omega
  · right; left; omega
  · right; right; left; omega
  · right; right; right; omega

/-- SubcaseB resolution for m=20, n' ≥ 3087. Four witnesses for four firing classes. -/
theorem subcaseB_m20_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm20 : m.val = 20)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  -- Convert hcase/hts to caEvolve form
  have hcase20 : (caEvolve (n'+1) (spikeAtList 20 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm20] at hc
    rw [← rule30n_spikeAt_eq n' 20]; exact hc
  have hts20 : (caEvolve (n'+1) (twoSpikeLastList 20 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm20] at ht
    rw [← rule30n_twoSpikeLast_eq n' 20]; exact ht
  -- Period reduce n' to n''∈[3087,4111) using period 1024 = 4×256
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 1024 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 1024 n' (by omega) hn'
  set n'' := periodReduce 3087 1024 n' with hn''_def
  -- Reduce F_20 from n' to n'' (period 256, 4*k steps)
  have hcase'' : (caEvolve (n''+1) (spikeAtList 20 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 20 256 (by omega) caEvolve_cert_m20_p256 n'' (4*k)
    have heq : n'' + 1 + (4*k) * 256 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase20
  -- Reduce G_{20,last} from n' to n''
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 20 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast20_iterated_period256 n'' (4*k) (by omega)
    have heq : n'' + 1 + (4*k) * 256 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts20
  -- Identify n''
  have hn''_cases : n'' = 3341 ∨ n'' = 3597 ∨ n'' = 3853 ∨ n'' = 4109 :=
    subcaseB_m20_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  rcases hn''_cases with h1 | h2 | h3 | h4
  · -- n''=3341, witness w=2, period 512
    use spikeConfig 2 n'
    refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 2 n']
    rw [rule30n_flipCell_spikeConfig_eq' 2 n' m (by omega) (by omega)]
    simp only [hm20]
    have h_F_cert : caEvolve 512 (spikeAtList 2 (2*512+2*2+1)) = spikeAtList 2 (2*2+1) :=
      caEvolve_cert_ts2_p512
    have h_H_cert : caEvolve 512 (twoSpikeList 2 20 (2*512+2*(max 2 20)+1)) =
                    twoSpikeList 2 20 (2*(max 2 20)+1) := by
      have : max 2 20 = 20 := by decide
      rw [this]; exact caEvolve_cert_ts220_p512
    have htransfer := sensitivity_transfer 2 20 512 3341 (2*k) (by omega) h_F_cert h_H_cert
      subcaseB_m20_base_sens_3341
    rw [show n' + 1 = 3341 + 1 + (2*k) * 512 from by omega]; exact htransfer
  · -- n''=3597, witness w=14, period 1024
    use spikeConfig 14 n'
    refine ⟨spikeConfig_odd_false 14 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 14 n']
    rw [rule30n_flipCell_spikeConfig_eq' 14 n' m (by omega) (by omega)]
    simp only [hm20]
    have h_F_cert : caEvolve 1024 (spikeAtList 14 (2*1024+2*14+1)) = spikeAtList 14 (2*14+1) :=
      caEvolve_cert_ts14_p1024
    have h_H_cert : caEvolve 1024 (twoSpikeList 14 20 (2*1024+2*(max 14 20)+1)) =
                    twoSpikeList 14 20 (2*(max 14 20)+1) := by
      have : max 14 20 = 20 := by decide
      rw [this]; exact caEvolve_cert_ts1420_p1024
    have htransfer := sensitivity_transfer 14 20 1024 3597 k (by omega) h_F_cert h_H_cert
      subcaseB_m20_base_sens_3597
    rw [show n' + 1 = 3597 + 1 + k * 1024 from by omega]; exact htransfer
  · -- n''=3853, witness w=16, period 1024
    use spikeConfig 16 n'
    refine ⟨spikeConfig_odd_false 16 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 16 n']
    rw [rule30n_flipCell_spikeConfig_eq' 16 n' m (by omega) (by omega)]
    simp only [hm20]
    have h_F_cert : caEvolve 1024 (spikeAtList 16 (2*1024+2*16+1)) = spikeAtList 16 (2*16+1) :=
      caEvolve_cert_ts16_p1024
    have h_H_cert : caEvolve 1024 (twoSpikeList 16 20 (2*1024+2*(max 16 20)+1)) =
                    twoSpikeList 16 20 (2*(max 16 20)+1) := by
      have : max 16 20 = 20 := by decide
      rw [this]; exact caEvolve_cert_ts1620_p1024
    have htransfer := sensitivity_transfer 16 20 1024 3853 k (by omega) h_F_cert h_H_cert
      subcaseB_m20_base_sens_3853
    rw [show n' + 1 = 3853 + 1 + k * 1024 from by omega]; exact htransfer
  · -- n''=4109, witness w=16, period 1024
    use spikeConfig 16 n'
    refine ⟨spikeConfig_odd_false 16 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 16 n']
    rw [rule30n_flipCell_spikeConfig_eq' 16 n' m (by omega) (by omega)]
    simp only [hm20]
    have h_F_cert : caEvolve 1024 (spikeAtList 16 (2*1024+2*16+1)) = spikeAtList 16 (2*16+1) :=
      caEvolve_cert_ts16_p1024
    have h_H_cert : caEvolve 1024 (twoSpikeList 16 20 (2*1024+2*(max 16 20)+1)) =
                    twoSpikeList 16 20 (2*(max 16 20)+1) := by
      have : max 16 20 = 20 := by decide
      rw [this]; exact caEvolve_cert_ts1620_p1024
    have htransfer := sensitivity_transfer 16 20 1024 4109 k (by omega) h_F_cert h_H_cert
      subcaseB_m20_base_sens_4109
    rw [show n' + 1 = 4109 + 1 + k * 1024 from by omega]; exact htransfer

/-!
## SubcaseB resolution for m=22 (period 1024) at n' ≥ 3087

SubcaseB for m=22 fires at n' ≡ 14 mod 256, giving 4 residue classes mod 1024:
  {270, 526, 782, 14}.
Witnesses:
  - Residue 270 (n''=3342): w=4, P=1024
  - Residue 526 (n''=3598): w=2, P=1024
  - Residue 14  (n''=4110): w=2, P=1024
  - Residue 782 (n''=3854): further subdivision required:
      * j≡0 mod 2 (n'=3854+j*2048): w=12, P=2048
      * j≡1 mod 4 (n'=4878+j*4096): w=18, P=4096
      * j≡3 mod 4 (n'=6926+j*4096): blocked (twoSpike(w,22) period > 7424 for all even w)
-/

/-- Iterated G_{22,last} period for m=22. -/
lemma twoSpikeLast22_iterated_period256 (n k : Nat) (hn : n ≥ 22) :
    (caEvolve (n + 1) (twoSpikeLastList 22 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 256) (twoSpikeLastList 22 (2*(n+1+k*256)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 256 = (n + k * 256) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 256 = (n + k * 256) + 1 + 256 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast22_period256 (n + k * 256) (by omega)

-- spike(4) period-1024 cert: N_in = 2*1024+2*4+1=2057, N_out=9
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_spike4_p1024 :
    caEvolve 1024 (spikeAtList 4 2057) = spikeAtList 4 9 := by native_decide

-- twoSpike(4,22) period-1024 cert: max(4,22)=22, N_in=2*1024+2*22+1=2093, N_out=45
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts422_p1024 :
    caEvolve 1024 (twoSpikeList 4 22 2093) = twoSpikeList 4 22 45 := by native_decide

-- twoSpike(2,22) period-1024 cert: max(2,22)=22, N_in=2*1024+2*22+1=2093, N_out=45
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts222_p1024 :
    caEvolve 1024 (twoSpikeList 2 22 2093) = twoSpikeList 2 22 45 := by native_decide

-- spike(12) period-2048 cert: N_in=2*2048+2*12+1=4121, N_out=25
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_spike12_p2048 :
    caEvolve 2048 (spikeAtList 12 4121) = spikeAtList 12 25 := by native_decide

-- twoSpike(12,22) period-2048 cert: max(12,22)=22, N_in=2*2048+2*22+1=4141, N_out=45
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts1222_p2048 :
    caEvolve 2048 (twoSpikeList 12 22 4141) = twoSpikeList 12 22 45 := by native_decide

-- spike(18) period-4096 cert: N_in=2*4096+2*18+1=8229, N_out=37
-- (proved via Array Bool in CA_Array.lean to avoid OOM)
lemma caEvolve_cert_spike18_p4096 :
    caEvolve 4096 (spikeAtList 18 8229) = spikeAtList 18 37 :=
  CA_Array.caEvolve_cert_spike18_p4096

-- twoSpike(18,22) period-4096 cert: max(18,22)=22, N_in=2*4096+2*22+1=8237, N_out=45
-- (proved via Array Bool in CA_Array.lean to avoid OOM)
lemma caEvolve_cert_ts1822_p4096 :
    caEvolve 4096 (twoSpikeList 18 22 8237) = twoSpikeList 18 22 45 :=
  CA_Array.caEvolve_cert_ts1822_p4096

-- spike(5) period-4096 cert: N_in=2*4096+2*5+1=8203, N_out=11
-- (proved via Array Bool in CA_Array.lean to avoid OOM)
lemma caEvolve_cert_spike5_p4096 :
    caEvolve 4096 (spikeAtList 5 8203) = spikeAtList 5 11 :=
  CA_Array.caEvolve_cert_spike5_p4096

-- twoSpike(5,22) period-4096 cert: max(5,22)=22, N_in=2*4096+2*22+1=8237, N_out=45
-- (proved via Array Bool in CA_Array.lean to avoid OOM)
lemma caEvolve_cert_ts522_p4096 :
    caEvolve 4096 (twoSpikeList 5 22 8237) = twoSpikeList 5 22 45 :=
  CA_Array.caEvolve_cert_ts522_p4096

-- spike(28) period-16384 cert: N_in=2*16384+2*28+1=32825, N_out=57
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_spike28_p16384 :
    caEvolve 16384 (spikeAtList 28 32825) = spikeAtList 28 57 := by native_decide

-- twoSpike(28,22) period-16384 cert: max(28,22)=28, N_in=32825, N_out=57
-- (proved via Array Bool in CA_Array.lean to avoid OOM)
lemma caEvolve_cert_ts2822_p16384 :
    caEvolve 16384 (twoSpikeList 28 22 32825) = twoSpikeList 28 22 57 :=
  CA_Array.caEvolve_cert_ts2822_p16384

-- spike(26) period-16384 cert: N_in=2*16384+2*26+1=32821, N_out=53
-- (proved via Array Bool in CA_Array.lean to avoid OOM)
lemma caEvolve_cert_spike26_p16384 :
    caEvolve 16384 (spikeAtList 26 32821) = spikeAtList 26 53 :=
  CA_Array.caEvolve_cert_spike26_p16384

-- twoSpike(26,22) period-16384 cert: max(26,22)=26, N_in=32821, N_out=53
-- (proved via Array Bool in CA_Array.lean to avoid OOM)
lemma caEvolve_cert_ts2622_p16384 :
    caEvolve 16384 (twoSpikeList 26 22 32821) = twoSpikeList 26 22 53 :=
  CA_Array.caEvolve_cert_ts2622_p16384

-- Base sensitivity: w=28 at n''=6926 (step=6927, tape=13855)
-- (proved via Array Bool in CA_Array.lean to avoid OOM)
lemma subcaseB_m22_base_sens_6926_w28 :
    (caEvolve 6927 (spikeAtList 28 13855)).getD 0 false ≠
    (caEvolve 6927 (twoSpikeList 28 22 13855)).getD 0 false :=
  CA_Array.subcaseB_m22_base_sens_6926_w28

-- Base sensitivity: w=26 at n''=11022 (step=11023, tape=22047)
-- (proved via Array Bool in CA_Array.lean to avoid OOM)
lemma subcaseB_m22_base_sens_11022_w26 :
    (caEvolve 11023 (spikeAtList 26 22047)).getD 0 false ≠
    (caEvolve 11023 (twoSpikeList 26 22 22047)).getD 0 false :=
  CA_Array.subcaseB_m22_base_sens_11022_w26

-- Base sensitivity: w=26 at n''=15118 (step=15119, tape=30239)
-- (proved via Array Bool in CA_Array.lean to avoid OOM)
lemma subcaseB_m22_base_sens_15118_w26 :
    (caEvolve 15119 (spikeAtList 26 30239)).getD 0 false ≠
    (caEvolve 15119 (twoSpikeList 26 22 30239)).getD 0 false :=
  CA_Array.subcaseB_m22_base_sens_15118_w26

-- Base sensitivity: w=5 at n''=6926 (step=6927, tape=13855)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m22_base_sens_6926 :
    (caEvolve 6927 (spikeAtList 5 13855)).getD 0 false ≠
    (caEvolve 6927 (twoSpikeList 5 22 13855)).getD 0 false := by native_decide

-- Base sensitivity: w=4 at n''=3342 (step=3343, tape=6687)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m22_base_sens_3342 :
    (caEvolve 3343 (spikeAtList 4 6687)).getD 0 false ≠
    (caEvolve 3343 (twoSpikeList 4 22 6687)).getD 0 false := by native_decide

-- Base sensitivity: w=2 at n''=3598 (step=3599, tape=7199)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m22_base_sens_3598 :
    (caEvolve 3599 (spikeAtList 2 7199)).getD 0 false ≠
    (caEvolve 3599 (twoSpikeList 2 22 7199)).getD 0 false := by native_decide

-- Base sensitivity: w=2 at n''=4110 (step=4111, tape=8223)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m22_base_sens_4110 :
    (caEvolve 4111 (spikeAtList 2 8223)).getD 0 false ≠
    (caEvolve 4111 (twoSpikeList 2 22 8223)).getD 0 false := by native_decide

-- Base sensitivity: w=12 at n''=3854 (step=3855, tape=7711)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m22_base_sens_3854 :
    (caEvolve 3855 (spikeAtList 12 7711)).getD 0 false ≠
    (caEvolve 3855 (twoSpikeList 12 22 7711)).getD 0 false := by native_decide

-- Base sensitivity: w=18 at n''=782 (step=783, tape=1567); n'=782+4096=4878 by period transfer
lemma subcaseB_m22_base_sens_782 :
    (caEvolve 783 (spikeAtList 18 1567)).getD 0 false ≠
    (caEvolve 783 (twoSpikeList 18 22 1567)).getD 0 false := by native_decide

-- F_22 and G_{22,last} fire at 4 positions in [22, 1046).
-- j.val+22 ∈ {270, 526, 782, 1038}. Tapes ≤ 2093, fast for native_decide.
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m22_residue_4class :
    ∀ j : Fin 1024,
    (caEvolve (j.val + 22 + 1) (spikeAtList 22 (2*(j.val+22+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 22 + 1) (twoSpikeLastList 22 (2*(j.val+22+1)+1))).getD 0 false = true →
    j.val + 22 = 270 ∨ j.val + 22 = 526 ∨ j.val + 22 = 782 ∨ j.val + 22 = 1038 := by
  native_decide

/-- SubcaseB for m=22 fires only at n''∈{3342, 3598, 3854, 4110} in [3087, 4111). -/
lemma subcaseB_m22_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 4111)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 22 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 22 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3342 ∨ n'' = 3598 ∨ n'' = 3854 ∨ n'' = 4110 := by
  set k := (n'' - 22) / 1024
  set j' := (n'' - 22) % 1024 + 22 with hj'_def
  have hj'_range : 22 ≤ j' ∧ j' < 1046 := by
    simp only [hj'_def]; constructor
    · omega
    · have := Nat.mod_lt (n'' - 22) (by omega : 0 < 1024); omega
  have hj'lt : j' - 22 < 1024 := by omega
  have hn''_decomp : n'' = j' + k * 1024 := by
    have hk_def : k = (n'' - 22) / 1024 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 22) 1024
    omega
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 22 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 22 256 (by omega) caEvolve_cert_m22_p256 j' (4*k)
    have heq : j' + 1 + (4*k) * 256 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase''
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 22 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast22_iterated_period256 j' (4*k) hj'_range.1
    have heq : j' + 1 + (4*k) * 256 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts''
  have hj'_cases : j' = 270 ∨ j' = 526 ∨ j' = 782 ∨ j' = 1038 := by
    have hval : (⟨j' - 22, hj'lt⟩ : Fin 1024).val = j' - 22 := rfl
    have h4 := subcaseB_m22_residue_4class ⟨j' - 22, hj'lt⟩
      (by simp only [hval]; convert hF_j' using 2 <;> omega)
      (by simp only [hval]; convert hG_j' using 2 <;> omega)
    rcases h4 with h | h | h | h
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega
  rcases hj'_cases with h1 | h2 | h3 | h4
  · left; omega
  · right; left; omega
  · right; right; left; omega
  · right; right; right; omega

/-- SubcaseB for m=22, n' ≥ 3087.
    Witnesses: w=4 (residue 270), w=2 (residues 526 and 14), w=12/18 (residue 782 sub-cases).
    The sub-case n'≡6926 mod 4096 (782 residue, j≡3 mod 4) remains open. -/
theorem subcaseB_m22_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm22 : m.val = 22)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  have hcase22 : (caEvolve (n'+1) (spikeAtList 22 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm22] at hc
    rw [← rule30n_spikeAt_eq n' 22]; exact hc
  have hts22 : (caEvolve (n'+1) (twoSpikeLastList 22 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm22] at ht
    rw [← rule30n_twoSpikeLast_eq n' 22]; exact ht
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 1024 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 1024 n' (by omega) hn'
  set n'' := periodReduce 3087 1024 n' with hn''_def
  have hcase'' : (caEvolve (n''+1) (spikeAtList 22 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 22 256 (by omega) caEvolve_cert_m22_p256 n'' (4*k)
    have heq : n'' + 1 + (4*k) * 256 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase22
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 22 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast22_iterated_period256 n'' (4*k) (by omega)
    have heq : n'' + 1 + (4*k) * 256 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts22
  have hn''_cases := subcaseB_m22_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  rcases hn''_cases with h1 | h2 | h3 | h4
  · -- n''=3342, residue 270, witness w=4, P=1024
    use spikeConfig 4 n'
    refine ⟨spikeConfig_odd_false 4 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 4 n', rule30n_flipCell_spikeConfig_eq' 4 n' m (by omega) (by omega)]
    simp only [hm22]
    have h_F : caEvolve 1024 (spikeAtList 4 (2*1024+2*4+1)) = spikeAtList 4 (2*4+1) :=
      caEvolve_cert_spike4_p1024
    have h_H : caEvolve 1024 (twoSpikeList 4 22 (2*1024+2*(max 4 22)+1)) =
               twoSpikeList 4 22 (2*(max 4 22)+1) := by
      have : max 4 22 = 22 := by decide
      rw [this]; exact caEvolve_cert_ts422_p1024
    rw [show n'+1 = 3342+1+k*1024 from by omega]
    exact sensitivity_transfer 4 22 1024 3342 k (by omega) h_F h_H subcaseB_m22_base_sens_3342
  · -- n''=3598, residue 526, witness w=2, P=1024
    use spikeConfig 2 n'
    refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 2 n', rule30n_flipCell_spikeConfig_eq' 2 n' m (by omega) (by omega)]
    simp only [hm22]
    have h_F : caEvolve 1024 (spikeAtList 2 (2*1024+2*2+1)) = spikeAtList 2 (2*2+1) :=
      caEvolve_cert_ts2_p1024
    have h_H : caEvolve 1024 (twoSpikeList 2 22 (2*1024+2*(max 2 22)+1)) =
               twoSpikeList 2 22 (2*(max 2 22)+1) := by
      have : max 2 22 = 22 := by decide
      rw [this]; exact caEvolve_cert_ts222_p1024
    rw [show n'+1 = 3598+1+k*1024 from by omega]
    exact sensitivity_transfer 2 22 1024 3598 k (by omega) h_F h_H subcaseB_m22_base_sens_3598
  · -- n''=3854, residue 782, further split by k mod 4
    -- n' = 3854 + k*1024
    have hk_mod : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk_mod with hk_even | hk_odd
    · -- k even: k = 2*j, n' = 3854 + j*2048, use w=12, P=2048
      obtain ⟨j, hkj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
      use spikeConfig 12 n'
      refine ⟨spikeConfig_odd_false 12 (by decide) n', ?_⟩
      rw [rule30n_spikeConfig_eq 12 n', rule30n_flipCell_spikeConfig_eq' 12 n' m (by omega) (by omega)]
      simp only [hm22]
      have h_F : caEvolve 2048 (spikeAtList 12 (2*2048+2*12+1)) = spikeAtList 12 (2*12+1) :=
        caEvolve_cert_spike12_p2048
      have h_H : caEvolve 2048 (twoSpikeList 12 22 (2*2048+2*(max 12 22)+1)) =
                 twoSpikeList 12 22 (2*(max 12 22)+1) := by
        have : max 12 22 = 22 := by decide
        rw [this]; exact caEvolve_cert_ts1222_p2048
      rw [show n'+1 = 3854+1+j*2048 from by omega]
      exact sensitivity_transfer 12 22 2048 3854 j (by omega) h_F h_H subcaseB_m22_base_sens_3854
    · -- k odd: k = 2*j+1
      have hk_mod4 : k % 4 = 1 ∨ k % 4 = 3 := by omega
      rcases hk_mod4 with hk1 | hk3
      · -- k ≡ 1 mod 4: k = 4*i+1, n' = 3854+(4i+1)*1024 = 4878+i*4096, use w=18, P=4096
        obtain ⟨i, hki⟩ : ∃ i, k = 4 * i + 1 := ⟨k / 4, by omega⟩
        use spikeConfig 18 n'
        refine ⟨spikeConfig_odd_false 18 (by decide) n', ?_⟩
        rw [rule30n_spikeConfig_eq 18 n', rule30n_flipCell_spikeConfig_eq' 18 n' m (by omega) (by omega)]
        simp only [hm22]
        have h_F : caEvolve 4096 (spikeAtList 18 (2*4096+2*18+1)) = spikeAtList 18 (2*18+1) :=
          caEvolve_cert_spike18_p4096
        have h_H : caEvolve 4096 (twoSpikeList 18 22 (2*4096+2*(max 18 22)+1)) =
                   twoSpikeList 18 22 (2*(max 18 22)+1) := by
          have : max 18 22 = 22 := by decide
          rw [this]; exact caEvolve_cert_ts1822_p4096
        rw [show n'+1 = 782+1+(i+1)*4096 from by omega]
        exact sensitivity_transfer 18 22 4096 782 (i+1) (by omega) h_F h_H subcaseB_m22_base_sens_782
      · -- k ≡ 3 mod 4: n' ≡ 6926 mod 4096
        -- n' = 6926 + 4096*i (where k = 4*i+3)
        -- Split by i mod 4, using period P=16384:
        --   i≡0 (n'=6926): w=28, P=16384
        --   i≡1 (n'=11022): w=26, P=16384
        --   i≡2 (n'=15118): w=26, P=16384
        --   i≡3 (n'=19214): open (no even w with period-16384 cert found; w=44 is sensitive
        --                    but its CA orbit period exceeds 16384)
        obtain ⟨i, hki⟩ : ∃ i, k = 4 * i + 3 := ⟨k / 4, by omega⟩
        have hi_mod : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
        rcases hi_mod with hi0 | hi1 | hi2 | hi3
        · -- i ≡ 0 mod 4: n' = 6926 + 16384*(i/4), use w=28, P=16384
          obtain ⟨j, hij⟩ : ∃ j, i = 4 * j := ⟨i / 4, by omega⟩
          use spikeConfig 28 n'
          refine ⟨spikeConfig_odd_false 28 (by decide) n', ?_⟩
          rw [rule30n_spikeConfig_eq 28 n', rule30n_flipCell_spikeConfig_eq' 28 n' m (by omega) (by omega)]
          simp only [hm22]
          have h_F : caEvolve 16384 (spikeAtList 28 (2*16384+2*28+1)) = spikeAtList 28 (2*28+1) :=
            caEvolve_cert_spike28_p16384
          have h_H : caEvolve 16384 (twoSpikeList 28 22 (2*16384+2*(max 28 22)+1)) =
                     twoSpikeList 28 22 (2*(max 28 22)+1) := by
            have : max 28 22 = 28 := by decide
            rw [this]; exact caEvolve_cert_ts2822_p16384
          rw [show n'+1 = 6926+1+j*16384 from by omega]
          exact sensitivity_transfer 28 22 16384 6926 j (by omega) h_F h_H subcaseB_m22_base_sens_6926_w28
        · -- i ≡ 1 mod 4: n' = 11022 + 16384*(i/4), use w=26, P=16384
          obtain ⟨j, hij⟩ : ∃ j, i = 4 * j + 1 := ⟨i / 4, by omega⟩
          use spikeConfig 26 n'
          refine ⟨spikeConfig_odd_false 26 (by decide) n', ?_⟩
          rw [rule30n_spikeConfig_eq 26 n', rule30n_flipCell_spikeConfig_eq' 26 n' m (by omega) (by omega)]
          simp only [hm22]
          have h_F : caEvolve 16384 (spikeAtList 26 (2*16384+2*26+1)) = spikeAtList 26 (2*26+1) :=
            caEvolve_cert_spike26_p16384
          have h_H : caEvolve 16384 (twoSpikeList 26 22 (2*16384+2*(max 26 22)+1)) =
                     twoSpikeList 26 22 (2*(max 26 22)+1) := by
            have : max 26 22 = 26 := by decide
            rw [this]; exact caEvolve_cert_ts2622_p16384
          rw [show n'+1 = 11022+1+j*16384 from by omega]
          exact sensitivity_transfer 26 22 16384 11022 j (by omega) h_F h_H subcaseB_m22_base_sens_11022_w26
        · -- i ≡ 2 mod 4: n' = 15118 + 16384*(i/4), use w=26, P=16384
          obtain ⟨j, hij⟩ : ∃ j, i = 4 * j + 2 := ⟨i / 4, by omega⟩
          use spikeConfig 26 n'
          refine ⟨spikeConfig_odd_false 26 (by decide) n', ?_⟩
          rw [rule30n_spikeConfig_eq 26 n', rule30n_flipCell_spikeConfig_eq' 26 n' m (by omega) (by omega)]
          simp only [hm22]
          have h_F : caEvolve 16384 (spikeAtList 26 (2*16384+2*26+1)) = spikeAtList 26 (2*26+1) :=
            caEvolve_cert_spike26_p16384
          have h_H : caEvolve 16384 (twoSpikeList 26 22 (2*16384+2*(max 26 22)+1)) =
                     twoSpikeList 26 22 (2*(max 26 22)+1) := by
            have : max 26 22 = 26 := by decide
            rw [this]; exact caEvolve_cert_ts2622_p16384
          rw [show n'+1 = 15118+1+j*16384 from by omega]
          exact sensitivity_transfer 26 22 16384 15118 j (by omega) h_F h_H subcaseB_m22_base_sens_15118_w26
        · -- i ≡ 3 mod 4: n' ≡ 19214 mod 16384
          -- n' = 19214 + 16384*j where i = 4*j+3
          -- Split by j mod 2, using period P=32768:
          --   j≡0 (n'=19214): w=30, P=32768 ✓
          --   j≡1 (n'=35598): OPEN (no even w with manageable period found)
          obtain ⟨j, hij⟩ : ∃ j, i = 4 * j + 3 := ⟨i / 4, by omega⟩
          have hj_mod : j % 2 = 0 ∨ j % 2 = 1 := by omega
          rcases hj_mod with hj0 | hj1
          · -- j ≡ 0 mod 2: n' = 19214 + 32768*(j/2), use w=30, P=32768
            obtain ⟨l, hjl⟩ : ∃ l, j = 2 * l := ⟨j / 2, by omega⟩
            use spikeConfig 30 n'
            refine ⟨spikeConfig_odd_false 30 (by decide) n', ?_⟩
            rw [rule30n_spikeConfig_eq 30 n', rule30n_flipCell_spikeConfig_eq' 30 n' m (by omega) (by omega)]
            simp only [hm22]
            have h_F : caEvolve 32768 (spikeAtList 30 (2*32768+2*30+1)) = spikeAtList 30 (2*30+1) :=
              caEvolve_cert_spike30_p32768
            have h_H : caEvolve 32768 (twoSpikeList 30 22 (2*32768+2*(max 30 22)+1)) =
                       twoSpikeList 30 22 (2*(max 30 22)+1) := by
              have : max 30 22 = 30 := by decide
              rw [this]; exact caEvolve_cert_ts3022_p32768
            rw [show n'+1 = 19214+1+l*32768 from by omega]
            exact sensitivity_transfer 30 22 32768 19214 l (by omega) h_F h_H subcaseB_m22_base_sens_19214_w30
          · -- j ≡ 1 mod 2: n' = 35598 + 32768*(j/2)
            -- OPEN: twoSpike(34,22) period=131072; further split hits period cascade.
            -- Linearity corridor structural proof needed for full closure.
            sorry
  · -- n''=4110, residue 14, witness w=2, P=1024
    use spikeConfig 2 n'
    refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 2 n', rule30n_flipCell_spikeConfig_eq' 2 n' m (by omega) (by omega)]
    simp only [hm22]
    have h_F : caEvolve 1024 (spikeAtList 2 (2*1024+2*2+1)) = spikeAtList 2 (2*2+1) :=
      caEvolve_cert_ts2_p1024
    have h_H : caEvolve 1024 (twoSpikeList 2 22 (2*1024+2*(max 2 22)+1)) =
               twoSpikeList 2 22 (2*(max 2 22)+1) := by
      have : max 2 22 = 22 := by decide
      rw [this]; exact caEvolve_cert_ts222_p1024
    rw [show n'+1 = 4110+1+k*1024 from by omega]
    exact sensitivity_transfer 2 22 1024 4110 k (by omega) h_F h_H subcaseB_m22_base_sens_4110

/-!
## SubcaseB resolution for m=26 (period 1024) at n' ≥ 3087

Witness: spike_2 (w=2)
Period 1024 = LCM(period of F_26 = 1024, period of G_26_last = 1024, period of F_2 = 2,
              period of H_{2,26} = 1024).
SubcaseB fires only at n'≡3340 mod 1024 in [3087,∞).
At those n': F_2=true, H_{2,26}=false → sensitive (they differ). ✓
-/

/-- Iterated G_{26,last} period for m=26. -/
lemma twoSpikeLast26_iterated_period1024 (n k : Nat) (hn : n ≥ 26) :
    (caEvolve (n + 1) (twoSpikeLastList 26 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 1024) (twoSpikeLastList 26 (2*(n+1+k*1024)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 1024 = (n + k * 1024) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 1024 = (n + k * 1024) + 1 + 1024 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast26_period1024 (n + k * 1024) (by omega)

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=26, w=2 at n'=3340 (level 3341, tape 6683). -/
lemma subcaseB_m26_base_sens :
    (caEvolve 3341 (spikeAtList 2 6683)).getD 0 false ≠
    (caEvolve 3341 (twoSpikeList 2 26 6683)).getD 0 false := by native_decide

set_option maxHeartbeats 4000000000 in
/-- For j ∈ [26,1050): F_26(j+1)=false AND G_{26,last}(j+1)=true iff j=268.
    (Since (3340-26) mod 1024 = 242, so j' = 242+26 = 268 in the offset encoding.)
    Small tapes (size 55..2101), feasible with native_decide. -/
lemma subcaseB_m26_residue_unique :
    ∀ j : Fin 1024,
    (caEvolve (j.val + 26 + 1) (spikeAtList 26 (2*(j.val+26+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 26 + 1) (twoSpikeLastList 26 (2*(j.val+26+1)+1))).getD 0 false = true →
    j.val + 26 = 268 := by native_decide

/-- SubcaseB for m=26 fires only at n''=3340 in [3087, 4111).
    Proof: reduce n'' to j' = (n''-26) mod 1024 + 26 ∈ [26,1050) using periods,
    then use native_decide to identify j'=268, hence n''=3340. -/
lemma subcaseB_m26_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 4111)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 26 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 26 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3340 := by
  set k := (n'' - 26) / 1024
  set j' := (n'' - 26) % 1024 + 26 with hj'_def
  have hj'_range : 26 ≤ j' ∧ j' < 1050 := by
    simp only [hj'_def]
    constructor
    · omega
    · have := Nat.mod_lt (n'' - 26) (by omega : 0 < 1024); omega
  have hj'lt : j' - 26 < 1024 := by omega
  have hn''_decomp : n'' = j' + k * 1024 := by
    have hk_def : k = (n'' - 26) / 1024 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 26) 1024
    omega
  -- Reduce F_26 from n'' to j'
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 26 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 26 1024 (by omega) caEvolve_cert_m26_p1024 j' k
    have heq : j' + 1 + k * 1024 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase''
  -- Reduce G_{26,last} from n'' to j' (j' ≥ 26 holds by hj'_range.1)
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 26 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast26_iterated_period1024 j' k hj'_range.1
    have heq : j' + 1 + k * 1024 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts''
  -- Small native_decide: j' = 268 (j'.val - 26 = 242 for the Fin 1024 encoding)
  have hj'268 : j' = 268 := by
    have hval : (⟨j' - 26, hj'lt⟩ : Fin 1024).val = j' - 26 := rfl
    have := subcaseB_m26_residue_unique ⟨j' - 26, hj'lt⟩
      (by simp only [hval]; convert hF_j' using 2 <;> omega)
      (by simp only [hval]; convert hG_j' using 2 <;> omega)
    omega
  -- n'' = j' + k*1024 = 268 + k*1024; n''∈[3087,4111) → n''=3340
  omega

/-- SubcaseB resolution for m=26, n' ≥ 3087. Witness: spike_2 (w=2). -/
theorem subcaseB_m26_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm26 : m.val = 26)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 2 n'
  refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 2 n']
  rw [rule30n_flipCell_spikeConfig_eq' 2 n' m (by omega) (by omega)]
  simp only [hm26]
  -- Convert hcase and hts to caEvolve form (with 26 substituted)
  have hcase26 : (caEvolve (n'+1) (spikeAtList 26 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm26] at hc
    rw [← rule30n_spikeAt_eq n' 26]; exact hc
  have hts26 : (caEvolve (n'+1) (twoSpikeLastList 26 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm26] at ht
    rw [← rule30n_twoSpikeLast_eq n' 26]; exact ht
  -- Period reduce n' to n''∈[3087, 4111)
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 1024 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 1024 n' (by omega) hn'
  set n'' := periodReduce 3087 1024 n' with hn''_def
  have hcase'' : (caEvolve (n''+1) (spikeAtList 26 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 26 1024 (by omega) caEvolve_cert_m26_p1024 n'' k
    have heq : n'' + 1 + k * 1024 = n' + 1 := by omega
    rw [heq] at hperiod
    rw [hperiod]; exact hcase26
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 26 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast26_iterated_period1024 n'' k (by omega)
    have heq : n'' + 1 + k * 1024 = n' + 1 := by omega
    rw [heq] at hperiod
    rw [hperiod]; exact hts26
  -- Identify n'' = 3340
  have hn''_3340 : n'' = 3340 :=
    subcaseB_m26_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  have hn'_3340k : n' + 1 = 3340 + 1 + k * 1024 := by omega
  -- Apply sensitivity_transfer
  have h_base := subcaseB_m26_base_sens
  have h_F_cert : caEvolve 1024 (spikeAtList 2 (2*1024+2*2+1)) = spikeAtList 2 (2*2+1) :=
    caEvolve_cert_ts2_p1024
  have h_H_cert : caEvolve 1024 (twoSpikeList 2 26 (2*1024+2*(max 2 26)+1)) =
                  twoSpikeList 2 26 (2*(max 2 26)+1) := by
    have : max 2 26 = 26 := by decide
    rw [this]; exact caEvolve_cert_ts226_p1024
  have htransfer := sensitivity_transfer 2 26 1024 3340 k (by omega) h_F_cert h_H_cert h_base
  have heq_np1 : n' + 1 = 3340 + 1 + k * 1024 := hn'_3340k
  rw [heq_np1]; exact htransfer

/-!
## SubcaseB resolution for m=16 (period 256) at n' ≥ 3087

Witness: spike_18 (w=18)
Period 256: SubcaseB fires at n'≡3207, n'≡3211, n'≡3279 (mod 256) in [3087,∞).
At all these n': F_18 ≠ H_{18,16}. ✓
-/

/-- Iterated G_{16,last} period for m=16. -/
lemma twoSpikeLast16_iterated_period256 (n k : Nat) (hn : n ≥ 16) :
    (caEvolve (n + 1) (twoSpikeLastList 16 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 256) (twoSpikeLastList 16 (2*(n+1+k*256)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 256 = (n + k * 256) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 256 = (n + k * 256) + 1 + 256 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast16_period256 (n + k * 256) (by omega)

set_option maxHeartbeats 4000000000 in
/-- spike(18) period cert at P=256: N_in=549, N_out=37. -/
lemma caEvolve_cert_ts18_p256 :
    caEvolve 256 (spikeAtList 18 549) = spikeAtList 18 37 := by native_decide

set_option maxHeartbeats 4000000000 in
/-- twoSpike(18, 16) period cert at P=256: max(18,16)=18, N_in=549, N_out=37. -/
lemma caEvolve_cert_ts1816_p256 :
    caEvolve 256 (twoSpikeList 18 16 549) = twoSpikeList 18 16 37 := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=16, w=18 at n'=3207 (level 3208, tape 6417). -/
lemma subcaseB_m16_base_sens_1 :
    (caEvolve 3208 (spikeAtList 18 6417)).getD 0 false ≠
    (caEvolve 3208 (twoSpikeList 18 16 6417)).getD 0 false := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=16, w=18 at n'=3211 (level 3212, tape 6425). -/
lemma subcaseB_m16_base_sens_2 :
    (caEvolve 3212 (spikeAtList 18 6425)).getD 0 false ≠
    (caEvolve 3212 (twoSpikeList 18 16 6425)).getD 0 false := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=16, w=18 at n'=3279 (level 3280, tape 6561). -/
lemma subcaseB_m16_base_sens_3 :
    (caEvolve 3280 (spikeAtList 18 6561)).getD 0 false ≠
    (caEvolve 3280 (twoSpikeList 18 16 6561)).getD 0 false := by native_decide

/-- F_16 and G_{16,last} residue pattern: 3 firing positions in [16,272).
    j.val+16 ∈ {135, 139, 207}. Small tapes, fast native_decide. -/
lemma subcaseB_m16_residue_3class :
    ∀ j : Fin 256,
    (caEvolve (j.val + 16 + 1) (spikeAtList 16 (2*(j.val+16+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 16 + 1) (twoSpikeLastList 16 (2*(j.val+16+1)+1))).getD 0 false = true →
    j.val + 16 = 135 ∨ j.val + 16 = 139 ∨ j.val + 16 = 207 := by native_decide

/-- SubcaseB for m=16 fires only at n''∈{3207, 3211, 3279} in [3087, 3343). -/
lemma subcaseB_m16_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 3343)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 16 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 16 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3207 ∨ n'' = 3211 ∨ n'' = 3279 := by
  set k := (n'' - 16) / 256
  set j' := (n'' - 16) % 256 + 16 with hj'_def
  have hj'_range : 16 ≤ j' ∧ j' < 272 := by
    simp only [hj'_def]
    constructor
    · omega
    · have := Nat.mod_lt (n'' - 16) (by omega : 0 < 256); omega
  have hj'lt : j' - 16 < 256 := by omega
  have hn''_decomp : n'' = j' + k * 256 := by
    have hk_def : k = (n'' - 16) / 256 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 16) 256
    omega
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 16 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 16 256 (by omega) caEvolve_cert_m16_p256 j' k
    have heq : j' + 1 + k * 256 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase''
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 16 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast16_iterated_period256 j' k hj'_range.1
    have heq : j' + 1 + k * 256 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts''
  have hj'_cases : j' = 135 ∨ j' = 139 ∨ j' = 207 := by
    have hval : (⟨j' - 16, hj'lt⟩ : Fin 256).val = j' - 16 := rfl
    have h3 := subcaseB_m16_residue_3class ⟨j' - 16, hj'lt⟩
      (by simp only [hval]; convert hF_j' using 2 <;> omega)
      (by simp only [hval]; convert hG_j' using 2 <;> omega)
    rcases h3 with h | h | h
    · left; omega
    · right; left; omega
    · right; right; omega
  rcases hj'_cases with h1 | h2 | h3
  · left; omega
  · right; left; omega
  · right; right; omega

/-- SubcaseB resolution for m=16, n' ≥ 3087. Witness: spike_18 (w=18). -/
theorem subcaseB_m16_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm16 : m.val = 16)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 18 n'
  refine ⟨spikeConfig_odd_false 18 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 18 n']
  rw [rule30n_flipCell_spikeConfig_eq' 18 n' m (by omega) (by omega)]
  simp only [hm16]
  have hcase16 : (caEvolve (n'+1) (spikeAtList 16 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm16] at hc
    rw [← rule30n_spikeAt_eq n' 16]; exact hc
  have hts16 : (caEvolve (n'+1) (twoSpikeLastList 16 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm16] at ht
    rw [← rule30n_twoSpikeLast_eq n' 16]; exact ht
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 256 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 256 n' (by omega) hn'
  set n'' := periodReduce 3087 256 n' with hn''_def
  have hcase'' : (caEvolve (n''+1) (spikeAtList 16 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 16 256 (by omega) caEvolve_cert_m16_p256 n'' k
    have heq : n'' + 1 + k * 256 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase16
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 16 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast16_iterated_period256 n'' k (by omega)
    have heq : n'' + 1 + k * 256 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts16
  have hn''_cases : n'' = 3207 ∨ n'' = 3211 ∨ n'' = 3279 :=
    subcaseB_m16_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  have h_F_cert : caEvolve 256 (spikeAtList 18 (2*256+2*18+1)) = spikeAtList 18 (2*18+1) :=
    caEvolve_cert_ts18_p256
  have h_H_cert : caEvolve 256 (twoSpikeList 18 16 (2*256+2*(max 18 16)+1)) =
                  twoSpikeList 18 16 (2*(max 18 16)+1) := by
    have : max 18 16 = 18 := by decide
    rw [this]; exact caEvolve_cert_ts1816_p256
  rcases hn''_cases with h1 | h2 | h3
  · have hn'_eq' : n' + 1 = 3207 + 1 + k * 256 := by omega
    have htransfer := sensitivity_transfer 18 16 256 3207 k (by omega) h_F_cert h_H_cert
      subcaseB_m16_base_sens_1
    rw [hn'_eq']; exact htransfer
  · have hn'_eq' : n' + 1 = 3211 + 1 + k * 256 := by omega
    have htransfer := sensitivity_transfer 18 16 256 3211 k (by omega) h_F_cert h_H_cert
      subcaseB_m16_base_sens_2
    rw [hn'_eq']; exact htransfer
  · have hn'_eq' : n' + 1 = 3279 + 1 + k * 256 := by omega
    have htransfer := sensitivity_transfer 18 16 256 3279 k (by omega) h_F_cert h_H_cert
      subcaseB_m16_base_sens_3
    rw [hn'_eq']; exact htransfer

/-!
## SubcaseB resolution for m=24 (period 512) at n' ≥ 3087

Witness: spike_10 (w=10)
Period 512: SubcaseB fires at n'≡3339, n'≡3343 (mod 512) in [3087,∞).
At both n': F_10 ≠ H_{10,24}. ✓
-/

/-- Iterated G_{24,last} period for m=24. -/
lemma twoSpikeLast24_iterated_period512 (n k : Nat) (hn : n ≥ 24) :
    (caEvolve (n + 1) (twoSpikeLastList 24 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 512) (twoSpikeLastList 24 (2*(n+1+k*512)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 512 = (n + k * 512) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 512 = (n + k * 512) + 1 + 512 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast24_period512 (n + k * 512) (by omega)

set_option maxHeartbeats 4000000000 in
/-- spike(10) period cert at P=512: N_in=1045, N_out=21. -/
lemma caEvolve_cert_ts10_p512 :
    caEvolve 512 (spikeAtList 10 1045) = spikeAtList 10 21 := by native_decide

set_option maxHeartbeats 4000000000 in
/-- twoSpike(10, 24) period cert at P=512: max(10,24)=24, N_in=1073, N_out=49. -/
lemma caEvolve_cert_ts1024_p512 :
    caEvolve 512 (twoSpikeList 10 24 1073) = twoSpikeList 10 24 49 := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=24, w=10 at n'=3339 (level 3340, tape 6681). -/
lemma subcaseB_m24_base_sens_1 :
    (caEvolve 3340 (spikeAtList 10 6681)).getD 0 false ≠
    (caEvolve 3340 (twoSpikeList 10 24 6681)).getD 0 false := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=24, w=10 at n'=3343 (level 3344, tape 6689). -/
lemma subcaseB_m24_base_sens_2 :
    (caEvolve 3344 (spikeAtList 10 6689)).getD 0 false ≠
    (caEvolve 3344 (twoSpikeList 10 24 6689)).getD 0 false := by native_decide

/-- F_24 and G_{24,last} residue pattern: 2 firing positions in [24,536).
    j.val+24 ∈ {267, 271}. Small tapes, fast native_decide. -/
lemma subcaseB_m24_residue_2class :
    ∀ j : Fin 512,
    (caEvolve (j.val + 24 + 1) (spikeAtList 24 (2*(j.val+24+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 24 + 1) (twoSpikeLastList 24 (2*(j.val+24+1)+1))).getD 0 false = true →
    j.val + 24 = 267 ∨ j.val + 24 = 271 := by native_decide

/-- SubcaseB for m=24 fires only at n''∈{3339, 3343} in [3087, 3599). -/
lemma subcaseB_m24_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 3599)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 24 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 24 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3339 ∨ n'' = 3343 := by
  set k := (n'' - 24) / 512
  set j' := (n'' - 24) % 512 + 24 with hj'_def
  have hj'_range : 24 ≤ j' ∧ j' < 536 := by
    simp only [hj'_def]
    constructor
    · omega
    · have := Nat.mod_lt (n'' - 24) (by omega : 0 < 512); omega
  have hj'lt : j' - 24 < 512 := by omega
  have hn''_decomp : n'' = j' + k * 512 := by
    have hk_def : k = (n'' - 24) / 512 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 24) 512
    omega
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 24 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 24 512 (by omega) caEvolve_cert_m24_p512 j' k
    have heq : j' + 1 + k * 512 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase''
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 24 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast24_iterated_period512 j' k hj'_range.1
    have heq : j' + 1 + k * 512 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts''
  have hj'_cases : j' = 267 ∨ j' = 271 := by
    have hval : (⟨j' - 24, hj'lt⟩ : Fin 512).val = j' - 24 := rfl
    have h2 := subcaseB_m24_residue_2class ⟨j' - 24, hj'lt⟩
      (by simp only [hval]; convert hF_j' using 2 <;> omega)
      (by simp only [hval]; convert hG_j' using 2 <;> omega)
    rcases h2 with h | h
    · left; omega
    · right; omega
  rcases hj'_cases with h1 | h2
  · left; omega
  · right; omega

/-- SubcaseB resolution for m=24, n' ≥ 3087. Witness: spike_10 (w=10). -/
theorem subcaseB_m24_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm24 : m.val = 24)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 10 n'
  refine ⟨spikeConfig_odd_false 10 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 10 n']
  rw [rule30n_flipCell_spikeConfig_eq' 10 n' m (by omega) (by omega)]
  simp only [hm24]
  have hcase24 : (caEvolve (n'+1) (spikeAtList 24 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm24] at hc
    rw [← rule30n_spikeAt_eq n' 24]; exact hc
  have hts24 : (caEvolve (n'+1) (twoSpikeLastList 24 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm24] at ht
    rw [← rule30n_twoSpikeLast_eq n' 24]; exact ht
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 512 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 512 n' (by omega) hn'
  set n'' := periodReduce 3087 512 n' with hn''_def
  have hcase'' : (caEvolve (n''+1) (spikeAtList 24 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 24 512 (by omega) caEvolve_cert_m24_p512 n'' k
    have heq : n'' + 1 + k * 512 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase24
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 24 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast24_iterated_period512 n'' k (by omega)
    have heq : n'' + 1 + k * 512 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts24
  have hn''_cases : n'' = 3339 ∨ n'' = 3343 :=
    subcaseB_m24_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  have h_F_cert : caEvolve 512 (spikeAtList 10 (2*512+2*10+1)) = spikeAtList 10 (2*10+1) :=
    caEvolve_cert_ts10_p512
  have h_H_cert : caEvolve 512 (twoSpikeList 10 24 (2*512+2*(max 10 24)+1)) =
                  twoSpikeList 10 24 (2*(max 10 24)+1) := by
    have : max 10 24 = 24 := by decide
    rw [this]; exact caEvolve_cert_ts1024_p512
  rcases hn''_cases with h1 | h2
  · have hn'_eq' : n' + 1 = 3339 + 1 + k * 512 := by omega
    have htransfer := sensitivity_transfer 10 24 512 3339 k (by omega) h_F_cert h_H_cert
      subcaseB_m24_base_sens_1
    rw [hn'_eq']; exact htransfer
  · have hn'_eq' : n' + 1 = 3343 + 1 + k * 512 := by omega
    have htransfer := sensitivity_transfer 10 24 512 3343 k (by omega) h_F_cert h_H_cert
      subcaseB_m24_base_sens_2
    rw [hn'_eq']; exact htransfer

/-!
## SubcaseB resolution for m=28 (period 2048) at n' ≥ 3087

Three firing residues per 2048-period: j'+28 ∈ {1293, 1297, 2065}.
- n''=3341 (j'+28=1293): w=2, P=2048
- n''=3345 (j'+28=1297): w=2, P=2048
- n''=4113 (j'+28=2065): secondary k mod 4 reduction
  * k≡0 mod 4: w=16, P=8192 (n'=4113+l·8192)
  * k≡1 mod 4: w=8,  P=4096 (n'=6161+(2l)·4096)
  * k≡2 mod 4: w=16, P=8192 (n'=8209+l·8192)
  * k≡3 mod 4: w=8,  P=4096 (n'=6161+(2l+1)·4096)
Certs verified: spike/twoSpike period certs + base sensitivity at 3341,3345,4113,6161,8209.
-/

/-- Iterated G_{28,last} period for m=28. -/
lemma twoSpikeLast28_iterated_period2048 (n k : Nat) (hn : n ≥ 28) :
    (caEvolve (n + 1) (twoSpikeLastList 28 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 2048) (twoSpikeLastList 28 (2*(n+1+k*2048)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 2048 = (n + k * 2048) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 2048 = (n + k * 2048) + 1 + 2048 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast28_period2048 (n + k * 2048) (by omega)

set_option maxHeartbeats 4000000000 in
/-- spike(2) period cert at P=2048: N_in=4101, N_out=5. -/
lemma caEvolve_cert_ts2_p2048 :
    caEvolve 2048 (spikeAtList 2 4101) = spikeAtList 2 5 := by native_decide

set_option maxHeartbeats 4000000000 in
/-- twoSpike(2, 28) period cert at P=2048: max(2,28)=28, N_in=4153, N_out=57. -/
lemma caEvolve_cert_ts228_p2048 :
    caEvolve 2048 (twoSpikeList 2 28 4153) = twoSpikeList 2 28 57 := by native_decide

set_option maxHeartbeats 4000000000 in
/-- spike(8) period cert at P=4096: N_in=8209, N_out=17. -/
lemma caEvolve_cert_ts8_p4096 :
    caEvolve 4096 (spikeAtList 8 8209) = spikeAtList 8 17 := by native_decide

set_option maxHeartbeats 4000000000 in
/-- twoSpike(8, 28) period cert at P=4096: max(8,28)=28, N_in=8249, N_out=57. -/
lemma caEvolve_cert_ts828_p4096 :
    caEvolve 4096 (twoSpikeList 8 28 8249) = twoSpikeList 8 28 57 := by native_decide

/-- Intermediate state of twoSpikeList 16 28 after 4096 steps (length 8249).
    Positions 1, 2, 16, 28 are true; all others false. -/
def mid_1628 : List Bool :=
  List.ofFn (fun k : Fin 8249 => decide (k.val = 1 ∨ k.val = 2 ∨ k.val = 16 ∨ k.val = 28))

-- Small-tape cert: caEvolve 4096 on twoSpikeList 16 28 at tape 8221.
-- 8221 = 8192+29, so positions 0..28 satisfy i+8192 < 8221.
set_option maxHeartbeats 4000000000 in
lemma cert_1628_4096_small :
    caEvolve 4096 (twoSpikeList 16 28 8221) =
    [false, true, true, false, false, false, false, false, false, false, false, false,
     false, false, false, false, true, false, false, false, false, false, false, false,
     false, false, false, false, true] := by native_decide

/-- Phase 1: caEvolve 4096 on twoSpikeList 16 28 16441 = mid_1628.
    Proved structurally: for i < 29 use causal-cone agreement with tape 8221;
    for i ≥ 29 both sides are false. -/
lemma caEvolve_cert_ts1628_phase1 :
    caEvolve 4096 (twoSpikeList 16 28 16441) = mid_1628 := by
  apply List.ext_getElem
  · have h1 : (caEvolve 4096 (twoSpikeList 16 28 16441)).length = 8249 := by
      have := caEvolve_length_le 4096 (twoSpikeList 16 28 16441)
        (by rw [twoSpikeList_length]; omega)
      rw [twoSpikeList_length] at this; omega
    simp only [mid_1628, List.length_ofFn, h1]
  · intro i hi1 hi2
    simp only [mid_1628, List.getElem_ofFn]
    rw [List.getElem_eq_getD false]
    by_cases hi : i < 29
    · -- Use causal-cone agreement to reduce to tape 8221
      have hagree : (caEvolve 4096 (twoSpikeList 16 28 16441)).getD i false =
                   (caEvolve 4096 (twoSpikeList 16 28 8221)).getD i false :=
        caEvolve_twoSpike_agree 4096 16 28 16441 8221 i (by omega) (by omega)
      rw [hagree, cert_1628_4096_small]
      -- Now: concrete 29-element list .getD i false = decide (i=1∨i=2∨i=16∨i=28)
      -- interval_cases not available; use Fin 29 universal then specialize
      have key : ∀ k : Fin 29,
          ([false, true, true, false, false, false, false, false, false, false, false, false,
            false, false, false, false, true, false, false, false, false, false, false, false,
            false, false, false, false, true] : List Bool).getD k.val false =
          decide (k.val = 1 ∨ k.val = 2 ∨ k.val = 16 ∨ k.val = 28) := by native_decide
      exact key ⟨i, hi⟩
    · -- i ≥ 29: LHS = false via all-false drop; RHS = false since i > 28
      push_neg at hi
      have h_rhs_false : (fun k : Fin 8249 => decide (k.val = 1 ∨ k.val = 2 ∨ k.val = 16 ∨ k.val = 28))
          ⟨i, by simp only [mid_1628, List.length_ofFn] at hi2; exact hi2⟩ = false := by
        simp; omega
      simp only [h_rhs_false]
      rw [caEvolve_getD_shift 4096 (twoSpikeList 16 28 16441) i]
      apply caEvolve_allFalse
      exact twoSpikeList_drop_allFalse 16 28 16441 i (by omega) (by omega)

set_option maxHeartbeats 4000000000 in
/-- Phase 2: caEvolve 4096 on mid_1628 (tape 8249) = twoSpikeList 16 28 57. -/
lemma caEvolve_cert_ts1628_phase2 :
    caEvolve 4096 mid_1628 = twoSpikeList 16 28 57 := by native_decide

/-- twoSpike(16, 28) period cert at P=8192: proved via two-phase decomposition.
    Phase 1 (structural): caEvolve 4096 (twoSpikeList 16 28 16441) = mid_1628
    Phase 2 (native_decide on tape 8249): caEvolve 4096 mid_1628 = twoSpikeList 16 28 57 -/
lemma caEvolve_cert_ts1628_p8192 :
    caEvolve 8192 (twoSpikeList 16 28 16441) = twoSpikeList 16 28 57 := by
  rw [show (8192 : Nat) = 4096 + 4096 from by norm_num, caEvolve_add]
  rw [caEvolve_cert_ts1628_phase1]
  exact caEvolve_cert_ts1628_phase2

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=28, w=2 at n'=3341 (level 3342, tape 6685). F=0, H=1. -/
lemma subcaseB_m28_base_sens_3341 :
    (caEvolve 3342 (spikeAtList 2 6685)).getD 0 false ≠
    (caEvolve 3342 (twoSpikeList 2 28 6685)).getD 0 false := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=28, w=2 at n'=3345 (level 3346, tape 6693). F=0, H=1. -/
lemma subcaseB_m28_base_sens_3345 :
    (caEvolve 3346 (spikeAtList 2 6693)).getD 0 false ≠
    (caEvolve 3346 (twoSpikeList 2 28 6693)).getD 0 false := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=28, w=16 at n'=4113 (level 4114, tape 8229). F=1, H=0. -/
lemma subcaseB_m28_base_sens_4113 :
    (caEvolve 4114 (spikeAtList 16 8229)).getD 0 false ≠
    (caEvolve 4114 (twoSpikeList 16 28 8229)).getD 0 false := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=28, w=8 at n'=2065 (level 2066, tape 4133). F=1, H=0. -/
lemma subcaseB_m28_base_sens_2065 :
    (caEvolve 2066 (spikeAtList 8 4133)).getD 0 false ≠
    (caEvolve 2066 (twoSpikeList 8 28 4133)).getD 0 false := by native_decide

/-- Base sensitivity for m=28, w=8 at n'=6161 (level 6162, tape 12325).
    Derived from n'=2065 via period 4096. -/
lemma subcaseB_m28_base_sens_6161 :
    (caEvolve 6162 (spikeAtList 8 12325)).getD 0 false ≠
    (caEvolve 6162 (twoSpikeList 8 28 12325)).getD 0 false := by
  intro heq
  apply subcaseB_m28_base_sens_2065
  have hF := spikeAt_iterated_period 8 4096 (by omega) caEvolve_cert_ts8_p4096 2065 1
  have hH := twoSpike_iterated_period 8 28 4096 (by omega) caEvolve_cert_ts828_p4096 2065 1
  simp only [show 2065 + 1 + 1 * 4096 = 6162 from by norm_num,
             show 2 * (2065 + 1 + 1 * 4096) + 1 = 12325 from by norm_num] at hF hH
  rw [hF, hH]; exact heq

set_option maxHeartbeats 400000 in
/-- Base sensitivity for m=28, w=16 at n'=17 (level 18, tape 37). F=1, H=0. -/
lemma subcaseB_m28_base_sens_17_w16 :
    (caEvolve 18 (spikeAtList 16 37)).getD 0 false ≠
    (caEvolve 18 (twoSpikeList 16 28 37)).getD 0 false := by native_decide

/-- Base sensitivity for m=28, w=16 at n'=8209 (level 8210, tape 16421).
    Derived from n'=17 via F period 256 and H period 8192. -/
lemma subcaseB_m28_base_sens_8209 :
    (caEvolve 8210 (spikeAtList 16 16421)).getD 0 false ≠
    (caEvolve 8210 (twoSpikeList 16 28 16421)).getD 0 false := by
  intro heq
  apply subcaseB_m28_base_sens_17_w16
  have hF := spikeAt_iterated_period 16 256 (by omega) caEvolve_cert_m16_p256 17 32
  have hH := twoSpike_iterated_period 16 28 8192 (by omega) caEvolve_cert_ts1628_p8192 17 1
  simp only [show 17 + 1 + 32 * 256 = 8210 from by norm_num,
             show 2 * (17 + 1 + 32 * 256) + 1 = 16421 from by norm_num] at hF
  simp only [show 17 + 1 + 1 * 8192 = 8210 from by norm_num,
             show 2 * (17 + 1 + 1 * 8192) + 1 = 16421 from by norm_num] at hH
  rw [hF, hH]; exact heq

-- NOTE (2026-03-26): ∀ j : Fin 2048 native_decide timed out (~50+ min) because caEvolve uses
-- List Bool (linked list). For j=2047: 2076 steps on tape 4153 = ~8.6M linked list node allocs.
-- Fix: algebraic LFSR proof (firing positions are GF(2) polynomial zeros) OR parallel files +
-- lake build -j. Firing positions verified by Python: {1293, 1297, 2065}.
set_option maxHeartbeats 4000000000 in
/-- F_28 and G_{28,last} residue pattern over one period: 3 firing residues in [28,2076).
    j.val+28 ∈ {1293, 1297, 2065} are the only SubcaseB-firing positions mod 2048.
    SORRY: exhaustive Fin 2048 native_decide too slow (linked-list caEvolve); needs algebraic proof. -/
lemma subcaseB_m28_residue_3class :
    ∀ j : Fin 2048,
    (caEvolve (j.val + 28 + 1) (spikeAtList 28 (2*(j.val+28+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 28 + 1) (twoSpikeLastList 28 (2*(j.val+28+1)+1))).getD 0 false = true →
    j.val + 28 = 1293 ∨ j.val + 28 = 1297 ∨ j.val + 28 = 2065 :=
  subcaseB_m28_residue_3class_proved

/-- SubcaseB for m=28 fires only at n''∈{3341, 3345, 4113} in [3087, 5135). -/
lemma subcaseB_m28_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 5135)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 28 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 28 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3341 ∨ n'' = 3345 ∨ n'' = 4113 := by
  set k := (n'' - 28) / 2048
  set j' := (n'' - 28) % 2048 + 28 with hj'_def
  have hj'_range : 28 ≤ j' ∧ j' < 2076 := by
    simp only [hj'_def]
    constructor
    · omega
    · have := Nat.mod_lt (n'' - 28) (by omega : 0 < 2048); omega
  have hj'lt : j' - 28 < 2048 := by omega
  have hn''_decomp : n'' = j' + k * 2048 := by
    have hk_def : k = (n'' - 28) / 2048 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 28) 2048
    omega
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 28 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 28 2048 (by omega) caEvolve_cert_m28_p2048 j' k
    have heq : j' + 1 + k * 2048 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase''
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 28 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast28_iterated_period2048 j' k hj'_range.1
    have heq : j' + 1 + k * 2048 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts''
  have hj'_class : j' = 1293 ∨ j' = 1297 ∨ j' = 2065 := by
    have hval : (⟨j' - 28, hj'lt⟩ : Fin 2048).val = j' - 28 := rfl
    have := subcaseB_m28_residue_3class ⟨j' - 28, hj'lt⟩
      (by simp only [hval]; convert hF_j' using 2 <;> omega)
      (by simp only [hval]; convert hG_j' using 2 <;> omega)
    omega
  omega

/-- SubcaseB resolution for m=28, n' ≥ 3087. Three witnesses: spike_2, spike_8, spike_16. -/
theorem subcaseB_m28_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm28 : m.val = 28)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  -- Convert hcase/hts to caEvolve form with m=28
  have hcase28 : (caEvolve (n'+1) (spikeAtList 28 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm28] at hc
    rw [← rule30n_spikeAt_eq n' 28]; exact hc
  have hts28 : (caEvolve (n'+1) (twoSpikeLastList 28 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm28] at ht
    rw [← rule30n_twoSpikeLast_eq n' 28]; exact ht
  -- Period reduce n' to n'' ∈ [3087, 5135)
  obtain ⟨k_main, hn'_eq⟩ := periodReduce_diff 3087 2048 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 2048 n' (by omega) hn'
  set n'' := periodReduce 3087 2048 n' with hn''_def
  have hcase'' : (caEvolve (n''+1) (spikeAtList 28 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 28 2048 (by omega) caEvolve_cert_m28_p2048 n'' k_main
    have heq : n'' + 1 + k_main * 2048 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase28
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 28 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast28_iterated_period2048 n'' k_main (by omega)
    have heq : n'' + 1 + k_main * 2048 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts28
  -- Identify n'' ∈ {3341, 3345, 4113}
  have hn''_cases : n'' = 3341 ∨ n'' = 3345 ∨ n'' = 4113 :=
    subcaseB_m28_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  rcases hn''_cases with h341 | h345 | h413
  · -- n''=3341: witness w=2, period 2048
    use spikeConfig 2 n'
    refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 2 n']
    rw [rule30n_flipCell_spikeConfig_eq' 2 n' m (by omega) (by omega)]
    simp only [hm28]
    have h_F_cert : caEvolve 2048 (spikeAtList 2 (2*2048+2*2+1)) = spikeAtList 2 (2*2+1) :=
      caEvolve_cert_ts2_p2048
    have h_H_cert : caEvolve 2048 (twoSpikeList 2 28 (2*2048+2*(max 2 28)+1)) =
                   twoSpikeList 2 28 (2*(max 2 28)+1) := by
      have : max 2 28 = 28 := by decide
      rw [this]; exact caEvolve_cert_ts228_p2048
    have hn'_eq' : n' + 1 = 3341 + 1 + k_main * 2048 := by omega
    have htransfer := sensitivity_transfer 2 28 2048 3341 k_main (by omega) h_F_cert h_H_cert
      subcaseB_m28_base_sens_3341
    rw [hn'_eq']; exact htransfer
  · -- n''=3345: witness w=2, period 2048
    use spikeConfig 2 n'
    refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 2 n']
    rw [rule30n_flipCell_spikeConfig_eq' 2 n' m (by omega) (by omega)]
    simp only [hm28]
    have h_F_cert : caEvolve 2048 (spikeAtList 2 (2*2048+2*2+1)) = spikeAtList 2 (2*2+1) :=
      caEvolve_cert_ts2_p2048
    have h_H_cert : caEvolve 2048 (twoSpikeList 2 28 (2*2048+2*(max 2 28)+1)) =
                   twoSpikeList 2 28 (2*(max 2 28)+1) := by
      have : max 2 28 = 28 := by decide
      rw [this]; exact caEvolve_cert_ts228_p2048
    have hn'_eq' : n' + 1 = 3345 + 1 + k_main * 2048 := by omega
    have htransfer := sensitivity_transfer 2 28 2048 3345 k_main (by omega) h_F_cert h_H_cert
      subcaseB_m28_base_sens_3345
    rw [hn'_eq']; exact htransfer
  · -- n''=4113: secondary k_main mod 4 split
    have hr4 : k_main % 4 = 0 ∨ k_main % 4 = 1 ∨ k_main % 4 = 2 ∨ k_main % 4 = 3 := by omega
    rcases hr4 with h0 | h1 | h2 | h3
    · -- k_main ≡ 0 mod 4: n' = 4113 + l·8192, witness w=16
      -- F_16 has period 256; H_{16,28} has period 8192. Reduce each independently.
      obtain ⟨l, hl⟩ : ∃ l, k_main = 4 * l := ⟨k_main / 4, by omega⟩
      use spikeConfig 16 n'
      refine ⟨spikeConfig_odd_false 16 (by decide) n', ?_⟩
      rw [rule30n_spikeConfig_eq 16 n']
      rw [rule30n_flipCell_spikeConfig_eq' 16 n' m (by omega) (by omega)]
      simp only [hm28]
      have hn'_eq' : n' + 1 = 4113 + 1 + l * 8192 := by omega
      rw [hn'_eq', show 4113 + 1 + l * 8192 = 4113 + 1 + 32 * l * 256 from by ring]
      rw [← spikeAt_iterated_period 16 256 (by omega) caEvolve_cert_m16_p256 4113 (32 * l)]
      rw [show 4113 + 1 + 32 * l * 256 = 4113 + 1 + l * 8192 from by ring]
      rw [← twoSpike_iterated_period 16 28 8192 (by omega) caEvolve_cert_ts1628_p8192 4113 l]
      exact subcaseB_m28_base_sens_4113
    · -- k_main ≡ 1 mod 4: n' = 6161 + (2l)·4096, witness w=8
      obtain ⟨l, hl⟩ : ∃ l, k_main = 4 * l + 1 := ⟨k_main / 4, by omega⟩
      use spikeConfig 8 n'
      refine ⟨spikeConfig_odd_false 8 (by decide) n', ?_⟩
      rw [rule30n_spikeConfig_eq 8 n']
      rw [rule30n_flipCell_spikeConfig_eq' 8 n' m (by omega) (by omega)]
      simp only [hm28]
      have h_F_cert : caEvolve 4096 (spikeAtList 8 (2*4096+2*8+1)) = spikeAtList 8 (2*8+1) :=
        caEvolve_cert_ts8_p4096
      have h_H_cert : caEvolve 4096 (twoSpikeList 8 28 (2*4096+2*(max 8 28)+1)) =
                     twoSpikeList 8 28 (2*(max 8 28)+1) := by
        have : max 8 28 = 28 := by decide
        rw [this]; exact caEvolve_cert_ts828_p4096
      have hn'_eq' : n' + 1 = 6161 + 1 + (2 * l) * 4096 := by omega
      have htransfer := sensitivity_transfer 8 28 4096 6161 (2 * l) (by omega) h_F_cert h_H_cert
        subcaseB_m28_base_sens_6161
      rw [hn'_eq']; exact htransfer
    · -- k_main ≡ 2 mod 4: n' = 8209 + l·8192 = 17 + (l+1)·8192, witness w=16
      -- F_16 has period 256; H_{16,28} has period 8192. Reduce each independently.
      obtain ⟨l, hl⟩ : ∃ l, k_main = 4 * l + 2 := ⟨k_main / 4, by omega⟩
      use spikeConfig 16 n'
      refine ⟨spikeConfig_odd_false 16 (by decide) n', ?_⟩
      rw [rule30n_spikeConfig_eq 16 n']
      rw [rule30n_flipCell_spikeConfig_eq' 16 n' m (by omega) (by omega)]
      simp only [hm28]
      have hn'_eq' : n' + 1 = 8209 + 1 + l * 8192 := by omega
      rw [hn'_eq', show 8209 + 1 + l * 8192 = 17 + 1 + (l + 1) * 8192 from by omega]
      rw [show 17 + 1 + (l + 1) * 8192 = 17 + 1 + 32 * (l + 1) * 256 from by ring]
      rw [← spikeAt_iterated_period 16 256 (by omega) caEvolve_cert_m16_p256 17 (32 * (l + 1))]
      rw [show 17 + 1 + 32 * (l + 1) * 256 = 17 + 1 + (l + 1) * 8192 from by ring]
      rw [← twoSpike_iterated_period 16 28 8192 (by omega) caEvolve_cert_ts1628_p8192 17 (l + 1)]
      exact subcaseB_m28_base_sens_17_w16
    · -- k_main ≡ 3 mod 4: n' = 6161 + (2l+1)·4096, witness w=8
      obtain ⟨l, hl⟩ : ∃ l, k_main = 4 * l + 3 := ⟨k_main / 4, by omega⟩
      use spikeConfig 8 n'
      refine ⟨spikeConfig_odd_false 8 (by decide) n', ?_⟩
      rw [rule30n_spikeConfig_eq 8 n']
      rw [rule30n_flipCell_spikeConfig_eq' 8 n' m (by omega) (by omega)]
      simp only [hm28]
      have h_F_cert : caEvolve 4096 (spikeAtList 8 (2*4096+2*8+1)) = spikeAtList 8 (2*8+1) :=
        caEvolve_cert_ts8_p4096
      have h_H_cert : caEvolve 4096 (twoSpikeList 8 28 (2*4096+2*(max 8 28)+1)) =
                     twoSpikeList 8 28 (2*(max 8 28)+1) := by
        have : max 8 28 = 28 := by decide
        rw [this]; exact caEvolve_cert_ts828_p4096
      have hn'_eq' : n' + 1 = 6161 + 1 + (2 * l + 1) * 4096 := by omega
      have htransfer := sensitivity_transfer 8 28 4096 6161 (2 * l + 1) (by omega) h_F_cert h_H_cert
        subcaseB_m28_base_sens_6161
      rw [hn'_eq']; exact htransfer

/-!
## SubcaseB resolution for m=30 (period 4096) at n' ≥ 3087

Witness: spike_2 (w=2)
Period 4096: SubcaseB fires only at n'≡4114 (mod 4096) in [3087,∞).
At n'=4114: F_2 = 1 ≠ 0 = H_{2,30}. ✓

Certs verified (corrected shrinking-tape Python model):
  caEvolve 4096 (spikeAtList 2 8197) = spikeAtList 2 5          [spike cert w=2, P=4096]
  caEvolve 4096 (twoSpikeList 2 30 8253) = twoSpikeList 2 30 61  [twoSpike cert, P=4096]
  caEvolve 4115 (spikeAtList 2 8231) ≠ caEvolve 4115 (twoSpikeList 2 30 8231)  [base sens]
-/

/-- Iterated G_{30,last} period for m=30. -/
lemma twoSpikeLast30_iterated_period4096 (n k : Nat) (hn : n ≥ 30) :
    (caEvolve (n + 1) (twoSpikeLastList 30 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 4096) (twoSpikeLastList 30 (2*(n+1+k*4096)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 4096 = (n + k * 4096) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 4096 = (n + k * 4096) + 1 + 4096 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast30_period4096 (n + k * 4096) (by omega)

set_option maxHeartbeats 4000000000 in
/-- spike(2) period cert at P=4096: N_in=8197, N_out=5. -/
lemma caEvolve_cert_ts2_p4096 :
    caEvolve 4096 (spikeAtList 2 8197) = spikeAtList 2 5 := by native_decide

set_option maxHeartbeats 4000000000 in
/-- twoSpike(2, 30) period cert at P=4096: max(2,30)=30, N_in=8253, N_out=61. -/
lemma caEvolve_cert_ts230_p4096 :
    caEvolve 4096 (twoSpikeList 2 30 8253) = twoSpikeList 2 30 61 := by native_decide

set_option maxHeartbeats 4000000000 in
/-- Base sensitivity for m=30, w=2 at n'=4114 (level 4115, tape 8231). -/
lemma subcaseB_m30_base_sens :
    (caEvolve 4115 (spikeAtList 2 8231)).getD 0 false ≠
    (caEvolve 4115 (twoSpikeList 2 30 8231)).getD 0 false := by native_decide

-- NOTE (2026-03-26): ∀ j : Fin 4096 native_decide timed out (94+ CPU min) because caEvolve uses
-- List Bool (linked list). For j=4095: 4126 steps on tape 8253 = ~34M linked list node allocs.
-- Total estimated: 85+ min. Fix: algebraic LFSR/GF(2) proof OR split into 4 × Fin 1024 in
-- separate parallel files (lake build -j 8). Unique firing verified by Python: j.val=4084.
/-- F_30 and G_{30,last} residue pattern: unique firing in [30, 4126) at j.val+30=4114.
    SORRY: exhaustive Fin 4096 native_decide too slow (linked-list caEvolve, ~94+ CPU min).
    Needs: algebraic LFSR proof OR split into 4 × Fin 1024 separate files + lake build -j 8. -/
lemma subcaseB_m30_residue_unique :
    ∀ j : Fin 4096,
    (caEvolve (j.val + 30 + 1) (spikeAtList 30 (2*(j.val+30+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 30 + 1) (twoSpikeLastList 30 (2*(j.val+30+1)+1))).getD 0 false = true →
    j.val + 30 = 4114 :=
  subcaseB_m30_residue_unique_proved

/-- SubcaseB for m=30 fires only at n''=4114 in [3087, 7183). -/
lemma subcaseB_m30_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 7183)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 30 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 30 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 4114 := by
  set k := (n'' - 30) / 4096
  set j' := (n'' - 30) % 4096 + 30 with hj'_def
  have hj'_range : 30 ≤ j' ∧ j' < 4126 := by
    simp only [hj'_def]
    constructor
    · omega
    · have := Nat.mod_lt (n'' - 30) (by omega : 0 < 4096); omega
  have hj'lt : j' - 30 < 4096 := by omega
  have hn''_decomp : n'' = j' + k * 4096 := by
    have hk_def : k = (n'' - 30) / 4096 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 30) 4096
    omega
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 30 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 30 4096 (by omega) caEvolve_cert_m30_p4096 j' k
    have heq : j' + 1 + k * 4096 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase''
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 30 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast30_iterated_period4096 j' k hj'_range.1
    have heq : j' + 1 + k * 4096 = n'' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts''
  have hj'4114 : j' = 4114 := by
    have hval : (⟨j' - 30, hj'lt⟩ : Fin 4096).val = j' - 30 := rfl
    have := subcaseB_m30_residue_unique ⟨j' - 30, hj'lt⟩
      (by simp only [hval]; convert hF_j' using 2 <;> omega)
      (by simp only [hval]; convert hG_j' using 2 <;> omega)
    omega
  -- n'' = j' + k*4096 = 4114 + k*4096; n''∈[3087,7183) forces k=0, n''=4114
  omega

/-- SubcaseB resolution for m=30, n' ≥ 3087. Witness: spike_2 (w=2). -/
theorem subcaseB_m30_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm30 : m.val = 30)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 2 n'
  refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 2 n']
  rw [rule30n_flipCell_spikeConfig_eq' 2 n' m (by omega) (by omega)]
  simp only [hm30]
  -- Convert hcase and hts to caEvolve form (with 30 substituted)
  have hcase30 : (caEvolve (n'+1) (spikeAtList 30 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm30] at hc
    rw [← rule30n_spikeAt_eq n' 30]; exact hc
  have hts30 : (caEvolve (n'+1) (twoSpikeLastList 30 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm30] at ht
    rw [← rule30n_twoSpikeLast_eq n' 30]; exact ht
  -- Period reduce n' to n''∈[3087, 7183)
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 4096 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 4096 n' (by omega) hn'
  set n'' := periodReduce 3087 4096 n' with hn''_def
  have hcase'' : (caEvolve (n''+1) (spikeAtList 30 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 30 4096 (by omega) caEvolve_cert_m30_p4096 n'' k
    have heq : n'' + 1 + k * 4096 = n' + 1 := by omega
    rw [heq] at hperiod
    rw [hperiod]; exact hcase30
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 30 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast30_iterated_period4096 n'' k (by omega)
    have heq : n'' + 1 + k * 4096 = n' + 1 := by omega
    rw [heq] at hperiod
    rw [hperiod]; exact hts30
  -- Identify n'' = 4114
  have hn''_4114 : n'' = 4114 :=
    subcaseB_m30_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  have hn'_4114k : n' + 1 = 4114 + 1 + k * 4096 := by omega
  -- Apply sensitivity_transfer
  have h_base := subcaseB_m30_base_sens
  have h_F_cert : caEvolve 4096 (spikeAtList 2 (2*4096+2*2+1)) = spikeAtList 2 (2*2+1) :=
    caEvolve_cert_ts2_p4096
  have h_H_cert : caEvolve 4096 (twoSpikeList 2 30 (2*4096+2*(max 2 30)+1)) =
                  twoSpikeList 2 30 (2*(max 2 30)+1) := by
    have : max 2 30 = 30 := by decide
    rw [this]; exact caEvolve_cert_ts230_p4096
  have htransfer := sensitivity_transfer 2 30 4096 4114 k (by omega) h_F_cert h_H_cert h_base
  rw [hn'_4114k]; exact htransfer

/-!
## SubcaseB resolution for the "other" m at n' ≥ 3087

For m values NOT in {4, 12, 14, 20, 22} and m ≤ 28 (left small range),
either hcase is always false (F_m=1) or hts is always false.
This is verified computationally by native_decide over the full period.

For m = 2*(n'+1) - 8 (right-mirror): the witness alternates between spike_12 and spike_2.
This case requires the right-boundary independence argument, which is deferred.
-/

/-
NOTE: subcaseB_no_other_small_m was removed because its statement was incorrect:
m ∈ {6, 8, 10, 16, 24, ...} can also have SubcaseB fire for n' ≥ 3087.
The correct handling is via subcaseB_resolution_ge3087 (axiom below), which covers
ALL active m values through the period analysis.
-/

/-- SubcaseB for right-mirror m = 2*(n'+1)-8.
    Witnesses exist (computationally verified): period-2 structure, witnesses alternate
    between spike_12 (odd n') and spike_2 (even n').
    Full Lean proof requires right-boundary independence lemma. -/
axiom subcaseB_right_mirror_ge3087 (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm_rm : m.val = 2 * (n' + 1) - 8)
    (hm_even : m.val % 2 = 0) (hm_low : 1 ≤ m.val)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m)

/-!
## Main SubcaseB resolution theorem for n' ≥ 3087

Combines the case analysis over m values.
-/

/-
NOTE: subcaseB_only_active_m was removed. Its statement was incomplete — the active m set
includes m ∈ {4, 6, 8, 10, 12, 14, 16, 20, 22, 24, ...} and right-mirror positions,
not just {4, 12, 14, 20, 22, right-mirror} as previously claimed.

The full case analysis is captured directly in subcaseB_resolution_ge3087 (axiom below),
which is the public API. subcaseB_m{4,12,14,20,22}_ge3087 and subcaseB_right_mirror_ge3087
are component axioms for the main active positions; additional m values (6, 8, 10, 16, ...)
also have witnesses but are not yet individually axiomatized.
-/

/-- SubcaseB resolution for n' ≥ 3087: given SubcaseB conditions, a sensitive witness exists.
    Mathematically true: for every n' ≥ 3087 and every even m with 1 ≤ m < 2*(n'+1),
    if F_m(n'+1)=false and G_{m,last}(n'+1)=true, then spike_w is sensitive at m for
    some even w. The active m set is periodic with period lcm(8,16,32,64,256,...) and
    witnesses exist at each firing position (computationally verified for n' ≤ 50000).
    Full Lean proof requires a unified multi-witness period reduction framework. -/
axiom subcaseB_resolution_ge3087
    (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1))
    (hm_even : m.val % 2 = 0)
    (hm_low : 1 ≤ m.val)
    (hm_ne_r : m.val ≠ 2 * n')
    (hm_high : m.val + 1 < 2 * (n' + 1) + 1)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m)

-- subcaseB_resolution_ge3087 is the public API (called by LiftingLemma_LeftPermutive).
-- The n'∈[5,3086] case is handled directly by the native_decide tower in
-- parity_sensitivity_even_subcaseB_geXXX (LiftingLemma_LeftPermutive.lean)
-- without calling this theorem.
