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
import P2p.CA_Array_m4
import P2p.CA_Array_m34
-- CA_Array_m34_residues: Fin 8192 native_decide deferred (infeasible compile time)
import P2p.CA_Array_m36
-- CA_Array_m36_residues: Fin 16384 native_decide deferred (infeasible compile time)
import P2p.CA_Array_m38
-- CA_Array_m38_residues: Fin 32768 native_decide deferred (infeasible compile time)
import P2p.SubcaseB_BaseSens
import P2p.SubcaseB_m4_RightEdge
import P2p.SubcaseB_m22_RightEdge
import P2p.SubcaseB_Firewall
import Mathlib.Tactic.Ring
import P2p.CA_Array_m32_residues
import P2p.CA_Array_m34_residues
import P2p.CA_Array_m36_residues
import P2p.CA_Array_m38_residues

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
## Period certs for m=4 proof witnesses (subcaseB_m4_ge3087_proved)

Argument order: twoSpikeList w 4 (witness w first, m_val=4 second) matching sensitivity_transfer.
Reuse via twoSpikeList_comm: ts46_p16 and ts412_p128 exist with reversed order.
New certs needed: ts104, ts164, sp18, ts184, sp22_p1024, ts224.
-/

-- spike(12) at P=128: input=2*128+2*12+1=281, output=2*12+1=25
-- (distinct from caEvolve_cert_m12_p64 which uses tape 153 for P=64)
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_sp12_p128 :
    caEvolve 128 (spikeAtList 12 281) = spikeAtList 12 25 := by native_decide

-- twoSpikeList(10,4) at P=64: max=10, input=2*64+2*10+1=149, output=2*10+1=21
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts104_p64 :
    caEvolve 64 (twoSpikeList 10 4 149) = twoSpikeList 10 4 21 := by native_decide

-- twoSpikeList(16,4) at P=512: max=16, input=2*512+2*16+1=1057, output=2*16+1=33
-- (spike(16) P=512 cert already in CausalConeLemmas as caEvolve_cert_sp16_p512)
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts164_p512 :
    caEvolve 512 (twoSpikeList 16 4 1057) = twoSpikeList 16 4 33 := by native_decide

-- spike(18) at P=256: input=2*256+2*18+1=549, output=2*18+1=37 (no spike_18 in CausalConeLemmas)
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_sp18_p256 :
    caEvolve 256 (spikeAtList 18 549) = spikeAtList 18 37 := by native_decide

-- twoSpikeList(18,4) at P=256: max=18, input=549, output=37
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts184_p256 :
    caEvolve 256 (twoSpikeList 18 4 549) = twoSpikeList 18 4 37 := by native_decide

-- spike(22) at P=1024: input=2*1024+2*22+1=2093, output=2*22+1=45
-- (caEvolve_cert_m22_p256 uses tape 557 for P=256; need P=1024 for m=4 witness)
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_sp22_p1024 :
    caEvolve 1024 (spikeAtList 22 2093) = spikeAtList 22 45 := by native_decide

-- twoSpikeList(22,4) at P=1024: max=22, input=2093, output=45
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_ts224_p1024 :
    caEvolve 1024 (twoSpikeList 22 4 2093) = twoSpikeList 22 4 45 := by native_decide

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

/-- Sensitivity transfer with different periods for spike and twoSpike.
    When PF divides PH (spike period divides twoSpike period),
    we use PH as the common stride: spike side uses k*r steps of PF,
    twoSpike side uses k steps of PH, where PH = r * PF. -/
lemma sensitivity_transfer_div (w m_val PF PH n'' k r : Nat)
    (hPF : 0 < PF) (hPH : 0 < PH)
    (hrP : PH = r * PF)
    (hF_cert : caEvolve PF (spikeAtList w (2*PF+2*w+1)) = spikeAtList w (2*w+1))
    (hH_cert : caEvolve PH (twoSpikeList w m_val (2*PH+2*(max w m_val)+1)) =
               twoSpikeList w m_val (2*(max w m_val)+1))
    (h_sens : (caEvolve (n''+1) (spikeAtList w (2*(n''+1)+1))).getD 0 false ≠
              (caEvolve (n''+1) (twoSpikeList w m_val (2*(n''+1)+1))).getD 0 false) :
    (caEvolve (n''+1+k*PH) (spikeAtList w (2*(n''+1+k*PH)+1))).getD 0 false ≠
    (caEvolve (n''+1+k*PH) (twoSpikeList w m_val (2*(n''+1+k*PH)+1))).getD 0 false := by
  -- Spike side: k*PH = (k*r)*PF, use spikeAt_iterated_period with k*r steps
  have hkP : k * PH = k * r * PF := by rw [hrP]; ring
  rw [show n'' + 1 + k * PH = n'' + 1 + (k * r) * PF from by omega]
  rw [← spikeAt_iterated_period w PF hPF hF_cert n'' (k * r)]
  -- twoSpike side: use twoSpike_iterated_period with k steps of PH
  rw [show n'' + 1 + k * r * PF = n'' + 1 + k * PH from by omega]
  rw [← twoSpike_iterated_period w m_val PH hPH hH_cert n'' k]
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

/-!
## Partial infrastructure for m=4 (period-8 reduction, partial proof)

SubcaseB fires at n'≡5 mod 8 (all residues mod 64 = {5,13,21,29,37,45,53,61}).
In [3087, 3095), the unique firing is n''=3093.

Witness analysis (verified computationally at n'∈[3085,3597)):
- ≡13 mod 64: w=6 (period 16) — base cert exists at n'=3085
- ≡21 mod 64: w=16 (need period ~512 cert) — w=6 FAILS here
- ≡29,45,61 mod 64: w=6 (period 16) — period-stable
- ≡37 mod 64: w=12 (period 128), but n'≡357 mod 512 has w≥32
- ≡53 mod 64: w=10 (period 64)
- ≡5 mod 64: w varies, n'≡5 mod 512 has w≥22

Full proof requires ≥64 base cases (one per firing in [3085, 3597)).
Deferred to subcaseB_m4_ge3087 axiom below.
-/

/-- SubcaseB for m=4 fires only at n''=3093 in [3087, 3095). -/
lemma subcaseB_m4_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 3095)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 4 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 4 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 3093 := by
  -- Reformulate with Nat membership to avoid Fin type coercion and maxRecDepth issues
  have h : ∀ n : Nat, n ∈ ([3087,3088,3089,3090,3091,3092,3093,3094] : List Nat) →
      (caEvolve (n+1) (spikeAtList 4 (2*(n+1)+1))).getD 0 false = false →
      (caEvolve (n+1) (twoSpikeLastList 4 (2*(n+1)+1))).getD 0 false = true →
      n = 3093 := by
    set_option maxRecDepth 4096 in native_decide
  have hn''_mem : n'' ∈ ([3087,3088,3089,3090,3091,3092,3093,3094] : List Nat) := by
    simp [List.mem_cons]; omega
  exact h n'' hn''_mem hcase'' hts''

-- Base sensitivity cert for m=4, w=6 at n'=3101 (≡29 mod 64): verified correct
-- NOTE: uses twoSpikeList 4 6 (m_val first); use twoSpikeList_comm to convert for sensitivity_transfer
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3101 :
    (caEvolve 3102 (spikeAtList 6 6205)).getD 0 false ≠
    (caEvolve 3102 (twoSpikeList 4 6 6205)).getD 0 false := by native_decide

/-!
## Base sensitivity certs for subcaseB_m4_ge3087_proved

14 firing positions in [3093, 3589], each with its witness w.
All use twoSpikeList w 4 (w first, m_val=4 second) for direct use with sensitivity_transfer.
Tape size = 2*(n'+1)+1.
-/

-- n'=3093, w=16 (j=0, covers j=0,64,128,... via P=512)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3093 :
    (caEvolve 3094 (spikeAtList 16 6189)).getD 0 false ≠
    (caEvolve 3094 (twoSpikeList 16 4 6189)).getD 0 false := by native_decide

-- n'=3109, w=12 (j=2, covers j=2,18,34,50 via P=128)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3109 :
    (caEvolve 3110 (spikeAtList 12 6221)).getD 0 false ≠
    (caEvolve 3110 (twoSpikeList 12 4 6221)).getD 0 false := by native_decide

-- n'=3125, w=10 (j=4, covers j=4,12,20,28,36,44,52,60 via P=64)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3125 :
    (caEvolve 3126 (spikeAtList 10 6253)).getD 0 false ≠
    (caEvolve 3126 (twoSpikeList 10 4 6253)).getD 0 false := by native_decide

-- n'=3141, w=12 (j=6, covers j=6,22,38,54 via P=128)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3141 :
    (caEvolve 3142 (spikeAtList 12 6285)).getD 0 false ≠
    (caEvolve 3142 (twoSpikeList 12 4 6285)).getD 0 false := by native_decide

-- n'=3157, w=12 (j=8, covers j=8,24,40,56 via P=128)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3157 :
    (caEvolve 3158 (spikeAtList 12 6317)).getD 0 false ≠
    (caEvolve 3158 (twoSpikeList 12 4 6317)).getD 0 false := by native_decide

-- n'=3173, w=16 (j=10, covers j=10,74,... via P=512)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3173 :
    (caEvolve 3174 (spikeAtList 16 6349)).getD 0 false ≠
    (caEvolve 3174 (twoSpikeList 16 4 6349)).getD 0 false := by native_decide

-- n'=3205, w=18 (j=14, covers j=14,46 via P=256)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3205 :
    (caEvolve 3206 (spikeAtList 18 6413)).getD 0 false ≠
    (caEvolve 3206 (twoSpikeList 18 4 6413)).getD 0 false := by native_decide

-- n'=3221, w=18 (j=16, covers j=16,48 via P=256)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3221 :
    (caEvolve 3222 (spikeAtList 18 6445)).getD 0 false ≠
    (caEvolve 3222 (twoSpikeList 18 4 6445)).getD 0 false := by native_decide

-- n'=3301, w=18 (j=26, covers j=26,58 via P=256)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3301 :
    (caEvolve 3302 (spikeAtList 18 6605)).getD 0 false ≠
    (caEvolve 3302 (twoSpikeList 18 4 6605)).getD 0 false := by native_decide

-- n'=3333, w=16 (j=30, covers j=30,94,... via P=512)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3333 :
    (caEvolve 3334 (spikeAtList 16 6669)).getD 0 false ≠
    (caEvolve 3334 (twoSpikeList 16 4 6669)).getD 0 false := by native_decide

-- n'=3349, w=18 (j=32, covers j=32,64,... via P=256)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3349 :
    (caEvolve 3350 (spikeAtList 18 6701)).getD 0 false ≠
    (caEvolve 3350 (twoSpikeList 18 4 6701)).getD 0 false := by native_decide

-- n'=3589, w=22 (j=62, covers j=62,190,... via P=1024)
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3589 :
    (caEvolve 3590 (spikeAtList 22 7181)).getD 0 false ≠
    (caEvolve 3590 (twoSpikeList 22 4 7181)).getD 0 false := by native_decide

-- n'=3429, w=32 (j=42, mod64=37 anomaly): provided by CA_Array_m4.lean Section 12
-- CA_Array_m4.subcaseB_m4_base_sens_3429_w32 covers this case.

-- n'=3117, w=6 (j=3, mod64=45): covers j=3,19,35,51 via P=16
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3117 :
    (caEvolve 3118 (spikeAtList 6 6237)).getD 0 false ≠
    (caEvolve 3118 (twoSpikeList 6 4 6237)).getD 0 false := by native_decide

-- n'=3133, w=6 (j=5, mod64=61): covers j=5,21,37,53 via P=16
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3133 :
    (caEvolve 3134 (spikeAtList 6 6269)).getD 0 false ≠
    (caEvolve 3134 (twoSpikeList 6 4 6269)).getD 0 false := by native_decide

-- n'=3149, w=6 (j=7, mod64=13): covers j=7,23,39,55 via P=16
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m4_base_sens_3149 :
    (caEvolve 3150 (spikeAtList 6 6301)).getD 0 false ≠
    (caEvolve 3150 (twoSpikeList 6 4 6301)).getD 0 false := by native_decide

/-- SubcaseB sensitivity for m=4, n'≡13 mod 16, n'≥3087.
    Witness: w=6, Period: 16.
    Covers mod64 classes {13,29,45,61}: these are exactly n'≡13 mod 16.
    First firing: n'=3101 (j=1, 3101%64=29). Period-16 witness valid by:
      spike(6) period = 16 (caEvolve_cert_m6_p16)
      twoSpike(6,4) period = 16 (via twoSpike(4,6)_p16 + twoSpikeList_comm)
      base sensitivity at n''=3101 (subcaseB_m4_base_sens_3101). -/
theorem subcaseB_m4_mod16_13_witness (n' : Nat) (hn' : 3087 ≤ n') (hmod : n' % 16 = 13)
    (m : Fin (2 * (n' + 1) + 1)) (hm4 : m.val = 4) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 6 n'
  refine ⟨spikeConfig_odd_false 6 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 6 n', rule30n_flipCell_spikeConfig_eq' 6 n' m (by omega) (by omega)]
  simp only [hm4]
  have h_F_cert : caEvolve 16 (spikeAtList 6 (2*16+2*6+1)) = spikeAtList 6 (2*6+1) :=
    caEvolve_cert_m6_p16
  have h_H_cert : caEvolve 16 (twoSpikeList 6 4 (2*16+2*(max 6 4)+1)) =
                  twoSpikeList 6 4 (2*(max 6 4)+1) := by
    have hmax : max 6 4 = 6 := by decide
    rw [hmax, twoSpikeList_comm 6 4, twoSpikeList_comm 6 4]
    exact caEvolve_cert_ts46_p16
  have h_base : (caEvolve 3102 (spikeAtList 6 6205)).getD 0 false ≠
                (caEvolve 3102 (twoSpikeList 6 4 6205)).getD 0 false := by
    rw [twoSpikeList_comm 6 4]; exact subcaseB_m4_base_sens_3101
  obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3101 + k * 16 := ⟨(n' - 3101) / 16, by omega⟩
  rw [show n' + 1 = 3101 + 1 + k * 16 from by omega]
  exact sensitivity_transfer 6 4 16 3101 k (by omega) h_F_cert h_H_cert h_base

/-- SubcaseB sensitivity for m=4, n'≡53 mod 64, n'≥3087.
    Witness: w=10, Period: 64.
    Covers mod64=53 (all n'≡53 mod 64 ≥ 3087).
    First firing: n'=3125 (3125 mod 64 = 53).
    Period-64 certs: caEvolve_cert_m10_p64, caEvolve_cert_ts104_p64.
    Base sensitivity: subcaseB_m4_base_sens_3125. -/
theorem subcaseB_m4_mod64_53_witness (n' : Nat) (hn' : 3087 ≤ n') (hmod : n' % 64 = 53)
    (m : Fin (2 * (n' + 1) + 1)) (hm4 : m.val = 4) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 10 n'
  refine ⟨spikeConfig_odd_false 10 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 10 n', rule30n_flipCell_spikeConfig_eq' 10 n' m (by omega) (by omega)]
  simp only [hm4]
  have h_F_cert : caEvolve 64 (spikeAtList 10 (2*64+2*10+1)) = spikeAtList 10 (2*10+1) :=
    caEvolve_cert_m10_p64
  have h_H_cert : caEvolve 64 (twoSpikeList 10 4 (2*64+2*(max 10 4)+1)) =
                  twoSpikeList 10 4 (2*(max 10 4)+1) := by
    have hmax : max 10 4 = 10 := by decide
    rw [hmax]; exact caEvolve_cert_ts104_p64
  have h_base : (caEvolve 3126 (spikeAtList 10 6253)).getD 0 false ≠
                (caEvolve 3126 (twoSpikeList 10 4 6253)).getD 0 false :=
    subcaseB_m4_base_sens_3125
  obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3125 + k * 64 := ⟨(n' - 3125) / 64, by omega⟩
  rw [show n' + 1 = 3125 + 1 + k * 64 from by omega]
  exact sensitivity_transfer 10 4 64 3125 k (by omega) h_F_cert h_H_cert h_base

/-- SubcaseB sensitivity for m=4, n'≡21 mod 64, n'≥3087.
    Witness: period-8 pattern in k (where n'=3093+64*k):
      k%8=0 (n'%512=21): w=16, P=512
      k%8=1,3,5,7 (n'%128=85): w=12, P=128
      k%8=2,6 (n'%256=149): w=18, P=256
      k%8=4 (n'%512=277): w=18, P=256
    All 4 period sub-cases covered by existing native_decide certs. -/
theorem subcaseB_m4_mod64_21_witness (n' : Nat) (hn' : 3087 ≤ n') (hmod : n' % 64 = 21)
    (m : Fin (2 * (n' + 1) + 1)) (hm4 : m.val = 4) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  by_cases h128 : n' % 128 = 85
  · -- k odd: n'≡85 mod 128, covers {85,213,341,469} mod 512, w=12, P=128, base=3157
    use spikeConfig 12 n'
    refine ⟨spikeConfig_odd_false 12 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 12 n', rule30n_flipCell_spikeConfig_eq' 12 n' m (by omega) (by omega)]
    simp only [hm4]
    have h_F : caEvolve 128 (spikeAtList 12 (2*128+2*12+1)) = spikeAtList 12 (2*12+1) :=
      caEvolve_cert_sp12_p128
    have h_H : caEvolve 128 (twoSpikeList 12 4 (2*128+2*(max 12 4)+1)) =
               twoSpikeList 12 4 (2*(max 12 4)+1) := by
      have hmax : max 12 4 = 12 := by decide
      rw [hmax, twoSpikeList_comm 12 4, twoSpikeList_comm 12 4]
      exact caEvolve_cert_ts412_p128
    obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3157 + k * 128 := ⟨(n' - 3157) / 128, by omega⟩
    rw [show n' + 1 = 3157 + 1 + k * 128 from by omega]
    exact sensitivity_transfer 12 4 128 3157 k (by omega) h_F h_H subcaseB_m4_base_sens_3157
  · -- n' % 128 = 21 (follows from hmod and h128)
    have hn'128 : n' % 128 = 21 := by omega
    by_cases h256 : n' % 256 = 149
    · -- k≡2 mod 4: n'≡149 mod 256, covers {149,405} mod 512, w=18, P=256, base=3221
      use spikeConfig 18 n'
      refine ⟨spikeConfig_odd_false 18 (by decide) n', ?_⟩
      rw [rule30n_spikeConfig_eq 18 n', rule30n_flipCell_spikeConfig_eq' 18 n' m (by omega) (by omega)]
      simp only [hm4]
      have h_F : caEvolve 256 (spikeAtList 18 (2*256+2*18+1)) = spikeAtList 18 (2*18+1) :=
        caEvolve_cert_sp18_p256
      have h_H : caEvolve 256 (twoSpikeList 18 4 (2*256+2*(max 18 4)+1)) =
                 twoSpikeList 18 4 (2*(max 18 4)+1) := by
        have hmax : max 18 4 = 18 := by decide
        rw [hmax]; exact caEvolve_cert_ts184_p256
      obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3221 + k * 256 := ⟨(n' - 3221) / 256, by omega⟩
      rw [show n' + 1 = 3221 + 1 + k * 256 from by omega]
      exact sensitivity_transfer 18 4 256 3221 k (by omega) h_F h_H subcaseB_m4_base_sens_3221
    · -- n' % 256 = 21 (follows from hn'128 and h256)
      have hn'256 : n' % 256 = 21 := by omega
      by_cases h512 : n' % 512 = 277
      · -- k≡4 mod 8: n'≡277 mod 512, w=18, P=256, base=3349
        use spikeConfig 18 n'
        refine ⟨spikeConfig_odd_false 18 (by decide) n', ?_⟩
        rw [rule30n_spikeConfig_eq 18 n', rule30n_flipCell_spikeConfig_eq' 18 n' m (by omega) (by omega)]
        simp only [hm4]
        have h_F : caEvolve 256 (spikeAtList 18 (2*256+2*18+1)) = spikeAtList 18 (2*18+1) :=
          caEvolve_cert_sp18_p256
        have h_H : caEvolve 256 (twoSpikeList 18 4 (2*256+2*(max 18 4)+1)) =
                   twoSpikeList 18 4 (2*(max 18 4)+1) := by
          have hmax : max 18 4 = 18 := by decide
          rw [hmax]; exact caEvolve_cert_ts184_p256
        obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3349 + k * 256 := ⟨(n' - 3349) / 256, by omega⟩
        rw [show n' + 1 = 3349 + 1 + k * 256 from by omega]
        exact sensitivity_transfer 18 4 256 3349 k (by omega) h_F h_H subcaseB_m4_base_sens_3349
      · -- n' % 512 = 21: k≡0 mod 8, w=16, P=512, base=3093
        have hn'512 : n' % 512 = 21 := by omega
        use spikeConfig 16 n'
        refine ⟨spikeConfig_odd_false 16 (by decide) n', ?_⟩
        rw [rule30n_spikeConfig_eq 16 n', rule30n_flipCell_spikeConfig_eq' 16 n' m (by omega) (by omega)]
        simp only [hm4]
        have h_F : caEvolve 512 (spikeAtList 16 (2*512+2*16+1)) = spikeAtList 16 (2*16+1) :=
          caEvolve_cert_sp16_p512
        have h_H : caEvolve 512 (twoSpikeList 16 4 (2*512+2*(max 16 4)+1)) =
                   twoSpikeList 16 4 (2*(max 16 4)+1) := by
          have hmax : max 16 4 = 16 := by decide
          rw [hmax]; exact caEvolve_cert_ts164_p512
        obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3093 + k * 512 := ⟨(n' - 3093) / 512, by omega⟩
        rw [show n' + 1 = 3093 + 1 + k * 512 from by omega]
        exact sensitivity_transfer 16 4 512 3093 k (by omega) h_F h_H subcaseB_m4_base_sens_3093

/-- SubcaseB sensitivity for m=4, n'≡37 mod 64, n'≥3087.
    Witness: period-8 pattern in k (where n'=3109+64*k):
      k%8=0,2,4,6 (n'%128=37): w=12, P=128, base=3109
      k%8=3,7 (n'%256=229): w=18, P=256, base=3301
      k%8=1 (n'%512=101): w=16, P=512, base=3173
      k%8=5 (n'%512=357): anomaly — hierarchical witnesses:
        j odd (n'%1024=869): w=22, P=1024, base=3941
        j=0 mod 8 (n'%4096=3429): w=32, P=4096, base=3429
        j=2,4,6 mod 8 (n'%1024=357, %4096≠3429): w=30, P=4096, bases=4453,5477,6501
    All cases fully covered by period certs + base sensitivity certs. -/
theorem subcaseB_m4_mod64_37_witness (n' : Nat) (hn' : 3087 ≤ n') (hmod : n' % 64 = 37)
    (m : Fin (2 * (n' + 1) + 1)) (hm4 : m.val = 4) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  by_cases h128 : n' % 128 = 37
  · -- k even: n'≡37 mod 128, w=12, P=128, base=3109
    use spikeConfig 12 n'
    refine ⟨spikeConfig_odd_false 12 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 12 n', rule30n_flipCell_spikeConfig_eq' 12 n' m (by omega) (by omega)]
    simp only [hm4]
    have h_F : caEvolve 128 (spikeAtList 12 (2*128+2*12+1)) = spikeAtList 12 (2*12+1) :=
      caEvolve_cert_sp12_p128
    have h_H : caEvolve 128 (twoSpikeList 12 4 (2*128+2*(max 12 4)+1)) =
               twoSpikeList 12 4 (2*(max 12 4)+1) := by
      have hmax : max 12 4 = 12 := by decide
      rw [hmax, twoSpikeList_comm 12 4, twoSpikeList_comm 12 4]
      exact caEvolve_cert_ts412_p128
    obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3109 + k * 128 := ⟨(n' - 3109) / 128, by omega⟩
    rw [show n' + 1 = 3109 + 1 + k * 128 from by omega]
    exact sensitivity_transfer 12 4 128 3109 k (by omega) h_F h_H subcaseB_m4_base_sens_3109
  · -- n' % 128 = 101 (follows from hmod and h128)
    have hn'128 : n' % 128 = 101 := by omega
    by_cases h256 : n' % 256 = 229
    · -- k≡3,7 mod 8: n'≡229 mod 256, w=18, P=256, base=3301
      use spikeConfig 18 n'
      refine ⟨spikeConfig_odd_false 18 (by decide) n', ?_⟩
      rw [rule30n_spikeConfig_eq 18 n', rule30n_flipCell_spikeConfig_eq' 18 n' m (by omega) (by omega)]
      simp only [hm4]
      have h_F : caEvolve 256 (spikeAtList 18 (2*256+2*18+1)) = spikeAtList 18 (2*18+1) :=
        caEvolve_cert_sp18_p256
      have h_H : caEvolve 256 (twoSpikeList 18 4 (2*256+2*(max 18 4)+1)) =
                 twoSpikeList 18 4 (2*(max 18 4)+1) := by
        have hmax : max 18 4 = 18 := by decide
        rw [hmax]; exact caEvolve_cert_ts184_p256
      obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3301 + k * 256 := ⟨(n' - 3301) / 256, by omega⟩
      rw [show n' + 1 = 3301 + 1 + k * 256 from by omega]
      exact sensitivity_transfer 18 4 256 3301 k (by omega) h_F h_H subcaseB_m4_base_sens_3301
    · -- n' % 256 = 101 (follows from hn'128 and h256)
      have hn'256 : n' % 256 = 101 := by omega
      by_cases h512 : n' % 512 = 357
      · -- k≡5 mod 8: n'≡357 mod 512, anomaly — hierarchical witnesses
        -- Sub-structure (period 8 in j, period 4096 in n'):
        --   j odd (n'≡869 mod 1024): w=22, P=1024
        --   j=0 mod 8 (n'≡3429 mod 4096): w=32, P=4096
        --   j=2,4,6 mod 8 (n'≡357 mod 1024, ≢3429 mod 4096): w=30, P=4096
        by_cases h1024 : n' % 1024 = 869
        · -- j odd: w=22, P=1024, base=3941
          use spikeConfig 22 n'
          refine ⟨spikeConfig_odd_false 22 (by decide) n', ?_⟩
          rw [rule30n_spikeConfig_eq 22 n', rule30n_flipCell_spikeConfig_eq' 22 n' m (by omega) (by omega)]
          simp only [hm4]
          have h_F : caEvolve 1024 (spikeAtList 22 (2*1024+2*22+1)) = spikeAtList 22 (2*22+1) :=
            caEvolve_cert_sp22_p1024
          have h_H : caEvolve 1024 (twoSpikeList 22 4 (2*1024+2*(max 22 4)+1)) =
                     twoSpikeList 22 4 (2*(max 22 4)+1) := by
            have hmax : max 22 4 = 22 := by decide
            rw [hmax]; exact caEvolve_cert_ts224_p1024
          obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3941 + k * 1024 := ⟨(n' - 3941) / 1024, by omega⟩
          rw [show n' + 1 = 3941 + 1 + k * 1024 from by omega]
          exact sensitivity_transfer 22 4 1024 3941 k (by omega) h_F h_H subcaseB_m4_base_sens_3941_w22
        · -- j even: n'≡357 mod 1024
          have hn'1024 : n' % 1024 = 357 := by omega
          by_cases h4096 : n' % 4096 = 3429
          · -- j=0 mod 8: w=32, P=4096, base=3429
            use spikeConfig 32 n'
            refine ⟨spikeConfig_odd_false 32 (by decide) n', ?_⟩
            rw [rule30n_spikeConfig_eq 32 n', rule30n_flipCell_spikeConfig_eq' 32 n' m (by omega) (by omega)]
            simp only [hm4]
            have h_F : caEvolve 4096 (spikeAtList 32 (2*4096+2*32+1)) = spikeAtList 32 (2*32+1) :=
              caEvolve_cert_spike32_p4096
            have h_H : caEvolve 4096 (twoSpikeList 32 4 (2*4096+2*(max 32 4)+1)) =
                       twoSpikeList 32 4 (2*(max 32 4)+1) := by
              have hmax : max 32 4 = 32 := by decide
              rw [hmax]; exact caEvolve_cert_ts324_p4096
            obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3429 + k * 4096 := ⟨(n' - 3429) / 4096, by omega⟩
            rw [show n' + 1 = 3429 + 1 + k * 4096 from by omega]
            exact sensitivity_transfer 32 4 4096 3429 k (by omega) h_F h_H subcaseB_m4_base_sens_3429_w32
          · -- j=2,4,6 mod 8: w=30, P=4096, three mod4096 classes
            -- n'%4096 ∈ {357, 1381, 2405} (each differs by 1024)
            use spikeConfig 30 n'
            refine ⟨spikeConfig_odd_false 30 (by decide) n', ?_⟩
            rw [rule30n_spikeConfig_eq 30 n', rule30n_flipCell_spikeConfig_eq' 30 n' m (by omega) (by omega)]
            simp only [hm4]
            have h_F : caEvolve 4096 (spikeAtList 30 (2*4096+2*30+1)) = spikeAtList 30 (2*30+1) :=
              caEvolve_cert_spike30_p4096
            have h_H : caEvolve 4096 (twoSpikeList 30 4 (2*4096+2*(max 30 4)+1)) =
                       twoSpikeList 30 4 (2*(max 30 4)+1) := by
              have hmax : max 30 4 = 30 := by decide
              rw [hmax]; exact caEvolve_cert_ts304_p4096
            by_cases h4096a : n' % 4096 = 357
            · obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 4453 + k * 4096 := ⟨(n' - 4453) / 4096, by omega⟩
              rw [show n' + 1 = 4453 + 1 + k * 4096 from by omega]
              exact sensitivity_transfer 30 4 4096 4453 k (by omega) h_F h_H subcaseB_m4_base_sens_4453_w30
            · by_cases h4096b : n' % 4096 = 1381
              · obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 5477 + k * 4096 := ⟨(n' - 5477) / 4096, by omega⟩
                rw [show n' + 1 = 5477 + 1 + k * 4096 from by omega]
                exact sensitivity_transfer 30 4 4096 5477 k (by omega) h_F h_H subcaseB_m4_base_sens_5477_w30
              · -- n' % 4096 = 2405 (last remaining class)
                have h4096c : n' % 4096 = 2405 := by omega
                obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 6501 + k * 4096 := ⟨(n' - 6501) / 4096, by omega⟩
                rw [show n' + 1 = 6501 + 1 + k * 4096 from by omega]
                exact sensitivity_transfer 30 4 4096 6501 k (by omega) h_F h_H subcaseB_m4_base_sens_6501_w30
      · -- n' % 512 = 101: k≡1 mod 8, w=16, P=512, base=3173
        have hn'512 : n' % 512 = 101 := by omega
        use spikeConfig 16 n'
        refine ⟨spikeConfig_odd_false 16 (by decide) n', ?_⟩
        rw [rule30n_spikeConfig_eq 16 n', rule30n_flipCell_spikeConfig_eq' 16 n' m (by omega) (by omega)]
        simp only [hm4]
        have h_F : caEvolve 512 (spikeAtList 16 (2*512+2*16+1)) = spikeAtList 16 (2*16+1) :=
          caEvolve_cert_sp16_p512
        have h_H : caEvolve 512 (twoSpikeList 16 4 (2*512+2*(max 16 4)+1)) =
                   twoSpikeList 16 4 (2*(max 16 4)+1) := by
          have hmax : max 16 4 = 16 := by decide
          rw [hmax]; exact caEvolve_cert_ts164_p512
        obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3173 + k * 512 := ⟨(n' - 3173) / 512, by omega⟩
        rw [show n' + 1 = 3173 + 1 + k * 512 from by omega]
        exact sensitivity_transfer 16 4 512 3173 k (by omega) h_F h_H subcaseB_m4_base_sens_3173

/-- SubcaseB sensitivity for m=4, n'≡5 mod 64, n'≥3087, EXCLUDING Level 3+ (n'%16384≠5).
    Binary hierarchy on 2-adic valuation of n'-5:
      mod128=69: w=12, P=128, base=3141 (covers mod512∈{69,197,325,453})
      mod256=133: w=18, P=256, base=3205 (covers mod512∈{133,389})
      mod512=261: w=16, P=512, base=3333
      mod1024=517: w=22, P=1024, base=3589
      mod4096∈{1029,2053,3077}: w=30, P=4096, bases from CA_Array_m4
      mod16384∈{4101,8197,12293}: w=34, P=16384, bases from CA_Array_m4 -/
theorem subcaseB_m4_mod64_5_mechanical (n' : Nat) (hn' : 3087 ≤ n') (hmod : n' % 64 = 5)
    (hmod16384 : n' % 16384 ≠ 5)
    (m : Fin (2 * (n' + 1) + 1)) (hm4 : m.val = 4) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  -- Binary case split on 2-adic valuation of n'-5
  by_cases h128 : n' % 128 = 69
  · -- Level 0a-1: mod128=69, w=12, P=128, base=3141
    use spikeConfig 12 n'
    refine ⟨spikeConfig_odd_false 12 (by decide) n', ?_⟩
    rw [rule30n_spikeConfig_eq 12 n', rule30n_flipCell_spikeConfig_eq' 12 n' m (by omega) (by omega)]
    simp only [hm4]
    have h_F : caEvolve 128 (spikeAtList 12 (2*128+2*12+1)) = spikeAtList 12 (2*12+1) :=
      caEvolve_cert_sp12_p128
    have h_H : caEvolve 128 (twoSpikeList 12 4 (2*128+2*(max 12 4)+1)) =
               twoSpikeList 12 4 (2*(max 12 4)+1) := by
      have hmax : max 12 4 = 12 := by decide
      rw [hmax, twoSpikeList_comm 12 4, twoSpikeList_comm 12 4]
      exact caEvolve_cert_ts412_p128
    obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3141 + k * 128 := ⟨(n' - 3141) / 128, by omega⟩
    rw [show n' + 1 = 3141 + 1 + k * 128 from by omega]
    exact sensitivity_transfer 12 4 128 3141 k (by omega) h_F h_H subcaseB_m4_base_sens_3141
  · -- n' % 128 = 5 (follows from hmod and h128)
    have hn'128 : n' % 128 = 5 := by omega
    by_cases h256 : n' % 256 = 133
    · -- Level 0a-2: mod256=133, w=18, P=256, base=3205
      use spikeConfig 18 n'
      refine ⟨spikeConfig_odd_false 18 (by decide) n', ?_⟩
      rw [rule30n_spikeConfig_eq 18 n', rule30n_flipCell_spikeConfig_eq' 18 n' m (by omega) (by omega)]
      simp only [hm4]
      have h_F : caEvolve 256 (spikeAtList 18 (2*256+2*18+1)) = spikeAtList 18 (2*18+1) :=
        caEvolve_cert_sp18_p256
      have h_H : caEvolve 256 (twoSpikeList 18 4 (2*256+2*(max 18 4)+1)) =
                 twoSpikeList 18 4 (2*(max 18 4)+1) := by
        have hmax : max 18 4 = 18 := by decide
        rw [hmax]; exact caEvolve_cert_ts184_p256
      obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3205 + k * 256 := ⟨(n' - 3205) / 256, by omega⟩
      rw [show n' + 1 = 3205 + 1 + k * 256 from by omega]
      exact sensitivity_transfer 18 4 256 3205 k (by omega) h_F h_H subcaseB_m4_base_sens_3205
    · -- n' % 256 = 5
      have hn'256 : n' % 256 = 5 := by omega
      by_cases h512 : n' % 512 = 261
      · -- Level 0a-3: mod512=261, w=16, P=512, base=3333
        use spikeConfig 16 n'
        refine ⟨spikeConfig_odd_false 16 (by decide) n', ?_⟩
        rw [rule30n_spikeConfig_eq 16 n', rule30n_flipCell_spikeConfig_eq' 16 n' m (by omega) (by omega)]
        simp only [hm4]
        have h_F : caEvolve 512 (spikeAtList 16 (2*512+2*16+1)) = spikeAtList 16 (2*16+1) :=
          caEvolve_cert_sp16_p512
        have h_H : caEvolve 512 (twoSpikeList 16 4 (2*512+2*(max 16 4)+1)) =
                   twoSpikeList 16 4 (2*(max 16 4)+1) := by
          have hmax : max 16 4 = 16 := by decide
          rw [hmax]; exact caEvolve_cert_ts164_p512
        obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3333 + k * 512 := ⟨(n' - 3333) / 512, by omega⟩
        rw [show n' + 1 = 3333 + 1 + k * 512 from by omega]
        exact sensitivity_transfer 16 4 512 3333 k (by omega) h_F h_H subcaseB_m4_base_sens_3333
      · -- n' % 512 = 5
        have hn'512 : n' % 512 = 5 := by omega
        by_cases h1024 : n' % 1024 = 517
        · -- Level 0b: mod1024=517, w=22, P=1024, base=3589
          use spikeConfig 22 n'
          refine ⟨spikeConfig_odd_false 22 (by decide) n', ?_⟩
          rw [rule30n_spikeConfig_eq 22 n', rule30n_flipCell_spikeConfig_eq' 22 n' m (by omega) (by omega)]
          simp only [hm4]
          have h_F : caEvolve 1024 (spikeAtList 22 (2*1024+2*22+1)) = spikeAtList 22 (2*22+1) :=
            caEvolve_cert_sp22_p1024
          have h_H : caEvolve 1024 (twoSpikeList 22 4 (2*1024+2*(max 22 4)+1)) =
                     twoSpikeList 22 4 (2*(max 22 4)+1) := by
            have hmax : max 22 4 = 22 := by decide
            rw [hmax]; exact caEvolve_cert_ts224_p1024
          obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 3589 + k * 1024 := ⟨(n' - 3589) / 1024, by omega⟩
          rw [show n' + 1 = 3589 + 1 + k * 1024 from by omega]
          exact sensitivity_transfer 22 4 1024 3589 k (by omega) h_F h_H subcaseB_m4_base_sens_3589
        · -- n' % 1024 = 5
          have hn'1024 : n' % 1024 = 5 := by omega
          by_cases h4096 : n' % 4096 = 5
          · -- n' % 4096 = 5 → Level 2 (mod16384≠5 by hypothesis)
            by_cases h16384_4101 : n' % 16384 = 4101
            · -- Level 2a: mod16384=4101, w=34, P=16384, base=4101
              use spikeConfig 34 n'
              refine ⟨spikeConfig_odd_false 34 (by decide) n', ?_⟩
              rw [rule30n_spikeConfig_eq 34 n', rule30n_flipCell_spikeConfig_eq' 34 n' m (by omega) (by omega)]
              simp only [hm4]
              have h_F : caEvolve 16384 (spikeAtList 34 (2*16384+2*34+1)) = spikeAtList 34 (2*34+1) :=
                caEvolve_cert_spike34_p16384
              have h_H : caEvolve 16384 (twoSpikeList 34 4 (2*16384+2*(max 34 4)+1)) =
                         twoSpikeList 34 4 (2*(max 34 4)+1) := by
                have hmax : max 34 4 = 34 := by decide
                rw [hmax]; exact caEvolve_cert_ts344_p16384
              obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 4101 + k * 16384 := ⟨(n' - 4101) / 16384, by omega⟩
              rw [show n' + 1 = 4101 + 1 + k * 16384 from by omega]
              exact sensitivity_transfer 34 4 16384 4101 k (by omega) h_F h_H subcaseB_m4_base_sens_4101_w34
            · by_cases h16384_8197 : n' % 16384 = 8197
              · -- Level 2b: mod16384=8197, w=34, P=16384, base=8197
                use spikeConfig 34 n'
                refine ⟨spikeConfig_odd_false 34 (by decide) n', ?_⟩
                rw [rule30n_spikeConfig_eq 34 n', rule30n_flipCell_spikeConfig_eq' 34 n' m (by omega) (by omega)]
                simp only [hm4]
                have h_F : caEvolve 16384 (spikeAtList 34 (2*16384+2*34+1)) = spikeAtList 34 (2*34+1) :=
                  caEvolve_cert_spike34_p16384
                have h_H : caEvolve 16384 (twoSpikeList 34 4 (2*16384+2*(max 34 4)+1)) =
                           twoSpikeList 34 4 (2*(max 34 4)+1) := by
                  have hmax : max 34 4 = 34 := by decide
                  rw [hmax]; exact caEvolve_cert_ts344_p16384
                obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 8197 + k * 16384 := ⟨(n' - 8197) / 16384, by omega⟩
                rw [show n' + 1 = 8197 + 1 + k * 16384 from by omega]
                exact sensitivity_transfer 34 4 16384 8197 k (by omega) h_F h_H subcaseB_m4_base_sens_8197_w34
              · -- Level 2c: mod16384=12293 (the only remaining case)
                have hn'16384 : n' % 16384 = 12293 := by omega
                use spikeConfig 34 n'
                refine ⟨spikeConfig_odd_false 34 (by decide) n', ?_⟩
                rw [rule30n_spikeConfig_eq 34 n', rule30n_flipCell_spikeConfig_eq' 34 n' m (by omega) (by omega)]
                simp only [hm4]
                have h_F : caEvolve 16384 (spikeAtList 34 (2*16384+2*34+1)) = spikeAtList 34 (2*34+1) :=
                  caEvolve_cert_spike34_p16384
                have h_H : caEvolve 16384 (twoSpikeList 34 4 (2*16384+2*(max 34 4)+1)) =
                           twoSpikeList 34 4 (2*(max 34 4)+1) := by
                  have hmax : max 34 4 = 34 := by decide
                  rw [hmax]; exact caEvolve_cert_ts344_p16384
                obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 12293 + k * 16384 := ⟨(n' - 12293) / 16384, by omega⟩
                rw [show n' + 1 = 12293 + 1 + k * 16384 from by omega]
                exact sensitivity_transfer 34 4 16384 12293 k (by omega) h_F h_H subcaseB_m4_base_sens_12293_w34
          · -- n' % 4096 ≠ 5 → Level 1: mod4096∈{1029,2053,3077}
            by_cases h4096_1029 : n' % 4096 = 1029
            · -- Level 1a: mod4096=1029, w=30, P=4096, base=5125
              use spikeConfig 30 n'
              refine ⟨spikeConfig_odd_false 30 (by decide) n', ?_⟩
              rw [rule30n_spikeConfig_eq 30 n', rule30n_flipCell_spikeConfig_eq' 30 n' m (by omega) (by omega)]
              simp only [hm4]
              have h_F : caEvolve 4096 (spikeAtList 30 (2*4096+2*30+1)) = spikeAtList 30 (2*30+1) :=
                caEvolve_cert_spike30_p4096
              have h_H : caEvolve 4096 (twoSpikeList 30 4 (2*4096+2*(max 30 4)+1)) =
                         twoSpikeList 30 4 (2*(max 30 4)+1) := by
                have hmax : max 30 4 = 30 := by decide
                rw [hmax]; exact caEvolve_cert_ts304_p4096
              obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 5125 + k * 4096 := ⟨(n' - 5125) / 4096, by omega⟩
              rw [show n' + 1 = 5125 + 1 + k * 4096 from by omega]
              exact sensitivity_transfer 30 4 4096 5125 k (by omega) h_F h_H subcaseB_m4_base_sens_5125_w30
            · by_cases h4096_2053 : n' % 4096 = 2053
              · -- Level 1b: mod4096=2053, w=30, P=4096, base=6149
                use spikeConfig 30 n'
                refine ⟨spikeConfig_odd_false 30 (by decide) n', ?_⟩
                rw [rule30n_spikeConfig_eq 30 n', rule30n_flipCell_spikeConfig_eq' 30 n' m (by omega) (by omega)]
                simp only [hm4]
                have h_F : caEvolve 4096 (spikeAtList 30 (2*4096+2*30+1)) = spikeAtList 30 (2*30+1) :=
                  caEvolve_cert_spike30_p4096
                have h_H : caEvolve 4096 (twoSpikeList 30 4 (2*4096+2*(max 30 4)+1)) =
                           twoSpikeList 30 4 (2*(max 30 4)+1) := by
                  have hmax : max 30 4 = 30 := by decide
                  rw [hmax]; exact caEvolve_cert_ts304_p4096
                obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 6149 + k * 4096 := ⟨(n' - 6149) / 4096, by omega⟩
                rw [show n' + 1 = 6149 + 1 + k * 4096 from by omega]
                exact sensitivity_transfer 30 4 4096 6149 k (by omega) h_F h_H subcaseB_m4_base_sens_6149_w30
              · -- Level 1c: mod4096=3077 (the only remaining case)
                have hn'4096 : n' % 4096 = 3077 := by omega
                use spikeConfig 30 n'
                refine ⟨spikeConfig_odd_false 30 (by decide) n', ?_⟩
                rw [rule30n_spikeConfig_eq 30 n', rule30n_flipCell_spikeConfig_eq' 30 n' m (by omega) (by omega)]
                simp only [hm4]
                have h_F : caEvolve 4096 (spikeAtList 30 (2*4096+2*30+1)) = spikeAtList 30 (2*30+1) :=
                  caEvolve_cert_spike30_p4096
                have h_H : caEvolve 4096 (twoSpikeList 30 4 (2*4096+2*(max 30 4)+1)) =
                           twoSpikeList 30 4 (2*(max 30 4)+1) := by
                  have hmax : max 30 4 = 30 := by decide
                  rw [hmax]; exact caEvolve_cert_ts304_p4096
                obtain ⟨k, hn'_eq⟩ : ∃ k, n' = 7173 + k * 4096 := ⟨(n' - 7173) / 4096, by omega⟩
                rw [show n' + 1 = 7173 + 1 + k * 4096 from by omega]
                exact sensitivity_transfer 30 4 4096 7173 k (by omega) h_F h_H subcaseB_m4_base_sens_7173_w30

/-- SubcaseB resolution for m=4, n' ≥ 3087.
    Loop66 analysis: mod64∈{13,29,45,61} use w=6 P=16; mod64=53 uses w=10 P=64;
    mod64=21 uses w∈{12,16,18} with multiple periods; mod64=37 uses w=12 (P=128)
    plus w=32 (P=4096) for anomaly class; mod64=5 is hierarchical (Level 0-3+).
    ONLY Level 3+ (n'≡5 mod 16384) requires algebraic proof (D-field linearity).
    All other cases mechanical via sensitivity_transfer + existing certs. -/
theorem subcaseB_m4_ge3087 (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm4 : m.val = 4)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) :=
  subcaseB_m4_ge3087_from_rightedge n' hn' m hm4 hcase hts

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


-- Base sensitivity proofs for m=22 (subcaseB_m22_base_sens_6926/3342/3598/4110/3854/782)
-- moved to SubcaseB_BaseSens.lean to avoid OOM during C code generation in this file
-- (tape sizes 6687–13855 caused symbol #9704 OOM when compiled together with this file)

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
            -- Split by (j/2) mod 2 = l mod 2:
            --   l even: n' = 35598 + 65536*(l/2) — period cascade, linearity corridor needed
            --   l odd:  n' = 2830 + 65536*(t+1)  — use w=32, P=65536 ✓
            obtain ⟨l, hjl⟩ : ∃ l, j = 2 * l + 1 := ⟨j / 2, by omega⟩
            have hl_mod : l % 2 = 0 ∨ l % 2 = 1 := by omega
            rcases hl_mod with hl0 | hl1
            · -- l ≡ 0 (even): n' = 35598 + 65536*s
              -- Structure (verified by C shrinking-CA, loop75):
              --   s≡0 mod 2 (n'=35598+131072*t): w=34 witnesses. F=0,H=1 at n'=35598 AND n'=166670.
              --   s≡1 mod 2 (n'=101134+131072*t): w=40 witnesses. F=1,H=0 at n'=101134.
              -- Closed by right-edge witness proof (SubcaseB_m22_RightEdge.lean):
              -- k=6 right-edge witnesses have period 256, bypassing the 131072 barrier entirely.
              exact subcaseB_m22_ge3087_from_rightedge n' hn' m hm22 hcase hts
            · -- l ≡ 1 (odd): l = 2*t+1, so n' = 2830 + 65536*(t+1), use w=32, P=65536
              -- Python (shrinking CA) verified: spike(32) P=65536 PASS, twoSpike(32,22) PASS,
              -- base sensitivity n''=2830 w=32: F=false≠H=true ✓
              obtain ⟨t, hlt⟩ : ∃ t, l = 2 * t + 1 := ⟨l / 2, by omega⟩
              use spikeConfig 32 n'
              refine ⟨spikeConfig_odd_false 32 (by decide) n', ?_⟩
              rw [rule30n_spikeConfig_eq 32 n', rule30n_flipCell_spikeConfig_eq' 32 n' m (by omega) (by omega)]
              simp only [hm22]
              have h_F : caEvolve 65536 (spikeAtList 32 (2*65536+2*32+1)) = spikeAtList 32 (2*32+1) :=
                caEvolve_cert_spike32_p65536
              have h_H : caEvolve 65536 (twoSpikeList 32 22 (2*65536+2*(max 32 22)+1)) =
                         twoSpikeList 32 22 (2*(max 32 22)+1) := by
                have : max 32 22 = 32 := by decide
                rw [this]; exact caEvolve_cert_ts3222_p65536
              rw [show n'+1 = 2830+1+(t+1)*65536 from by omega]
              exact sensitivity_transfer 32 22 65536 2830 (t+1) (by omega) h_F h_H subcaseB_m22_base_sens_2830_w32
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
## Late-active seed: m=34 via witness w=12

The full `m=34` branch still needs the residue-class theorem that SubcaseB
fires only at `n' ≡ 4112` or `4116` modulo `8192`. This section closes the
mechanical part of that branch: once a residue is known, `w=12` gives a
compile-checked witness by sensitivity transfer.
-/

/-- `m=34`, residue `4112 mod 8192`: witness `w=12`. -/
theorem subcaseB_m34_residue_4112_w12 (n' k : Nat)
    (hk : n' = 4112 + k * 8192)
    (m : Fin (2 * (n' + 1) + 1)) (hm34 : m.val = 34) :
    ∃ c_n : Config (n' + 1),
      (∀ j : Fin (n' + 1), c_n ⟨2 * j.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 12 n'
  refine ⟨spikeConfig_odd_false 12 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 12 n', rule30n_flipCell_spikeConfig_eq' 12 n' m (by omega) (by omega)]
  simp only [hm34]
  have h_H : caEvolve 8192 (twoSpikeList 12 34 (2 * 8192 + 2 * (max 12 34) + 1)) =
      twoSpikeList 12 34 (2 * (max 12 34) + 1) := by
    have hmax : max 12 34 = 34 := by decide
    rw [hmax]
    exact caEvolve_cert_ts1234_p8192
  rw [show n' + 1 = 4112 + 1 + k * 8192 from by omega]
  exact sensitivity_transfer_div 12 34 64 8192 4112 k 128
    (by omega) (by omega) (by decide)
    caEvolve_cert_m12_p64 h_H subcaseB_m34_base_sens_4112_w12

/-- `m=34`, residue `4116 mod 8192`: witness `w=12`. -/
theorem subcaseB_m34_residue_4116_w12 (n' k : Nat)
    (hk : n' = 4116 + k * 8192)
    (m : Fin (2 * (n' + 1) + 1)) (hm34 : m.val = 34) :
    ∃ c_n : Config (n' + 1),
      (∀ j : Fin (n' + 1), c_n ⟨2 * j.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 12 n'
  refine ⟨spikeConfig_odd_false 12 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 12 n', rule30n_flipCell_spikeConfig_eq' 12 n' m (by omega) (by omega)]
  simp only [hm34]
  have h_H : caEvolve 8192 (twoSpikeList 12 34 (2 * 8192 + 2 * (max 12 34) + 1)) =
      twoSpikeList 12 34 (2 * (max 12 34) + 1) := by
    have hmax : max 12 34 = 34 := by decide
    rw [hmax]
    exact caEvolve_cert_ts1234_p8192
  rw [show n' + 1 = 4116 + 1 + k * 8192 from by omega]
  exact sensitivity_transfer_div 12 34 64 8192 4116 k 128
    (by omega) (by omega) (by decide)
    caEvolve_cert_m12_p64 h_H subcaseB_m34_base_sens_4116_w12

/-- Iterated `G_{34,last}` period for `m=34`. -/
lemma twoSpikeLast34_iterated_period8192 (n k : Nat) (hn : n ≥ 34) :
    (caEvolve (n + 1) (twoSpikeLastList 34 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 8192) (twoSpikeLastList 34 (2*(n+1+k*8192)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 8192 = (n + k * 8192) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 8192 = (n + k * 8192) + 1 + 8192 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast34_period8192 (n + k * 8192) (by omega)

-- subcaseB_m34_residue_2class_proved: imported from CA_Array_m34_residues.lean

/-- SubcaseB for `m=34` fires only at `n'' ∈ {4112, 4116}` in `[3087, 11279)`. -/
lemma subcaseB_m34_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 11279)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 34 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 34 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 4112 ∨ n'' = 4116 := by
  set k := (n'' - 34) / 8192
  set j' := (n'' - 34) % 8192 + 34 with hj'_def
  have hj'_range : 34 ≤ j' ∧ j' < 8226 := by
    simp only [hj'_def]
    constructor
    · omega
    · have := Nat.mod_lt (n'' - 34) (by omega : 0 < 8192)
      omega
  have hj'lt : j' - 34 < 8192 := by
    omega
  have hn''_decomp : n'' = j' + k * 8192 := by
    have hk_def : k = (n'' - 34) / 8192 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 34) 8192
    omega
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 34 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 34 8192 (by omega) caEvolve_cert_spike34_p8192 j' k
    have heq : j' + 1 + k * 8192 = n'' + 1 := by
      omega
    rw [heq] at hperiod
    rw [hperiod]
    exact hcase''
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 34 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast34_iterated_period8192 j' k hj'_range.1
    have heq : j' + 1 + k * 8192 = n'' + 1 := by
      omega
    rw [heq] at hperiod
    rw [hperiod]
    exact hts''
  have hj'_cases : j' = 4112 ∨ j' = 4116 := by
    have hval : (⟨j' - 34, hj'lt⟩ : Fin 8192).val = j' - 34 := rfl
    have h2 := subcaseB_m34_residue_2class_proved ⟨j' - 34, hj'lt⟩
      (by
        simp only [hval]
        convert hF_j' using 2 <;> omega)
      (by
        simp only [hval]
        convert hG_j' using 2 <;> omega)
    rcases h2 with h | h
    · left
      omega
    · right
      omega
  rcases hj'_cases with h1 | h2
  · left
    omega
  · right
    omega

/-- SubcaseB resolution for `m=34`, `n' ≥ 3087`. Witness: `spike_12` (`w=12`). -/
theorem subcaseB_m34_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm34 : m.val = 34)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  have hcase34 : (caEvolve (n'+1) (spikeAtList 34 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase
    simp only [hm34] at hc
    rw [← rule30n_spikeAt_eq n' 34]
    exact hc
  have hts34 : (caEvolve (n'+1) (twoSpikeLastList 34 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts
    simp only [hm34] at ht
    rw [← rule30n_twoSpikeLast_eq n' 34]
    exact ht
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 8192 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 8192 n' (by omega) hn'
  set n'' := periodReduce 3087 8192 n' with hn''_def
  have hcase'' : (caEvolve (n''+1) (spikeAtList 34 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 34 8192 (by omega) caEvolve_cert_spike34_p8192 n'' k
    have heq : n'' + 1 + k * 8192 = n' + 1 := by
      omega
    rw [heq] at hperiod
    rw [hperiod]
    exact hcase34
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 34 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast34_iterated_period8192 n'' k (by omega)
    have heq : n'' + 1 + k * 8192 = n' + 1 := by
      omega
    rw [heq] at hperiod
    rw [hperiod]
    exact hts34
  have hn''_cases : n'' = 4112 ∨ n'' = 4116 :=
    subcaseB_m34_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  rcases hn''_cases with h1 | h2
  · exact subcaseB_m34_residue_4112_w12 n' k (by omega) m hm34
  · exact subcaseB_m34_residue_4116_w12 n' k (by omega) m hm34

/-!
## Late-active seed: m=36 via witnesses w=2 and w=4

The `m=36` branch mirrors `m=34` with period `P=16384 = 2^14`.
SubcaseB fires only at `n' ≡ 4113` or `4117` modulo `16384`.
- Residue `4113`: witness `w=2` (F_w=false, H_{w,36}=true)
- Residue `4117`: witness `w=4` (F_w=false, H_{w,36}=true)

Both witnesses transfer via `sensitivity_transfer_div` using:
- spike(w) period: P_w=2 for w=2, P_w=2 for w=4 (both divide 16384)
- twoSpike(w,36) period: P=16384 (certified in CA_Array_m36)
-/

/-- `m=36`, residue `4113 mod 16384`: witness `w=2`. -/
theorem subcaseB_m36_residue_4113_w2 (n' k : Nat)
    (hk : n' = 4113 + k * 16384)
    (m : Fin (2 * (n' + 1) + 1)) (hm36 : m.val = 36) :
    ∃ c_n : Config (n' + 1),
      (∀ j : Fin (n' + 1), c_n ⟨2 * j.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 2 n'
  refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 2 n', rule30n_flipCell_spikeConfig_eq' 2 n' m (by omega) (by omega)]
  simp only [hm36]
  have h_H : caEvolve 16384 (twoSpikeList 2 36 (2 * 16384 + 2 * (max 2 36) + 1)) =
      twoSpikeList 2 36 (2 * (max 2 36) + 1) := by
    have hmax : max 2 36 = 36 := by decide
    rw [hmax]
    exact caEvolve_cert_ts236_p16384
  rw [show n' + 1 = 4113 + 1 + k * 16384 from by omega]
  exact sensitivity_transfer_div 2 36 2 16384 4113 k 8192
    (by omega) (by omega) (by decide)
    caEvolve_cert_m2_p2 h_H subcaseB_m36_base_sens_4113_w2

/-- `m=36`, residue `4117 mod 16384`: witness `w=4`. -/
theorem subcaseB_m36_residue_4117_w4 (n' k : Nat)
    (hk : n' = 4117 + k * 16384)
    (m : Fin (2 * (n' + 1) + 1)) (hm36 : m.val = 36) :
    ∃ c_n : Config (n' + 1),
      (∀ j : Fin (n' + 1), c_n ⟨2 * j.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 4 n'
  refine ⟨spikeConfig_odd_false 4 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 4 n', rule30n_flipCell_spikeConfig_eq' 4 n' m (by omega) (by omega)]
  simp only [hm36]
  have h_H : caEvolve 16384 (twoSpikeList 4 36 (2 * 16384 + 2 * (max 4 36) + 1)) =
      twoSpikeList 4 36 (2 * (max 4 36) + 1) := by
    have hmax : max 4 36 = 36 := by decide
    rw [hmax]
    exact caEvolve_cert_ts436_p16384
  rw [show n' + 1 = 4117 + 1 + k * 16384 from by omega]
  exact sensitivity_transfer_div 4 36 8 16384 4117 k 2048
    (by omega) (by omega) (by decide)
    caEvolve_cert_m4_p8 h_H subcaseB_m36_base_sens_4117_w4

/-- Iterated `G_{36,last}` period for `m=36`. -/
lemma twoSpikeLast36_iterated_period16384 (n k : Nat) (hn : n ≥ 36) :
    (caEvolve (n + 1) (twoSpikeLastList 36 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 16384) (twoSpikeLastList 36 (2*(n+1+k*16384)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 16384 = (n + k * 16384) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 16384 = (n + k * 16384) + 1 + 16384 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast36_period16384 (n + k * 16384) (by omega)

-- subcaseB_m36_residue_2class: imported from CA_Array_m36_residues.lean

/-- SubcaseB for `m=36` fires only at `n'' ∈ {4113, 4117}` in `[3087, 19471)`. -/
lemma subcaseB_m36_unique_in_period (n'' : Nat) (hn''_lo : 3087 ≤ n'') (hn''_hi : n'' < 19471)
    (hcase'' : (caEvolve (n''+1) (spikeAtList 36 (2*(n''+1)+1))).getD 0 false = false)
    (hts'' : (caEvolve (n''+1) (twoSpikeLastList 36 (2*(n''+1)+1))).getD 0 false = true) :
    n'' = 4113 ∨ n'' = 4117 := by
  set k := (n'' - 36) / 16384
  set j' := (n'' - 36) % 16384 + 36 with hj'_def
  have hj'_range : 36 ≤ j' ∧ j' < 16420 := by
    simp only [hj'_def]
    constructor
    · omega
    · have := Nat.mod_lt (n'' - 36) (by omega : 0 < 16384)
      omega
  have hj'lt : j' - 36 < 16384 := by
    omega
  have hn''_decomp : n'' = j' + k * 16384 := by
    have hk_def : k = (n'' - 36) / 16384 := rfl
    simp only [hj'_def, hk_def]
    have := Nat.div_add_mod (n'' - 36) 16384
    omega
  have hF_j' : (caEvolve (j' + 1) (spikeAtList 36 (2*(j'+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 36 16384 (by omega) caEvolve_cert_spike36_p16384 j' k
    have heq : j' + 1 + k * 16384 = n'' + 1 := by
      omega
    rw [heq] at hperiod
    rw [hperiod]
    exact hcase''
  have hG_j' : (caEvolve (j' + 1) (twoSpikeLastList 36 (2*(j'+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast36_iterated_period16384 j' k hj'_range.1
    have heq : j' + 1 + k * 16384 = n'' + 1 := by
      omega
    rw [heq] at hperiod
    rw [hperiod]
    exact hts''
  have hj'_cases : j' = 4113 ∨ j' = 4117 := by
    have hval : (⟨j' - 36, hj'lt⟩ : Fin 16384).val = j' - 36 := rfl
    have h2 := subcaseB_m36_residue_2class ⟨j' - 36, hj'lt⟩
      (by
        simp only [hval]
        convert hF_j' using 2 <;> omega)
      (by
        simp only [hval]
        convert hG_j' using 2 <;> omega)
    rcases h2 with h | h
    · left
      omega
    · right
      omega
  rcases hj'_cases with h1 | h2
  · left
    omega
  · right
    omega

/-- SubcaseB resolution for `m=36`, `n' ≥ 3087`. Witnesses: `spike_2` (residue 4113) and `spike_4` (residue 4117). -/
theorem subcaseB_m36_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm36 : m.val = 36)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  have hcase36 : (caEvolve (n'+1) (spikeAtList 36 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase
    simp only [hm36] at hc
    rw [← rule30n_spikeAt_eq n' 36]
    exact hc
  have hts36 : (caEvolve (n'+1) (twoSpikeLastList 36 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts
    simp only [hm36] at ht
    rw [← rule30n_twoSpikeLast_eq n' 36]
    exact ht
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 16384 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 16384 n' (by omega) hn'
  set n'' := periodReduce 3087 16384 n' with hn''_def
  have hcase'' : (caEvolve (n''+1) (spikeAtList 36 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 36 16384 (by omega) caEvolve_cert_spike36_p16384 n'' k
    have heq : n'' + 1 + k * 16384 = n' + 1 := by
      omega
    rw [heq] at hperiod
    rw [hperiod]
    exact hcase36
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 36 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast36_iterated_period16384 n'' k (by omega)
    have heq : n'' + 1 + k * 16384 = n' + 1 := by
      omega
    rw [heq] at hperiod
    rw [hperiod]
    exact hts36
  have hn''_cases : n'' = 4113 ∨ n'' = 4117 :=
    subcaseB_m36_unique_in_period n'' hn''_range.1 hn''_range.2 hcase'' hts''
  rcases hn''_cases with h1 | h2
  · exact subcaseB_m36_residue_4113_w2 n' k (by omega) m hm36
  · exact subcaseB_m36_residue_4117_w4 n' k (by omega) m hm36

/-!
## SubcaseB resolution for m=38

SubcaseB fires for m=38 only at n' ≡ 8210 or 8214 (mod 32768), as computationally verified.
Witnesses: w=2 at n'=8210, w=4 at n'=8214. Period = 32768.
-/

lemma twoSpikeLast38_iterated_period32768 (n k : Nat) (hn : n ≥ 38) :
    (caEvolve (n + 1) (twoSpikeLastList 38 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 32768) (twoSpikeLastList 38 (2*(n+1+k*32768)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 32768 = (n + k * 32768) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 32768 = (n + k * 32768) + 1 + 32768 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast38_period32768 (n + k * 32768) (by omega)

-- subcaseB_m38_residue_2class_proved: imported from CA_Array_m38_residues.lean

/-- Witness for m=38 SubcaseB at n' = 8210 (w=2). -/
private lemma subcaseB_m38_residue_8210_w2 (n' k : Nat) (hn' : n' = 8210 + k * 32768)
    (m : Fin (2 * (n' + 1) + 1)) (hm38 : m.val = 38) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 2 n'
  refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 2 n', rule30n_flipCell_spikeConfig_eq' 2 n' m (by omega) (by omega)]
  simp only [hm38]
  have h_H : caEvolve 32768 (twoSpikeList 2 38 (2 * 32768 + 2 * (max 2 38) + 1)) =
      twoSpikeList 2 38 (2 * (max 2 38) + 1) := by
    have hmax : max 2 38 = 38 := by decide
    rw [hmax]
    exact caEvolve_cert_ts238_p32768
  rw [show n' + 1 = 8210 + 1 + k * 32768 from by omega]
  exact sensitivity_transfer_div 2 38 2 32768 8210 k 16384
    (by omega) (by omega) (by decide)
    caEvolve_cert_m2_p2 h_H subcaseB_m38_base_sens_8210_w2

/-- Witness for m=38 SubcaseB at n' = 8214 (w=4). -/
private lemma subcaseB_m38_residue_8214_w4 (n' k : Nat) (hn' : n' = 8214 + k * 32768)
    (m : Fin (2 * (n' + 1) + 1)) (hm38 : m.val = 38) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  use spikeConfig 4 n'
  refine ⟨spikeConfig_odd_false 4 (by decide) n', ?_⟩
  rw [rule30n_spikeConfig_eq 4 n', rule30n_flipCell_spikeConfig_eq' 4 n' m (by omega) (by omega)]
  simp only [hm38]
  have h_H : caEvolve 32768 (twoSpikeList 4 38 (2 * 32768 + 2 * (max 4 38) + 1)) =
      twoSpikeList 4 38 (2 * (max 4 38) + 1) := by
    have hmax : max 4 38 = 38 := by decide
    rw [hmax]
    exact caEvolve_cert_ts438_p32768
  rw [show n' + 1 = 8214 + 1 + k * 32768 from by omega]
  exact sensitivity_transfer_div 4 38 8 32768 8214 k 4096
    (by omega) (by omega) (by decide)
    caEvolve_cert_m4_p8 h_H subcaseB_m38_base_sens_8214_w4

theorem subcaseB_m38_ge3087_proved (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm38 : m.val = 38)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  have hcase38 : (caEvolve (n'+1) (spikeAtList 38 (2*(n'+1)+1))).getD 0 false = false := by
    have hc := hcase; simp only [hm38] at hc
    rw [← rule30n_spikeAt_eq n' 38]; exact hc
  have hts38 : (caEvolve (n'+1) (twoSpikeLastList 38 (2*(n'+1)+1))).getD 0 false = true := by
    have ht := hts; simp only [hm38] at ht
    rw [← rule30n_twoSpikeLast_eq n' 38]; exact ht
  obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3087 32768 n' (by omega) hn'
  have hn''_range := periodReduce_range 3087 32768 n' (by omega) hn'
  set n'' := periodReduce 3087 32768 n' with hn''_def
  have hcase'' : (caEvolve (n''+1) (spikeAtList 38 (2*(n''+1)+1))).getD 0 false = false := by
    have hperiod := spikeAt_iterated_period 38 32768 (by omega) caEvolve_cert_spike38_p32768 n'' k
    have heq : n'' + 1 + k * 32768 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hcase38
  have hts'' : (caEvolve (n''+1) (twoSpikeLastList 38 (2*(n''+1)+1))).getD 0 false = true := by
    have hperiod := twoSpikeLast38_iterated_period32768 n'' k (by omega)
    have heq : n'' + 1 + k * 32768 = n' + 1 := by omega
    rw [heq] at hperiod; rw [hperiod]; exact hts38
  have hn''_cases : n'' = 8210 ∨ n'' = 8214 := by
    have hj : n'' - 38 < 32768 := by omega
    have := subcaseB_m38_residue_2class_proved ⟨n'' - 38, hj⟩
      (by simp; convert hcase'' using 5 <;> omega)
      (by simp; convert hts'' using 5 <;> omega)
    omega
  rcases hn''_cases with h1 | h2
  · exact subcaseB_m38_residue_8210_w2 n' k (by omega) m hm38
  · exact subcaseB_m38_residue_8214_w4 n' k (by omega) m hm38

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

/-!
## Right-mirror SubcaseB resolution lemmas

For m = 2*(n'+1)-8 (right-boundary position), we need sensitivity witnesses.
The witnesses alternate: spike_2 for even n', spike_12 for odd n'.

Key facts (computationally verified, proved via sorrys):
- LHS (spike_2): caEvolve(n'+1)(spikeAtList 2 N).getD 0 = decide(n'%2=0)  (parity lemma)
- RHS even case: caEvolve(n'+1)(twoSpikeList 2 m.val N).getD 0 = false for n' even, n'≥3087
- RHS odd case (spike_12): caEvolve(n'+1)(spikeAtList 12 N).getD 0 ≠
                            caEvolve(n'+1)(twoSpikeList 12 m.val N).getD 0 for n' odd, n'≥3087
-/

/-- Parity of center value for spike-at-2 initial condition.
    Proved structurally in Spike2Parity.lean; here restated in caEvolve form.
    The 2-step cycle: spike2 → three-ones → spike2 (smaller tape) gives parity period 2. -/
private lemma rm_spike2_parity (n' : Nat) :
    (caEvolve (n' + 1) (spikeAtList 2 (2 * (n' + 1) + 1))).getD 0 false =
    decide (n' % 2 = 0) := by
  -- Prove by strong induction using the period-2 certificate.
  induction n' using Nat.strongRecOn with
  | ind n' ih =>
    match n' with
    | 0 => native_decide
    | 1 => native_decide
    | (m + 2) =>
      -- Period-2 step (backwards): caEvolve(m+3) = caEvolve(m+1) since period is 2
      -- rule30n_spikeAt2_period2 m: caEvolve(m+1)@N = caEvolve(m+3)@N'
      -- Taking .symm: caEvolve(m+3)@N' = caEvolve(m+1)@N
      have h2 : (caEvolve (m + 3) (spikeAtList 2 (2 * (m + 3) + 1))).getD 0 false =
                (caEvolve (m + 1) (spikeAtList 2 (2 * (m + 1) + 1))).getD 0 false :=
        (rule30n_spikeAt2_period2 m).symm
      -- ih m: caEvolve(m+1)(spikeAt2(2*(m+1)+1)).getD 0 = decide(m%2=0)
      rw [h2, ih m (by omega)]
      simp [show (m + 2) % 2 = m % 2 from by omega]

/-- RC_config: the intermediate tape with 1s at positions {2, M-9, M-8, M-5, M-1}
    (equivalently: k=2, k+1=M, k+5=M, k+8=M, k+9=M). -/
private def rcConfigList (M : Nat) : List Bool :=
  List.ofFn (fun k : Fin M => decide (k.val = 2 ∨ k.val + 1 = M ∨ k.val + 5 = M ∨ k.val + 8 = M ∨ k.val + 9 = M))

/-- Period cert: twoSpike(2, 14, 23) → 4 steps → rcConfigList(15). -/
private lemma twoSpike_to_RC_cert :
    caEvolve 4 (twoSpikeList 2 14 23) = rcConfigList 15 := by native_decide

/-- Period cert: rcConfigList(23) → 4 steps → rcConfigList(15). -/
private lemma RC_period_cert :
    caEvolve 4 (rcConfigList 23) = rcConfigList 15 := by native_decide

/-- Base: twoSpike(2, 6, 15) center after 7 steps = false. -/
private lemma rm_twoSpike_base_n6 :
    (caEvolve 7 (twoSpikeList 2 6 15)).getD 0 false = false := by native_decide

/-- Base: rcConfigList(15) center after 7 steps = false. -/
private lemma rm_RC_base :
    (caEvolve 7 (rcConfigList 15)).getD 0 false = false := by native_decide

-- ============================================================
-- Helper lemmas for parametric twoSpike→RC and RC period certs
-- ============================================================

private lemma rcConfigList_length (M : Nat) : (rcConfigList M).length = M := by
  simp [rcConfigList, List.length_ofFn]

private lemma rcConfigList_getD (M i : Nat) (hi : i < M) :
    (rcConfigList M).getD i false =
    decide (i = 2 ∨ i + 1 = M ∨ i + 5 = M ∨ i + 8 = M ∨ i + 9 = M) := by
  simp [rcConfigList, List.getD_eq_getElem?_getD, hi]

/-- rcConfigList drop getD: (rcConfigList M).drop s at position r gives
    decide(s+r = 2 ∨ s+r+1 = M ∨ s+r+5 = M ∨ s+r+8 = M ∨ s+r+9 = M),
    provided s+r < M. -/
private lemma rcConfigList_drop_getD (M s r : Nat) (h : s + r < M) :
    (List.drop s (rcConfigList M)).getD r false =
    decide (s + r = 2 ∨ s + r + 1 = M ∨ s + r + 5 = M ∨ s + r + 8 = M ∨ s + r + 9 = M) := by
  rw [show ((List.drop s (rcConfigList M)).getD r false) =
        (rcConfigList M).getD (s + r) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  exact rcConfigList_getD M (s + r) h

/-- Parametric twoSpike→RC cert for all j ≥ 1:
    caEvolve 4 (twoSpikeList 2 (8*j+6) (8*j+15)) = rcConfigList (8*j+7). -/
private lemma twoSpike_to_RC_all (j : Nat) (hj : 1 ≤ j) :
    caEvolve 4 (twoSpikeList 2 (8 * j + 6) (8 * j + 15)) = rcConfigList (8 * j + 7) := by
  apply List.ext_getElem
  · -- length equality
    have hlen : (caEvolve 4 (twoSpikeList 2 (8 * j + 6) (8 * j + 15))).length = 8 * j + 7 := by
      have := caEvolve_length_le 4 (twoSpikeList 2 (8 * j + 6) (8 * j + 15))
        (by rw [twoSpikeList_length]; omega)
      rw [twoSpikeList_length] at this; omega
    rw [hlen, rcConfigList_length]
  · intro i h1 h2
    -- Convert LHS to getD form
    rw [List.getElem_eq_getD false]
    -- Convert RHS to decide form
    have hrhs : (rcConfigList (8 * j + 7))[i]'h2 =
        decide (i = 2 ∨ i + 1 = 8 * j + 7 ∨ i + 5 = 8 * j + 7 ∨ i + 8 = 8 * j + 7 ∨ i + 9 = 8 * j + 7) := by
      simp only [rcConfigList, List.getElem_ofFn]
    rw [hrhs]
    -- LHS length bound
    have h1' : i < 8 * j + 7 := by
      have := caEvolve_length_le 4 (twoSpikeList 2 (8 * j + 6) (8 * j + 15))
        (by rw [twoSpikeList_length]; omega)
      rw [twoSpikeList_length] at this; omega
    -- Use caEvolve_getD_shift to move position i to drop
    rw [caEvolve_getD_shift 4 (twoSpikeList 2 (8 * j + 6) (8 * j + 15)) i]
    by_cases hiL : i ≤ 2
    · -- LEFT REGION: i ≤ 2. Window [i, i+8] ⊆ [0, 10], misses right spike at 8*j+6 ≥ 14.
      -- Use caEvolve_agree against (twoSpikeList 2 14 23).drop i
      have hagree : (caEvolve 4 ((twoSpikeList 2 (8 * j + 6) (8 * j + 15)).drop i)).getD 0 false =
                   (caEvolve 4 ((twoSpikeList 2 14 23).drop i)).getD 0 false := by
        apply caEvolve_agree 4
        · rw [List.length_drop, twoSpikeList_length]; omega
        · rw [List.length_drop, twoSpikeList_length]; omega
        · intro r hr
          -- Both dropped tapes at position r: decide(i+r = 2) (left spike only)
          -- Right spike at 8*j+6 ≥ 14 (j≥1), but i+r ≤ 2+8 = 10 < 14
          rw [show ((twoSpikeList 2 (8 * j + 6) (8 * j + 15)).drop i).getD r false =
                (twoSpikeList 2 (8 * j + 6) (8 * j + 15)).getD (i + r) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
          rw [show ((twoSpikeList 2 14 23).drop i).getD r false =
                (twoSpikeList 2 14 23).getD (i + r) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
          by_cases hir : i + r < 8 * j + 15
          · rw [twoSpikeList_getD 2 (8 * j + 6) (8 * j + 15) (i + r) (by omega)]
            by_cases hir2 : i + r < 23
            · rw [twoSpikeList_getD 2 14 23 (i + r) (by omega)]
              -- Both: decide(i+r = 2 ∨ i+r = 8*j+6) vs decide(i+r = 2 ∨ i+r = 14)
              -- Since i+r ≤ 10 and 8*j+6 ≥ 14: neither 8*j+6 nor 14 is hit (unless i+r=14, but ≤10)
              simp only [decide_eq_decide]
              constructor
              · rintro (h | h)
                · exact Or.inl h
                · omega  -- i+r ≤ 10, can't equal 8*j+6 ≥ 14
              · rintro (h | h)
                · exact Or.inl h
                · omega  -- i+r ≤ 10, can't equal 14
            · push_neg at hir2
              simp only [List.getD_eq_getElem?_getD, twoSpikeList, List.getElem?_ofFn]
              simp [Nat.not_lt.mpr hir2]
              -- but i+r ≤ 10 < 23, contradiction
              omega
          · push_neg at hir
            -- i+r ≥ 8*j+15 ≥ 23 (j≥1), so both tapes are out-of-bounds → getD = false = false
            simp only [List.getD_eq_getElem?_getD, twoSpikeList, List.getElem?_ofFn]
            have h1 : ¬(i + r < 8 * j + 15) := Nat.not_lt.mpr hir
            have h2 : ¬(i + r < 23) := by omega
            simp [h1, h2]
      rw [hagree]
      -- Now reduce to twoSpike_to_RC_cert via shift
      rw [← caEvolve_getD_shift 4 (twoSpikeList 2 14 23) i]
      have hcert_i : (caEvolve 4 (twoSpikeList 2 14 23)).getD i false =
                     (rcConfigList 15).getD i false := by
        rw [twoSpike_to_RC_cert]
      rw [hcert_i, rcConfigList_getD 15 i (by omega)]
      -- Both: decide(i=2 ∨ i+1=15 ∨ i+5=15 ∨ i+8=15 ∨ i+9=15) vs
      --       decide(i=2 ∨ i+1=8*j+7 ∨ i+5=8*j+7 ∨ i+8=8*j+7 ∨ i+9=8*j+7)
      -- For i ≤ 2: i+1 ≤ 3, i+5 ≤ 7, i+8 ≤ 10, i+9 ≤ 11 — neither 15 nor 8*j+7 reachable
      simp only [decide_eq_decide]
      constructor
      · rintro (h | h | h | h | h) <;> omega
      · rintro (h | h | h | h | h) <;> omega
    · push_neg at hiL
      by_cases hiR : 8 * j - 2 ≤ i
      · -- RIGHT REGION: 8*j-2 ≤ i ≤ 8*j+6.
        -- Let s = i - (8*j - 8) = i - 8*j + 8, which is in [6, 14] for j=1 and shifts correctly.
        -- Use caEvolve_agree against (twoSpikeList 2 14 23).drop s where s = i - 8*j + 8
        -- s = i + 8 - 8*j (Nat-safe: i ≥ 8*j-2 ensures i+8 ≥ 8*j+6 > 8*j)
        set s := i + 8 - 8 * j with hs_def
        have hs_range : 6 ≤ s ∧ s ≤ 14 := by omega
        have hagree : (caEvolve 4 ((twoSpikeList 2 (8 * j + 6) (8 * j + 15)).drop i)).getD 0 false =
                     (caEvolve 4 ((twoSpikeList 2 14 23).drop s)).getD 0 false := by
          apply caEvolve_agree 4
          · rw [List.length_drop, twoSpikeList_length]; omega
          · rw [List.length_drop, twoSpikeList_length]; omega
          · intro r hr
            -- Position i+r in first tape, s+r in second tape
            -- Left spike at 2: i ≥ 8*j-2 ≥ 6 > 2, and s ≥ 6 > 2. So 2 is behind both drops.
            -- Right spike: 8*j+6 in first, 14 in second. Relative position = 8-k where k=i-(8*j-2)
            rw [show ((twoSpikeList 2 (8 * j + 6) (8 * j + 15)).drop i).getD r false =
                  (twoSpikeList 2 (8 * j + 6) (8 * j + 15)).getD (i + r) false from by
              simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
            rw [show ((twoSpikeList 2 14 23).drop s).getD r false =
                  (twoSpikeList 2 14 23).getD (s + r) false from by
              simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
            -- i+r < 8*j+15 since i ≤ 8*j+6 and r ≤ 8
            have hir1 : i + r < 8 * j + 15 := by omega
            -- s+r < 23 since s ≤ 14 and r ≤ 8
            have hsr2 : s + r < 23 := by omega
            rw [twoSpikeList_getD 2 (8 * j + 6) (8 * j + 15) (i + r) (by omega)]
            rw [twoSpikeList_getD 2 14 23 (s + r) (by omega)]
            -- Both: decide(i+r=2 ∨ i+r=8*j+6) vs decide(s+r=2 ∨ s+r=14)
            -- i+r = 2 iff i+r=2; but i ≥ 8*j-2 ≥ 6 > 2, so i+r ≠ 2
            -- s+r = 2 iff s+r=2; but s ≥ 6, so s+r ≠ 2
            -- i+r = 8*j+6 iff s+r = 8*j+6 - 8*j + 8 = 14? No: i+r=8*j+6 iff s+r = 8*j+6 - (8*j-8) = 14. ✓
            simp only [decide_eq_decide]
            constructor
            · rintro (h | h)
              · omega  -- i+r ≠ 2
              · right; omega  -- i+r = 8*j+6 → s+r = 14
            · rintro (h | h)
              · omega  -- s+r ≠ 2
              · right; omega  -- s+r = 14 → i+r = 8*j+6
        rw [hagree]
        -- Now reduce to twoSpike_to_RC_cert via shift
        rw [← caEvolve_getD_shift 4 (twoSpikeList 2 14 23) s]
        -- (caEvolve 4 (twoSpikeList 2 14 23)).getD s = (rcConfigList 15).getD s
        have hcert_s : (caEvolve 4 (twoSpikeList 2 14 23)).getD s false =
                       (rcConfigList 15).getD s false := by
          rw [twoSpike_to_RC_cert]
        rw [hcert_s]
        -- Now show (rcConfigList 15).getD s false = decide(i=2 ∨ ...)
        -- s in [6,14], rcConfigList 15 has 1s at {2,6,7,10,14}
        -- The goal: decide(s=2 ∨ s+1=15 ∨ s+5=15 ∨ s+8=15 ∨ s+9=15) =
        --           decide(i=2 ∨ i+1=8*j+7 ∨ i+5=8*j+7 ∨ i+8=8*j+7 ∨ i+9=8*j+7)
        -- s = i-8*j+8: s+1=15 ↔ i-8*j+9=15 ↔ i=8*j+6 ↔ i+1=8*j+7 ✓
        -- s+5=15 ↔ i-8*j+13=15 ↔ i=8*j+2 ↔ i+5=8*j+7 ✓
        -- s+8=15 ↔ i-8*j+16=15 ↔ i=8*j-1 ↔ i+8=8*j+7 ✓
        -- s+9=15 ↔ i-8*j+17=15 ↔ i=8*j-2 ↔ i+9=8*j+7 ✓
        -- s=2 ↔ i=8*j-6; but i≥8*j-2, so s≠2. Also i=2 is impossible (i≥8*j-2≥6).
        rw [rcConfigList_getD 15 s (by omega)]
        simp only [decide_eq_decide]
        constructor
        · rintro (h | h | h | h | h) <;> omega
        · rintro (h | h | h | h | h) <;> omega
      · -- ZERO REGION: 3 ≤ i ≤ 8*j-3 (since ¬(i ≤ 2) and ¬(8*j-2 ≤ i))
        push_neg at hiR
        -- Window [i, i+8] ⊆ [3, 8*j+5], no spikes (left at 2 < i, right at 8*j+6 > i+8)
        -- So the dropped tape at positions 0..8 is all-false → caEvolve gives false
        have hzero : (caEvolve 4 ((twoSpikeList 2 (8 * j + 6) (8 * j + 15)).drop i)).getD 0 false =
                     false := by
          have heq : (caEvolve 4 ((twoSpikeList 2 (8 * j + 6) (8 * j + 15)).drop i)).getD 0 false =
                     (caEvolve 4 (List.replicate (8 * j + 15 - i) false)).getD 0 false := by
            apply caEvolve_agree 4
            · rw [List.length_drop, twoSpikeList_length]; omega
            · rw [List.length_replicate]; omega
            · intro r hr
              rw [show ((twoSpikeList 2 (8 * j + 6) (8 * j + 15)).drop i).getD r false =
                    (twoSpikeList 2 (8 * j + 6) (8 * j + 15)).getD (i + r) false from by
                simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
              rw [twoSpikeList_getD 2 (8 * j + 6) (8 * j + 15) (i + r) (by omega)]
              -- LHS = decide(i+r=2 ∨ i+r=8*j+6) = false (since i≥3 and i+r≤8*j+5<8*j+6)
              -- RHS = (replicate ...).getD r false = false
              have hrep : (List.replicate (8 * j + 15 - i) false).getD r false = false := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
                split_ifs <;> rfl
              rw [hrep]
              simp only [decide_eq_false_iff_not, not_or]
              exact ⟨by omega, by omega⟩
          rw [heq]
          apply caEvolve_allFalse
          intro k hk
          rw [List.length_replicate] at hk
          simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
          split_ifs <;> rfl
        rw [hzero]
        -- RHS is also false for 3 ≤ i ≤ 8*j-3
        symm
        simp only [decide_eq_false_iff_not]
        omega

/-- Parametric RC period cert for all j ≥ 1:
    caEvolve 4 (rcConfigList (8*j+15)) = rcConfigList (8*j+7). -/
private lemma RC_period_all (j : Nat) (hj : 1 ≤ j) :
    caEvolve 4 (rcConfigList (8 * j + 15)) = rcConfigList (8 * j + 7) := by
  apply List.ext_getElem
  · -- length equality
    have hlen : (caEvolve 4 (rcConfigList (8 * j + 15))).length = 8 * j + 7 := by
      have := caEvolve_length_le 4 (rcConfigList (8 * j + 15))
        (by rw [rcConfigList_length]; omega)
      rw [rcConfigList_length] at this; omega
    rw [hlen, rcConfigList_length]
  · intro i h1 h2
    rw [List.getElem_eq_getD false]
    have hrhs : (rcConfigList (8 * j + 7))[i]'h2 =
        decide (i = 2 ∨ i + 1 = 8 * j + 7 ∨ i + 5 = 8 * j + 7 ∨ i + 8 = 8 * j + 7 ∨ i + 9 = 8 * j + 7) := by
      simp only [rcConfigList, List.getElem_ofFn]
    rw [hrhs]
    have h1' : i < 8 * j + 7 := by
      have := caEvolve_length_le 4 (rcConfigList (8 * j + 15))
        (by rw [rcConfigList_length]; omega)
      rw [rcConfigList_length] at this; omega
    rw [caEvolve_getD_shift 4 (rcConfigList (8 * j + 15)) i]
    by_cases hiL : i ≤ 2
    · -- LEFT REGION: i ≤ 2
      have hagree : (caEvolve 4 ((rcConfigList (8 * j + 15)).drop i)).getD 0 false =
                   (caEvolve 4 ((rcConfigList 23).drop i)).getD 0 false := by
        apply caEvolve_agree 4
        · rw [List.length_drop, rcConfigList_length]; omega
        · rw [List.length_drop, rcConfigList_length]; omega
        · intro r hr
          rw [rcConfigList_drop_getD (8 * j + 15) i r (by omega)]
          rw [rcConfigList_drop_getD 23 i r (by omega)]
          -- decide(i+r=2 ∨ i+r+1=8*j+15 ∨ ...) vs decide(i+r=2 ∨ i+r+1=23 ∨ ...)
          -- For r ≤ 8, i ≤ 2: i+r ≤ 10 < 14 ≤ 8*j+6 (j≥1)
          -- i+r+1=8*j+15: i+r ≤ 10 vs 8*j+14 ≥ 22; NO
          -- i+r+5=8*j+15: i+r ≤ 10 vs 8*j+10 ≥ 18; NO
          -- i+r+8=8*j+15: i+r ≤ 10 vs 8*j+7 ≥ 15; NO (for j≥1, 8*j+7≥15>10)
          -- i+r+9=8*j+15: i+r ≤ 10 vs 8*j+6 ≥ 14; NO (>10)
          -- Similarly for 23: i+r+1=23 → i+r=22 > 10; NO. etc.
          simp only [decide_eq_decide]
          -- For r ≤ 8, i ≤ 2: i+r ≤ 10, so i+r+1 ≤ 11 < 15 ≤ 8*j+15, 23, etc.
          -- Only the i+r=2 condition can match on both sides.
          constructor
          · rintro (h | h | h | h | h) <;> first | (left; exact h) | omega
          · rintro (h | h | h | h | h) <;> first | (left; exact h) | omega
      rw [hagree, ← caEvolve_getD_shift 4 (rcConfigList 23) i]
      have hcert_i : (caEvolve 4 (rcConfigList 23)).getD i false =
                     (rcConfigList 15).getD i false := by
        rw [RC_period_cert]
      rw [hcert_i, rcConfigList_getD 15 i (by omega)]
      simp only [decide_eq_decide]
      constructor
      · rintro (h | h | h | h | h) <;> omega
      · rintro (h | h | h | h | h) <;> omega
    · push_neg at hiL
      by_cases hiR : 8 * j - 2 ≤ i
      · -- RIGHT REGION: 8*j-2 ≤ i ≤ 8*j+6
        -- s = i + 8 - 8*j (Nat-safe: i ≥ 8*j-2 ensures i+8 ≥ 8*j+6 > 8*j)
        set s := i + 8 - 8 * j with hs_def
        have hs_range : 6 ≤ s ∧ s ≤ 14 := by omega
        have hagree : (caEvolve 4 ((rcConfigList (8 * j + 15)).drop i)).getD 0 false =
                     (caEvolve 4 ((rcConfigList 23).drop s)).getD 0 false := by
          apply caEvolve_agree 4
          · rw [List.length_drop, rcConfigList_length]; omega
          · rw [List.length_drop, rcConfigList_length]; omega
          · intro r hr
            rw [rcConfigList_drop_getD (8 * j + 15) i r (by omega)]
            rw [rcConfigList_drop_getD 23 s r (by omega)]
            -- Both have form decide(X=2 ∨ X+1=M ∨ X+5=M ∨ X+8=M ∨ X+9=M)
            -- X1 = i+r, M1 = 8*j+15;  X2 = s+r, M2 = 23
            -- i+r = 2 ↔ impossible (i≥8*j-2≥6>2)
            -- s+r = 2 ↔ impossible (s≥6>2)
            -- i+r+1=8*j+15 ↔ i+r=8*j+14 ↔ s+r=8*j+14-8*j+8=22 ↔ s+r+1=23 ✓
            -- i+r+5=8*j+15 ↔ i+r=8*j+10 ↔ s+r=18 ↔ s+r+5=23 ✓
            -- i+r+8=8*j+15 ↔ i+r=8*j+7 ↔ s+r=15 ↔ s+r+8=23 ✓
            -- i+r+9=8*j+15 ↔ i+r=8*j+6 ↔ s+r=14 ↔ s+r+9=23 ✓
            simp only [decide_eq_decide]
            constructor <;> rintro (h | h | h | h | h) <;> omega
        rw [hagree, ← caEvolve_getD_shift 4 (rcConfigList 23) s]
        have hcert_s : (caEvolve 4 (rcConfigList 23)).getD s false =
                       (rcConfigList 15).getD s false := by
          rw [RC_period_cert]
        rw [hcert_s, rcConfigList_getD 15 s (by omega)]
        -- (rcConfigList 15).getD s false = decide(s=2 ∨ s+1=15 ∨ s+5=15 ∨ s+8=15 ∨ s+9=15)
        -- s = i - 8*j + 8, i ∈ [8*j-2, 8*j+6] → s ∈ [6, 14]
        -- s=2 impossible; s+1=15 ↔ i+1=8*j+7; etc.
        simp only [decide_eq_decide]
        constructor <;> rintro (h | h | h | h | h) <;> omega
      · -- ZERO REGION: 3 ≤ i ≤ 8*j-3
        push_neg at hiR
        have hzero : (caEvolve 4 ((rcConfigList (8 * j + 15)).drop i)).getD 0 false = false := by
          have heq : (caEvolve 4 ((rcConfigList (8 * j + 15)).drop i)).getD 0 false =
                     (caEvolve 4 (List.replicate (8 * j + 15 - i) false)).getD 0 false := by
            apply caEvolve_agree 4
            · rw [List.length_drop, rcConfigList_length]; omega
            · rw [List.length_replicate]; omega
            · intro r hr
              rw [rcConfigList_drop_getD (8 * j + 15) i r (by omega)]
              -- i+r ≠ 2 (i ≥ 3), and no right cluster reached (i+r ≤ 8*j+5 < 8*j+6)
              -- Specifically: i+r+1 ≠ 8*j+15 (i+r ≤ 8*j+5 < 8*j+14)
              have hrep : (List.replicate (8 * j + 15 - i) false).getD r false = false := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
                split_ifs <;> rfl
              rw [hrep]
              simp only [decide_eq_false_iff_not, not_or]
              exact ⟨by omega, by omega, by omega, by omega, by omega⟩
          rw [heq]
          apply caEvolve_allFalse
          intro k hk
          rw [List.length_replicate] at hk
          simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
          split_ifs <;> rfl
        rw [hzero]
        symm
        simp only [decide_eq_false_iff_not]
        omega

/-- For n'≡2 mod 4, n'≥6: twoSpike(2, 2*(n'+1)-8, N) gives center = false.
    Proved by joint induction with rcConfigList using the 4-step period chain. -/
private lemma rm_twoSpike_mod4_2 (n' : Nat) (hn' : 6 ≤ n') (hmod4 : n' % 4 = 2) :
    (caEvolve (n' + 1) (twoSpikeList 2 (2 * (n' + 1) - 8) (2 * (n' + 1) + 1))).getD 0 false =
    false := by
  -- Write n' = 4*j+2 for j ≥ 1.  We prove A(j) and B(j) jointly by induction on j.
  -- A(j): (caEvolve (4*j+3) (twoSpikeList 2 (8*j-2) (8*j+7))).getD 0 false = false
  -- B(j): (caEvolve (4*j+3) (rcConfigList (8*j+7))).getD 0 false = false
  -- Base j=1: A(1) = rm_twoSpike_base_n6, B(1) = rm_RC_base
  -- Step: A(j+1) follows from B(j) via twoSpike_to_RC_cert + caEvolve_add
  --       B(j+1) follows from B(j) via RC_period_cert + caEvolve_add
  -- Here n' = 4*j+2, so j = (n'-2)/4.
  -- We massage n' back to the induction form after the joint proof.
  suffices h : ∀ j : Nat, 1 ≤ j →
      ((caEvolve (4*j+3) (twoSpikeList 2 (8*j-2) (8*j+7))).getD 0 false = false ∧
       (caEvolve (4*j+3) (rcConfigList (8*j+7))).getD 0 false = false) by
    -- n' = 4*j+2 for j = (n'-2)/4
    have hj : n' = 4 * ((n' - 2) / 4) + 2 := by omega
    have hjge : 1 ≤ (n' - 2) / 4 := by omega
    set k := (n' - 2) / 4 with hk_def
    obtain ⟨hA, _⟩ := h k hjge
    rw [show n' + 1 = 4 * k + 3 from by omega,
        show 2 * (4 * k + 3) - 8 = 8 * k - 2 from by omega,
        show 2 * (4 * k + 3) + 1 = 8 * k + 7 from by omega]
    exact hA
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    cases Nat.eq_or_lt_of_le hj with
    | inl h =>
      -- j+1 = 1, so j = 0 — base case
      have hj0 : j = 0 := by omega
      subst hj0
      exact ⟨rm_twoSpike_base_n6, rm_RC_base⟩
    | inr h =>
      -- j+1 ≥ 2, inductive step from j ≥ 1
      have hjge1 : 1 ≤ j := by omega
      obtain ⟨_hAj, hBj⟩ := ih hjge1
      constructor
      · -- A(j+1): use caEvolve_add to split 4*(j+1)+3 = (4*j+3) + 4, then twoSpike_to_RC_cert
        have hstep : (caEvolve (4 * (j + 1) + 3) (twoSpikeList 2 (8 * (j + 1) - 2) (8 * (j + 1) + 7))).getD 0 false =
                     (caEvolve (4 * j + 3) (caEvolve 4 (twoSpikeList 2 (8 * (j + 1) - 2) (8 * (j + 1) + 7)))).getD 0 false := by
          rw [show 4 * (j + 1) + 3 = (4 * j + 3) + 4 from by ring]
          rw [caEvolve_add]
        rw [hstep]
        -- Now need: caEvolve 4 (twoSpikeList 2 (8*(j+1)-2) (8*(j+1)+7)) = rcConfigList (8*j+7)
        -- This is the parametric version of twoSpike_to_RC_cert (which handles j+1=2, i.e., j=1)
        -- For j ≥ 1: 8*(j+1)-2 = 8j+6, 8*(j+1)+7 = 8j+15, result = rcConfigList(8j+7)
        --
        -- [SORRY] Parametric twoSpike→RC cert.
        -- Statement: caEvolve 4 (twoSpikeList 2 (8*j+6) (8*j+15)) = rcConfigList (8*j+7)
        -- Proof strategy: List.ext_getD position-by-position, three-region independence:
        --   • LEFT region (i ∈ 0..2): window i..i+8 contains left spike at 2 but NOT right
        --     spike at 8*j+6 (since i+8 ≤ 10 < 8*j+6 for j ≥ 1). Apply caEvolve_agree 4
        --     against twoSpikeList 2 14 23 (same left spike, far right spike), then use
        --     twoSpike_to_RC_cert + rcConfigList agree at these positions.
        --   • ZERO region (i ∈ 3..8*j-3): window i..i+8 contains no spikes at all
        --     (left spike at 2 < i, right spike at 8*j+6 > i+8). caEvolve 4 of all-false
        --     window = false; rcConfigList (8*j+7) at i = false. ✓
        --   • RIGHT region (i ∈ 8*j-2..8*j+6): window contains right spike at 8*j+6.
        --     Left spike at 2 < i (since i ≥ 8*j-2 ≥ 6 for j ≥ 1). Apply caEvolve_agree 4
        --     against spikeAtList (8*j+6) (8*j+15) shifted by i, then use shift equivalence
        --     to reduce to twoSpike_to_RC_cert right-region positions.
        -- Infrastructure needed: caEvolve_agree, drop_twoSpike_agree, caEvolve_getD_shift,
        --   twoSpikeList_allFalse_outside_spikes, caEvolve_allFalse_zero.
        -- Reference cert twoSpike_to_RC_cert handles j=1 (size 23); pattern holds for all j≥1.
        suffices hparam : caEvolve 4 (twoSpikeList 2 (8 * (j + 1) - 2) (8 * (j + 1) + 7)) = rcConfigList (8 * j + 7) by
          rw [hparam]; exact hBj
        have heq : 8 * (j + 1) - 2 = 8 * j + 6 := by omega
        have heq2 : 8 * (j + 1) + 7 = 8 * j + 15 := by omega
        rw [heq, heq2]
        exact twoSpike_to_RC_all j hjge1
      · -- B(j+1): use caEvolve_add to split, then RC_period_cert
        have hstep : (caEvolve (4 * (j + 1) + 3) (rcConfigList (8 * (j + 1) + 7))).getD 0 false =
                     (caEvolve (4 * j + 3) (caEvolve 4 (rcConfigList (8 * (j + 1) + 7)))).getD 0 false := by
          rw [show 4 * (j + 1) + 3 = (4 * j + 3) + 4 from by ring]
          rw [caEvolve_add]
        rw [hstep]
        -- Need: caEvolve 4 (rcConfigList (8*(j+1)+7)) = rcConfigList (8*j+7)
        -- Parametric version of RC_period_cert
        --
        -- [SORRY] Parametric RC period cert.
        -- Statement: caEvolve 4 (rcConfigList (8*(j+1)+7)) = rcConfigList (8*j+7)
        --   i.e., caEvolve 4 (rcConfigList (8*j+15)) = rcConfigList (8*j+7)
        -- rcConfigList M has 1s at positions {2, M-9, M-8, M-5, M-1}.
        -- For M = 8*j+15: 1s at {2, 8*j+6, 8*j+7, 8*j+10, 8*j+14}.
        -- Proof strategy: same three-region independence as above.
        --   • LEFT cluster {pos 2}: window 0..10 sees only the left 1-bit. For j ≥ 2
        --     the right cluster starts at 8*j+6 ≥ 22 > 10; for j=1, rcConfigList(23)
        --     is handled by RC_period_cert (native_decide).
        --   • ZERO region (i ∈ 3..8*j-3): no 1-bits in window → output 0.
        --     rcConfigList(8*j+7) at these positions = 0. ✓
        --   • RIGHT cluster {8*j+6, 8*j+7, 8*j+10, 8*j+14}: for i ∈ 8*j-2..8*j+6,
        --     window sees the right cluster but NOT pos 2 (since i ≥ 8*j-2 ≥ 6 > 2+8=10
        --     fails for small i; for j≥2 i≥14>10 ✓; j=1 use cert directly).
        --     Apply caEvolve_agree against rcConfigList 23 (right cluster shifted), then
        --     RC_period_cert gives the result at positions 6..14.
        -- Infrastructure needed: same as above plus rcConfigList_getD,
        --   caEvolve_agree, List.ext_getD.
        -- Reference cert RC_period_cert handles j=1 (M=23→15). Pattern holds for all j≥1.
        suffices hparam : caEvolve 4 (rcConfigList (8 * (j + 1) + 7)) = rcConfigList (8 * j + 7) by
          rw [hparam]; exact hBj
        have heq : 8 * (j + 1) + 7 = 8 * j + 15 := by omega
        rw [heq]
        exact RC_period_all j hjge1

-- ============================================================
-- ts4ConfigList / ts3ConfigList: right-cluster intermediate configs
-- ts4ConfigList M: ones at {M-9, M-8, M-5, M-1}
-- ts3ConfigList M: ones at {M-9, M-8, M-5} (no M-1 spike)
-- Used for the period-4 reduction of the right-mirror spike/twoSpike.
-- ============================================================

/-- Right-cluster-4 config: ones at {M-9, M-8, M-5, M-1}. -/
private def ts4ConfigList (M : Nat) : List Bool :=
  List.ofFn (fun k : Fin M =>
    decide (k.val + 1 = M ∨ k.val + 5 = M ∨ k.val + 8 = M ∨ k.val + 9 = M))

/-- Right-cluster-3 config: ones at {M-9, M-8, M-5} (no M-1). -/
private def ts3ConfigList (M : Nat) : List Bool :=
  List.ofFn (fun k : Fin M =>
    decide (k.val + 5 = M ∨ k.val + 8 = M ∨ k.val + 9 = M))

private lemma ts4ConfigList_length (M : Nat) : (ts4ConfigList M).length = M := by
  simp [ts4ConfigList, List.length_ofFn]

private lemma ts3ConfigList_length (M : Nat) : (ts3ConfigList M).length = M := by
  simp [ts3ConfigList, List.length_ofFn]

private lemma ts4ConfigList_getD (M i : Nat) (hi : i < M) :
    (ts4ConfigList M).getD i false =
    decide (i + 1 = M ∨ i + 5 = M ∨ i + 8 = M ∨ i + 9 = M) := by
  simp [ts4ConfigList, List.getD_eq_getElem?_getD, hi]

private lemma ts3ConfigList_getD (M i : Nat) (hi : i < M) :
    (ts3ConfigList M).getD i false =
    decide (i + 5 = M ∨ i + 8 = M ∨ i + 9 = M) := by
  simp [ts3ConfigList, List.getD_eq_getElem?_getD, hi]

private lemma ts4ConfigList_drop_getD (M s r : Nat) (h : s + r < M) :
    (List.drop s (ts4ConfigList M)).getD r false =
    decide (s + r + 1 = M ∨ s + r + 5 = M ∨ s + r + 8 = M ∨ s + r + 9 = M) := by
  rw [show ((List.drop s (ts4ConfigList M)).getD r false) =
        (ts4ConfigList M).getD (s + r) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  exact ts4ConfigList_getD M (s + r) h

private lemma ts3ConfigList_drop_getD (M s r : Nat) (h : s + r < M) :
    (List.drop s (ts3ConfigList M)).getD r false =
    decide (s + r + 5 = M ∨ s + r + 8 = M ∨ s + r + 9 = M) := by
  rw [show ((List.drop s (ts3ConfigList M)).getD r false) =
        (ts3ConfigList M).getD (s + r) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  exact ts3ConfigList_getD M (s + r) h

-- Base certs: M=17 (spike/twoSpike) → M-8=9 (ts4/ts3), verified by native_decide
private lemma rm_cert_spike_to_ts4 :
    caEvolve 4 (spikeAtList 8 17) = ts4ConfigList 9 := by native_decide

private lemma rm_cert_ts4_period :
    caEvolve 4 (ts4ConfigList 17) = ts4ConfigList 9 := by native_decide

private lemma rm_cert_twoSpike_to_ts3 :
    caEvolve 4 (twoSpikeList 8 16 17) = ts3ConfigList 9 := by native_decide

private lemma rm_cert_ts3_period :
    caEvolve 4 (ts3ConfigList 17) = ts3ConfigList 9 := by native_decide

-- Additional base certs for the top-level result values (native_decide for small T)
-- n'=4 (≡0 mod 4): T=5, spike at 2 in tape 11 → center = true
private lemma rm_spike_base_k1 :
    (caEvolve 5 (spikeAtList 2 11)).getD 0 false = true := by native_decide
-- ts4Config(11) center after 5 steps = true
private lemma rm_ts4_base_k1 :
    (caEvolve 5 (ts4ConfigList 11)).getD 0 false = true := by native_decide
-- n'=3 (≡3 mod 4): T=4, twoSpike at {0,8} in tape 9 → center = false
private lemma rm_twoSpike_base_k0 :
    (caEvolve 4 (twoSpikeList 0 8 9)).getD 0 false = false := by native_decide
-- ts3Config(9) center after 4 steps = false
private lemma rm_ts3_base_k0 :
    (caEvolve 4 (ts3ConfigList 9)).getD 0 false = false := by native_decide

-- ============================================================
-- Parametric period certs for ts4 and ts3
-- ============================================================

/-- Parametric cert: spike(M-9,M) →4 steps→ ts4Config(M-8), for all M≥17. -/
private lemma rm_spike_to_ts4_all (M : Nat) (hM : M ≥ 17) :
    caEvolve 4 (spikeAtList (M - 9) M) = ts4ConfigList (M - 8) := by
  apply List.ext_getElem
  · have hlen : (caEvolve 4 (spikeAtList (M - 9) M)).length = M - 8 := by
      have := caEvolve_length_le 4 (spikeAtList (M - 9) M) (by rw [spikeAtList_length]; omega)
      rw [spikeAtList_length] at this; omega
    rw [hlen, ts4ConfigList_length]
  · intro i h1 h2
    rw [List.getElem_eq_getD false]
    have hiM8 : i < M - 8 := by rw [ts4ConfigList_length] at h2; exact h2
    have hrhs : (ts4ConfigList (M - 8))[i]'h2 =
        decide (i + 1 = M - 8 ∨ i + 5 = M - 8 ∨ i + 8 = M - 8 ∨ i + 9 = M - 8) := by
      simp only [ts4ConfigList, List.getElem_ofFn]
    rw [hrhs]
    rw [caEvolve_getD_shift 4 (spikeAtList (M - 9) M) i]
    -- Case split: left region vs right region (no zero region, only right cluster)
    by_cases hiR : M - 17 ≤ i
    · -- RIGHT REGION: i ≥ M-17, window [i, i+8] overlaps the spike at M-9
      set s := i - (M - 17) with hs_def
      have hs_range : s ≤ 8 := by omega
      have hagree : (caEvolve 4 ((spikeAtList (M - 9) M).drop i)).getD 0 false =
                   (caEvolve 4 ((spikeAtList 8 17).drop s)).getD 0 false := by
        apply caEvolve_agree 4
        · rw [List.length_drop, spikeAtList_length]; omega
        · rw [List.length_drop, spikeAtList_length]; omega
        · intro r hr
          rw [show ((spikeAtList (M - 9) M).drop i).getD r false =
                (spikeAtList (M - 9) M).getD (i + r) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
          rw [show ((spikeAtList 8 17).drop s).getD r false =
                (spikeAtList 8 17).getD (s + r) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
          -- i = s + (M-17), so i+r = s+r + (M-17)
          -- s+r ≤ 16 (since s ≤ 8 and r ≤ 8), so i+r ≤ M-1 < M
          have hir : i + r < M := by omega
          rw [spikeAtList_getD (M - 9) M (i + r) (by omega)]
          -- For (spikeAtList 8 17): need s+r < 17; since s ≤ 8, r ≤ 8 → s+r ≤ 16 < 17
          have hsr : s + r < 17 := by omega
          rw [spikeAtList_getD 8 17 (s + r) (by omega)]
          simp only [decide_eq_decide]; omega
      rw [hagree, ← caEvolve_getD_shift 4 (spikeAtList 8 17) s, rm_cert_spike_to_ts4]
      rw [ts4ConfigList_getD 9 s (by omega)]
      simp only [decide_eq_decide]; omega
    · -- LEFT REGION: i < M-17, window [i, i+8] misses the spike at M-9
      -- Use caEvolve_agree 4 against a short all-false tape (window 0..8 is all false)
      push_neg at hiR
      have hzero : (caEvolve 4 ((spikeAtList (M - 9) M).drop i)).getD 0 false = false := by
        have heq : (caEvolve 4 ((spikeAtList (M - 9) M).drop i)).getD 0 false =
                   (caEvolve 4 (List.replicate (M - i) false)).getD 0 false := by
          apply caEvolve_agree 4
          · rw [List.length_drop, spikeAtList_length]; omega
          · rw [List.length_replicate]; omega
          · intro r hr
            rw [show ((spikeAtList (M - 9) M).drop i).getD r false =
                  (spikeAtList (M - 9) M).getD (i + r) false from by
              simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
            have hrep : (List.replicate (M - i) false).getD r false = false := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
              split_ifs <;> rfl
            rw [hrep, spikeAtList_getD (M - 9) M (i + r) (by omega)]
            -- spike position M-9 > i+8, so i+r ≠ M-9 for r ≤ 8
            simp only [decide_eq_false_iff_not]; omega
        rw [heq]
        apply caEvolve_allFalse
        intro k hk
        rw [List.length_replicate] at hk
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      rw [hzero]
      symm; simp only [decide_eq_false_iff_not, not_or]; omega

/-- Parametric cert: ts4Config(M) →4 steps→ ts4Config(M-8), for all M≥17. -/
private lemma rm_ts4_period_all (M : Nat) (hM : M ≥ 17) :
    caEvolve 4 (ts4ConfigList M) = ts4ConfigList (M - 8) := by
  apply List.ext_getElem
  · have hlen : (caEvolve 4 (ts4ConfigList M)).length = M - 8 := by
      have := caEvolve_length_le 4 (ts4ConfigList M) (by rw [ts4ConfigList_length]; omega)
      rw [ts4ConfigList_length] at this; omega
    rw [hlen, ts4ConfigList_length]
  · intro i h1 h2
    rw [List.getElem_eq_getD false]
    have hiM8 : i < M - 8 := by rw [ts4ConfigList_length] at h2; exact h2
    have hrhs : (ts4ConfigList (M - 8))[i]'h2 =
        decide (i + 1 = M - 8 ∨ i + 5 = M - 8 ∨ i + 8 = M - 8 ∨ i + 9 = M - 8) := by
      simp only [ts4ConfigList, List.getElem_ofFn]
    rw [hrhs]
    rw [caEvolve_getD_shift 4 (ts4ConfigList M) i]
    by_cases hiR : M - 17 ≤ i
    · set s := i - (M - 17) with hs_def
      have hs_range : s ≤ 8 := by omega
      have hagree : (caEvolve 4 ((ts4ConfigList M).drop i)).getD 0 false =
                   (caEvolve 4 ((ts4ConfigList 17).drop s)).getD 0 false := by
        apply caEvolve_agree 4
        · rw [List.length_drop, ts4ConfigList_length]; omega
        · rw [List.length_drop, ts4ConfigList_length]; omega
        · intro r hr
          rw [ts4ConfigList_drop_getD M i r (by omega)]
          rw [ts4ConfigList_drop_getD 17 s r (by omega)]
          simp only [decide_eq_decide]; omega
      rw [hagree, ← caEvolve_getD_shift 4 (ts4ConfigList 17) s, rm_cert_ts4_period]
      rw [ts4ConfigList_getD 9 s (by omega)]
      simp only [decide_eq_decide]; omega
    · push_neg at hiR
      have hzero : (caEvolve 4 ((ts4ConfigList M).drop i)).getD 0 false = false := by
        have heq : (caEvolve 4 ((ts4ConfigList M).drop i)).getD 0 false =
                   (caEvolve 4 (List.replicate (M - i) false)).getD 0 false := by
          apply caEvolve_agree 4
          · rw [List.length_drop, ts4ConfigList_length]; omega
          · rw [List.length_replicate]; omega
          · intro r hr
            rw [ts4ConfigList_drop_getD M i r (by omega)]
            have hrep : (List.replicate (M - i) false).getD r false = false := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
              split_ifs <;> rfl
            rw [hrep]
            simp only [decide_eq_false_iff_not, not_or]; omega
        rw [heq]
        apply caEvolve_allFalse
        intro k hk
        rw [List.length_replicate] at hk
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      rw [hzero]
      symm; simp only [decide_eq_false_iff_not, not_or]; omega

/-- Parametric cert: twoSpike(M-9,M-1,M) →4 steps→ ts3Config(M-8), for all M≥17. -/
private lemma rm_twoSpike_to_ts3_all (M : Nat) (hM : M ≥ 17) :
    caEvolve 4 (twoSpikeList (M - 9) (M - 1) M) = ts3ConfigList (M - 8) := by
  apply List.ext_getElem
  · have hlen : (caEvolve 4 (twoSpikeList (M - 9) (M - 1) M)).length = M - 8 := by
      have := caEvolve_length_le 4 (twoSpikeList (M - 9) (M - 1) M)
        (by rw [twoSpikeList_length]; omega)
      rw [twoSpikeList_length] at this; omega
    rw [hlen, ts3ConfigList_length]
  · intro i h1 h2
    rw [List.getElem_eq_getD false]
    have hiM8 : i < M - 8 := by rw [ts3ConfigList_length] at h2; exact h2
    have hrhs : (ts3ConfigList (M - 8))[i]'h2 =
        decide (i + 5 = M - 8 ∨ i + 8 = M - 8 ∨ i + 9 = M - 8) := by
      simp only [ts3ConfigList, List.getElem_ofFn]
    rw [hrhs]
    rw [caEvolve_getD_shift 4 (twoSpikeList (M - 9) (M - 1) M) i]
    by_cases hiR : M - 17 ≤ i
    · set s := i - (M - 17) with hs_def
      have hs_range : s ≤ 8 := by omega
      have hagree : (caEvolve 4 ((twoSpikeList (M - 9) (M - 1) M).drop i)).getD 0 false =
                   (caEvolve 4 ((twoSpikeList 8 16 17).drop s)).getD 0 false := by
        apply caEvolve_agree 4
        · rw [List.length_drop, twoSpikeList_length]; omega
        · rw [List.length_drop, twoSpikeList_length]; omega
        · intro r hr
          rw [show ((twoSpikeList (M - 9) (M - 1) M).drop i).getD r false =
                (twoSpikeList (M - 9) (M - 1) M).getD (i + r) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
          rw [show ((twoSpikeList 8 16 17).drop s).getD r false =
                (twoSpikeList 8 16 17).getD (s + r) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
          -- s ≤ 8, r ≤ 8 → s+r ≤ 16 < 17, and i = s+(M-17), so i+r = s+r+(M-17) ≤ M-1 < M
          have hir : i + r < M := by omega
          have hsr : s + r < 17 := by omega
          rw [twoSpikeList_getD (M - 9) (M - 1) M (i + r) (by omega)]
          rw [twoSpikeList_getD 8 16 17 (s + r) (by omega)]
          simp only [decide_eq_decide]; omega
      rw [hagree, ← caEvolve_getD_shift 4 (twoSpikeList 8 16 17) s, rm_cert_twoSpike_to_ts3]
      rw [ts3ConfigList_getD 9 s (by omega)]
      simp only [decide_eq_decide]; omega
    · push_neg at hiR
      have hzero : (caEvolve 4 ((twoSpikeList (M - 9) (M - 1) M).drop i)).getD 0 false = false := by
        have heq : (caEvolve 4 ((twoSpikeList (M - 9) (M - 1) M).drop i)).getD 0 false =
                   (caEvolve 4 (List.replicate (M - i) false)).getD 0 false := by
          apply caEvolve_agree 4
          · rw [List.length_drop, twoSpikeList_length]; omega
          · rw [List.length_replicate]; omega
          · intro r hr
            rw [show ((twoSpikeList (M - 9) (M - 1) M).drop i).getD r false =
                  (twoSpikeList (M - 9) (M - 1) M).getD (i + r) false from by
              simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
            have hrep : (List.replicate (M - i) false).getD r false = false := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
              split_ifs <;> rfl
            rw [hrep, twoSpikeList_getD (M - 9) (M - 1) M (i + r) (by omega)]
            simp only [decide_eq_false_iff_not, not_or]; omega
        rw [heq]
        apply caEvolve_allFalse
        intro k hk
        rw [List.length_replicate] at hk
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      rw [hzero]
      symm; simp only [decide_eq_false_iff_not, not_or]; omega

/-- Parametric cert: ts3Config(M) →4 steps→ ts3Config(M-8), for all M≥17. -/
private lemma rm_ts3_period_all (M : Nat) (hM : M ≥ 17) :
    caEvolve 4 (ts3ConfigList M) = ts3ConfigList (M - 8) := by
  apply List.ext_getElem
  · have hlen : (caEvolve 4 (ts3ConfigList M)).length = M - 8 := by
      have := caEvolve_length_le 4 (ts3ConfigList M) (by rw [ts3ConfigList_length]; omega)
      rw [ts3ConfigList_length] at this; omega
    rw [hlen, ts3ConfigList_length]
  · intro i h1 h2
    rw [List.getElem_eq_getD false]
    have hiM8 : i < M - 8 := by rw [ts3ConfigList_length] at h2; exact h2
    have hrhs : (ts3ConfigList (M - 8))[i]'h2 =
        decide (i + 5 = M - 8 ∨ i + 8 = M - 8 ∨ i + 9 = M - 8) := by
      simp only [ts3ConfigList, List.getElem_ofFn]
    rw [hrhs]
    rw [caEvolve_getD_shift 4 (ts3ConfigList M) i]
    by_cases hiR : M - 17 ≤ i
    · set s := i - (M - 17) with hs_def
      have hs_range : s ≤ 8 := by omega
      have hagree : (caEvolve 4 ((ts3ConfigList M).drop i)).getD 0 false =
                   (caEvolve 4 ((ts3ConfigList 17).drop s)).getD 0 false := by
        apply caEvolve_agree 4
        · rw [List.length_drop, ts3ConfigList_length]; omega
        · rw [List.length_drop, ts3ConfigList_length]; omega
        · intro r hr
          rw [ts3ConfigList_drop_getD M i r (by omega)]
          rw [ts3ConfigList_drop_getD 17 s r (by omega)]
          simp only [decide_eq_decide]; omega
      rw [hagree, ← caEvolve_getD_shift 4 (ts3ConfigList 17) s, rm_cert_ts3_period]
      rw [ts3ConfigList_getD 9 s (by omega)]
      simp only [decide_eq_decide]; omega
    · push_neg at hiR
      have hzero : (caEvolve 4 ((ts3ConfigList M).drop i)).getD 0 false = false := by
        have heq : (caEvolve 4 ((ts3ConfigList M).drop i)).getD 0 false =
                   (caEvolve 4 (List.replicate (M - i) false)).getD 0 false := by
          apply caEvolve_agree 4
          · rw [List.length_drop, ts3ConfigList_length]; omega
          · rw [List.length_replicate]; omega
          · intro r hr
            rw [ts3ConfigList_drop_getD M i r (by omega)]
            have hrep : (List.replicate (M - i) false).getD r false = false := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
              split_ifs <;> rfl
            rw [hrep]
            simp only [decide_eq_false_iff_not, not_or]; omega
        rw [heq]
        apply caEvolve_allFalse
        intro k hk
        rw [List.length_replicate] at hk
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      rw [hzero]
      symm; simp only [decide_eq_false_iff_not, not_or]; omega

-- ============================================================
-- Period-4 proofs for rm_spike_mod4_0_true and rm_twoSpike_mod4_3_false
-- Joint induction: A(k) + B(k) proved simultaneously
-- ============================================================

/-- For n'≡0 mod 4, n'≥3087: spike at m_right = 2*(n'+1)-8 gives true
    (contradicts hcase hypothesis, so SubcaseB cannot fire). -/
private lemma rm_spike_mod4_0_true (n' : Nat) (hn' : 3087 ≤ n') (hmod4 : n' % 4 = 0) :
    (caEvolve (n' + 1) (spikeAtList (2 * (n' + 1) - 8) (2 * (n' + 1) + 1))).getD 0 false = true := by
  -- Write n' = 4*k, T = 4*k+1. Joint induction on k ≥ 1:
  -- A(k): (caEvolve (4*k+1) (spikeAtList (8*k-6) (8*k+3))).getD 0 false = true
  -- B(k): (caEvolve (4*k+1) (ts4ConfigList (8*k+3))).getD 0 false = true
  -- Step A(k+1) from B(k): caEvolve(4*k+5) spike(8k+2,8k+11) = caEvolve(4*k+1) ts4(8k+3) via cert1
  -- Step B(k+1) from B(k): caEvolve(4*k+5) ts4(8k+11) = caEvolve(4*k+1) ts4(8k+3) via cert2
  suffices h : ∀ k : Nat, k ≥ 1 →
      ((caEvolve (4 * k + 1) (spikeAtList (8 * k - 6) (8 * k + 3))).getD 0 false = true ∧
       (caEvolve (4 * k + 1) (ts4ConfigList (8 * k + 3))).getD 0 false = true) by
    have hk : n' = 4 * (n' / 4) := by omega
    have hkge : 1 ≤ n' / 4 := by omega
    set k := n' / 4 with hk_def
    obtain ⟨hA, _⟩ := h k hkge
    rw [show n' + 1 = 4 * k + 1 from by omega,
        show 2 * (4 * k + 1) - 8 = 8 * k - 6 from by omega,
        show 2 * (4 * k + 1) + 1 = 8 * k + 3 from by omega]
    exact hA
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    cases Nat.eq_or_lt_of_le hk with
    | inl h =>
      have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨rm_spike_base_k1, rm_ts4_base_k1⟩
    | inr h =>
      have hkge1 : 1 ≤ k := by omega
      obtain ⟨_, hBk⟩ := ih hkge1
      constructor
      · -- A(k+1): split off 4 steps, apply cert1 to get ts4Config(8k+3)
        have hstep : (caEvolve (4 * (k + 1) + 1) (spikeAtList (8 * (k + 1) - 6) (8 * (k + 1) + 3))).getD 0 false =
                     (caEvolve (4 * k + 1) (caEvolve 4 (spikeAtList (8 * (k + 1) - 6) (8 * (k + 1) + 3)))).getD 0 false := by
          rw [show 4 * (k + 1) + 1 = (4 * k + 1) + 4 from by ring, caEvolve_add]
        rw [hstep]
        -- caEvolve 4 (spikeAtList (8k+2) (8k+11)) = ts4Config(8k+3)
        -- = rm_spike_to_ts4_all (8k+11) (by omega) where M-9=8k+2, M-8=8k+3
        suffices heq : caEvolve 4 (spikeAtList (8 * (k + 1) - 6) (8 * (k + 1) + 3)) =
                       ts4ConfigList (8 * k + 3) by
          rw [heq]; exact hBk
        have := rm_spike_to_ts4_all (8 * (k + 1) + 3) (by omega)
        convert this using 2 <;> omega
      · -- B(k+1): split off 4 steps, apply cert2 to get ts4Config(8k+3)
        have hstep : (caEvolve (4 * (k + 1) + 1) (ts4ConfigList (8 * (k + 1) + 3))).getD 0 false =
                     (caEvolve (4 * k + 1) (caEvolve 4 (ts4ConfigList (8 * (k + 1) + 3)))).getD 0 false := by
          rw [show 4 * (k + 1) + 1 = (4 * k + 1) + 4 from by ring, caEvolve_add]
        rw [hstep]
        suffices heq : caEvolve 4 (ts4ConfigList (8 * (k + 1) + 3)) = ts4ConfigList (8 * k + 3) by
          rw [heq]; exact hBk
        have := rm_ts4_period_all (8 * (k + 1) + 3) (by omega)
        convert this using 2 <;> omega

/-- For n'≡3 mod 4, n'≥3087: twoSpike(m_right, last, N) gives false
    (contradicts hts hypothesis, so SubcaseB cannot fire). -/
private lemma rm_twoSpike_mod4_3_false (n' : Nat) (hn' : 3087 ≤ n') (hmod4 : n' % 4 = 3) :
    (caEvolve (n' + 1) (twoSpikeList (2 * (n' + 1) - 8) (2 * (n' + 1)) (2 * (n' + 1) + 1))).getD 0 false = false := by
  -- Write n' = 4*k+3, T = 4*k+4 = 4*(k+1). Joint induction on k ≥ 0:
  -- A'(k): (caEvolve (4*(k+1)) (twoSpikeList (8*k) (8*k+8) (8*k+9))).getD 0 false = false
  -- B'(k): (caEvolve (4*(k+1)) (ts3ConfigList (8*k+9))).getD 0 false = false
  -- Step A'(k+1) from B'(k): 4 steps via cert3
  -- Step B'(k+1) from B'(k): 4 steps via cert4
  suffices h : ∀ k : Nat,
      ((caEvolve (4 * (k + 1)) (twoSpikeList (8 * k) (8 * k + 8) (8 * k + 9))).getD 0 false = false ∧
       (caEvolve (4 * (k + 1)) (ts3ConfigList (8 * k + 9))).getD 0 false = false) by
    -- n' = 4*k+3, k = (n'-3)/4
    have hk : n' = 4 * ((n' - 3) / 4) + 3 := by omega
    set k := (n' - 3) / 4 with hk_def
    obtain ⟨hA, _⟩ := h k
    rw [show 4 * (k + 1) = n' + 1 from by omega,
        show 8 * k + 9 = 2 * (n' + 1) + 1 from by omega,
        show 8 * k + 8 = 2 * (n' + 1) from by omega,
        show 8 * k = 2 * (n' + 1) - 8 from by omega] at hA
    exact hA
  intro k
  induction k with
  | zero =>
    exact ⟨rm_twoSpike_base_k0, rm_ts3_base_k0⟩
  | succ k ih =>
    obtain ⟨_, hBk⟩ := ih
    constructor
    · -- A'(k+1): split off 4 steps, apply cert3 to get ts3Config(8k+9)
      have hstep : (caEvolve (4 * (k + 1 + 1)) (twoSpikeList (8 * (k + 1)) (8 * (k + 1) + 8) (8 * (k + 1) + 9))).getD 0 false =
                   (caEvolve (4 * (k + 1)) (caEvolve 4 (twoSpikeList (8 * (k + 1)) (8 * (k + 1) + 8) (8 * (k + 1) + 9)))).getD 0 false := by
        rw [show 4 * (k + 1 + 1) = (4 * (k + 1)) + 4 from by ring, caEvolve_add]
      rw [hstep]
      -- caEvolve 4 (twoSpikeList (8k+8) (8k+16) (8k+17)) = ts3Config(8k+9)
      -- = rm_twoSpike_to_ts3_all (8k+17) where M-9=8k+8, M-1=8k+16, M-8=8k+9
      suffices heq : caEvolve 4 (twoSpikeList (8 * (k + 1)) (8 * (k + 1) + 8) (8 * (k + 1) + 9)) =
                     ts3ConfigList (8 * k + 9) by
        rw [heq]; exact hBk
      have := rm_twoSpike_to_ts3_all (8 * (k + 1) + 9) (by omega)
      convert this using 2 <;> omega
    · -- B'(k+1): split off 4 steps, apply cert4 to get ts3Config(8k+9)
      have hstep : (caEvolve (4 * (k + 1 + 1)) (ts3ConfigList (8 * (k + 1) + 9))).getD 0 false =
                   (caEvolve (4 * (k + 1)) (caEvolve 4 (ts3ConfigList (8 * (k + 1) + 9)))).getD 0 false := by
        rw [show 4 * (k + 1 + 1) = (4 * (k + 1)) + 4 from by ring, caEvolve_add]
      rw [hstep]
      suffices heq : caEvolve 4 (ts3ConfigList (8 * (k + 1) + 9)) = ts3ConfigList (8 * k + 9) by
        rw [heq]; exact hBk
      have := rm_ts3_period_all (8 * (k + 1) + 9) (by omega)
      convert this using 2 <;> omega

-- ============================================================
-- ts5CList / ts5EList: right-cluster intermediate configs for n'≡1 mod 4
-- Used for the period-4 reduction of the right-mirror witness case.
-- ts5CList M: ones at {M-3, M-4, M-5, M-9, M-12, M-13}
-- ts5EList M: ones at {M-1, M-2, M-4, M-9, M-12, M-13}
-- ============================================================

/-- Right-cluster-C config for n'≡1 mod 4: ones at {M-3,M-4,M-5,M-9,M-12,M-13}. -/
private def ts5CList (M : Nat) : List Bool :=
  List.ofFn (fun k : Fin M =>
    decide (k.val + 3 = M ∨ k.val + 4 = M ∨ k.val + 5 = M ∨
            k.val + 9 = M ∨ k.val + 12 = M ∨ k.val + 13 = M))

/-- Right-cluster-E config for n'≡1 mod 4: ones at {M-1,M-2,M-4,M-9,M-12,M-13}. -/
private def ts5EList (M : Nat) : List Bool :=
  List.ofFn (fun k : Fin M =>
    decide (k.val + 1 = M ∨ k.val + 2 = M ∨ k.val + 4 = M ∨
            k.val + 9 = M ∨ k.val + 12 = M ∨ k.val + 13 = M))

private lemma ts5CList_length (M : Nat) : (ts5CList M).length = M := by
  simp [ts5CList, List.length_ofFn]

private lemma ts5EList_length (M : Nat) : (ts5EList M).length = M := by
  simp [ts5EList, List.length_ofFn]

private lemma ts5CList_getD (M i : Nat) (hi : i < M) :
    (ts5CList M).getD i false =
    decide (i + 3 = M ∨ i + 4 = M ∨ i + 5 = M ∨ i + 9 = M ∨ i + 12 = M ∨ i + 13 = M) := by
  simp [ts5CList, List.getD_eq_getElem?_getD, hi]

private lemma ts5EList_getD (M i : Nat) (hi : i < M) :
    (ts5EList M).getD i false =
    decide (i + 1 = M ∨ i + 2 = M ∨ i + 4 = M ∨ i + 9 = M ∨ i + 12 = M ∨ i + 13 = M) := by
  simp [ts5EList, List.getD_eq_getElem?_getD, hi]

private lemma ts5CList_drop_getD (M s r : Nat) (h : s + r < M) :
    (List.drop s (ts5CList M)).getD r false =
    decide (s + r + 3 = M ∨ s + r + 4 = M ∨ s + r + 5 = M ∨
            s + r + 9 = M ∨ s + r + 12 = M ∨ s + r + 13 = M) := by
  rw [show ((List.drop s (ts5CList M)).getD r false) =
        (ts5CList M).getD (s + r) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  exact ts5CList_getD M (s + r) h

private lemma ts5EList_drop_getD (M s r : Nat) (h : s + r < M) :
    (List.drop s (ts5EList M)).getD r false =
    decide (s + r + 1 = M ∨ s + r + 2 = M ∨ s + r + 4 = M ∨
            s + r + 9 = M ∨ s + r + 12 = M ∨ s + r + 13 = M) := by
  rw [show ((List.drop s (ts5EList M)).getD r false) =
        (ts5EList M).getD (s + r) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  exact ts5EList_getD M (s + r) h

-- Base certs (native_decide)
private lemma rm_cert_ts5C_period :
    caEvolve 4 (ts5CList 21) = ts5CList 13 := by native_decide

private lemma rm_cert_ts5E_period :
    caEvolve 4 (ts5EList 21) = ts5EList 13 := by native_decide

private lemma rm_cert_spike_to_ts5C :
    caEvolve 8 (spikeAtList 16 29) = ts5CList 13 := by native_decide

private lemma rm_cert_twoSpike_to_ts5E :
    caEvolve 12 (twoSpikeList 24 28 37) = ts5EList 13 := by native_decide

-- Center-value base certs
private lemma rm_ts5C_center_k3 :
    (caEvolve 6 (ts5CList 13)).getD 0 false = true := by native_decide

private lemma rm_ts5C_center_k4 :
    (caEvolve 10 (ts5CList 21)).getD 0 false = true := by native_decide

private lemma rm_ts5E_center_k3 :
    (caEvolve 2 (ts5EList 5)).getD 0 false = false := by native_decide

private lemma rm_ts5E_center_k4 :
    (caEvolve 6 (ts5EList 13)).getD 0 false = false := by native_decide

-- ============================================================
-- Parametric period cert: ts5CList(M) →4 steps→ ts5CList(M-8), M≥21
-- ============================================================

/-- Parametric cert: ts5CList(M) →4 steps→ ts5CList(M-8), for all M≥21. -/
private lemma rm_ts5C_period_all (M : Nat) (hM : M ≥ 21) :
    caEvolve 4 (ts5CList M) = ts5CList (M - 8) := by
  apply List.ext_getElem
  · have hlen : (caEvolve 4 (ts5CList M)).length = M - 8 := by
      have := caEvolve_length_le 4 (ts5CList M) (by rw [ts5CList_length]; omega)
      rw [ts5CList_length] at this; omega
    rw [hlen, ts5CList_length]
  · intro i h1 h2
    rw [List.getElem_eq_getD false]
    have hiM8 : i < M - 8 := by rw [ts5CList_length] at h2; exact h2
    have hrhs : (ts5CList (M - 8))[i]'h2 =
        decide (i + 3 = M - 8 ∨ i + 4 = M - 8 ∨ i + 5 = M - 8 ∨
                i + 9 = M - 8 ∨ i + 12 = M - 8 ∨ i + 13 = M - 8) := by
      simp only [ts5CList, List.getElem_ofFn]
    rw [hrhs]
    rw [caEvolve_getD_shift 4 (ts5CList M) i]
    by_cases hiR : M - 21 ≤ i
    · -- RIGHT REGION: i ≥ M-21, window overlaps cluster at M-13
      set s := i - (M - 21) with hs_def
      have hs_range : s ≤ 12 := by omega
      have hagree : (caEvolve 4 ((ts5CList M).drop i)).getD 0 false =
                   (caEvolve 4 ((ts5CList 21).drop s)).getD 0 false := by
        apply caEvolve_agree 4
        · rw [List.length_drop, ts5CList_length]; omega
        · rw [List.length_drop, ts5CList_length]; omega
        · intro r hr
          rw [ts5CList_drop_getD M i r (by omega)]
          rw [ts5CList_drop_getD 21 s r (by omega)]
          simp only [decide_eq_decide]; omega
      rw [hagree, ← caEvolve_getD_shift 4 (ts5CList 21) s, rm_cert_ts5C_period]
      rw [ts5CList_getD 13 s (by omega)]
      simp only [decide_eq_decide]; omega
    · -- ZERO REGION: i < M-21, window has no ones
      push_neg at hiR
      have hzero : (caEvolve 4 ((ts5CList M).drop i)).getD 0 false = false := by
        have heq : (caEvolve 4 ((ts5CList M).drop i)).getD 0 false =
                   (caEvolve 4 (List.replicate (M - i) false)).getD 0 false := by
          apply caEvolve_agree 4
          · rw [List.length_drop, ts5CList_length]; omega
          · rw [List.length_replicate]; omega
          · intro r hr
            rw [ts5CList_drop_getD M i r (by omega)]
            have hrep : (List.replicate (M - i) false).getD r false = false := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
              split_ifs <;> rfl
            rw [hrep]
            simp only [decide_eq_false_iff_not, not_or]; omega
        rw [heq]
        apply caEvolve_allFalse
        intro k hk
        rw [List.length_replicate] at hk
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      rw [hzero]
      symm; simp only [decide_eq_false_iff_not, not_or]; omega

-- ============================================================
-- Parametric period cert: ts5EList(M) →4 steps→ ts5EList(M-8), M≥21
-- ============================================================

/-- Parametric cert: ts5EList(M) →4 steps→ ts5EList(M-8), for all M≥21. -/
private lemma rm_ts5E_period_all (M : Nat) (hM : M ≥ 21) :
    caEvolve 4 (ts5EList M) = ts5EList (M - 8) := by
  apply List.ext_getElem
  · have hlen : (caEvolve 4 (ts5EList M)).length = M - 8 := by
      have := caEvolve_length_le 4 (ts5EList M) (by rw [ts5EList_length]; omega)
      rw [ts5EList_length] at this; omega
    rw [hlen, ts5EList_length]
  · intro i h1 h2
    rw [List.getElem_eq_getD false]
    have hiM8 : i < M - 8 := by rw [ts5EList_length] at h2; exact h2
    have hrhs : (ts5EList (M - 8))[i]'h2 =
        decide (i + 1 = M - 8 ∨ i + 2 = M - 8 ∨ i + 4 = M - 8 ∨
                i + 9 = M - 8 ∨ i + 12 = M - 8 ∨ i + 13 = M - 8) := by
      simp only [ts5EList, List.getElem_ofFn]
    rw [hrhs]
    rw [caEvolve_getD_shift 4 (ts5EList M) i]
    by_cases hiR : M - 21 ≤ i
    · set s := i - (M - 21) with hs_def
      have hs_range : s ≤ 12 := by omega
      have hagree : (caEvolve 4 ((ts5EList M).drop i)).getD 0 false =
                   (caEvolve 4 ((ts5EList 21).drop s)).getD 0 false := by
        apply caEvolve_agree 4
        · rw [List.length_drop, ts5EList_length]; omega
        · rw [List.length_drop, ts5EList_length]; omega
        · intro r hr
          rw [ts5EList_drop_getD M i r (by omega)]
          rw [ts5EList_drop_getD 21 s r (by omega)]
          simp only [decide_eq_decide]; omega
      rw [hagree, ← caEvolve_getD_shift 4 (ts5EList 21) s, rm_cert_ts5E_period]
      rw [ts5EList_getD 13 s (by omega)]
      simp only [decide_eq_decide]; omega
    · push_neg at hiR
      have hzero : (caEvolve 4 ((ts5EList M).drop i)).getD 0 false = false := by
        have heq : (caEvolve 4 ((ts5EList M).drop i)).getD 0 false =
                   (caEvolve 4 (List.replicate (M - i) false)).getD 0 false := by
          apply caEvolve_agree 4
          · rw [List.length_drop, ts5EList_length]; omega
          · rw [List.length_replicate]; omega
          · intro r hr
            rw [ts5EList_drop_getD M i r (by omega)]
            have hrep : (List.replicate (M - i) false).getD r false = false := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
              split_ifs <;> rfl
            rw [hrep]
            simp only [decide_eq_false_iff_not, not_or]; omega
        rw [heq]
        apply caEvolve_allFalse
        intro k hk
        rw [List.length_replicate] at hk
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      rw [hzero]
      symm; simp only [decide_eq_false_iff_not, not_or]; omega

-- ============================================================
-- Entry cert: spike(M-13, M) →8 steps→ ts5CList(M-16), M≥29
-- ============================================================

/-- Entry cert: spikeAtList(M-13, M) →8 steps→ ts5CList(M-16), for all M≥29. -/
private lemma rm_spike_to_ts5C_all (M : Nat) (hM : M ≥ 29) :
    caEvolve 8 (spikeAtList (M - 13) M) = ts5CList (M - 16) := by
  apply List.ext_getElem
  · have hlen : (caEvolve 8 (spikeAtList (M - 13) M)).length = M - 16 := by
      have := caEvolve_length_le 8 (spikeAtList (M - 13) M)
        (by rw [spikeAtList_length]; omega)
      rw [spikeAtList_length] at this; omega
    rw [hlen, ts5CList_length]
  · intro i h1 h2
    rw [List.getElem_eq_getD false]
    have hiM16 : i < M - 16 := by rw [ts5CList_length] at h2; exact h2
    have hrhs : (ts5CList (M - 16))[i]'h2 =
        decide (i + 3 = M - 16 ∨ i + 4 = M - 16 ∨ i + 5 = M - 16 ∨
                i + 9 = M - 16 ∨ i + 12 = M - 16 ∨ i + 13 = M - 16) := by
      simp only [ts5CList, List.getElem_ofFn]
    rw [hrhs]
    rw [caEvolve_getD_shift 8 (spikeAtList (M - 13) M) i]
    by_cases hiR : M - 29 ≤ i
    · -- RIGHT REGION: i ≥ M-29, window [i, i+16] overlaps spike at M-13
      set s := i - (M - 29) with hs_def
      have hs_range : s ≤ 12 := by omega
      have hagree : (caEvolve 8 ((spikeAtList (M - 13) M).drop i)).getD 0 false =
                   (caEvolve 8 ((spikeAtList 16 29).drop s)).getD 0 false := by
        apply caEvolve_agree 8
        · rw [List.length_drop, spikeAtList_length]; omega
        · rw [List.length_drop, spikeAtList_length]; omega
        · intro r hr
          rw [show ((spikeAtList (M - 13) M).drop i).getD r false =
                (spikeAtList (M - 13) M).getD (i + r) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
          rw [show ((spikeAtList 16 29).drop s).getD r false =
                (spikeAtList 16 29).getD (s + r) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
          rw [spikeAtList_getD (M - 13) M (i + r) (by omega)]
          rw [spikeAtList_getD 16 29 (s + r) (by omega)]
          simp only [decide_eq_decide]; omega
      rw [hagree, ← caEvolve_getD_shift 8 (spikeAtList 16 29) s, rm_cert_spike_to_ts5C]
      rw [ts5CList_getD 13 s (by omega)]
      simp only [decide_eq_decide]; omega
    · -- ZERO REGION: i < M-29, window misses spike at M-13
      push_neg at hiR
      have hzero : (caEvolve 8 ((spikeAtList (M - 13) M).drop i)).getD 0 false = false := by
        have heq : (caEvolve 8 ((spikeAtList (M - 13) M).drop i)).getD 0 false =
                   (caEvolve 8 (List.replicate (M - i) false)).getD 0 false := by
          apply caEvolve_agree 8
          · rw [List.length_drop, spikeAtList_length]; omega
          · rw [List.length_replicate]; omega
          · intro r hr
            rw [show ((spikeAtList (M - 13) M).drop i).getD r false =
                  (spikeAtList (M - 13) M).getD (i + r) false from by
              simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
            have hrep : (List.replicate (M - i) false).getD r false = false := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
              split_ifs <;> rfl
            rw [hrep, spikeAtList_getD (M - 13) M (i + r) (by omega)]
            simp only [decide_eq_false_iff_not]; omega
        rw [heq]
        apply caEvolve_allFalse
        intro k hk
        rw [List.length_replicate] at hk
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      rw [hzero]
      symm; simp only [decide_eq_false_iff_not, not_or]; omega

-- ============================================================
-- Entry cert: twoSpikeList(M-13, M-9, M) →12 steps→ ts5EList(M-24), M≥37
-- ============================================================

/-- Entry cert: twoSpikeList(M-13, M-9, M) →12 steps→ ts5EList(M-24), for all M≥37. -/
private lemma rm_twoSpike_to_ts5E_all (M : Nat) (hM : M ≥ 37) :
    caEvolve 12 (twoSpikeList (M - 13) (M - 9) M) = ts5EList (M - 24) := by
  apply List.ext_getElem
  · have hlen : (caEvolve 12 (twoSpikeList (M - 13) (M - 9) M)).length = M - 24 := by
      have := caEvolve_length_le 12 (twoSpikeList (M - 13) (M - 9) M)
        (by rw [twoSpikeList_length]; omega)
      rw [twoSpikeList_length] at this; omega
    rw [hlen, ts5EList_length]
  · intro i h1 h2
    rw [List.getElem_eq_getD false]
    have hiM24 : i < M - 24 := by rw [ts5EList_length] at h2; exact h2
    have hrhs : (ts5EList (M - 24))[i]'h2 =
        decide (i + 1 = M - 24 ∨ i + 2 = M - 24 ∨ i + 4 = M - 24 ∨
                i + 9 = M - 24 ∨ i + 12 = M - 24 ∨ i + 13 = M - 24) := by
      simp only [ts5EList, List.getElem_ofFn]
    rw [hrhs]
    rw [caEvolve_getD_shift 12 (twoSpikeList (M - 13) (M - 9) M) i]
    by_cases hiR : M - 37 ≤ i
    · -- RIGHT REGION: i ≥ M-37, window [i, i+24] overlaps spikes at M-13 and M-9
      set s := i - (M - 37) with hs_def
      have hs_range : s ≤ 12 := by omega
      have hagree : (caEvolve 12 ((twoSpikeList (M - 13) (M - 9) M).drop i)).getD 0 false =
                   (caEvolve 12 ((twoSpikeList 24 28 37).drop s)).getD 0 false := by
        apply caEvolve_agree 12
        · rw [List.length_drop, twoSpikeList_length]; omega
        · rw [List.length_drop, twoSpikeList_length]; omega
        · intro r hr
          rw [show ((twoSpikeList (M - 13) (M - 9) M).drop i).getD r false =
                (twoSpikeList (M - 13) (M - 9) M).getD (i + r) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
          rw [show ((twoSpikeList 24 28 37).drop s).getD r false =
                (twoSpikeList 24 28 37).getD (s + r) false from by
            simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
          rw [twoSpikeList_getD (M - 13) (M - 9) M (i + r) (by omega)]
          rw [twoSpikeList_getD 24 28 37 (s + r) (by omega)]
          simp only [decide_eq_decide]; omega
      rw [hagree, ← caEvolve_getD_shift 12 (twoSpikeList 24 28 37) s, rm_cert_twoSpike_to_ts5E]
      rw [ts5EList_getD 13 s (by omega)]
      simp only [decide_eq_decide]; omega
    · -- ZERO REGION: i < M-37, window misses both spikes
      push_neg at hiR
      have hzero : (caEvolve 12 ((twoSpikeList (M - 13) (M - 9) M).drop i)).getD 0 false = false := by
        have heq : (caEvolve 12 ((twoSpikeList (M - 13) (M - 9) M).drop i)).getD 0 false =
                   (caEvolve 12 (List.replicate (M - i) false)).getD 0 false := by
          apply caEvolve_agree 12
          · rw [List.length_drop, twoSpikeList_length]; omega
          · rw [List.length_replicate]; omega
          · intro r hr
            rw [show ((twoSpikeList (M - 13) (M - 9) M).drop i).getD r false =
                  (twoSpikeList (M - 13) (M - 9) M).getD (i + r) false from by
              simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
            have hrep : (List.replicate (M - i) false).getD r false = false := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
              split_ifs <;> rfl
            rw [hrep, twoSpikeList_getD (M - 13) (M - 9) M (i + r) (by omega)]
            simp only [decide_eq_false_iff_not, not_or]; omega
        rw [heq]
        apply caEvolve_allFalse
        intro k hk
        rw [List.length_replicate] at hk
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      rw [hzero]
      symm; simp only [decide_eq_false_iff_not, not_or]; omega

-- ============================================================
-- Period inductions for rm_ts5C_true and rm_ts5E_false
-- ============================================================

/-- For all k≥3: caEvolve(4k-6)(ts5CList(8k-11)).getD 0 false = true.
    Joint induction carrying (C(k), C(k+1)) simultaneously. -/
private lemma rm_ts5C_true (k : Nat) (hk : k ≥ 3) :
    (caEvolve (4 * k - 6) (ts5CList (8 * k - 11))).getD 0 false = true := by
  suffices h : ∀ j : Nat, j ≥ 3 →
      (caEvolve (4 * j - 6) (ts5CList (8 * j - 11))).getD 0 false = true ∧
      (caEvolve (4 * j - 2) (ts5CList (8 * j - 3))).getD 0 false = true by
    exact (h k hk).1
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    cases Nat.eq_or_lt_of_le hj with
    | inl h =>
      -- j+1 = 3, so j = 2: base cases C(3) and C(4)
      have hj2 : j = 2 := by omega
      subst hj2
      exact ⟨rm_ts5C_center_k3, rm_ts5C_center_k4⟩
    | inr h =>
      -- j+1 ≥ 4, so j ≥ 3
      have hjge3 : j ≥ 3 := by omega
      obtain ⟨_, hCj1⟩ := ih hjge3
      -- hCj1 : (caEvolve (4*j-2) (ts5CList (8*j-3))).getD 0 false = true
      constructor
      · -- C(j+1): caEvolve(4j-2)(ts5C(8j-3)) = true
        exact hCj1
      · -- C(j+2): caEvolve(4j+2)(ts5C(8j+5)) = true
        -- = caEvolve(4j-2)(caEvolve 4 (ts5C(8j+5))) [split off 4 steps]
        -- caEvolve 4 (ts5C(8j+5)) = ts5C(8j-3) [period cert at M=8j+5 ≥ 21 for j≥3... wait 8j+5≥29]
        -- Hmm: C(j+2) has 4*(j+2)-2 = 4j+6 steps on ts5C(8*(j+2)-3) = ts5C(8j+13)
        -- Let me recompute: the pair is (C(j+1), C(j+2)):
        -- C(j+1) = caEvolve(4(j+1)-6)(ts5C(8(j+1)-11)) = caEvolve(4j-2)(ts5C(8j-3))
        -- C(j+2) = caEvolve(4(j+2)-6)(ts5C(8(j+2)-11)) = caEvolve(4j+2)(ts5C(8j+5))
        have hstep : (caEvolve (4 * (j + 1) - 2) (ts5CList (8 * (j + 1) - 3))).getD 0 false =
                     (caEvolve (4 * j - 2) (caEvolve 4 (ts5CList (8 * (j + 1) - 3)))).getD 0 false := by
          rw [show 4 * (j + 1) - 2 = (4 * j - 2) + 4 from by omega, caEvolve_add]
        rw [hstep]
        suffices heq : caEvolve 4 (ts5CList (8 * (j + 1) - 3)) = ts5CList (8 * j - 3) by
          rw [heq]; exact hCj1
        have := rm_ts5C_period_all (8 * (j + 1) - 3) (by omega)
        convert this using 2 <;> omega

/-- For all k≥3: caEvolve(4k-10)(ts5EList(8k-19)).getD 0 false = false.
    Joint induction carrying (G(k), G(k+1)) simultaneously. -/
private lemma rm_ts5E_false (k : Nat) (hk : k ≥ 3) :
    (caEvolve (4 * k - 10) (ts5EList (8 * k - 19))).getD 0 false = false := by
  suffices h : ∀ j : Nat, j ≥ 3 →
      (caEvolve (4 * j - 10) (ts5EList (8 * j - 19))).getD 0 false = false ∧
      (caEvolve (4 * j - 6) (ts5EList (8 * j - 11))).getD 0 false = false by
    exact (h k hk).1
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    cases Nat.eq_or_lt_of_le hj with
    | inl h =>
      -- j+1 = 3, so j = 2: base cases G(3) and G(4)
      have hj2 : j = 2 := by omega
      subst hj2
      exact ⟨rm_ts5E_center_k3, rm_ts5E_center_k4⟩
    | inr h =>
      -- j+1 ≥ 4, so j ≥ 3
      have hjge3 : j ≥ 3 := by omega
      obtain ⟨_, hGj1⟩ := ih hjge3
      -- hGj1 : (caEvolve (4*j-6) (ts5EList (8*j-11))).getD 0 false = false
      constructor
      · -- G(j+1): caEvolve(4j-6)(ts5E(8j-11)) = false
        exact hGj1
      · -- G(j+2): caEvolve(4j-2)(ts5E(8j-3)) = false
        -- = caEvolve(4j-6)(caEvolve 4 (ts5E(8j-3))) [split 4 steps]
        -- caEvolve 4 (ts5E(8j-3)) = ts5E(8j-11) [period cert at M=8j-3 ≥ 21 for j≥3: 8*3-3=21 ✓]
        -- G(j+2) = caEvolve(4(j+2)-10)(ts5E(8(j+2)-19)) = caEvolve(4j-2)(ts5E(8j-3))
        have hstep : (caEvolve (4 * (j + 1) - 6) (ts5EList (8 * (j + 1) - 11))).getD 0 false =
                     (caEvolve (4 * j - 6) (caEvolve 4 (ts5EList (8 * (j + 1) - 11)))).getD 0 false := by
          rw [show 4 * (j + 1) - 6 = (4 * j - 6) + 4 from by omega, caEvolve_add]
        rw [hstep]
        suffices heq : caEvolve 4 (ts5EList (8 * (j + 1) - 11)) = ts5EList (8 * j - 11) by
          rw [heq]; exact hGj1
        have := rm_ts5E_period_all (8 * (j + 1) - 11) (by omega)
        convert this using 2 <;> omega

/-- For n'≡1 mod 4, n'≥3087: sensitivity witness exists for m_right.
    Witness: spikeConfig(2*(n'+1)-12)(n'); proves via 8-step/12-step period chains. -/
private lemma rm_mod4_1_witness (n' : Nat) (hn' : 3087 ≤ n') (hmod4 : n' % 4 = 1)
    (m : Fin (2 * (n' + 1) + 1)) (hm_rm : m.val = 2 * (n' + 1) - 8)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  -- Witness: spikeConfig w where w = 2*(n'+1)-12 = m.val - 4 (always even)
  set w := 2 * (n' + 1) - 12 with hw_def
  have hw_even : w % 2 = 0 := by omega
  have hwm : w ≠ m.val := by omega
  have hwb : w < 2 * (n' + 1) + 1 := by omega
  use spikeConfig w n'
  refine ⟨spikeConfig_odd_false w hw_even n', ?_⟩
  rw [rule30n_spikeConfig_eq w n']
  rw [rule30n_flipCell_spikeConfig_eq' w n' m hwm hwb]
  -- After rewriting, goal: (caEvolve(n'+1)(spike(w,N))).getD 0 false ≠
  --                        (caEvolve(n'+1)(twoSpike(w,m.val,N))).getD 0 false
  -- where N = 2*(n'+1)+1 = 8k+5, w = 8k-8, m.val = 8k-4, and k = (n'-1)/4
  set k := (n' - 1) / 4 with hk_def
  have hk_ge : k ≥ 3 := by omega  -- n' ≥ 3087 ≥ 4*3+1, so k ≥ 3
  have hn'_eq : n' = 4 * k + 1 := by omega
  have hT : n' + 1 = 4 * k + 2 := by omega
  have hw_eq : w = 8 * k - 8 := by omega
  have hm_eq : m.val = 8 * k - 4 := by omega
  have hN_eq : 2 * (n' + 1) + 1 = 8 * k + 5 := by omega
  -- Prove spike → True: A(k)
  have hspike_true : (caEvolve (n' + 1) (spikeAtList w (2 * (n' + 1) + 1))).getD 0 false = true := by
    rw [hN_eq, hT, hw_eq]
    -- caEvolve(4k+2)(spike(8k-8, 8k+5))
    -- = caEvolve(4k-6)(caEvolve 8 (spike(8k-8, 8k+5)))  [caEvolve_add: 4k+2 = (4k-6)+8]
    -- = caEvolve(4k-6)(ts5C(8k-11))                     [spike_to_ts5C at M=8k+5]
    -- = True                                              [rm_ts5C_true]
    rw [show 4 * k + 2 = (4 * k - 6) + 8 from by omega, caEvolve_add]
    suffices heq : caEvolve 8 (spikeAtList (8 * k - 8) (8 * k + 5)) = ts5CList (8 * k - 11) by
      rw [heq]; exact rm_ts5C_true k hk_ge
    have := rm_spike_to_ts5C_all (8 * k + 5) (by omega)
    convert this using 2 <;> omega
  -- Prove twoSpike → False: D(k)
  have htwo_false : (caEvolve (n' + 1) (twoSpikeList w m.val (2 * (n' + 1) + 1))).getD 0 false = false := by
    simp only [hm_eq, hN_eq, hT, hw_eq]
    -- caEvolve(4k+2)(twoSpike(8k-8, 8k-4, 8k+5))
    -- = caEvolve(4k-10)(caEvolve 12 (twoSpike(8k-8, 8k-4, 8k+5)))  [caEvolve_add: 4k+2 = (4k-10)+12]
    -- = caEvolve(4k-10)(ts5E(8k-19))                                [twoSpike_to_ts5E at M=8k+5]
    -- = False                                                         [rm_ts5E_false]
    rw [show 4 * k + 2 = (4 * k - 10) + 12 from by omega, caEvolve_add,
        show 2 * (4 * k - 10 + 12) + 1 = 8 * k + 5 from by omega]
    suffices heq : caEvolve 12 (twoSpikeList (8 * k - 8) (8 * k - 4) (8 * k + 5)) = ts5EList (8 * k - 19) by
      rw [heq]; exact rm_ts5E_false k hk_ge
    have := rm_twoSpike_to_ts5E_all (8 * k + 5) (by omega)
    convert this using 2 <;> omega
  -- Conclude: True ≠ False
  rw [hspike_true, htwo_false]
  decide

/-- SubcaseB for right-mirror m = 2*(n'+1)-8.
    Proof by mod-4 case split:
    - n'≡0 mod 4: spike_m = true → contradicts hcase (no SubcaseB)
    - n'≡1 mod 4: complex periodic witness (sorry'd, 17+ sub-classes)
    - n'≡2 mod 4: witness = spike_2 (proved via rcConfigList joint induction)
    - n'≡3 mod 4: twoSpike = false → contradicts hts (no SubcaseB) -/
theorem subcaseB_right_mirror_ge3087 (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm_rm : m.val = 2 * (n' + 1) - 8)
    (hm_even : m.val % 2 = 0) (hm_low : 1 ≤ m.val)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  -- Case split on n' mod 4
  rcases Nat.lt_or_ge (n' % 4) 2 with h | h
  · rcases Nat.lt_or_ge (n' % 4) 1 with h' | h'
    · -- n' % 4 = 0: spike_m gives true, contradicts hcase
      exfalso
      have hmod4 : n' % 4 = 0 := by omega
      have hspike_true : (caEvolve (n' + 1) (spikeAtList (2 * (n' + 1) - 8) (2 * (n' + 1) + 1))).getD 0 false = true :=
        rm_spike_mod4_0_true n' hn' hmod4
      have hcase_val : (caEvolve (n' + 1) (spikeAtList (m.val) (2 * (n' + 1) + 1))).getD 0 false = false := by
        have h_eq := (rule30n_spikeConfig_eq m.val n').symm
        simp only [spikeConfig] at h_eq
        -- h_eq : (caEvolve ...).getD 0 false = rule30n (n'+1) (fun k => decide (k.val = m.val))
        rw [h_eq]
        exact hcase
      rw [hm_rm] at hcase_val
      rw [hspike_true] at hcase_val
      exact absurd hcase_val (by decide)
    · -- n' % 4 = 1: complex witness (sorry'd)
      have hmod4 : n' % 4 = 1 := by omega
      exact rm_mod4_1_witness n' hn' hmod4 m hm_rm hcase hts
  · rcases Nat.lt_or_ge (n' % 4) 3 with h' | h'
    · -- n' % 4 = 2: witness = spike_2
      have hmod4 : n' % 4 = 2 := by omega
      use spikeConfig 2 n'
      refine ⟨spikeConfig_odd_false 2 (by decide) n', ?_⟩
      rw [rule30n_spikeConfig_eq 2 n']
      rw [rule30n_flipCell_spikeConfig_eq' 2 n' m
            (by omega)   -- 2 ≠ m.val since m.val = 2*(n'+1)-8 ≥ 2*3088-8 > 2
            (by omega)]  -- 2 < 2*(n'+1)+1
      have hLHS : (caEvolve (n' + 1) (spikeAtList 2 (2 * (n' + 1) + 1))).getD 0 false = true := by
        rw [rm_spike2_parity n']
        simp [show n' % 2 = 0 from by omega]
      have hRHS : (caEvolve (n' + 1) (twoSpikeList 2 (2 * (n' + 1) - 8) (2 * (n' + 1) + 1))).getD 0 false = false :=
        rm_twoSpike_mod4_2 n' (by omega) hmod4
      rw [hm_rm, hLHS, hRHS]
      decide
    · -- n' % 4 = 3: twoSpike_m gives false, contradicts hts
      exfalso
      have hmod4 : n' % 4 = 3 := by omega
      have hts_false : (caEvolve (n' + 1) (twoSpikeList (2 * (n' + 1) - 8) (2 * (n' + 1)) (2 * (n' + 1) + 1))).getD 0 false = false :=
        rm_twoSpike_mod4_3_false n' hn' hmod4
      -- Connect rule30n hts to caEvolve form.
      -- hts says: rule30n(n'+1)(fun k => decide(k=m.val ∨ k=2*(n'+1))) = true
      -- This equals (caEvolve(n'+1)(twoSpikeList m.val (2*(n'+1)) N)).getD 0 false = true
      -- by the same simp/congr argument as rule30n_spikeConfig_eq.
      have hts_caE : (caEvolve (n' + 1) (twoSpikeList m.val (2 * (n' + 1)) (2 * (n' + 1) + 1))).getD 0 false = true := by
        have heq := rule30n_twoSpikeLast_eq n' m.val
        -- heq : rule30n (n'+1) (fun k => decide (k.val = m.val ∨ k.val = 2*(n'+1)))
        --     = (caEvolve (n'+1) (twoSpikeLastList m.val (2*(n'+1)+1))).getD 0 false
        rw [heq] at hts
        -- twoSpikeLastList m.val N = twoSpikeList m.val (N-1) N since N-1 = 2*(n'+1)+1-1 = 2*(n'+1)
        -- Note: twoSpikeLastList uses ||  (Bool.or via decide coercion),
        --       twoSpikeList uses ∨ (Or). They agree pointwise.
        have hlist_eq : twoSpikeLastList m.val (2 * (n' + 1) + 1) =
                        twoSpikeList m.val (2 * (n' + 1)) (2 * (n' + 1) + 1) := by
          simp only [twoSpikeLastList, twoSpikeList]
          congr 1; ext ⟨i, hi⟩
          -- LHS: decide (i = m.val || i = (2*(n'+1)+1) - 1)  (Bool.or via decide coerce)
          -- RHS: decide (i = m.val ∨  i = 2*(n'+1))          (Or, same as ||)
          -- Equal: (2*(n'+1)+1)-1 = 2*(n'+1) by Nat arithmetic
          cases Nat.decEq i m.val with
          | isTrue h => simp [h]
          | isFalse h => simp [h]
        rw [← hlist_eq]
        exact hts
      rw [hm_rm] at hts_caE
      rw [hts_false] at hts_caE
      exact absurd hts_caE (by decide)

/-!
## Inactive m infrastructure (m=2 and m=18)

For inactive m values, SubcaseB never fires for large n'.
We prove this by period reduction + base case native_decide.
-/

-- Period certs for m=32 (period 4096, inactive)
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_m32_p4096 :
    caEvolve 4096 (spikeAtList 32 8257) = spikeAtList 32 65 := by native_decide

lemma rule30n_twoSpikeLast32_period4096 (n : Nat) (hn : n ≥ 32) :
    (caEvolve (n + 1) (twoSpikeLastList 32 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 4096) (twoSpikeLastList 32 (2 * ((n + 1) + 4096) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 32 4096 caEvolve_cert_m32_p4096 caEvolve_h1_p4096 n hn

lemma twoSpikeLast32_iterated_period4096 (n k : Nat) (hn : n ≥ 32) :
    (caEvolve (n + 1) (twoSpikeLastList 32 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 4096) (twoSpikeLastList 32 (2*(n+1+k*4096)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 4096 = (n + k * 4096) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 4096 = (n + k * 4096) + 1 + 4096 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast32_period4096 (n + k * 4096) (by omega)

-- Period certs for m=2 (period 2)
set_option maxHeartbeats 800000 in
lemma caEvolve_cert_m2_p2 :
    caEvolve 2 (spikeAtList 2 9) = spikeAtList 2 5 := by native_decide

set_option maxHeartbeats 800000 in
lemma caEvolve_h1_p2 :
    (caEvolve 2 (spikeAtList 4 5)).getD 0 false = true := by native_decide

lemma rule30n_twoSpikeLast2_period2 (n : Nat) (hn : n ≥ 2) :
    (caEvolve (n + 1) (twoSpikeLastList 2 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 2) (twoSpikeLastList 2 (2 * ((n + 1) + 2) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 2 2 caEvolve_cert_m2_p2 caEvolve_h1_p2 n hn

lemma twoSpikeLast2_iterated_period2 (n k : Nat) (hn : n ≥ 2) :
    (caEvolve (n + 1) (twoSpikeLastList 2 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 2) (twoSpikeLastList 2 (2*(n+1+k*2)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 2 = (n + k * 2) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 2 = (n + k * 2) + 1 + 2 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast2_period2 (n + k * 2) (by omega)

/-- For m=2, twoSpikeLast gives center=false for all n'' ∈ [2, 4). -/
set_option maxHeartbeats 800000 in
lemma subcaseB_m2_G_always_false :
    ∀ j : Fin 2,
    (caEvolve (j.val + 2 + 1) (twoSpikeLastList 2 (2*(j.val + 2 + 1)+1))).getD 0 false = false := by
  native_decide

-- Period certs for m=18 (period 256)
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_m18_p256 :
    caEvolve 256 (spikeAtList 18 549) = spikeAtList 18 37 := by native_decide

lemma rule30n_twoSpikeLast18_period256 (n : Nat) (hn : n ≥ 18) :
    (caEvolve (n + 1) (twoSpikeLastList 18 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 256) (twoSpikeLastList 18 (2 * ((n + 1) + 256) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 18 256 caEvolve_cert_m18_p256 caEvolve_h1_p256 n hn

lemma twoSpikeLast18_iterated_period256 (n k : Nat) (hn : n ≥ 18) :
    (caEvolve (n + 1) (twoSpikeLastList 18 (2*(n+1)+1))).getD 0 false =
    (caEvolve (n + 1 + k * 256) (twoSpikeLastList 18 (2*(n+1+k*256)+1))).getD 0 false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih]
    conv_lhs => rw [show n + 1 + k * 256 = (n + k * 256) + 1 from by omega]
    have hstep : n + 1 + (k + 1) * 256 = (n + k * 256) + 1 + 256 := by ring
    rw [hstep]
    exact rule30n_twoSpikeLast18_period256 (n + k * 256) (by omega)

/-- For m=18, SubcaseB never fires in base period [18, 274). -/
set_option maxHeartbeats 4000000000 in
lemma subcaseB_m18_never_fires :
    ∀ j : Fin 256,
    (caEvolve (j.val + 18 + 1) (spikeAtList 18 (2*(j.val + 18 + 1)+1))).getD 0 false = false →
    (caEvolve (j.val + 18 + 1) (twoSpikeLastList 18 (2*(j.val + 18 + 1)+1))).getD 0 false = true →
    False := by native_decide

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
    For every n' ≥ 3087 and every even m with 1 ≤ m < 2*(n'+1), m ≠ 2*n',
    if F_m(n'+1)=false and G_{m,last}(n'+1)=true, then spike_w is sensitive at m.
    Proof: case analysis over m values. Known active m for n'≥3087 are
    {4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38} plus right-mirror at 2T-8.
    Inactive m ∈ {2,18} are proved via period reduction.
    Remaining late-tail work: split m>30 into active exceptions {34,36,38}
    and the conjectural inactive tail. -/
theorem subcaseB_resolution_ge3087
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
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  -- Case split: m ≤ 30 or m > 30
  by_cases hm30 : m.val ≤ 30
  · -- m ≤ 30: enumerate all even values 2, 4, 6, ..., 30
    -- m is even (hm_even), m ≥ 1 (hm_low), m ≤ 30
    interval_cases (m.val)
    all_goals (first
      | (-- odd: contradicts hm_even
         omega)
      | (-- m = 0: contradicts hm_low
         omega)
      | (-- m = 2: SubcaseB never fires (inactive, G always false)
         exfalso
         have hts2 : (caEvolve (n'+1) (twoSpikeLastList 2 (2*(n'+1)+1))).getD 0 false = true := by
           rw [← rule30n_twoSpikeLast_eq n' 2]; exact hts
         obtain ⟨k, hn'_eq⟩ := periodReduce_diff 2 2 n' (by omega) (by omega)
         have hn''_range := periodReduce_range 2 2 n' (by omega) (by omega)
         set n'' := periodReduce 2 2 n'
         have hG_n'' : (caEvolve (n''+1) (twoSpikeLastList 2 (2*(n''+1)+1))).getD 0 false = true := by
           have hp := twoSpikeLast2_iterated_period2 n'' k (by omega)
           rw [show n''+1+k*2 = n'+1 from by omega] at hp; rw [hp]; exact hts2
         have hG_false : (caEvolve (n''+1) (twoSpikeLastList 2 (2*(n''+1)+1))).getD 0 false = false := by
           have := subcaseB_m2_G_always_false ⟨n'' - 2, by omega⟩
           convert this using 2 <;> omega
         exact absurd hG_n'' (by rw [hG_false]; decide))
      | (-- m = 4
         exact subcaseB_m4_ge3087 n' hn' m (by omega) hcase hts)
      | (-- m = 6
         exact subcaseB_m6_ge3087_proved n' hn' m (by omega) hcase hts)
      | (-- m = 8
         exact subcaseB_m8_ge3087_proved n' hn' m (by omega) hcase hts)
      | (-- m = 10
         exact subcaseB_m10_ge3087_proved n' hn' m (by omega) hcase hts)
      | (-- m = 12
         exact subcaseB_m12_ge3087_proved n' hn' m (by omega) hcase hts)
      | (-- m = 14
         exact subcaseB_m14_ge3087_proved n' hn' m (by omega) hcase hts)
      | (-- m = 16
         exact subcaseB_m16_ge3087_proved n' hn' m (by omega) hcase hts)
      | (-- m = 18: SubcaseB never fires (inactive, F=false ∧ G=true impossible)
         exfalso
         have hcase18 : (caEvolve (n'+1) (spikeAtList 18 (2*(n'+1)+1))).getD 0 false = false := by
           rw [← rule30n_spikeAt_eq n' 18]; exact hcase
         have hts18 : (caEvolve (n'+1) (twoSpikeLastList 18 (2*(n'+1)+1))).getD 0 false = true := by
           rw [← rule30n_twoSpikeLast_eq n' 18]; exact hts
         obtain ⟨k, hn'_eq⟩ := periodReduce_diff 18 256 n' (by omega) (by omega)
         have hn''_range := periodReduce_range 18 256 n' (by omega) (by omega)
         set n'' := periodReduce 18 256 n'
         have hF_n'' : (caEvolve (n''+1) (spikeAtList 18 (2*(n''+1)+1))).getD 0 false = false := by
           have hp := spikeAt_iterated_period 18 256 (by omega) caEvolve_cert_m18_p256 n'' k
           rw [show n''+1+k*256 = n'+1 from by omega] at hp; rw [hp]; exact hcase18
         have hG_n'' : (caEvolve (n''+1) (twoSpikeLastList 18 (2*(n''+1)+1))).getD 0 false = true := by
           have hp := twoSpikeLast18_iterated_period256 n'' k (by omega)
           rw [show n''+1+k*256 = n'+1 from by omega] at hp; rw [hp]; exact hts18
         exact subcaseB_m18_never_fires ⟨n'' - 18, by omega⟩
           (by convert hF_n'' using 2; omega)
           (by convert hG_n'' using 2; omega))
      | (-- m = 20
         exact subcaseB_m20_ge3087_proved n' hn' m (by omega) hcase hts)
      | (-- m = 22
         exact subcaseB_m22_ge3087_proved n' hn' m (by omega) hcase hts)
      | (-- m = 24
         exact subcaseB_m24_ge3087_proved n' hn' m (by omega) hcase hts)
      | (-- m = 26
         exact subcaseB_m26_ge3087_proved n' hn' m (by omega) hcase hts)
      | (-- m = 28
         exact subcaseB_m28_ge3087_proved n' hn' m (by omega) hcase hts)
      | (-- m = 30
         exact subcaseB_m30_ge3087_proved n' hn' m (by omega) hcase hts))
  · -- m > 30
    push_neg at hm30
    by_cases hrm : m.val = 2 * (n' + 1) - 8
    · -- right-mirror case
      exact subcaseB_right_mirror_ge3087 n' hn' m hrm hm_even hm_low hcase hts
    · -- m > 30, not right-mirror: split into late active exceptions and inactive tail.
      by_cases hm32 : m.val = 32
      · -- m=32: inactive, SubcaseB never fires (G_32 = 0 for all n' ≥ 32)
        exfalso
        have hcase32 : (caEvolve (n'+1) (spikeAtList 32 (2*(n'+1)+1))).getD 0 false = false := by
          rw [← rule30n_spikeAt_eq n' 32]; simp only [hm32] at hcase; exact hcase
        have hts32 : (caEvolve (n'+1) (twoSpikeLastList 32 (2*(n'+1)+1))).getD 0 false = true := by
          rw [← rule30n_twoSpikeLast_eq n' 32]; simp only [hm32] at hts; exact hts
        obtain ⟨k, hn'_eq⟩ := periodReduce_diff 32 4096 n' (by omega) (by omega)
        have hn''_range := periodReduce_range 32 4096 n' (by omega) (by omega)
        set n'' := periodReduce 32 4096 n'
        have hF_n'' : (caEvolve (n''+1) (spikeAtList 32 (2*(n''+1)+1))).getD 0 false = false := by
          have hp := spikeAt_iterated_period 32 4096 (by omega) caEvolve_cert_m32_p4096 n'' k
          rw [show n''+1+k*4096 = n'+1 from by omega] at hp; rw [hp]; exact hcase32
        have hG_n'' : (caEvolve (n''+1) (twoSpikeLastList 32 (2*(n''+1)+1))).getD 0 false = true := by
          have hp := twoSpikeLast32_iterated_period4096 n'' k (by omega)
          rw [show n''+1+k*4096 = n'+1 from by omega] at hp; rw [hp]; exact hts32
        exact subcaseB_m32_never_fires_period ⟨n'' - 32, by omega⟩
          (by convert hF_n'' using 2; omega)
          (by convert hG_n'' using 2; omega)
      · by_cases hm34 : m.val = 34
        · exact subcaseB_m34_ge3087_proved n' hn' m hm34 hcase hts
        · by_cases hm36 : m.val = 36
          · exact subcaseB_m36_ge3087_proved n' hn' m hm36 hcase hts
          · by_cases hm38 : m.val = 38
            · exact subcaseB_m38_ge3087_proved n' hn' m hm38 hcase hts
            · exfalso
              exact subcaseB_mgt30_split n' hn' m hm_even hm_low (by omega) hm_ne_r hrm hm_high hcase hts

-- subcaseB_resolution_ge3087 is the public API (called by LiftingLemma_LeftPermutive).
-- The n'∈[5,3086] case is handled directly by the native_decide tower in
-- parity_sensitivity_even_subcaseB_geXXX (LiftingLemma_LeftPermutive.lean)
-- without calling this theorem.
