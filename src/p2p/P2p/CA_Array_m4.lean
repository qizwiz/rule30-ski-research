/-
CA_Array_m4.lean — Array Bool certs for m=4 SubcaseB (j=42, Level 1, Level 2)
============================================================================

Fast native_decide certificates for m=4 SubcaseB residue classes that require
large periods (P=4096 or P=16384). These certs support sensitivity_transfer
for the subcaseB_m4_ge3087 proof in SubcaseBPeriod.lean.

Sections:
  12: j=42 case (k≡42 mod 64, n'=3429): w=32, P=4096
  13: Level 1 case (n'≡5 mod 1024, ≢5 mod 4096): w=30, P=4096
  14: Level 2 case (n'≡5 mod 4096, ≢5 mod 16384): w=34, P=16384

All certs verified with Python (shrinking CA) before adding here.
-/
import P2p.CA_ArrayDef

namespace P2p

/-
================================================================================
SECTION 12: PERIOD CERTS FOR m=4 SubcaseB j=42 case: w=32, P=4096
(SubcaseBPeriod.lean: subcaseB_m4_ge3087, k≡42 mod 64 sub-case)

spike(32) full-config period divides 4096.
twoSpike(32,4) full-config period divides 4096.
Coverage: n' = 3429 + 4096*t for t ≥ 0.
Sizes: N_in = 2*4096+2*32+1 = 8257, N_out = 2*32+1 = 65.

Verified by Python (shrinking CA):
  caEvolveN(4096, spike(32, 8257)) → spike(32, 65) ✓
  caEvolveN(4096, twoSpike(32,4,8257)) → twoSpike(32,4,65) ✓
  caEvolveN(3430, spike(32,6861))[0]=false ≠ caEvolveN(3430,twoSpike(32,4,6861))[0]=true ✓
================================================================================
-/

-- Period cert: spike(32) returns to itself after 4096 CA steps
-- N_in = 2*4096+2*32+1 = 8257, N_out = 2*32+1 = 65
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_spike32_p4096 :
    (caEvolveArr 4096 (spikeArr 32 8257)).toList = (spikeArr 32 65).toList := by
  native_decide

-- Period cert: twoSpike(32,4) returns to itself after 4096 CA steps
-- max(32,4)=32, N_in=8257, N_out=65
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts324_p4096 :
    (caEvolveArr 4096 (twoSpikeArr 32 4 8257)).toList =
    (twoSpikeArr 32 4 65).toList := by
  native_decide

-- Base sensitivity: w=32 at n''=3429 (k≡42 mod 64 case)
-- n_steps=3430, tape=2*3430+1=6861
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m4_base_sens_3429_w32 :
    (caEvolveArr 3430 (spikeArr 32 6861)).toList.getD 0 false ≠
    (caEvolveArr 3430 (twoSpikeArr 32 4 6861)).toList.getD 0 false := by
  native_decide

/-- Period cert: spike(32) P=4096, List Bool form -/
theorem caEvolve_cert_spike32_p4096 :
    caEvolve 4096 (spikeAtList 32 8257) = spikeAtList 32 65 := by
  have h := caEvolveArr_cert_spike32_p4096
  rw [caEvolveArr_toList_eq, spikeArr_toList_eq, spikeArr_toList_eq] at h
  exact h

/-- Period cert: twoSpike(32,4) P=4096, List Bool form -/
theorem caEvolve_cert_ts324_p4096 :
    caEvolve 4096 (twoSpikeList 32 4 8257) = twoSpikeList 32 4 65 := by
  have h := caEvolveArr_cert_ts324_p4096
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- Base sensitivity: w=32 at n''=3429 (j=42), List Bool form -/
theorem subcaseB_m4_base_sens_3429_w32 :
    (caEvolve 3430 (spikeAtList 32 6861)).getD 0 false ≠
    (caEvolve 3430 (twoSpikeList 32 4 6861)).getD 0 false := by
  have h := caEvolveArr_m4_base_sens_3429_w32
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-
================================================================================
SECTION 13: PERIOD CERTS FOR m=4 SubcaseB Level 1 case: w=30, P=4096
(SubcaseBPeriod.lean: subcaseB_m4_ge3087, n'≡5 mod 1024, ≢5 mod 4096 sub-case)

spike(30) full-config period divides 4096.
twoSpike(30,4) full-config period divides 4096.
Coverage: n'=5125+4096*t, n'=6149+4096*t, n'=7173+4096*t (three residue classes mod 4096).
Residues mod 4096: {1029, 2053, 3077} = {5+1024k : k=1,2,3}.
Sizes: N_in = 2*4096+2*30+1 = 8253, N_out = 2*30+1 = 61.

Verified by C (shrinking CA):
  caEvolveN(4096, spike(30, 8253)) → spike(30, 61) ✓
  caEvolveN(4096, twoSpike(30,4,8253)) → twoSpike(30,4,61) ✓
  caEvolveN(5126, spike(30,10253))[0]=false ≠ caEvolveN(5126,twoSpike(30,4,10253))[0]=true ✓
  caEvolveN(6150, spike(30,12301))[0]=false ≠ caEvolveN(6150,twoSpike(30,4,12301))[0]=true ✓
  caEvolveN(7174, spike(30,14349))[0]=false ≠ caEvolveN(7174,twoSpike(30,4,14349))[0]=true ✓
================================================================================
-/

-- Period cert: spike(30) returns to itself after 4096 CA steps
-- N_in = 2*4096+2*30+1 = 8253, N_out = 2*30+1 = 61
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_spike30_p4096 :
    (caEvolveArr 4096 (spikeArr 30 8253)).toList = (spikeArr 30 61).toList := by
  native_decide

-- Period cert: twoSpike(30,4) returns to itself after 4096 CA steps
-- max(30,4)=30, N_in=8253, N_out=61
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts304_p4096 :
    (caEvolveArr 4096 (twoSpikeArr 30 4 8253)).toList =
    (twoSpikeArr 30 4 61).toList := by
  native_decide

-- Base sensitivity: w=30 at n''=5125 (Level 1 base 1, mod4096=1029)
-- n_steps=5126, tape=2*5126+1=10253
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m4_base_sens_5125_w30 :
    (caEvolveArr 5126 (spikeArr 30 10253)).toList.getD 0 false ≠
    (caEvolveArr 5126 (twoSpikeArr 30 4 10253)).toList.getD 0 false := by
  native_decide

-- Base sensitivity: w=30 at n''=6149 (Level 1 base 2, mod4096=2053)
-- n_steps=6150, tape=2*6150+1=12301
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m4_base_sens_6149_w30 :
    (caEvolveArr 6150 (spikeArr 30 12301)).toList.getD 0 false ≠
    (caEvolveArr 6150 (twoSpikeArr 30 4 12301)).toList.getD 0 false := by
  native_decide

-- Base sensitivity: w=30 at n''=7173 (Level 1 base 3, mod4096=3077)
-- n_steps=7174, tape=2*7174+1=14349
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m4_base_sens_7173_w30 :
    (caEvolveArr 7174 (spikeArr 30 14349)).toList.getD 0 false ≠
    (caEvolveArr 7174 (twoSpikeArr 30 4 14349)).toList.getD 0 false := by
  native_decide

/-- Period cert: spike(30) P=4096, List Bool form -/
theorem caEvolve_cert_spike30_p4096 :
    caEvolve 4096 (spikeAtList 30 8253) = spikeAtList 30 61 := by
  have h := caEvolveArr_cert_spike30_p4096
  rw [caEvolveArr_toList_eq, spikeArr_toList_eq, spikeArr_toList_eq] at h
  exact h

/-- Period cert: twoSpike(30,4) P=4096, List Bool form -/
theorem caEvolve_cert_ts304_p4096 :
    caEvolve 4096 (twoSpikeList 30 4 8253) = twoSpikeList 30 4 61 := by
  have h := caEvolveArr_cert_ts304_p4096
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- Base sensitivity: w=30 at n''=5125 (Level 1 base 1), List Bool form -/
theorem subcaseB_m4_base_sens_5125_w30 :
    (caEvolve 5126 (spikeAtList 30 10253)).getD 0 false ≠
    (caEvolve 5126 (twoSpikeList 30 4 10253)).getD 0 false := by
  have h := caEvolveArr_m4_base_sens_5125_w30
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-- Base sensitivity: w=30 at n''=6149 (Level 1 base 2, mod4096=2053), List Bool form -/
theorem subcaseB_m4_base_sens_6149_w30 :
    (caEvolve 6150 (spikeAtList 30 12301)).getD 0 false ≠
    (caEvolve 6150 (twoSpikeList 30 4 12301)).getD 0 false := by
  have h := caEvolveArr_m4_base_sens_6149_w30
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-- Base sensitivity: w=30 at n''=7173 (Level 1 base 3, mod4096=3077), List Bool form -/
theorem subcaseB_m4_base_sens_7173_w30 :
    (caEvolve 7174 (spikeAtList 30 14349)).getD 0 false ≠
    (caEvolve 7174 (twoSpikeList 30 4 14349)).getD 0 false := by
  have h := caEvolveArr_m4_base_sens_7173_w30
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-
================================================================================
SECTION 14: PERIOD CERTS FOR m=4 SubcaseB Level 2 case: w=34, P=16384
(SubcaseBPeriod.lean: subcaseB_m4_ge3087, n'≡5 mod 4096, ≢5 mod 16384 sub-case)

spike(34) full-config period divides 16384.
twoSpike(34,4) full-config period divides 16384.
Coverage: n'=4101, 8197, 12293 (+ 16384*t each) — three residue classes mod 16384.
Sizes: N_in = 2*16384+2*34+1 = 32837, N_out = 2*34+1 = 69.

Verified by Python (shrinking CA):
  caEvolveN(16384, spike(34, 32837)) → spike(34, 69) ✓
  caEvolveN(16384, twoSpike(34,4,32837)) → twoSpike(34,4,69) ✓
  caEvolveN(4102, spike(34,8205))[0]=false ≠ caEvolveN(4102,twoSpike(34,4,8205))[0]=true ✓
  caEvolveN(8198, spike(34,16397))[0]=false ≠ caEvolveN(8198,twoSpike(34,4,16397))[0]=true ✓
  caEvolveN(12294, spike(34,24589))[0]=false ≠ caEvolveN(12294,twoSpike(34,4,24589))[0]=true ✓
================================================================================
-/

-- Period cert: spike(34) returns to itself after 16384 CA steps
-- N_in = 2*16384+2*34+1 = 32837, N_out = 2*34+1 = 69
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_spike34_p16384 :
    (caEvolveArr 16384 (spikeArr 34 32837)).toList = (spikeArr 34 69).toList := by
  native_decide

-- Period cert: twoSpike(34,4) returns to itself after 16384 CA steps
-- max(34,4)=34, N_in=32837, N_out=69
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts344_p16384 :
    (caEvolveArr 16384 (twoSpikeArr 34 4 32837)).toList =
    (twoSpikeArr 34 4 69).toList := by
  native_decide

-- Base sensitivity: w=34 at n''=4101 (Level 2 base 1, mod16384=4101)
-- n_steps=4102, tape=2*4102+1=8205
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m4_base_sens_4101_w34 :
    (caEvolveArr 4102 (spikeArr 34 8205)).toList.getD 0 false ≠
    (caEvolveArr 4102 (twoSpikeArr 34 4 8205)).toList.getD 0 false := by
  native_decide

-- Base sensitivity: w=34 at n''=8197 (Level 2 base 2, mod16384=8197)
-- n_steps=8198, tape=2*8198+1=16397
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m4_base_sens_8197_w34 :
    (caEvolveArr 8198 (spikeArr 34 16397)).toList.getD 0 false ≠
    (caEvolveArr 8198 (twoSpikeArr 34 4 16397)).toList.getD 0 false := by
  native_decide

-- Base sensitivity: w=34 at n''=12293 (Level 2 base 3, mod16384=12293)
-- n_steps=12294, tape=2*12294+1=24589
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m4_base_sens_12293_w34 :
    (caEvolveArr 12294 (spikeArr 34 24589)).toList.getD 0 false ≠
    (caEvolveArr 12294 (twoSpikeArr 34 4 24589)).toList.getD 0 false := by
  native_decide

/-- Period cert: spike(34) P=16384, List Bool form -/
theorem caEvolve_cert_spike34_p16384 :
    caEvolve 16384 (spikeAtList 34 32837) = spikeAtList 34 69 := by
  have h := caEvolveArr_cert_spike34_p16384
  rw [caEvolveArr_toList_eq, spikeArr_toList_eq, spikeArr_toList_eq] at h
  exact h

/-- Period cert: twoSpike(34,4) P=16384, List Bool form -/
theorem caEvolve_cert_ts344_p16384 :
    caEvolve 16384 (twoSpikeList 34 4 32837) = twoSpikeList 34 4 69 := by
  have h := caEvolveArr_cert_ts344_p16384
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- Base sensitivity: w=34 at n''=4101 (Level 2 base 1), List Bool form -/
theorem subcaseB_m4_base_sens_4101_w34 :
    (caEvolve 4102 (spikeAtList 34 8205)).getD 0 false ≠
    (caEvolve 4102 (twoSpikeList 34 4 8205)).getD 0 false := by
  have h := caEvolveArr_m4_base_sens_4101_w34
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-- Base sensitivity: w=34 at n''=8197 (Level 2 base 2), List Bool form -/
theorem subcaseB_m4_base_sens_8197_w34 :
    (caEvolve 8198 (spikeAtList 34 16397)).getD 0 false ≠
    (caEvolve 8198 (twoSpikeList 34 4 16397)).getD 0 false := by
  have h := caEvolveArr_m4_base_sens_8197_w34
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-- Base sensitivity: w=34 at n''=12293 (Level 2 base 3), List Bool form -/
theorem subcaseB_m4_base_sens_12293_w34 :
    (caEvolve 12294 (spikeAtList 34 24589)).getD 0 false ≠
    (caEvolve 12294 (twoSpikeList 34 4 24589)).getD 0 false := by
  have h := caEvolveArr_m4_base_sens_12293_w34
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

end P2p
