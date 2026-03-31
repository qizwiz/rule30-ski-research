/-
SubcaseB_BaseSens.lean
======================
Split-off file containing large native_decide base-sensitivity proofs for m=22.

These were previously in SubcaseBPeriod.lean but caused OOM during C code generation
(symbol #9704: subcaseB_m22_base_sens_6926._native.native_decide.decl_1_1._closed_1)
because the combined C symbol count for SubcaseBPeriod.lean exceeded memory limits.

Solution: compile these 6 large native_decide proofs in a separate file (own C symbol
namespace) using Array Bool (caEvolveArr) for efficiency, then export List Bool theorems.

Pattern mirrors CA_Array.lean: caEvolveArr native_decide + theorem wrapper via toList_eq.
-/

import P2p.CA_ArrayDef

/-
================================================================================
SECTION: m=22 BASE SENSITIVITY PROOFS (large tapes, moved out of SubcaseBPeriod)
================================================================================
-/

-- Base sensitivity: w=5 at n''=6926 (step=6927, tape=13855)
-- caEvolve(spike(5,13855)) ≠ caEvolve(twoSpike(5,22,13855)) at step 6927
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m22_base_sens_6926_w5 :
    (caEvolveArr 6927 (spikeArr 5 13855)).toList.getD 0 false ≠
    (caEvolveArr 6927 (twoSpikeArr 5 22 13855)).toList.getD 0 false := by
  native_decide

/-- Base sensitivity: w=5 at n''=6926, List Bool form -/
theorem subcaseB_m22_base_sens_6926 :
    (caEvolve 6927 (spikeAtList 5 13855)).getD 0 false ≠
    (caEvolve 6927 (twoSpikeList 5 22 13855)).getD 0 false := by
  have h := caEvolveArr_m22_base_sens_6926_w5
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

-- Base sensitivity: w=4 at n''=3342 (step=3343, tape=6687)
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m22_base_sens_3342_w4 :
    (caEvolveArr 3343 (spikeArr 4 6687)).toList.getD 0 false ≠
    (caEvolveArr 3343 (twoSpikeArr 4 22 6687)).toList.getD 0 false := by
  native_decide

/-- Base sensitivity: w=4 at n''=3342, List Bool form -/
theorem subcaseB_m22_base_sens_3342 :
    (caEvolve 3343 (spikeAtList 4 6687)).getD 0 false ≠
    (caEvolve 3343 (twoSpikeList 4 22 6687)).getD 0 false := by
  have h := caEvolveArr_m22_base_sens_3342_w4
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

-- Base sensitivity: w=2 at n''=3598 (step=3599, tape=7199)
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m22_base_sens_3598_w2 :
    (caEvolveArr 3599 (spikeArr 2 7199)).toList.getD 0 false ≠
    (caEvolveArr 3599 (twoSpikeArr 2 22 7199)).toList.getD 0 false := by
  native_decide

/-- Base sensitivity: w=2 at n''=3598, List Bool form -/
theorem subcaseB_m22_base_sens_3598 :
    (caEvolve 3599 (spikeAtList 2 7199)).getD 0 false ≠
    (caEvolve 3599 (twoSpikeList 2 22 7199)).getD 0 false := by
  have h := caEvolveArr_m22_base_sens_3598_w2
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

-- Base sensitivity: w=2 at n''=4110 (step=4111, tape=8223)
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m22_base_sens_4110_w2 :
    (caEvolveArr 4111 (spikeArr 2 8223)).toList.getD 0 false ≠
    (caEvolveArr 4111 (twoSpikeArr 2 22 8223)).toList.getD 0 false := by
  native_decide

/-- Base sensitivity: w=2 at n''=4110, List Bool form -/
theorem subcaseB_m22_base_sens_4110 :
    (caEvolve 4111 (spikeAtList 2 8223)).getD 0 false ≠
    (caEvolve 4111 (twoSpikeList 2 22 8223)).getD 0 false := by
  have h := caEvolveArr_m22_base_sens_4110_w2
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

-- Base sensitivity: w=12 at n''=3854 (step=3855, tape=7711)
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m22_base_sens_3854_w12 :
    (caEvolveArr 3855 (spikeArr 12 7711)).toList.getD 0 false ≠
    (caEvolveArr 3855 (twoSpikeArr 12 22 7711)).toList.getD 0 false := by
  native_decide

/-- Base sensitivity: w=12 at n''=3854, List Bool form -/
theorem subcaseB_m22_base_sens_3854 :
    (caEvolve 3855 (spikeAtList 12 7711)).getD 0 false ≠
    (caEvolve 3855 (twoSpikeList 12 22 7711)).getD 0 false := by
  have h := caEvolveArr_m22_base_sens_3854_w12
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

-- Base sensitivity: w=18 at n''=782 (step=783, tape=1567)
-- Small tape — fast even with List Bool; here for completeness
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m22_base_sens_782_w18 :
    (caEvolveArr 783 (spikeArr 18 1567)).toList.getD 0 false ≠
    (caEvolveArr 783 (twoSpikeArr 18 22 1567)).toList.getD 0 false := by
  native_decide

/-- Base sensitivity: w=18 at n''=782, List Bool form -/
theorem subcaseB_m22_base_sens_782 :
    (caEvolve 783 (spikeAtList 18 1567)).getD 0 false ≠
    (caEvolve 783 (twoSpikeList 18 22 1567)).getD 0 false := by
  have h := caEvolveArr_m22_base_sens_782_w18
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h
