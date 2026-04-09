/-
SubcaseB_X2_Core.lean — Heavy native_decide theorems for SubcaseB X-witness proofs
======================================================================================

This file is split from SubcaseB_X2_Witness.lean to protect the olean cache.
SubcaseB_X2_Witness.lean imports this file.

Build times (approximate, this machine):
  Section A (4 X=2 witness theorems):
    G2mFast40_T40984  : ~55s   (T=40984,  tape~1282 words)
    G2mFast40_T61460  : ~115s  (T=61460,  tape~1922 words)
    G2mFast42_T118805 : ~15min (T=118805, tape~3714 words)
    G2mFast46_T106523 : ~15min (T=106523, tape~3330 words)
    Section A total   : ~30-35 min

  Section C (period cert for G_{2,40}):
    G2m40_period_cert_arr : ~5-30 min (Array Bool, 65536 steps)

  Section D (combined witness theorems for m=44, m=48):
    x4_witnesses_m44_at_n249877_core : ~1-2 hours (T=249878, tape~7810 words)
    x6_witnesses_m48_at_n262167_core : ~1-2 hours (T=262168, tape~8194 words)
    Section D total : ~2-4 hours

Total overnight build: ~5-8 hours.
-/

import P2p.CA_ArrayDef

/-
================================================================================
SECTION A: PROVED THEOREMS (X=2 witnesses for m=40,42,46)
================================================================================
-/

-- G_{2,40}(40984) = true. Proved by native_decide.
-- F_2(40984) = (40984%2==1) = false → G ≠ F → X=2 witnesses SubcaseB at n'=40983.
set_option maxHeartbeats 16000000000 in
theorem G2mFast40_T40984 : G2mFast 40 40984 = true := by native_decide

-- G_{2,40}(61460) = true. Proved by native_decide.
-- F_2(61460) = (61460%2==1) = false → G ≠ F → X=2 witnesses SubcaseB at n'=61459.
set_option maxHeartbeats 16000000000 in
theorem G2mFast40_T61460 : G2mFast 40 61460 = true := by native_decide

-- G_{2,42}(118805) = false. Proved by native_decide.
-- F_2(118805) = (118805%2==1) = true → G ≠ F → X=2 witnesses SubcaseB at n'=118804.
set_option maxHeartbeats 64000000000 in
theorem G2mFast42_T118805 : G2mFast 42 118805 = false := by native_decide

-- G_{2,46}(106523) = false. Proved by native_decide.
-- F_2(106523) = (106523%2==1) = true → G ≠ F → X=2 witnesses SubcaseB at n'=106522.
set_option maxHeartbeats 64000000000 in
theorem G2mFast46_T106523 : G2mFast 46 106523 = false := by native_decide

/-
================================================================================
SECTION C: PERIOD CERTIFICATES (Array Bool via native_decide)
================================================================================

G_{2,40} period: 65536 steps on tape size 131153 → 81-element tape.
caEvolveArr shrinks by 2 per step: 131153 - 2*65536 = 81 ✓
Total Array Bool ops ≈ 4.3B. Estimated time: 5-30 min.

Converted to list form via G2m40_period_cert in SubcaseB_X2_Witness.lean:
  caEvolve 65536 (twoSpikeList 2 40 131153) = twoSpikeList 2 40 81
-/

/-- Period cert for G_{2,40}: Array Bool version, proved via native_decide.
    Tape: twoSpikeArr 2 40 131153 (size 131153). After 65536 steps → size 81.
    Result = twoSpikeArr 2 40 81 (spikes at 2 and 40 on 81-cell tape). -/
set_option maxHeartbeats 300000000000 in
theorem G2m40_period_cert_arr :
    caEvolveArr 65536 (twoSpikeArr 2 40 131153) = twoSpikeArr 2 40 81 := by
  native_decide  -- estimated 5-30 min (Array Bool, 65536 steps, shrinking tape)

/-
================================================================================
SECTION D: COMBINED WITNESS THEOREMS (X=4 for m=44, X=6 for m=48)
================================================================================

Instead of proving GXmFast and FXFast separately (4 theorems, 4 native_decides),
we directly prove inequality in 2 combined theorems (2 native_decides).
Each evaluates both computations and checks they differ in one shot.

Performance estimates (tape~7810-8194 UInt64 words, T~250K steps):
  x4_witnesses_m44_at_n249877_core : ~1-2 hours
  x6_witnesses_m48_at_n262167_core : ~1-2 hours

Total Section D build: ~2-4 hours. Run overnight after Section A+C complete.
Verified by C program (stream_G2m_all.c, 280s): X=4 witnesses m=44, X=6 witnesses m=48.
-/

-- m=44 at n'=249877 (T=249878): X=4 witnesses.
-- G_{4,44}(249878)=true, F_4(249878)=false → differ.
-- Period of F_4 is 8; 249878 mod 8 = 6; FXFast 4 6 = false (proved in Witness.lean).
set_option maxHeartbeats 300000000000 in
theorem x4_witnesses_m44_at_n249877_core : GXmFast 4 44 249878 ≠ FXFast 4 249878 := by
  native_decide  -- ~1-2 hours; computes both GXmFast and FXFast at T=249878

-- m=48 at n'=262167 (T=262168): X=6 witnesses.
-- G_{6,48}(262168)=false, F_6(262168)=true → differ.
-- Period of F_6 is 16; 262168 mod 16 = 8; FXFast 6 8 = true (proved in Witness.lean).
set_option maxHeartbeats 300000000000 in
theorem x6_witnesses_m48_at_n262167_core : GXmFast 6 48 262168 ≠ FXFast 6 262168 := by
  native_decide  -- ~1-2 hours; computes both GXmFast and FXFast at T=262168
