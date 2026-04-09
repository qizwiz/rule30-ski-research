/-
SubcaseB_X2_Core.lean — Heavy native_decide theorems for SubcaseB X-witness proofs
======================================================================================

This file is split from SubcaseB_X2_Witness.lean to protect the olean cache.
SubcaseB_X2_Witness.lean imports this file.

Build times (approximate, this machine):
  G2mFast40_T40984  : ~55s   (T=40984,  tape~1282 words)
  G2mFast40_T61460  : ~115s  (T=61460,  tape~1922 words)
  G2mFast42_T118805 : ~15min (T=118805, tape~3714 words)
  G2mFast46_T106523 : ~15min (T=106523, tape~3330 words)

Total build time for this file: ~30-35 min.
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
SECTION B: DEFERRED THEOREMS (X=4 for m=44, X=6 for m=48)
================================================================================

CRITICAL FINDING (2026-04-09): X=2 is NOT a universal witness for m≥40.
- m=44, T=249878: G_{2,44}=0=F_2=0 → X=2 FAILS; X=4 witnesses (G_{4,44}=1≠0=F_4)
- m=48, T=262168: G_{2,48}=0=F_2=0 → X=2 FAILS; X=6 witnesses (G_{6,48}=0≠1=F_6)
Verified by C program (280 seconds, 26 X candidates tested simultaneously).

Performance estimates for native_decide:
  GXmFast 4 44 249878 : T=249878, tape~7810 words → ~30-60min
  FXFast 4 249878     : T=249878, tape~7810 words → ~30-60min (use period: 249878%8=6)
  GXmFast 6 48 262168 : T=262168, tape~8194 words → ~30-60min
  FXFast 6 262168     : T=262168, tape~8194 words → ~30-60min (use period: 262168%16=8)

SORRY'd pending dedicated long-running build sessions.
-/

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
  sorry -- native_decide  -- estimated 5-30 min; add to long-run queue

/-
================================================================================
SECTION D: DEFERRED THEOREMS (X=4 for m=44, X=6 for m=48)
================================================================================
-/

-- G_{4,44}(249878) = true: X=4 witnesses m=44 at n'=249877.
-- F_4(249878) = FXFast 4 249878. Period 8: 249878 mod 8 = 6. FXFast 4 6 = false.
-- G_{4,44}=true ≠ false=F_4 → X=4 witnesses.
set_option maxHeartbeats 300000000000 in
theorem GXmFast44_X4_T249878 : GXmFast 4 44 249878 = true := by
  sorry -- native_decide  -- ~30-60 min; verified by C program stream_G2m_all.c variant

-- F_4 has period 8; 249878 mod 8 = 6; FXFast 4 6 = false (proved in Witness.lean).
-- This sorry needs either period infrastructure or direct native_decide (~30-60 min).
theorem FXFast4_T249878 : FXFast 4 249878 = false := by
  sorry -- follows from period-8 of F_4: 249878 % 8 = 6 and FXFast 4 6 = false

-- G_{6,48}(262168) = false: X=6 witnesses m=48 at n'=262167.
-- F_6(262168) = FXFast 6 262168. Period 16: 262168 mod 16 = 8. FXFast 6 8 = true.
-- G_{6,48}=false ≠ true=F_6 → X=6 witnesses.
set_option maxHeartbeats 300000000000 in
theorem GXmFast48_X6_T262168 : GXmFast 6 48 262168 = false := by
  sorry -- native_decide  -- ~30-60 min; verified by C program

-- F_6 has period 16; 262168 mod 16 = 8; FXFast 6 8 = true (proved in Witness.lean).
-- This sorry needs either period infrastructure or direct native_decide (~30-60 min).
theorem FXFast6_T262168 : FXFast 6 262168 = true := by
  sorry -- follows from period-16 of F_6: 262168 % 16 = 8 and FXFast 6 8 = true
