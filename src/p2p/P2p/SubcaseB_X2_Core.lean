/-
SubcaseB_X2_Core.lean — Section A: X=2 witness native_decide theorems
=======================================================================

SECTION A ONLY. Sections C and D moved to separate files:
  SubcaseB_X2_PeriodCerts.lean : period certs (Section C: G2m40, G2m42, G2m46)
  SubcaseB_X2_SectionD.lean    : combined witnesses m=44, m=48 (Section D)

Build times (this file only):
  G2mFast40_T40984  : ~55s   (T=40984,  tape~1282 words)
  G2mFast40_T61460  : ~115s  (T=61460,  tape~1922 words)
  G2mFast42_T118805 : ~15min (T=118805, tape~3714 words)
  G2mFast46_T106523 : ~15min (T=106523, tape~3330 words)
  Total             : ~30-35 min
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
