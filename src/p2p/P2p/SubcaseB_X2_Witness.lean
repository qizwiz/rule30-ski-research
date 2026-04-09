/-
SubcaseB_X2_Witness.lean — Per-m Sensitivity Witnesses for SubcaseB at m ≥ 40
===============================================================================

For even m ≥ 40, SubcaseB fires at infinitely many n'. We verify sensitivity
witnesses at specific SubcaseB events. CORRECTION (2026-04-09): X=2 is NOT a
universal witness — it fails for m=44 and m=48.

Per-m witnesses verified:
  m=40, m=42, m=46: X=2 witnesses (G_{2,m} ≠ F_2 at first SubcaseB events)
  m=44: X=4 witnesses (G_{4,44} ≠ F_4; X=2 fails)
  m=48: X=6 witnesses (G_{6,48} ≠ F_6; X=2, X=4 fail)

Notation:
  F_X(T) = FXFast X T = center after T steps from single spike at X
  G_{X,m}(T) = GXmFast X m T = center after T steps from spikes at X AND m
  SubcaseB at n': F_m(n'+1)=false AND G_{m,last}(n'+1)=true
  X witnesses at n': G_{X,m}(n'+1) ≠ F_X(n'+1)

Architecture: heavy native_decide proofs are in SubcaseB_X2_Core.lean (imported).
This file imports Core and contains only fast theorems (FXFast small-T, witnesses).

Build times: this file ~5s. Core.lean ~30-35 min (heavy native_decides).
-/

import P2p.CA_ArrayDef
import P2p.SubcaseB_X2_Core

/-
================================================================================
SECTION 1: SMALL SANITY CHECK (PROVED via native_decide)
================================================================================

G_{2,40}(41) = false and F_2(41) = true → they differ → X=2 witnesses at T=41.
(Note: T=41 is not a SubcaseB event for m=40, but confirms the infrastructure works.)
Build time: ~5.6s total.
-/

set_option maxHeartbeats 400000000 in
/-- Sanity check: G_{2,40}(41) = false. Proved by native_decide in 5.6s. -/
theorem G2m40_at_T41 :
    (G2mCenterSeq 40 41).getD 40 false = false := by
  native_decide

/-- G_{2,40}(41) ≠ F_2(41): false ≠ true. -/
theorem x2_at_T41_witnesses :
    (G2mCenterSeq 40 41).getD 40 false ≠ (41 % 2 == 1) := by
  rw [G2m40_at_T41]; decide

/-
================================================================================
SECTION 2: MAIN WITNESS THEOREMS (defined in SubcaseB_X2_Core.lean)
================================================================================

The heavy native_decide theorems are in SubcaseB_X2_Core.lean to protect the
olean cache. This file imports Core, so all theorems are available here.

Proved in Core:
  G2mFast40_T40984 : G2mFast 40 40984 = true   (X=2 witnesses m=40 at n'=40983)
  G2mFast40_T61460 : G2mFast 40 61460 = true   (X=2 witnesses m=40 at n'=61459)
  G2mFast42_T118805 : G2mFast 42 118805 = false (X=2 witnesses m=42 at n'=118804)
  G2mFast46_T106523 : G2mFast 46 106523 = false (X=2 witnesses m=46 at n'=106522)
-/

/-
================================================================================
SECTION 3: WITNESS STATEMENTS (depend on Core theorems)
================================================================================
-/

-- X=2 witnesses SubcaseB for m=40 at n'=40983.
-- G_{2,40}(40984) = true ≠ false = F_2(40984).
theorem x2_witnesses_m40_at_n40983 : G2mFast 40 40984 ≠ (40984 % 2 == 1) := by
  rw [G2mFast40_T40984]; decide

-- X=2 witnesses SubcaseB for m=40 at n'=61459.
-- G_{2,40}(61460) = true ≠ false = F_2(61460).
theorem x2_witnesses_m40_at_n61459 : G2mFast 40 61460 ≠ (61460 % 2 == 1) := by
  rw [G2mFast40_T61460]; decide

-- X=2 witnesses SubcaseB for m=42 at n'=118804.
-- G_{2,42}(118805) = false ≠ true = F_2(118805).
theorem x2_witnesses_m42_at_n118804 : G2mFast 42 118805 ≠ (118805 % 2 == 1) := by
  rw [G2mFast42_T118805]; decide

-- X=2 witnesses SubcaseB for m=46 at n'=106522.
-- G_{2,46}(106523) = false ≠ true = F_2(106523).
theorem x2_witnesses_m46_at_n106522 : G2mFast 46 106523 ≠ (106523 % 2 == 1) := by
  rw [G2mFast46_T106523]; decide

/-
================================================================================
SECTION 4: G2mCenterSeq CORRECTNESS — PROVED IN CA_ArrayDef
================================================================================

G2mCenterSeq_correct is proved in CA_ArrayDef.lean (imported).
It connects G2mCenterSeq to direct caEvolveArr computations:
  (G2mCenterSeq m T_max).getD t false =
  (caEvolveArr (t+1) (twoSpikeArr 2 m (2*(t+1)+1))).getD 0 false

The proof uses G2mCenterSeqAux_inv (loop invariant) + caEvolve_agree (causal cone).
-/

-- Check G2mCenterSeq_correct is accessible (proved in CA_ArrayDef.lean)
example : ∀ m T_max t : Nat, t < T_max →
    (G2mCenterSeq m T_max).getD t false =
    (caEvolveArr (t + 1) (twoSpikeArr 2 m (2 * (t + 1) + 1))).getD 0 false :=
  G2mCenterSeq_correct

/-
================================================================================
SECTION 5: PERIOD CERTIFICATE (SORRY — deferred, cost ~96 min native_decide)
================================================================================

G_{2,40} has period 65536 (verified by LFSR analysis in patterns.md).
Cert form: caEvolveArr 65536 (twoSpikeArr 2 40 131153) = twoSpikeArr 2 40 81.
Once proved, rule30n_twoSpike_period extends coverage to all n' ≡ {40983, 61459} mod 65536.
-/

/-- Period cert: G_{2,40} sequence has period 65536. -/
theorem G2m40_period_cert :
    caEvolve 65536 (twoSpikeList 2 40 131153) = twoSpikeList 2 40 81 := by
  sorry

/-
================================================================================
SECTION 6: NEW WITNESSES FOR m=44 AND m=48
================================================================================

CRITICAL FINDING (2026-04-09): X=2 is NOT a universal witness for m≥40.
- m=44, T=249878: G_{2,44}=0=F_2=0 → X=2 FAILS; X=4 witnesses (G_{4,44}=1≠0=F_4)
- m=48, T=262168: G_{2,48}=0=F_2=0 → X=2 FAILS; X=6 witnesses (G_{6,48}=0≠1=F_6)
Verified by C program (280 seconds, 26 X candidates tested simultaneously).

Heavy theorems (GXmFast44_X4_T249878, FXFast4_T249878, GXmFast48_X6_T262168,
FXFast6_T262168) are SORRY'd in SubcaseB_X2_Core.lean, pending long native_decide runs.
-/

-- F4 period 8: F4(6) = false. 249878 mod 8 = 6, so FXFast4_T249878 = false.
set_option maxHeartbeats 4000000 in
theorem FXFast4_T6 : FXFast 4 6 = false := by native_decide

-- F6 period 16: F6(8) = true. 262168 mod 16 = 8, so FXFast6_T262168 = true.
set_option maxHeartbeats 4000000 in
theorem FXFast6_T8 : FXFast 6 8 = true := by native_decide

-- m=44 at n'=249877 (T=249878): X=4 witnesses.
-- GXmFast44_X4_T249878 = true and FXFast4_T249878 = false (both in Core, sorry'd).
theorem x4_witnesses_m44_at_n249877 : GXmFast 4 44 249878 ≠ FXFast 4 249878 := by
  rw [GXmFast44_X4_T249878, FXFast4_T249878]; decide

-- m=48 at n'=262167 (T=262168): X=6 witnesses.
-- GXmFast48_X6_T262168 = false and FXFast6_T262168 = true (both in Core, sorry'd).
theorem x6_witnesses_m48_at_n262167 : GXmFast 6 48 262168 ≠ FXFast 6 262168 := by
  rw [GXmFast48_X6_T262168, FXFast6_T262168]; decide

