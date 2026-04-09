/-
SubcaseB_X2_SectionD.lean — Combined witness theorems for m=44 and m=48
=========================================================================

Section D: GXmFast ≠ FXFast at the first SubcaseB events for m=44 and m=48.

These proofs take ~1-2 hours each. Split into a separate file to:
1. Protect Section A's olean cache (SubcaseB_X2_Core.lean)
2. Allow independent build/rebuild of these heavy theorems

Verified by C program (stream_G2m_all.c, 280s, 2026-04-08):
  X=4 witnesses m=44 at n'=249877: G_{4,44}=1 ≠ F_4=0
  X=6 witnesses m=48 at n'=262167: G_{6,48}=0 ≠ F_6=1

Build times (approximate):
  x4_witnesses_m44_at_n249877_core : ~1-2 hours (T=249878, tape~7810 UInt64 words)
  x6_witnesses_m48_at_n262167_core : ~1-2 hours (T=262168, tape~8194 UInt64 words)
  Total: ~2-4 hours
-/

import P2p.CA_ArrayDef

/-
================================================================================
COMBINED WITNESS THEOREMS (X=4 for m=44, X=6 for m=48)
================================================================================

Instead of proving GXmFast and FXFast separately (4 theorems, 4 native_decides),
we directly prove inequality in 2 combined theorems (2 native_decides).
Each evaluates both computations and checks they differ in one shot.
-/

-- m=44 at n'=249877 (T=249878): X=4 witnesses.
-- G_{4,44}(249878)=true, F_4(249878)=false → differ.
-- F_4 period = 8; 249878 mod 8 = 6; F_4(6) = false ✓
-- C-program verified (stream_G2m_all.c, 2026-04-08)
set_option maxHeartbeats 300000000000 in
theorem x4_witnesses_m44_at_n249877_core : GXmFast 4 44 249878 ≠ FXFast 4 249878 := by
  native_decide  -- ~1-2 hours; computes both GXmFast and FXFast at T=249878

-- m=48 at n'=262167 (T=262168): X=6 witnesses.
-- G_{6,48}(262168)=false, F_6(262168)=true → differ.
-- F_6 period = 16; 262168 mod 16 = 8; F_6(8) = true ✓
-- C-program verified (stream_G2m_all.c, 2026-04-08)
set_option maxHeartbeats 300000000000 in
theorem x6_witnesses_m48_at_n262167_core : GXmFast 6 48 262168 ≠ FXFast 6 262168 := by
  native_decide  -- ~1-2 hours; computes both GXmFast and FXFast at T=262168
