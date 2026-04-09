/-
SubcaseB_X2_PeriodCerts.lean — Period certificates for G_{X,m} sequences
==========================================================================

Per-m period certificates enabling sensitivity_transfer to cover all periodic
SubcaseB events (not just the first one).

Architecture: heavy native_decide proofs only. Imports CA_ArrayDef directly.
This file is imported by SubcaseB_X2_Witness.lean.

Verified by Python (numpy, shrinking tape):
  G2m40 period 65536 (62K steps, 18s)  — PYTHON CONFIRMED 2026-04-09
  G2m42 period 131072 (262K steps, 24s) — PYTHON CONFIRMED 2026-04-09

Build time estimates (caEvolveArr, Array Bool):
  G2m40_period_cert_arr: ~5-30 min (65536 steps, tape 131153)
  G2m42_period_cert_arr: ~20 min - 2 hours (131072 steps, tape 262229)
  G2m46_period_cert_arr: ~2-10 hours (524288 steps, tape 1048661)
  (SubcaseB_X2_Core.lean handles Section A; this file only has period certs)
-/

import P2p.CA_ArrayDef
import P2p.SubcaseB_X2_Core

/-
================================================================================
SECTION 0: G_{2,40} PERIOD CERTIFICATE (period = 65536 = 2^16)
================================================================================

G_{2,40} has period 65536 (LFSR analysis: L=57347, P=2^16=65536).
Tape: twoSpikeArr 2 40 131153 (size = 2*65536 + 2*40 + 1 = 131153).
After P steps: 131153 - 2*65536 = 81 = 2*40 + 1.

Python-verified 2026-04-09: caEvolve 65536 (twoSpikeList 2 40 131153) = twoSpikeList 2 40 81
Build time estimate: ~5-30 min (Array Bool, 65536 steps, ~4.3B bool ops).
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
SECTION 1: G_{2,42} PERIOD CERTIFICATE (period = 131072 = 2^17)
================================================================================

Verified by Python: caEvolve 131072 (twoSpikeList 2 42 262229) = twoSpikeList 2 42 85

Tape parameters:
  N = 2*P + 2*m + 1 = 2*131072 + 2*42 + 1 = 262229
  After P steps: N - 2*P = 262229 - 262144 = 85 = 2*42 + 1

This proves G_{2,42} has period dividing 131072.
Combined with the LFSR analysis (L=122884, P=2^17=131072), period = exactly 131072.
-/

/-- Period cert for G_{2,42}: Array Bool version, proved via native_decide.
    Tape: twoSpikeArr 2 42 262229 (size 262229). After 131072 steps → size 85.
    Result = twoSpikeArr 2 42 85 (spikes at 2 and 42 on 85-cell tape).
    Python-verified 2026-04-09: MATCH True (24s with numpy). -/
set_option maxHeartbeats 1200000000000 in
theorem G2m42_period_cert_arr :
    caEvolveArr 131072 (twoSpikeArr 2 42 262229) = twoSpikeArr 2 42 85 := by
  native_decide  -- estimated 20 min - 2 hours (4× G2m40 cert, 131072 steps)

/-- Period cert for G_{2,42}: list version. Derived from G2m42_period_cert_arr.
    caEvolve 131072 (twoSpikeList 2 42 262229) = twoSpikeList 2 42 85 -/
theorem G2m42_period_cert :
    caEvolve 131072 (twoSpikeList 2 42 262229) = twoSpikeList 2 42 85 := by
  have h := congrArg Array.toList G2m42_period_cert_arr
  simp only [caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-
================================================================================
SECTION 2: G_{2,46} PERIOD CERTIFICATE (period = 524288 = 2^19)
================================================================================

Period of G_{2,46}: 524288 (from LFSR analysis: L=262145, P=2^19).
Tape: N = 2*524288 + 2*46 + 1 = 1048669.
After P steps: 1048669 - 2*524288 = 93 = 2*46 + 1.

Python verification (numpy, 2026-04-09): 398.7s, MATCH: True.
  - Initial tape size: 1048669 elements
  - Final size: 93, spikes at [2, 46] ✓

Lean native_decide estimate: unclear due to Array Bool overhead.
The G2m40 cert (N=131153, P=65536) is estimated 5-30 min.
G2m46 is 64× larger: may take 5-32 hours with Array Bool.
ALTERNATIVE NEEDED: UInt64 approach or algebraic proof.
-/

-- NOTE: caEvolveArr with Array Bool is likely too slow for P=524288 (estimated 5-32 hours).
-- Activating this pending investigation of alternative approaches.
-- Python-confirmed: caEvolve 524288 (twoSpikeList 2 46 1048669) = twoSpikeList 2 46 93
-- set_option maxHeartbeats 4800000000000 in
-- theorem G2m46_period_cert_arr :
--     caEvolveArr 524288 (twoSpikeArr 2 46 1048669) = twoSpikeArr 2 46 93 := by
--   native_decide  -- may need hours; use algebraic approach instead

/-
================================================================================
SECTION 3: G_{4,44} PERIOD CERTIFICATE (period = 262144 = 2^18)
================================================================================

G_{4,44} has period dividing 262144 (LFSR analysis: P=2^18).
Tape for sensitivity_transfer: twoSpikeArr 4 44 N where N = 2*P + 2*44 + 1 = 524377.
After P steps: 524377 - 2*262144 = 89 = 2*44 + 1.

TODO: Python-verify first.
-/

-- TODO: Python verification then native_decide

/-
================================================================================
SECTION 4: G_{6,48} PERIOD CERTIFICATE
================================================================================

G_{6,48} period unknown. Need computational analysis.
TODO: Determine period by LFSR analysis or C program.
-/
