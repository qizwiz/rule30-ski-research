/-
CA_Array_m44.lean — Array Bool certs for the active m=44 branch
===========================================================================

This file packages the compile-checked witness kernel for `m=44` using
the interior witness `w=4`:

- `spike(44)` period cert at `P=262144` (for twoSpikeLast period lemma)
- H=1 cert for the right spike at `P=262144`
- `twoSpike(4,44)` period cert at `P=262144` (witness period)
- base sensitivity at `n''=249877` (w=4, T=249878): F_4=0, G_{4,44}=1 → differ ✓

SubcaseB events verified (2026-04-13):
- SubcaseB for m=44 fires at T=249878 (n''=249877) in first period
- Exactly 1 event per period: 37-candidate offset search found no second event
- Period P=262144 confirmed by numba period cert (period_certs_v2.out ✓ PASS)
- X=4 witness verified (check_m44_T249878.py: F_4=0, G_{4,44}=1 at T=249878)
- X=2 fails at T=249878 (F_2=0=G_{2,44}=0 — same)

Lean cert sizes:
  spike(44) cert: caEvolveArr 262144 (spikeArr 44 524377) = spikeArr 44 89
    (N_in = 2*262144+2*44+1 = 524377, N_out = 2*44+1 = 89)
  twoSpike cert: caEvolveArr 262144 (twoSpikeArr 4 44 524377) = twoSpikeArr 4 44 89
    (N_in = 2*262144+2*max(4,44)+1 = 524377, N_out = 2*44+1 = 89)
  H=1 cert: caEvolveArr 262144 (spikeArr 524288 524289).getD 0 = true
  base sens n''=249877: caEvolveArr 249878 (spikeArr 4 499757) getD 0 ≠ caEvolveArr 249878 (twoSpikeArr 4 44 499757) getD 0
-/
import P2p.CA_ArrayDef

namespace P2p

-- spike(44) period cert at P=262144 (for twoSpikeLast period lemma):
-- N_in = 2*262144+2*44+1 = 524377, N_out = 2*44+1 = 89
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_spike44_p262144 :
    (caEvolveArr 262144 (spikeArr 44 524377)).toList =
    (spikeArr 44 89).toList := by native_decide

-- H=1 cert for right spike at P=262144:
-- spikeArr (2*P) (2*P+1) = spikeArr 524288 524289
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_h1_p262144 :
    (caEvolveArr 262144 (spikeArr 524288 524289)).toList.getD 0 false = true := by native_decide

-- twoSpike(4,44) period cert at P=262144 (witness period):
-- N_in = 2*262144+2*max(4,44)+1 = 524377, N_out = 2*44+1 = 89
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts444_p262144 :
    (caEvolveArr 262144 (twoSpikeArr 4 44 524377)).toList =
    (twoSpikeArr 4 44 89).toList := by native_decide

-- Base sensitivity at n''=249877, w=4 (T=249878):
-- F_4(249878) = 0, G_{4,44}(249878) = 1 → differ ✓
-- Tape size = 2*249878+1 = 499757
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m44_base_sens_249877_w4 :
    (caEvolveArr 249878 (spikeArr 4 499757)).toList.getD 0 false ≠
    (caEvolveArr 249878 (twoSpikeArr 4 44 499757)).toList.getD 0 false := by
  native_decide

/-- Base sensitivity for `m=44`, `w=4` at `n''=249877`, in `List Bool` form. -/
theorem subcaseB_m44_base_sens_249877_w4 :
    (caEvolve 249878 (spikeAtList 4 499757)).getD 0 false ≠
    (caEvolve 249878 (twoSpikeList 4 44 499757)).getD 0 false := by
  have h := caEvolveArr_m44_base_sens_249877_w4
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-- `spike(44)` period cert at `P=262144`, in `List Bool` form. -/
theorem caEvolve_cert_spike44_p262144 :
    caEvolve 262144 (spikeAtList 44 524377) = spikeAtList 44 89 := by
  have h := caEvolveArr_cert_spike44_p262144
  rw [caEvolveArr_toList_eq, spikeArr_toList_eq, spikeArr_toList_eq] at h
  exact h

/-- Right-spike `H=1` cert for `P=262144`, in `List Bool` form. -/
theorem caEvolve_h1_p262144 :
    (caEvolve 262144 (spikeAtList 524288 524289)).getD 0 false = true := by
  have h := caEvolveArr_h1_p262144
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq] at h

/-- `twoSpike(4,44)` period cert at `P=262144`, in `List Bool` form. -/
theorem caEvolve_cert_ts444_p262144 :
    caEvolve 262144 (twoSpikeList 4 44 524377) = twoSpikeList 4 44 89 := by
  have h := caEvolveArr_cert_ts444_p262144
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- `G_{44,last}` period lemma at `P=262144`. -/
lemma rule30n_twoSpikeLast44_period262144 (n : Nat) (hn : n ≥ 44) :
    (caEvolve (n + 1) (twoSpikeLastList 44 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 262144) (twoSpikeLastList 44 (2 * ((n + 1) + 262144) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 44 262144 caEvolve_cert_spike44_p262144 caEvolve_h1_p262144 n hn

end P2p
