/-
CA_Array_m46.lean — Array Bool certs for the active m=46 branch
===========================================================================

This file packages the compile-checked witness kernel for `m=46` using
the interior witness `w=2`:

- `spike(46)` period cert at `P=524288` (for twoSpikeLast period lemma)
- H=1 cert for the right spike at `P=524288`
- `twoSpike(2,46)` period cert at `P=524288` (witness period)
- base sensitivity at `n''=106522` (w=2, T=106523): F_2=1, G_{2,46}=0 → differ ✓

SubcaseB events verified (2026-04-13):
- SubcaseB for m=46 fires at T=106523 (n''=106522) in first period
- Exactly 1 event per period: 37-candidate offset search found no second event
- Period P=524288 confirmed by numba period cert (period_certs_v2.out ✓ PASS)
- X=2 witness verified (verify_all_events.py: F_2=1, G_{2,46}=0 at T=106523)

Lean cert sizes:
  spike(46) cert: caEvolveArr 524288 (spikeArr 46 1048669) = spikeArr 46 93
    (N_in = 2*524288+2*46+1 = 1048669, N_out = 2*46+1 = 93)
  twoSpike cert: caEvolveArr 524288 (twoSpikeArr 2 46 1048669) = twoSpikeArr 2 46 93
    (N_in = 2*524288+2*max(2,46)+1 = 1048669, N_out = 2*46+1 = 93)
  H=1 cert: caEvolveArr 524288 (spikeArr 1048576 1048577).getD 0 = true
  base sens n''=106522: caEvolveArr 106523 (spikeArr 2 213047) getD 0 ≠ caEvolveArr 106523 (twoSpikeArr 2 46 213047) getD 0
-/
import P2p.CA_ArrayDef

namespace P2p

-- spike(46) period cert at P=524288 (for twoSpikeLast period lemma):
-- N_in = 2*524288+2*46+1 = 1048669, N_out = 2*46+1 = 93
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_spike46_p524288 :
    (caEvolveArr 524288 (spikeArr 46 1048669)).toList =
    (spikeArr 46 93).toList := by native_decide

-- H=1 cert for right spike at P=524288:
-- spikeArr (2*P) (2*P+1) = spikeArr 1048576 1048577
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_h1_p524288 :
    (caEvolveArr 524288 (spikeArr 1048576 1048577)).toList.getD 0 false = true := by native_decide

-- twoSpike(2,46) period cert at P=524288 (witness period):
-- N_in = 2*524288+2*max(2,46)+1 = 1048669, N_out = 2*46+1 = 93
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts246_p524288 :
    (caEvolveArr 524288 (twoSpikeArr 2 46 1048669)).toList =
    (twoSpikeArr 2 46 93).toList := by native_decide

-- Base sensitivity at n''=106522, w=2 (T=106523):
-- F_2(106523) = 1, G_{2,46}(106523) = 0 → differ ✓
-- Tape size = 2*106523+1 = 213047
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m46_base_sens_106522_w2 :
    (caEvolveArr 106523 (spikeArr 2 213047)).toList.getD 0 false ≠
    (caEvolveArr 106523 (twoSpikeArr 2 46 213047)).toList.getD 0 false := by
  native_decide

/-- Base sensitivity for `m=46`, `w=2` at `n''=106522`, in `List Bool` form. -/
theorem subcaseB_m46_base_sens_106522_w2 :
    (caEvolve 106523 (spikeAtList 2 213047)).getD 0 false ≠
    (caEvolve 106523 (twoSpikeList 2 46 213047)).getD 0 false := by
  have h := caEvolveArr_m46_base_sens_106522_w2
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-- `spike(46)` period cert at `P=524288`, in `List Bool` form. -/
theorem caEvolve_cert_spike46_p524288 :
    caEvolve 524288 (spikeAtList 46 1048669) = spikeAtList 46 93 := by
  have h := caEvolveArr_cert_spike46_p524288
  rw [caEvolveArr_toList_eq, spikeArr_toList_eq, spikeArr_toList_eq] at h
  exact h

/-- Right-spike `H=1` cert for `P=524288`, in `List Bool` form. -/
theorem caEvolve_h1_p524288 :
    (caEvolve 524288 (spikeAtList 1048576 1048577)).getD 0 false = true := by
  have h := caEvolveArr_h1_p524288
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq] at h

/-- `twoSpike(2,46)` period cert at `P=524288`, in `List Bool` form. -/
theorem caEvolve_cert_ts246_p524288 :
    caEvolve 524288 (twoSpikeList 2 46 1048669) = twoSpikeList 2 46 93 := by
  have h := caEvolveArr_cert_ts246_p524288
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- `G_{46,last}` period lemma at `P=524288`. -/
lemma rule30n_twoSpikeLast46_period524288 (n : Nat) (hn : n ≥ 46) :
    (caEvolve (n + 1) (twoSpikeLastList 46 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 524288) (twoSpikeLastList 46 (2 * ((n + 1) + 524288) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 46 524288 caEvolve_cert_spike46_p524288 caEvolve_h1_p524288 n hn

end P2p
