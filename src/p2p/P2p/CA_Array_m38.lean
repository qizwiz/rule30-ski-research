/-
CA_Array_m38.lean — Array Bool certs for the late active m=38 branch
===========================================================================

This file packages the compile-checked witness kernel for `m=38` using
the interior witnesses `w=2` (residue 8210) and `w=4` (residue 8214):

- `spike(38)` period cert at `P=32768`
- `H=1` cert for the right spike at `P=32768`
- `twoSpikeLast(38)` period lemma at `P=32768`
- `twoSpike(2,38)` period cert at `P=32768` (for residue 8210)
- `twoSpike(4,38)` period cert at `P=32768` (for residue 8214)
- base sensitivity at `n'=8210` (w=2)
- base sensitivity at `n'=8214` (w=4)

These certs do NOT prove the full `m=38` branch by themselves. The remaining
gap is the residue-class lemma that `m=38` SubcaseB fires only at
`n' ≡ 8210, 8214 (mod 32768)`.

Empirical basis (loop-30, loop-61): exhaustive G-check confirms SubcaseB at
{8210, 8214} in the first period window. Period P=32768 confirmed (F-period
holds, P/2 fails). Period repeats verified at {40978, 40982} = {8210, 8214} + 32768.

Witness family (loop-18):
  - n'=8210: w=2 (spike at position 2)
  - n'=8214: w=4 (spike at position 4)
  - n'=22 (period-reduced rep for 32790): w=2
-/
import P2p.CA_ArrayDef

namespace P2p

-- spike(38) period cert at P=32768:
-- N_in = 2*32768+2*38+1 = 65613, N_out = 2*38+1 = 77
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_spike38_p32768 :
    (caEvolveArr 32768 (spikeArr 38 65613)).toList =
    (spikeArr 38 77).toList := by native_decide

-- H=1 cert for right spike at P=32768:
-- spikeArr (2*P) (2*P+1) = spikeArr 65536 65537
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_h1_p32768 :
    (caEvolveArr 32768 (spikeArr 65536 65537)).toList.getD 0 false = true := by native_decide

-- twoSpike(2,38) period cert at P=32768:
-- N_in = 2*32768+2*38+1 = 65613, N_out = 2*38+1 = 77
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts238_p32768 :
    (caEvolveArr 32768 (twoSpikeArr 2 38 65613)).toList =
    (twoSpikeArr 2 38 77).toList := by native_decide

-- twoSpike(4,38) period cert at P=32768:
-- N_in = 2*32768+2*38+1 = 65613, N_out = 2*38+1 = 77
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts438_p32768 :
    (caEvolveArr 32768 (twoSpikeArr 4 38 65613)).toList =
    (twoSpikeArr 4 38 77).toList := by native_decide

-- Base sensitivity at n'=8210, w=2:
-- Tape size = 2*8211+1 = 16423, level = 8211
-- Feasible: ~67M cells, ~0.1s native (loop-18 estimate)
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m38_base_sens_8210_w2 :
    (caEvolveArr 8211 (spikeArr 2 16423)).toList.getD 0 false ≠
    (caEvolveArr 8211 (twoSpikeArr 2 38 16423)).toList.getD 0 false := by
  native_decide

-- Base sensitivity at n'=8214, w=4:
-- Tape size = 2*8215+1 = 16431, level = 8215
-- Feasible: ~67M cells, ~0.1s native (loop-18 estimate)
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m38_base_sens_8214_w4 :
    (caEvolveArr 8215 (spikeArr 4 16431)).toList.getD 0 false ≠
    (caEvolveArr 8215 (twoSpikeArr 4 38 16431)).toList.getD 0 false := by
  native_decide

/-- Base sensitivity for `m=38`, `w=2` at `n'=8210`, in `List Bool` form. -/
theorem subcaseB_m38_base_sens_8210_w2 :
    (caEvolve 8211 (spikeAtList 2 16423)).getD 0 false ≠
    (caEvolve 8211 (twoSpikeList 2 38 16423)).getD 0 false := by
  have h := caEvolveArr_m38_base_sens_8210_w2
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-- Base sensitivity for `m=38`, `w=4` at `n'=8214`, in `List Bool` form. -/
theorem subcaseB_m38_base_sens_8214_w4 :
    (caEvolve 8215 (spikeAtList 4 16431)).getD 0 false ≠
    (caEvolve 8215 (twoSpikeList 4 38 16431)).getD 0 false := by
  have h := caEvolveArr_m38_base_sens_8214_w4
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-- `spike(38)` period cert at `P=32768`, in `List Bool` form. -/
theorem caEvolve_cert_spike38_p32768 :
    caEvolve 32768 (spikeAtList 38 65613) = spikeAtList 38 77 := by
  have h := caEvolveArr_cert_spike38_p32768
  rw [caEvolveArr_toList_eq, spikeArr_toList_eq, spikeArr_toList_eq] at h
  exact h

/-- Right-spike `H=1` cert for `P=32768`, in `List Bool` form. -/
theorem caEvolve_h1_p32768 :
    (caEvolve 32768 (spikeAtList 65536 65537)).getD 0 false = true := by
  have h := caEvolveArr_h1_p32768
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq] at h

/-- `twoSpike(2,38)` period cert at `P=32768`, in `List Bool` form. -/
theorem caEvolve_cert_ts238_p32768 :
    caEvolve 32768 (twoSpikeList 2 38 65613) = twoSpikeList 2 38 77 := by
  have h := caEvolveArr_cert_ts238_p32768
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- `twoSpike(4,38)` period cert at `P=32768`, in `List Bool` form. -/
theorem caEvolve_cert_ts438_p32768 :
    caEvolve 32768 (twoSpikeList 4 38 65613) = twoSpikeList 4 38 77 := by
  have h := caEvolveArr_cert_ts438_p32768
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- `G_{38,last}` period lemma at `P=32768`. -/
lemma rule30n_twoSpikeLast38_period32768 (n : Nat) (hn : n ≥ 38) :
    (caEvolve (n + 1) (twoSpikeLastList 38 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 32768) (twoSpikeLastList 38 (2 * ((n + 1) + 32768) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 38 32768 caEvolve_cert_spike38_p32768 caEvolve_h1_p32768 n hn

end P2p
