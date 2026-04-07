/-
CA_Array_m36.lean — Array Bool certs for the late active m=36 branch
===========================================================================

This file packages the compile-checked witness kernel for `m=36` using
the interior witnesses `w=2` (residue 4113) and `w=4` (residue 4117):

- `spike(36)` period cert at `P=16384`
- `H=1` cert for the right spike at `P=16384`
- `twoSpikeLast(36)` period lemma at `P=16384`
- `twoSpike(2,36)` period cert at `P=16384` (for residue 4113)
- `twoSpike(4,36)` period cert at `P=16384` (for residue 4117)
- base sensitivity at `n'=4113` (w=2)
- base sensitivity at `n'=4117` (w=4)

These certs do NOT prove the full `m=36` branch by themselves. The remaining
gap is the residue-class lemma that `m=36` SubcaseB fires only at
`n' ≡ 4113, 4117 (mod 16384)`.

Empirical basis (loop-58, exhaustive G-check of [3087,5000)):
  SubcaseB fires at exactly {4113, 4117} in the first period window.
  Period P=16384 confirmed (F-period holds, P/2 fails).
-/
import P2p.CA_ArrayDef

namespace P2p

set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_spike36_p16384 :
    (caEvolveArr 16384 (spikeArr 36 32841)).toList =
    (spikeArr 36 73).toList := by
  native_decide

set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_h1_p16384 :
    (caEvolveArr 16384 (spikeArr 32768 32769)).toList.getD 0 false = true := by
  native_decide

set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts236_p16384 :
    (caEvolveArr 16384 (twoSpikeArr 2 36 32841)).toList =
    (twoSpikeArr 2 36 73).toList := by
  native_decide

set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts436_p16384 :
    (caEvolveArr 16384 (twoSpikeArr 4 36 32841)).toList =
    (twoSpikeArr 4 36 73).toList := by
  native_decide

set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m36_base_sens_4113_w2 :
    (caEvolveArr 4114 (spikeArr 2 8229)).toList.getD 0 false ≠
    (caEvolveArr 4114 (twoSpikeArr 2 36 8229)).toList.getD 0 false := by
  native_decide

set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m36_base_sens_4117_w4 :
    (caEvolveArr 4118 (spikeArr 4 8237)).toList.getD 0 false ≠
    (caEvolveArr 4118 (twoSpikeArr 4 36 8237)).toList.getD 0 false := by
  native_decide

/-- `spike(36)` period cert at `P=16384`, in `List Bool` form. -/
theorem caEvolve_cert_spike36_p16384 :
    caEvolve 16384 (spikeAtList 36 32841) = spikeAtList 36 73 := by
  have h := caEvolveArr_cert_spike36_p16384
  rw [caEvolveArr_toList_eq, spikeArr_toList_eq, spikeArr_toList_eq] at h
  exact h

/-- Right-spike `H=1` cert for `P=16384`, in `List Bool` form. -/
theorem caEvolve_h1_p16384 :
    (caEvolve 16384 (spikeAtList 32768 32769)).getD 0 false = true := by
  have h := caEvolveArr_h1_p16384
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq] at h

/-- `twoSpike(2,36)` period cert at `P=16384`, in `List Bool` form. -/
theorem caEvolve_cert_ts236_p16384 :
    caEvolve 16384 (twoSpikeList 2 36 32841) = twoSpikeList 2 36 73 := by
  have h := caEvolveArr_cert_ts236_p16384
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- `twoSpike(4,36)` period cert at `P=16384`, in `List Bool` form. -/
theorem caEvolve_cert_ts436_p16384 :
    caEvolve 16384 (twoSpikeList 4 36 32841) = twoSpikeList 4 36 73 := by
  have h := caEvolveArr_cert_ts436_p16384
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- `G_{36,last}` period lemma at `P=16384`. -/
lemma rule30n_twoSpikeLast36_period16384 (n : Nat) (hn : n ≥ 36) :
    (caEvolve (n + 1) (twoSpikeLastList 36 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 16384) (twoSpikeLastList 36 (2 * ((n + 1) + 16384) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 36 16384 caEvolve_cert_spike36_p16384 caEvolve_h1_p16384 n hn

/-- Base sensitivity for `m=36`, `w=2` at `n'=4113`, in `List Bool` form. -/
theorem subcaseB_m36_base_sens_4113_w2 :
    (caEvolve 4114 (spikeAtList 2 8229)).getD 0 false ≠
    (caEvolve 4114 (twoSpikeList 2 36 8229)).getD 0 false := by
  have h := caEvolveArr_m36_base_sens_4113_w2
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-- Base sensitivity for `m=36`, `w=4` at `n'=4117`, in `List Bool` form. -/
theorem subcaseB_m36_base_sens_4117_w4 :
    (caEvolve 4118 (spikeAtList 4 8237)).getD 0 false ≠
    (caEvolve 4118 (twoSpikeList 4 36 8237)).getD 0 false := by
  have h := caEvolveArr_m36_base_sens_4117_w4
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

end P2p
