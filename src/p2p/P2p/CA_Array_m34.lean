/- 
CA_Array_m34.lean — Array Bool certs for the late active m=34 branch
===========================================================================

This file packages the compile-checked witness kernel for `m=34` using
the interior witness `w=12`:

- `spike(34)` period cert at `P=8192`
- `H=1` cert for the right spike at `P=8192`
- `twoSpikeLast(34)` period lemma at `P=8192`
- `twoSpike(12,34)` period cert at `P=8192`
- base sensitivity at `n'=4112`
- base sensitivity at `n'=4116`

These certs do NOT prove the full `m=34` branch by themselves. The remaining
gap is the residue-class lemma that `m=34` SubcaseB fires only at
`n' ≡ 4112, 4116 (mod 8192)`.
-/
import P2p.CA_ArrayDef

namespace P2p

set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_spike34_p8192 :
    (caEvolveArr 8192 (spikeArr 34 16453)).toList =
    (spikeArr 34 69).toList := by
  native_decide

set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_h1_p8192 :
    (caEvolveArr 8192 (spikeArr 16384 16385)).toList.getD 0 false = true := by
  native_decide

set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts1234_p8192 :
    (caEvolveArr 8192 (twoSpikeArr 12 34 16453)).toList =
    (twoSpikeArr 12 34 69).toList := by
  native_decide

set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m34_base_sens_4112_w12 :
    (caEvolveArr 4113 (spikeArr 12 8227)).toList.getD 0 false ≠
    (caEvolveArr 4113 (twoSpikeArr 12 34 8227)).toList.getD 0 false := by
  native_decide

set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m34_base_sens_4116_w12 :
    (caEvolveArr 4117 (spikeArr 12 8235)).toList.getD 0 false ≠
    (caEvolveArr 4117 (twoSpikeArr 12 34 8235)).toList.getD 0 false := by
  native_decide

/-- `twoSpike(12,34)` period cert at `P=8192`, in `List Bool` form. -/
theorem caEvolve_cert_spike34_p8192 :
    caEvolve 8192 (spikeAtList 34 16453) = spikeAtList 34 69 := by
  have h := caEvolveArr_cert_spike34_p8192
  rw [caEvolveArr_toList_eq, spikeArr_toList_eq, spikeArr_toList_eq] at h
  exact h

/-- Right-spike `H=1` cert for `P=8192`, in `List Bool` form. -/
theorem caEvolve_h1_p8192 :
    (caEvolve 8192 (spikeAtList 16384 16385)).getD 0 false = true := by
  have h := caEvolveArr_h1_p8192
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq] at h

/-- `G_{34,last}` period lemma at `P=8192`. -/
lemma rule30n_twoSpikeLast34_period8192 (n : Nat) (hn : n ≥ 34) :
    (caEvolve (n + 1) (twoSpikeLastList 34 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 8192) (twoSpikeLastList 34 (2 * ((n + 1) + 8192) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 34 8192 caEvolve_cert_spike34_p8192 caEvolve_h1_p8192 n hn

/-- `twoSpike(12,34)` period cert at `P=8192`, in `List Bool` form. -/
theorem caEvolve_cert_ts1234_p8192 :
    caEvolve 8192 (twoSpikeList 12 34 16453) = twoSpikeList 12 34 69 := by
  have h := caEvolveArr_cert_ts1234_p8192
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- Base sensitivity for `m=34`, `w=12` at `n'=4112`, in `List Bool` form. -/
theorem subcaseB_m34_base_sens_4112_w12 :
    (caEvolve 4113 (spikeAtList 12 8227)).getD 0 false ≠
    (caEvolve 4113 (twoSpikeList 12 34 8227)).getD 0 false := by
  have h := caEvolveArr_m34_base_sens_4112_w12
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-- Base sensitivity for `m=34`, `w=12` at `n'=4116`, in `List Bool` form. -/
theorem subcaseB_m34_base_sens_4116_w12 :
    (caEvolve 4117 (spikeAtList 12 8235)).getD 0 false ≠
    (caEvolve 4117 (twoSpikeList 12 34 8235)).getD 0 false := by
  have h := caEvolveArr_m34_base_sens_4116_w12
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

end P2p
