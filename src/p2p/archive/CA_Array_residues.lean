/-
CA_Array_residues.lean — native_decide proofs for m=28 and m=30 residue classification
===================================================================================

Proves the two remaining axioms from CA_Array.lean:
  - subcaseB_m28_residue_3class_proved  (Fin 2048 check)
  - subcaseB_m30_residue_unique_proved  (Fin 4096 check)

Strategy: Use Array Bool (caEvolveArr) for native_decide speed, then convert
to List Bool (caEvolve) form using the equivalence lemmas in CA_ArrayDef.lean.
The linked-list CA is too slow for native_decide; Array Bool is ~50x faster.

Verified computationally (Python, shrinking CA):
  m=28 firing positions mod 2048: {1293, 1297, 2065} (j values: {1265, 1269, 2037})
  m=30 firing position  mod 4096: {4114}             (j value:  {4084})
-/

import P2p.CA_ArrayDef

namespace P2p

/-
================================================================================
SECTION 1: m=28 RESIDUE CLASSIFICATION
Claim: SubcaseB fires at n' ≡ 1293, 1297, or 2065 (mod 2048) only.
================================================================================
-/

/-- Array-based m=28 residue check (efficient for native_decide).
    For each j in Fin 2048, if spike(28) center=false AND twoSpikeLastArr(28) center=true,
    then j+28 ∈ {1293, 1297, 2065}. -/
set_option maxHeartbeats 4000000000 in
private lemma m28_residue_arr :
    ∀ j : Fin 2048,
    (caEvolveArr (j.val + 28 + 1) (spikeArr 28 (2*(j.val+28+1)+1))).toList.getD 0 false = false →
    (caEvolveArr (j.val + 28 + 1) (twoSpikeLastArr 28 (2*(j.val+28+1)+1))).toList.getD 0 false = true →
    j.val + 28 = 1293 ∨ j.val + 28 = 1297 ∨ j.val + 28 = 2065 := by
  native_decide

/-- m=28 residue classification (List Bool form, matching the axiom signature in CA_Array.lean).
    Proves subcaseB_m28_residue_3class_proved as a theorem instead of an axiom. -/
theorem subcaseB_m28_residue_3class_proved :
    ∀ j : Fin 2048,
    (caEvolve (j.val + 28 + 1) (spikeAtList 28 (2*(j.val+28+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 28 + 1) (twoSpikeLastList 28 (2*(j.val+28+1)+1))).getD 0 false = true →
    j.val + 28 = 1293 ∨ j.val + 28 = 1297 ∨ j.val + 28 = 2065 := by
  intro j hF hH
  apply m28_residue_arr j
  · rw [caEvolveArr_toList_eq, spikeArr_toList_eq]
    exact hF
  · rw [caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq]
    exact hH

/-
================================================================================
SECTION 2: m=30 RESIDUE CLASSIFICATION
Claim: SubcaseB fires at n' ≡ 4114 (mod 4096) only.
================================================================================
-/

/-- Array-based m=30 residue check (efficient for native_decide).
    For each j in Fin 4096, if spike(30) center=false AND twoSpikeLastArr(30) center=true,
    then j+30 = 4114. -/
set_option maxHeartbeats 4000000000 in
private lemma m30_residue_arr :
    ∀ j : Fin 4096,
    (caEvolveArr (j.val + 30 + 1) (spikeArr 30 (2*(j.val+30+1)+1))).toList.getD 0 false = false →
    (caEvolveArr (j.val + 30 + 1) (twoSpikeLastArr 30 (2*(j.val+30+1)+1))).toList.getD 0 false = true →
    j.val + 30 = 4114 := by
  native_decide

/-- m=30 residue classification (List Bool form, matching the axiom signature in CA_Array.lean).
    Proves subcaseB_m30_residue_unique_proved as a theorem instead of an axiom. -/
theorem subcaseB_m30_residue_unique_proved :
    ∀ j : Fin 4096,
    (caEvolve (j.val + 30 + 1) (spikeAtList 30 (2*(j.val+30+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 30 + 1) (twoSpikeLastList 30 (2*(j.val+30+1)+1))).getD 0 false = true →
    j.val + 30 = 4114 := by
  intro j hF hH
  apply m30_residue_arr j
  · rw [caEvolveArr_toList_eq, spikeArr_toList_eq]
    exact hF
  · rw [caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq]
    exact hH

end P2p
