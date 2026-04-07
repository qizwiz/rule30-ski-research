/-
CA_Array_m36_residues.lean — fast spikeAtCenterSeq + gCenterSeq residue proof for m=36
========================================================================================

Claim: in one full 16384-period window, SubcaseB for m=36 fires only at
n' ∈ {4113, 4117}.

Strategy: precompute F_36 and G_36 center-output sequences once, then scan
all 16384 positions with O(1) lookups. checkResiduesBool is defined in CA_ArrayDef
(an imported file) so native_decide uses pre-compiled native code, not kernel reducer.
-/

import P2p.CA_ArrayDef

namespace P2p

set_option maxHeartbeats 4000000000 in
/-- Fast native_decide: checkResiduesBool pre-compiled; sequences evaluated once. -/
private lemma checkM36ResiduesBool_holds :
    checkResiduesBool 36 16384 [4113, 4117]
      (spikeAtCenterSeq 36 16420) (gCenterSeq 36 16420) = true := by
  native_decide

/-- m=36 residue classification: SubcaseB fires only at n' ∈ {4113,4117} mod 16384. -/
theorem subcaseB_m36_residue_2class :
    ∀ j : Fin 16384,
    (caEvolve (j.val + 36 + 1) (spikeAtList 36 (2*(j.val+36+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 36 + 1) (twoSpikeLastList 36 (2*(j.val+36+1)+1))).getD 0 false = true →
    j.val + 36 = 4113 ∨ j.val + 36 = 4117 := by
  intro j hF hG
  have hmem := checkResiduesBool_spec 36 16384 [4113, 4117]
    (spikeAtCenterSeq 36 16420) (gCenterSeq 36 16420) checkM36ResiduesBool_holds j
  rw [spikeAtCenterSeq_correct 36 16420 (j.val + 36) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, spikeArr_toList_eq] at hmem
  rw [gCenterSeq_correct 36 16420 (j.val + 36) (by decide) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq] at hmem
  have h := hmem hF hG
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  exact h

end P2p
