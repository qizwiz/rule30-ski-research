/-
CA_Array_m28_residues.lean — fast spikeAtCenterSeq + gCenterSeq residue proof for m=28
========================================================================================

Claim: in one full 2048-period window, SubcaseB for m=28 fires only at
n' ∈ {1293, 1297, 2065}.

Strategy: precompute F_28 and G_28 center-output sequences once, then scan
all 2048 positions with O(1) lookups. checkResiduesBool is defined in CA_ArrayDef
(an imported file) so native_decide uses pre-compiled native code, not kernel reducer.
-/

import P2p.CA_ArrayDef

namespace P2p

set_option maxHeartbeats 4000000000 in
/-- Fast native_decide: checkResiduesBool pre-compiled; sequences evaluated once. -/
private lemma checkM28ResiduesBool_holds :
    checkResiduesBool 28 2048 [1293, 1297, 2065]
      (spikeAtCenterSeq 28 2076) (gCenterSeq 28 2076) = true := by
  native_decide

/-- m=28 residue classification: SubcaseB fires only at n' ∈ {1293,1297,2065} mod 2048. -/
theorem subcaseB_m28_residue_3class_proved :
    ∀ j : Fin 2048,
    (caEvolve (j.val + 28 + 1) (spikeAtList 28 (2*(j.val+28+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 28 + 1) (twoSpikeLastList 28 (2*(j.val+28+1)+1))).getD 0 false = true →
    j.val + 28 = 1293 ∨ j.val + 28 = 1297 ∨ j.val + 28 = 2065 := by
  intro j hF hG
  have hmem := checkResiduesBool_spec 28 2048 [1293, 1297, 2065]
    (spikeAtCenterSeq 28 2076) (gCenterSeq 28 2076) checkM28ResiduesBool_holds j
  rw [spikeAtCenterSeq_correct 28 2076 (j.val + 28) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, spikeArr_toList_eq] at hmem
  rw [gCenterSeq_correct 28 2076 (j.val + 28) (by decide) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq] at hmem
  have h := hmem hF hG
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  exact h

end P2p
