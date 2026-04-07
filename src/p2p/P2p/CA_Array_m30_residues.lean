/-
CA_Array_m30_residues.lean — fast spikeAtCenterSeq + gCenterSeq residue proof for m=30
========================================================================================

Claim: in one full 4096-period window, SubcaseB for m=30 fires only at
n' = 4114.

Strategy: precompute F_30 and G_30 center-output sequences once, then scan
all 4096 positions with O(1) lookups. checkResiduesBool is defined in CA_ArrayDef
(an imported file) so native_decide uses pre-compiled native code, not kernel reducer.
-/

import P2p.CA_ArrayDef

namespace P2p

set_option maxHeartbeats 4000000000 in
/-- Fast native_decide: checkResiduesBool pre-compiled; sequences evaluated once. -/
private lemma checkM30ResiduesBool_holds :
    checkResiduesBool 30 4096 [4114]
      (spikeAtCenterSeq 30 4126) (gCenterSeq 30 4126) = true := by
  native_decide

/-- m=30 residue classification: SubcaseB fires only at n' = 4114 mod 4096. -/
theorem subcaseB_m30_residue_unique_proved :
    ∀ j : Fin 4096,
    (caEvolve (j.val + 30 + 1) (spikeAtList 30 (2*(j.val+30+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 30 + 1) (twoSpikeLastList 30 (2*(j.val+30+1)+1))).getD 0 false = true →
    j.val + 30 = 4114 := by
  intro j hF hG
  have hmem := checkResiduesBool_spec 30 4096 [4114]
    (spikeAtCenterSeq 30 4126) (gCenterSeq 30 4126) checkM30ResiduesBool_holds j
  rw [spikeAtCenterSeq_correct 30 4126 (j.val + 30) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, spikeArr_toList_eq] at hmem
  rw [gCenterSeq_correct 30 4126 (j.val + 30) (by decide) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq] at hmem
  have h := hmem hF hG
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  exact h

end P2p
