/-
CA_Array_m34_residues.lean — fast spikeAtCenterSeq + gCenterSeq residue proof for m=34
========================================================================================

Claim: in one full 8192-period window, SubcaseB for m=34 fires only at
n' ∈ {4112, 4116}.

Strategy: precompute F_34 and G_34 center-output sequences once, then scan
all 8192 positions with O(1) lookups. checkResiduesBool is defined in CA_ArrayDef
(an imported file) so native_decide uses pre-compiled native code, not kernel reducer.
-/

import P2p.CA_ArrayDef

namespace P2p

set_option maxHeartbeats 4000000000 in
/-- Fast native_decide: checkResiduesBool pre-compiled; sequences evaluated once. -/
private lemma checkM34ResiduesBool_holds :
    checkResiduesBool 34 8192 [4112, 4116]
      (spikeAtCenterSeq 34 8226) (gCenterSeq 34 8226) = true := by
  native_decide

/-- m=34 residue classification: SubcaseB fires only at n' ∈ {4112,4116} mod 8192. -/
theorem subcaseB_m34_residue_2class_proved :
    ∀ j : Fin 8192,
    (caEvolve (j.val + 34 + 1) (spikeAtList 34 (2*(j.val+34+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 34 + 1) (twoSpikeLastList 34 (2*(j.val+34+1)+1))).getD 0 false = true →
    j.val + 34 = 4112 ∨ j.val + 34 = 4116 := by
  intro j hF hG
  have hmem := checkResiduesBool_spec 34 8192 [4112, 4116]
    (spikeAtCenterSeq 34 8226) (gCenterSeq 34 8226) checkM34ResiduesBool_holds j
  rw [spikeAtCenterSeq_correct 34 8226 (j.val + 34) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, spikeArr_toList_eq] at hmem
  rw [gCenterSeq_correct 34 8226 (j.val + 34) (by decide) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq] at hmem
  have h := hmem hF hG
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  exact h

end P2p
