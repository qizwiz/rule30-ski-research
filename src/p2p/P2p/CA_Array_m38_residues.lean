/-
CA_Array_m38_residues.lean — fast spikeAtCenterSeq + gCenterSeq residue proof for m=38
========================================================================================

Claim: in one full 32768-period window, SubcaseB for m=38 fires only at
n' ∈ {8210, 8214}.

Strategy: precompute F_38 and G_38 center-output sequences once, then scan
all 32768 positions with O(1) lookups. checkResiduesBool is defined in CA_ArrayDef
(an imported file) so native_decide uses pre-compiled native code, not kernel reducer.
-/

import P2p.CA_ArrayDef

namespace P2p

set_option maxHeartbeats 4000000000 in
/-- Fast native_decide: checkResiduesBool pre-compiled; sequences evaluated once. -/
private lemma checkM38ResiduesBool_holds :
    checkResiduesBool 38 32768 [8210, 8214]
      (spikeAtCenterSeq 38 32806) (gCenterSeq 38 32806) = true := by
  native_decide

/-- m=38 residue classification: SubcaseB fires only at n' ∈ {8210,8214} mod 32768. -/
theorem subcaseB_m38_residue_2class :
    ∀ j : Fin 32768,
    (caEvolve (j.val + 38 + 1) (spikeAtList 38 (2*(j.val+38+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 38 + 1) (twoSpikeLastList 38 (2*(j.val+38+1)+1))).getD 0 false = true →
    j.val + 38 = 8210 ∨ j.val + 38 = 8214 := by
  intro j hF hG
  have hmem := checkResiduesBool_spec 38 32768 [8210, 8214]
    (spikeAtCenterSeq 38 32806) (gCenterSeq 38 32806) checkM38ResiduesBool_holds j
  rw [spikeAtCenterSeq_correct 38 32806 (j.val + 38) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, spikeArr_toList_eq] at hmem
  rw [gCenterSeq_correct 38 32806 (j.val + 38) (by decide) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq] at hmem
  have h := hmem hF hG
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  exact h

/-- Alias for SubcaseBPeriod.lean compatibility. -/
theorem subcaseB_m38_residue_2class_proved :
    ∀ j : Fin 32768,
    (caEvolve (j.val + 38 + 1) (spikeAtList 38 (2*(j.val+38+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 38 + 1) (twoSpikeLastList 38 (2*(j.val+38+1)+1))).getD 0 false = true →
    j.val + 38 = 8210 ∨ j.val + 38 = 8214 :=
  subcaseB_m38_residue_2class

end P2p
