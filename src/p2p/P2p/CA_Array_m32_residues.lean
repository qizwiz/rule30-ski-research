/-
CA_Array_m32_residues.lean — empty-residue proof for m=32 (inactive)
=====================================================================

Claim: in one full 4096-period window, SubcaseB for m=32 NEVER fires.
m=32 is an inactive value — both F_32 and G_32 are zero for n' ≥ 32.

Strategy: precompute F_32 and G_32 center-output sequences once, then
check all 4096 positions with O(1) lookups. The valid set is empty [].
-/

import P2p.CA_ArrayDef

namespace P2p

set_option maxHeartbeats 4000000000 in
/-- Fast native_decide: checkResiduesBool with empty valid set, confirming
    SubcaseB never fires for m=32 in base period window [32, 4128). -/
private lemma checkM32ResiduesBool_holds :
    checkResiduesBool 32 4096 []
      (spikeAtCenterSeq 32 4128) (gCenterSeq 32 4128) = true := by
  native_decide

/-- m=32 SubcaseB never fires in base period [32, 4128). -/
theorem subcaseB_m32_never_fires_period :
    ∀ j : Fin 4096,
    (caEvolve (j.val + 32 + 1) (spikeAtList 32 (2*(j.val+32+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 32 + 1) (twoSpikeLastList 32 (2*(j.val+32+1)+1))).getD 0 false = true →
    False := by
  intro j hF hG
  have hmem := checkResiduesBool_spec 32 4096 []
    (spikeAtCenterSeq 32 4128) (gCenterSeq 32 4128) checkM32ResiduesBool_holds j
  rw [spikeAtCenterSeq_correct 32 4128 (j.val + 32) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, spikeArr_toList_eq] at hmem
  rw [gCenterSeq_correct 32 4128 (j.val + 32) (by decide) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq] at hmem
  exact absurd (hmem hF hG) (List.not_mem_nil _)

end P2p
