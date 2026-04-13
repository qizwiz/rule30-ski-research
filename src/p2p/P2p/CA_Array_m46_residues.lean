/-
CA_Array_m46_residues.lean — fast spikeAtCenterSeq + gCenterSeq residue proof for m=46
========================================================================================

Claim: in one full 524288-period window, SubcaseB for m=46 fires only at
n'' ∈ {106522}.

Strategy: precompute F_46 and G_46 center-output sequences once, then scan
all 524288 positions with O(1) lookups. checkResiduesBool is defined in CA_ArrayDef
(an imported file) so native_decide uses pre-compiled native code, not kernel reducer.

Verified (2026-04-13):
- 37-candidate offset search found no second event in period (second_events.out)
- T=106523 (n''=106522) confirmed as the only SubcaseB event by direct check
- Period P=524288 confirmed by numba period cert

NOTE: This file requires very significant computation time for native_decide
(spikeAtCenterSeq 46 524334 has 524334 elements, ~275B ops). May need algebraic
alternative or splitting strategy if native_decide build times are prohibitive.
-/

import P2p.CA_ArrayDef

namespace P2p

set_option maxHeartbeats 4000000000 in
/-- Fast native_decide: checkResiduesBool pre-compiled; sequences evaluated once. -/
private lemma checkM46ResiduesBool_holds :
    checkResiduesBool 46 524288 [106522]
      (spikeAtCenterSeq 46 524334) (gCenterSeq 46 524334) = true := by
  native_decide

/-- m=46 residue classification: SubcaseB fires only at n'' = 106522 mod 524288. -/
theorem subcaseB_m46_residue_1class :
    ∀ j : Fin 524288,
    (caEvolve (j.val + 46 + 1) (spikeAtList 46 (2*(j.val+46+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 46 + 1) (twoSpikeLastList 46 (2*(j.val+46+1)+1))).getD 0 false = true →
    j.val + 46 = 106522 := by
  intro j hF hG
  have hmem := checkResiduesBool_spec 46 524288 [106522]
    (spikeAtCenterSeq 46 524334) (gCenterSeq 46 524334) checkM46ResiduesBool_holds j
  rw [spikeAtCenterSeq_correct 46 524334 (j.val + 46) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, spikeArr_toList_eq] at hmem
  rw [gCenterSeq_correct 46 524334 (j.val + 46) (by decide) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq] at hmem
  have h := hmem hF hG
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  exact h

end P2p
