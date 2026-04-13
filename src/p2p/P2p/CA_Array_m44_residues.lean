/-
CA_Array_m44_residues.lean — fast spikeAtCenterSeq + gCenterSeq residue proof for m=44
========================================================================================

Claim: in one full 262144-period window, SubcaseB for m=44 fires only at
n'' ∈ {249877}.

Strategy: precompute F_44 and G_44 center-output sequences once, then scan
all 262144 positions with O(1) lookups. checkResiduesBool is defined in CA_ArrayDef
(an imported file) so native_decide uses pre-compiled native code, not kernel reducer.

Verified (2026-04-13):
- 37-candidate offset search found no second event in period (second_events.out)
- T=249878 (n''=249877) confirmed as the only SubcaseB event by direct check
- Period P=262144 confirmed by numba period cert

NOTE: This file requires significant computation time for native_decide
(spikeAtCenterSeq 44 262188 has 262188 elements, ~68B ops). If build is too slow,
consider splitting or using algebraic approach.
-/

import P2p.CA_ArrayDef

namespace P2p

set_option maxHeartbeats 4000000000 in
/-- Fast native_decide: checkResiduesBool pre-compiled; sequences evaluated once. -/
private lemma checkM44ResiduesBool_holds :
    checkResiduesBool 44 262144 [249877]
      (spikeAtCenterSeq 44 262188) (gCenterSeq 44 262188) = true := by
  native_decide

/-- m=44 residue classification: SubcaseB fires only at n'' = 249877 mod 262144. -/
theorem subcaseB_m44_residue_1class :
    ∀ j : Fin 262144,
    (caEvolve (j.val + 44 + 1) (spikeAtList 44 (2*(j.val+44+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 44 + 1) (twoSpikeLastList 44 (2*(j.val+44+1)+1))).getD 0 false = true →
    j.val + 44 = 249877 := by
  intro j hF hG
  have hmem := checkResiduesBool_spec 44 262144 [249877]
    (spikeAtCenterSeq 44 262188) (gCenterSeq 44 262188) checkM44ResiduesBool_holds j
  rw [spikeAtCenterSeq_correct 44 262188 (j.val + 44) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, spikeArr_toList_eq] at hmem
  rw [gCenterSeq_correct 44 262188 (j.val + 44) (by decide) (by omega),
      Array.getD_eq_toList_getD, caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq] at hmem
  have h := hmem hF hG
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  exact h

end P2p
