/-
Prize3_AxiomFree.lean - Axiom-free bridge for Wolfram Prize 3
================================================================================

PURPOSE: Wire rule30_prize3_direct (from LiftingLemma_LeftPermutive) to derive
the Prize 3 block-sensitivity theorem without the lifting_lemma axiom.

DESIGN: Prize3_Complete defines core types and lifting_lemma as an axiom.
LiftingLemma_LeftPermutive imports Prize3_Complete (for types) and proves
rule30_prize3_direct : ∀ n k, Essential n k -- no lifting_lemma used.
This file imports LiftingLemma_LeftPermutive (transitively gets Prize3_Complete)
and re-derives the prize theorem using rule30_prize3_direct instead of
all_essential_all (which uses lifting_lemma).

STATUS (2026-04-05):
  BLOCKED — builds of CA_Array_m34_residues and CA_Array_m36_residues still
  running; SubcaseBPeriod.lean and LiftingLemma_LeftPermutive.lean have no
  oleans yet. Also blocked by SubcaseB_Firewall.lean sorry in
  subcaseB_mgt30_split (line 119), which propagates into subcaseB_resolution_ge3087
  and thus into rule30_prize3_direct.

REMAINING GAPS before this file compiles 0-axiom, 0-sorry:
  1. Close SubcaseB_Firewall sorry (subcaseB_mgt30_split: prove m>38,
     non-right-mirror SubcaseB never fires for n'≥3087).
  2. Builds of CA_Array_m34_residues, CA_Array_m36_residues must finish
     (currently parallel-race blocked — two lean instances on m34_residues).
  3. SubcaseBPeriod.lean and LiftingLemma_LeftPermutive.lean must compile clean.

CIRCULAR IMPORT NOTE: Prize3_Complete cannot import LiftingLemma_LeftPermutive
(circular: LiftingLemma imports Prize3_Complete for type definitions). This
bridge file resolves the circularity by importing the other direction.
-/

import P2p.LiftingLemma_LeftPermutive

-- rule30_prize3_direct is proved in LiftingLemma_LeftPermutive.lean:
--   theorem rule30_prize3_direct (n : Nat) (k : Fin (2 * n + 1)) : Essential n k
-- It does NOT use lifting_lemma axiom.
-- Current dependency: subcaseB_resolution_ge3087 (theorem, no axiom),
--   which calls subcaseB_mgt30_split (has 1 sorry in SubcaseB_Firewall.lean).

/-- All cells are essential, proved without lifting_lemma axiom. -/
theorem all_essential_all_axiom_free (n : Nat) : AllEssential n :=
  fun k => rule30_prize3_direct n k

/-- Prize 3 block-sensitivity lower bound, axiom-free once SubcaseB_Firewall sorry closed.
    Proof mirrors rule30_bs_ge_n_from_all_essential (Prize3_Complete.lean:646)
    but substitutes all_essential_all_axiom_free for all_essential_all. -/
theorem rule30_bs_ge_n_axiom_free (n : Nat) : HasBlockSensitivity n (rule30n n) n := by
  have hall : AllEssential n := all_essential_all_axiom_free n
  have h_bound : ∀ i : Fin n, i.val < 2 * n + 1 :=
    fun i => Nat.lt_of_lt_of_le i.is_lt (by omega)
  let mkPos : Fin n → Fin (2 * n + 1) := fun i => ⟨i.val, h_bound i⟩
  let mkBlock : Fin n → Finset (Fin (2 * n + 1)) := fun i => {mkPos i}
  let blocks : Finset (Finset (Fin (2 * n + 1))) :=
    (Finset.univ : Finset (Fin n)).image mkBlock
  have h_inj : Function.Injective mkBlock := by
    intro a b h
    simp only [mkBlock, Finset.singleton_inj, mkPos, Fin.mk.injEq] at h
    exact Fin.ext h
  refine ⟨blocks, ?_, ?_, ?_⟩
  · simp only [blocks, Finset.card_image_of_injective _ h_inj,
               Finset.card_univ, Fintype.card_fin]
  · intro B hB
    simp only [blocks, mkBlock, Finset.mem_image, Finset.mem_univ, true_and] at hB
    obtain ⟨i, rfl⟩ := hB
    obtain ⟨c, hc⟩ := hall (mkPos i)
    refine ⟨c, ?_⟩
    convert hc using 2
    funext k
    simp [flipCell, Finset.mem_singleton]
  · intro B₁ B₂ hB₁ hB₂ hne
    simp only [blocks, mkBlock, Finset.mem_image, Finset.mem_univ, true_and] at hB₁ hB₂
    obtain ⟨i, rfl⟩ := hB₁
    obtain ⟨j, rfl⟩ := hB₂
    have hpos_ne : mkPos i ≠ mkPos j := by
      intro h; exact hne (by simp [h])
    ext x
    simp [Finset.mem_inter, Finset.mem_singleton]
    intro h1 h2
    exact hpos_ne (h1.symm.trans h2)
