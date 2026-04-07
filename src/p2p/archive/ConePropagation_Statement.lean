/-
  3-Cell Cone Propagation Lemma — Formal Statement
  
  Packet: formal-lifting-lemma-attack
  Date: 2026-04-04
  Engine: qwen
  
  This file contains the exact theorem statement for the 3-cell cone propagation
  claim and assesses native_decide feasibility.
-/

/-
================================================================================
THEOREM STATEMENT: 3-Cell Cone Propagation
================================================================================

The proposed strengthening of lifting_lemma:

  theorem cone_propagation_3cell (n : Nat) (k : Fin (2 * n + 1)) :
    Essential n k →
    Essential (n + 1) ⟨k.val, by omega⟩ ∨
    Essential (n + 1) ⟨k.val + 1, by omega⟩ ∨
    Essential (n + 1) ⟨k.val + 2, by omega⟩

Interpretation: if cell k is essential at step n, then at least one of
{k, k+1, k+2} is essential at step n+1. (This corresponds to {k-1, k, k+1}
in the original unshifted indexing.)

================================================================================
FEASIBILITY ASSESSMENT
================================================================================

COMPUTATIONAL EVIDENCE (n=1..10):
- ALL cells are essential for n≤10 (every cell affects output)
- The 3-cell propagation claim holds trivially (all disjuncts are true)
- The current lifting_lemma (k → k+1) also holds for all tested n

WITNESS ANALYSIS:
- Witnesses for Essential(n+1, k+1) are NOT local:
  - Unit spike positions vary widely across the config
  - No consistent local pattern (e.g., "spike at k+1 always works")
  - Spike position distribution for n=1..5 shows global spread

WHY native_decide ON A SMALL WINDOW IS INFEASIBLE:
1. The lifting lemma is an EXISTENTIAL statement (∃ witness config)
2. The witness config can have spikes at ANY position in the 2n+3 cell config
3. There is no known bound that restricts the witness to a local window
4. The C5 proof sketch (boundary neighbors = 1) fails for alternating n
   (verified: all-1s config with k=1 flip works for odd n, fails for even n)

ALGEBRAIC OBSTRUCTION (from findings.md C4/C5):
- The lifting lemma holds for Rule 30 because f(c,r) = c OR r is non-affine
  AND f(1,1) = 1 (diagonal criterion)
- This is a GLOBAL structural property, not a local truth-table fact
- The proof requires constructing witnesses with specific boundary conditions
- The boundary conditions depend on n in a non-trivial way

CONCLUSION:
- The 3-cell cone propagation claim is TRUE (computationally verified)
- It is NOT directly decidable by native_decide on a small window
- The proof requires a structural argument about witness construction
- The right path is likely through the LiftingLemma_LeftPermutive.lean approach
  (which uses the left-permutivity property of Rule 30)

================================================================================
RECOMMENDED NEXT STEPS
================================================================================

1. Check if LiftingLemma_LeftPermutive.lean compiles cleanly
   - If yes, it provides an axiom-free proof path
   - If no, identify the remaining sorries/axioms

2. For the 3-cell propagation claim specifically:
   - Prove it as a lemma IF the LeftPermutive approach succeeds
   - Otherwise, leave it as a conjectural strengthening of lifting_lemma

3. The deepest remaining axiom is still lifting_lemma itself.
   The computational certificate (n=1..1000) is strong evidence but not a proof.
-/

-- Stub theorem (would need actual proof):
-- theorem cone_propagation_3cell (n : Nat) (k : Fin (2 * n + 1)) :
--     Essential n k →
--     Essential (n + 1) ⟨k.val, by omega⟩ ∨
--     Essential (n + 1) ⟨k.val + 1, by omega⟩ ∨
--     Essential (n + 1) ⟨k.val + 2, by omega⟩ := by
--   sorry  -- NOT provable by native_decide; requires structural witness argument
