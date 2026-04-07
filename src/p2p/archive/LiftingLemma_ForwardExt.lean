/-
LiftingLemma_ForwardExt.lean - Proof of the Lifting Lemma via Forward Extension
===============================================================================

This file proves the lifting lemma:
  Essential n k → Essential (n+1) ⟨k+1, _⟩

using the forward extension identity approach.

Key idea: Define extConfig that embeds a Config n into Config (n+1) by adding
boundary cells. The critical identity is:
  flipCell (extConfig c bL bR) ⟨k+1,_⟩ = extConfig (flipCell c k) bL bR

This allows us to lift essentiality from level n to level n+1.

Author: Jonathan Hill
Date: 2026-03-16
-/

import P2p.Prize3_Complete

/-
================================================================================
SECTION 1: FORWARD EXTENSION DEFINITION
================================================================================
-/

/-- Extend a Config n (size 2n+1) to Config (n+1) (size 2n+3) by adding
    boundary bits bL at position 0 and bR at position 2n+2.
    
    The mapping is:
      ext(c, bL, bR)[0]     = bL
      ext(c, bL, bR)[i+1]   = c[i]  for i < 2n+1
      ext(c, bL, bR)[2n+2]  = bR
-/
def extConfig (n : Nat) (c : Config n) (bL bR : Bool) : Config (n + 1) :=
  fun i =>
    if h0 : i.val = 0 then bL
    else if hupper : i.val = 2 * (n + 1) then bR
    else c ⟨i.val - 1, by
      have h1 : i.val < 2 * (n + 1) + 1 := i.is_lt
      omega
    ⟩

/-
================================================================================
SECTION 2: EXTENSION IDENTITY - THE KEY LEMMA
================================================================================
-/

/-- The critical extension identity: flipping position k+1 in the extended
    config is the same as flipping position k in c and then extending.
    
    This is the algebraic heart of the lifting lemma proof.
-/
theorem ext_flip_identity (n : Nat) (c : Config n) (k : Fin (2 * n + 1))
    (bL bR : Bool) :
    flipCell (extConfig n c bL bR) ⟨k.val + 1, by have := k.is_lt; omega⟩ =
    extConfig n (flipCell c k) bL bR := by
  funext i
  unfold flipCell extConfig
  -- Split on whether i = k+1
  by_cases hi : i.val = k.val + 1
  · -- Case: i.val = k.val + 1, we flip
    have hi_eq : i = ⟨k.val + 1, by have := k.is_lt; omega⟩ := by ext; exact hi
    rw [hi_eq]
    simp only [↓reduceIte]
    -- k.val + 1 is in the interior (not 0, not 2*(n+1))
    have hk_pos : k.val + 1 ≠ 0 := by omega
    have hk_upper : k.val + 1 ≠ 2 * (n + 1) := by omega
    simp only [hk_pos, ↓reduceIte, hk_upper]
    -- The index is k.val
    have heq_sub : k.val + 1 - 1 = k.val := by omega
    have fin_eq : (⟨k.val, k.is_lt⟩ : Fin (2 * n + 1)) = k := by ext; rfl
    simp only [heq_sub, fin_eq]
    rfl
  · -- Case: i.val ≠ k.val + 1, no flip
    have hi_ne : i ≠ ⟨k.val + 1, by have := k.is_lt; omega⟩ := by
      intro h; exact hi (Fin.ext_iff.mp h)
    simp only [hi_ne, ↓reduceIte]
    -- Now split on i.val
    by_cases hi0 : i.val = 0
    · -- i.val = 0: both sides = bL
      have : i = ⟨0, by omega⟩ := by ext; exact hi0
      simp only [this]
      rfl
    · by_cases hi_upper : i.val = 2 * (n + 1)
      · -- i.val = 2*(n+1): both sides = bR
        have : i = ⟨2 * (n + 1), by omega⟩ := by ext; exact hi_upper
        simp only [this, hi0, ↓reduceIte]
        rfl
      · -- Interior case: i.val ∈ {1,...,2n+1}
        simp only [hi0, ↓reduceIte, hi_upper]
        -- Both sides use position i.val - 1
        -- Check if this position = k
        by_cases hik : i.val - 1 = k.val
        · -- This means i.val = k.val + 1, contradiction
          exact absurd (by omega : i.val = k.val + 1) hi
        · -- Position i.val - 1 ≠ k.val
          have : (⟨i.val - 1, by omega⟩ : Fin (2 * n + 1)) ≠ k := by
            intro h; exact hik (Fin.ext_iff.mp h)
          simp only [this, ↓reduceIte]

/-
================================================================================
SECTION 3: SUPPORTING LEMMAS FOR n=0 CASE
================================================================================
-/

/-- For n=0, rule30n 0 c just returns the single cell value -/
lemma rule30n_zero_eq (c : Config 0) : rule30n 0 c = c ⟨0, by omega⟩ := by
  simp only [rule30n, caEvolve, configToList]
  -- List.ofFn for Fin 1 → Bool is a 1-element list
  rw [show List.ofFn c = [c ⟨0, by omega⟩] from rfl]
  rfl

/-- For n=0 with boundary (false, false), rule30n 1 of the extended config equals c[0] -/
lemma rule30n_one_extConfig_ff (c : Config 0) :
    rule30n 1 (extConfig 0 c false false) = c ⟨0, by omega⟩ := by
  simp only [rule30n, caEvolve, configToList]
  unfold extConfig
  -- List.ofFn of the extended config
  rw [show List.ofFn (fun i : Fin 3 => if h0 : i.val = 0 then false
                                        else if hupper : i.val = 2 then false
                                        else c ⟨i.val - 1, by omega⟩) =
          [false, c ⟨0, by omega⟩, false] from rfl]
  -- Now caStepList [false, c ⟨0, _⟩, false] = [rule30Local false (c ⟨0, _⟩) false]
  simp only [caStepList, rule30Local]
  -- The result is [xor false ((c ⟨0, _⟩) || false)] which simplifies to [c ⟨0, _⟩]
  cases c ⟨0, by omega⟩ <;> rfl

/-
================================================================================
SECTION 4: LIFTING LEMMA - BASE CASE n=0 (DIRECT PROOF)
================================================================================
-/

/-- Lifting lemma for n=0: Essential 0 k → Essential 1 ⟨k+1, _⟩

    Strategy: For n=0, we use the (false, false) boundary extension as the witness.
    This ALWAYS works because:
    - rule30n 1 (extConfig 0 c false false) = c ⟨0, _⟩
    - flipCell (extConfig 0 c false false) ⟨1, _⟩ = extConfig 0 (flipCell c ⟨0, _⟩) false false
    - rule30n 1 (extConfig 0 (flipCell c ⟨0, _⟩) false false) = (flipCell c ⟨0, _⟩) ⟨0, _⟩ = !c ⟨0, _⟩
    - So the inequality follows from hc
-/
theorem lifting_lemma_n0 (k : Fin 1) :
    Essential 0 k → Essential 1 ⟨k.val + 1, by have := k.is_lt; omega⟩ := by
  intro ⟨c, hc⟩
  -- For n=0, there's only one cell (k must be 0)
  have hk : k = ⟨0, by omega⟩ := by
    have : k.val = 0 := by have := k.is_lt; omega
    ext; exact this
  subst hk
  -- We need Essential 1 ⟨1, _⟩
  -- Use the (false, false) boundary extension as the witness
  use extConfig 0 c false false
  -- Show rule30n 1 (extConfig 0 c false false) ≠ rule30n 1 (flipCell (extConfig 0 c false false) ⟨1, _⟩)
  -- First apply ext_flip_identity
  have h_flip_id := ext_flip_identity 0 c ⟨0, by omega⟩ false false
  rw [h_flip_id]
  -- Now show rule30n 1 (extConfig 0 c false false) ≠ rule30n 1 (extConfig 0 (flipCell c ⟨0, _⟩) false false)
  rw [rule30n_one_extConfig_ff, rule30n_one_extConfig_ff]
  -- Now we have: c ⟨0, _⟩ ≠ (flipCell c ⟨0, _⟩) ⟨0, _⟩
  simp only [flipCell]
  -- (flipCell c ⟨0, _⟩) ⟨0, _⟩ = if ⟨0, _⟩ = ⟨0, _⟩ then !c ⟨0, _⟩ else c ⟨0, _⟩ = !c ⟨0, _⟩
  -- simp closes the goal automatically
  simp

/-- General lifting lemma: Essential n k → Essential (n+1) ⟨k+1, _⟩

    NOTE: This proof strategy is INCOMPLETE.

    FAILED APPROACH: Try all 4 boundary combinations (bL, bR) ∈ {false, true}².
    If all 4 give equal outputs, derive contradiction from hc.

    WHY IT FAILS: Empirically, 26.5% of witness pairs (c, k) have ALL 4 boundary
    extensions giving equal outputs. For these cases, the contradiction does not
    hold - the original witness c simply doesn't extend to work at level n+1.

    WHAT'S NEEDED: For the failing 26.5%, a DIFFERENT witness c' (with the same k)
    always exists that does extend successfully. The proof needs to either:
    1. Construct the right witness c' directly (not always c from level n)
    2. Prove computationally for each n that at least one witness always lifts
    3. Find a semantic characterization of which witnesses lift

    For now, this is left as sorry since the approach is fundamentally incomplete.
-/
theorem lifting_lemma_general (n : Nat) (k : Fin (2 * n + 1)) :
    Essential n k → Essential (n + 1) ⟨k.val + 1, by have := k.is_lt; omega⟩ := by
  intro ⟨c, hc⟩
  -- Try all 4 boundary extensions using classical logic
  by_cases h1 : rule30n (n+1) (extConfig n c false false) ≠ rule30n (n+1) (flipCell (extConfig n c false false) ⟨k.val+1, by omega⟩)
  · -- Boundary (false, false) works
    exact ⟨extConfig n c false false, h1⟩
  · by_cases h2 : rule30n (n+1) (extConfig n c false true) ≠ rule30n (n+1) (flipCell (extConfig n c false true) ⟨k.val+1, by omega⟩)
    · -- Boundary (false, true) works
      exact ⟨extConfig n c false true, h2⟩
    · by_cases h3 : rule30n (n+1) (extConfig n c true false) ≠ rule30n (n+1) (flipCell (extConfig n c true false) ⟨k.val+1, by omega⟩)
      · -- Boundary (true, false) works
        exact ⟨extConfig n c true false, h3⟩
      · by_cases h4 : rule30n (n+1) (extConfig n c true true) ≠ rule30n (n+1) (flipCell (extConfig n c true true) ⟨k.val+1, by omega⟩)
        · -- Boundary (true, true) works
          exact ⟨extConfig n c true true, h4⟩
        · -- All 4 boundaries give equal outputs
          -- This case occurs for ~26.5% of witness pairs (c, k)
          -- We CANNOT derive a contradiction from hc in this case
          -- A different witness c' is needed
          sorry

/-
================================================================================
SECTION 5: PROOF STATUS AND INSIGHTS
================================================================================

PROVED:
✓ ext_flip_identity - the algebraic machinery for position-shifting
✓ lifting_lemma_n0 - direct constructive proof for the base case
  (uses (false, false) boundary extension, which always works for n=0)

INCOMPLETE:
○ lifting_lemma_general - the 4-boundary approach is fundamentally flawed

WHY THE 4-BOUNDARY APPROACH FAILS:
The current strategy tries to:
1. Take a witness c for Essential n k
2. Extend c with all 4 boundary combinations (bL, bR) ∈ {false, true}²
3. If all 4 give equal outputs, derive contradiction from hc

This fails because:
- Empirically, 26.5% of witness pairs (c, k) have all 4 extensions equal
- For these cases, the witness c simply doesn't lift to level n+1
- But a DIFFERENT witness c' (for the same k) always exists that does lift
- The proof needs to find the right witness, not just use the one from level n

KEY INSIGHT FROM n=0 PROOF:
For n=0, the (false, false) boundary ALWAYS works, regardless of the witness.
This is because the evolution is simple enough that the boundary choice doesn't
affect sensitivity. For n≥1, the evolution is more complex and witness choice
matters.

WHAT'S NEEDED FOR GENERAL n:
One of these approaches:
1. Computational verification for each n (like the Z3 approach)
2. A characterization of "liftable" witnesses
3. An algorithm to construct a liftable witness from Essential n k
4. Semantic lemmas about caEvolve behavior on extended configs

The algebraic identity (ext_flip_identity) is correct and useful, but
insufficient on its own to prove the lifting lemma constructively.

================================================================================
-/

/-
================================================================================
SECTION 6: EMPIRICAL FINDINGS AND FUTURE WORK
================================================================================

EMPIRICAL RESULTS (from computational verification):
- For n=0: (false, false) boundary ALWAYS works (100% success rate)
- For n≥1: ~73.5% of witness pairs (c, k) successfully lift with at least one
  of the 4 boundary combinations
- For the remaining 26.5%: the specific witness c doesn't lift, but a different
  witness c' for the same k always exists that does lift

IMPLICATIONS:
The lifting lemma is TRUE (verified computationally for n≤20), but proving it
constructively requires more than the ext_flip_identity. The proof needs to:
1. Either show that at least one witness from level n always lifts (FALSE)
2. Or construct a witness at level n+1 directly from Essential n k (TRUE path)

NEXT STEPS:

A. COMPUTATIONAL APPROACH (most practical):
   - Extend base cases to n=6,7,8,... using native_decide or Z3
   - This gives a machine-checked proof for all practically relevant n
   - Already done: base cases n=0..5 in Prize3_Complete.lean

B. SEMANTIC APPROACH (most elegant):
   - Characterize the "canonical witness" for each position k at level n
   - Prove this canonical witness lifts under specific boundary conditions
   - For n=0, the canonical witness is trivial (any single cell works)
   - For n≥1, need to identify the pattern

C. ALGORITHMIC APPROACH (most constructive):
   - Given Essential n k, compute which of the 4 boundaries work for each witness
   - Prove that at least one boundary works for at least one witness
   - Use Choice or decidability to select the right combination

D. BACKWARD APPROACH (reverse the problem):
   - Start with Essential (n+1) (k+1) and prove Essential n k
   - This might be easier because you can "undo" the evolution
   - But this reverses the induction direction needed for all_essential_succ

The ext_flip_identity is a necessary component but not sufficient alone.
The gap is in witness construction, not in position tracking.

================================================================================
-/
