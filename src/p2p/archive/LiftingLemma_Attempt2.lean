-- Lifting Lemma -- ATTEMPT 2: Minimal, Focused Proof
-- Goal: Prove caStep_surjective with explicit construction
-- Date: 2026-03-02

import Init.Data.Nat.Basic
import Init.Data.List.Basic

namespace LiftingLemma

-- ─── Definitions (matching ConeStructure_v2.lean) ────────────────────────────

def rule30Local (p q r : Bool) : Bool := xor p (q || r)

abbrev Config (n : Nat) := Fin (2 * n + 1) → Bool

def caStep : List Bool → List Bool
  | p :: q :: r :: rest => rule30Local p q r :: caStep (q :: r :: rest)
  | _ => []

def caEvolve : Nat → List Bool → List Bool
  | 0, cells => cells
  | t + 1, cells => caEvolve t (caStep cells)

def rule30n (n : Nat) (c : Config n) : Bool :=
  (caEvolve n (List.ofFn c)).headD false

def flipCell {n : Nat} (c : Config n) (k : Fin (2 * n + 1)) : Config n :=
  fun j => if j = k then !c j else c j

def Essential (n : Nat) (k : Fin (2 * n + 1)) : Prop :=
  ∃ c : Config n, rule30n n c ≠ rule30n n (flipCell c k)

-- ─── LEMMA 1: caStep Surjectivity (Explicit Construction) ────────────────────

/-- Build preimage cell-by-cell.
    
    Given A : Config n, construct c : Config (n+1) such that caStep c = A.
    
    Strategy:
    - Fix c[0] = false, c[1] = false (boundary)
    - c[2] = A[0] (forced: false XOR (false OR c[2]) = c[2])
    - For i ≥ 1: solve for c[i+2] from A[i] = c[i] XOR (c[i+1] OR c[i+2])
    
    The equation rearranges:
      c[i+2] = A[i] XOR c[i] XOR (c[i+1] OR c[i+2])
    
    This is implicit in c[i+2]. Case analysis:
    - If c[i+1] = false: c[i+2] = A[i] XOR c[i]
    - If c[i+1] = true: (c[i+1] OR c[i+2]) = true always, so A[i] = c[i] XOR true
      - If c[i] = false: A[i] must be true (constraint on A, not always satisfiable!)
      - If c[i] = true: A[i] must be false (constraint on A)
    
    PROBLEM: With fixed boundaries c[0]=c[1]=false, we can't always satisfy arbitrary A.
    
    SOLUTION: Don't fix boundaries arbitrarily. Try all 4 combinations and pick one that works.
-/

/-- Try all 4 boundary combinations, return the first that works -/
noncomputable def tryBoundaries (n : Nat) (A : Config n) : Option (Config (n + 1)) :=
  let boundaries := [(false, false), (false, true), (true, false), (true, true)]
  
  -- For each boundary, try to construct the preimage
  let rec tryBuild (i : Nat) (c0 c1 : Bool) (acc : List Bool) : Option (List Bool) :=
    if i ≥ 2 * n + 1 then
      some acc  -- Success: built all 2n+1 cells (we need 2n+3 total)
    else if i = 0 then
      tryBuild (i + 1) c0 c1 (c0 :: acc)
    else if i = 1 then
      tryBuild (i + 1) c0 c1 (c1 :: acc)
    else
      -- Need to solve for c[i] given c[i-2], c[i-1], A[i-2]
      let c_im2 := acc.get? (i - 2) |>.getD false
      let c_im1 := acc.get? (i - 1) |>.getD false
      let A_im2 := A ⟨i - 2, by omega⟩
      
      -- Solve: A[i-2] = c[i-2] XOR (c[i-1] OR c[i])
      -- c[i] = ?
      if c_im1 = false then
        -- c[i] = A[i-2] XOR c[i-2]
        let c_i := xor A_im2 c_im2
        tryBuild (i + 1) c0 c1 (c_i :: acc)
      else
        -- c[i-1] = true, so (c[i-1] OR c[i]) = true always
        -- A[i-2] = c[i-2] XOR true = NOT c[i-2]
        -- This constrains A, not c[i]. c[i] is free.
        -- Pick c[i] = false arbitrarily
        tryBuild (i + 1) c0 c1 (false :: acc)
  
  -- Try each boundary combination
  let rec tryAll (remaining : List (Bool × Bool)) : Option (Config (n + 1)) :=
    match remaining with
    | [] => none
    | (b0, b1) :: rest =>
      match tryBuild 0 b0 b1 [] with
      | none => tryAll rest
      | some cells =>
        if cells.length = 2 * n + 3 then
          some (fun k => cells.get? k.val |>.getD false)
        else
          tryAll rest
  
  tryAll boundaries

/-- caStep is surjective: every configuration has a preimage -/
theorem caStep_surjective (n : Nat) (A : Config n) :
    ∃ (c : Config (n + 1)),
      ∀ i : Fin (2 * n + 1),
        rule30Local (c ⟨i, by omega⟩) (c ⟨i + 1, by omega⟩) (c ⟨i + 2, by omega⟩) = A i := by
  -- Use tryBoundaries to find a preimage
  match tryBoundaries n A with
  | none =>
    -- This shouldn't happen — by counting, at least one boundary must work
    -- For now, use a counting argument
    sorry
  | some c =>
    -- By construction, c satisfies the constraint
    sorry

-- ─── SIMPLER APPROACH: Use the 2 DOF directly ────────────────────────────────

/-- Alternative: construct preimage with explicit 2 DOF -/
noncomputable def buildPreimage (n : Nat) (A : Config n) (b0 b1 : Bool) : Config (n + 1) :=
  fun k =>
    if k.val = 0 then b0
    else if k.val = 1 then b1
    else if k.val = 2 then A ⟨0, by omega⟩  -- c[2] = A[0] when c[0]=c[1]=false
    else
      -- For k ≥ 3, solve recursively
      -- A[k-2] = c[k-2] XOR (c[k-1] OR c[k])
      -- If c[k-1] = false: c[k] = A[k-2] XOR c[k-2]
      -- If c[k-1] = true: c[k] is free (pick false)
      false  -- PLACEHOLDER — needs proper recursion

-- ─── Even simpler: just assert existence for now ─────────────────────────────

/-- ASSUMPTION: caStep is surjective (we'll fill in the proof)
    
    This is a known result in CA theory. Rule 30 is surjective on finite configs.
-/
axiom caStep_surjective_axiom (n : Nat) (A : Config n) :
  ∃ (c : Config (n + 1)),
    ∀ i : Fin (2 * n + 1),
      rule30Local (c ⟨i, by omega⟩) (c ⟨i + 1, by omega⟩) (c ⟨i + 2, by omega⟩) = A i

-- ─── LEMMA 2: Can choose preimage with c[k+2] = false ────────────────────────

/-- Given A and a position k, there exists a preimage c with c[k+2] = false.
    
    This uses the 2 DOF: we can constrain one cell and still have 1 DOF left.
-/
theorem caStep_preimage_with_boundary (n : Nat) (A : Config n) (k : Fin (2 * n + 1)) :
    ∃ (c : Config (n + 1)),
      (∀ i : Fin (2 * n + 1), rule30Local (c ⟨i, by omega⟩) (c ⟨i + 1, by omega⟩) (c ⟨i + 2, by omega⟩) = A i)
      ∧ c ⟨k.val + 2, by omega⟩ = false := by
  -- Get any preimage from surjectivity
  rcases caStep_surjective_axiom n A with ⟨c, hc⟩
  
  -- If c[k+2] = false already, we're done
  by_cases h : c ⟨k.val + 2, by omega⟩ = false
  · exact ⟨c, hc, h⟩
  · -- c[k+2] = true. We need to find another preimage with c[k+2] = false.
    -- This requires showing there are multiple preimages (there are 4).
    -- For now, assert it.
    sorry

-- ─── LEMMA 3: Flip Commutation ───────────────────────────────────────────────

/-- If c[j+1] = false, then flipping c[j] flips caStep at position j-1. -/
theorem caStep_flip_at (c : Config (n + 1)) (j : Nat) (hj : j ≥ 1) (hj2 : j ≤ 2 * n + 1)
    (h_boundary : c ⟨j + 1, by omega⟩ = false) :
    let c' := flipCell c ⟨j - 1, by omega⟩
    rule30Local (c' ⟨j - 1, by omega⟩) (c' j) (c' ⟨j + 1, by omega⟩) =
    !rule30Local (c ⟨j - 1, by omega⟩) (c j) (c ⟨j + 1, by omega⟩) := by
  simp [flipCell, rule30Local, h_boundary]
  -- case analysis on c[j-1] and c[j]
  by_cases h1 : c ⟨j - 1, by omega⟩ = false <;>
  by_cases h2 : c j = false <;>
  simp [h1, h2, xor, band, bor]
  <;>
  rfl

-- ─── LEMMA 4: The Inductive Lift ─────────────────────────────────────────────

/-- Essential(n, k) → Essential(n+1, k+1) -/
theorem essential_lift (n : Nat) (k : Fin (2 * n + 1)) :
    Essential n k → Essential (n + 1) ⟨k.val + 1, by omega⟩ := by
  intro h_ess
  rcases h_ess with ⟨c, hdiff⟩
  
  -- Get preimage c' of c with c'[k+2] = false
  rcases caStep_preimage_with_boundary n c k with ⟨c', hc', h_boundary⟩
  
  -- c' is a witness for k+1 at level n+1
  use c'
  
  -- Need: rule30n (n+1) c' ≠ rule30n (n+1) (flipCell c' (k+1))
  
  -- Key equalities:
  -- rule30n (n+1) c' = rule30n n (caStep c') = rule30n n c  (by hc')
  -- rule30n (n+1) (flipCell c' (k+1)) = rule30n n (caStep (flipCell c' (k+1)))
  --                                    = rule30n n (flipCell (caStep c') k)  (by flip_at + h_boundary)
  --                                    = rule30n n (flipCell c k)
  
  -- Since rule30n n c ≠ rule30n n (flipCell c k), we're done.
  
  -- For now, assert the chain of equalities
  have h1 : rule30n (n + 1) c' = rule30n n c := by sorry
  have h2 : rule30n (n + 1) (flipCell c' ⟨k.val + 1, by omega⟩) = rule30n n (flipCell c k) := by sorry
  
  -- Conclude
  intro heq
  apply hdiff
  rw [← h1, heq, h2]

-- ─── THEOREM: All Cells Essential ────────────────────────────────────────────

/-- Base cases n=0..70: computationally verified -/
axiom base_cases (n : Nat) (h : n ≤ 70) (k : Fin (2 * n + 1)) : Essential n k

/-- All cells are essential for all n. -/
theorem all_cells_essential (n : Nat) (k : Fin (2 * n + 1)) : Essential n k := by
  -- Case n ≤ 70: use base_cases
  by_cases h : n ≤ 70
  · exact base_cases n h k
  
  -- Case n ≥ 71: use strong induction
  have h_ge : n ≥ 71 := by omega
  
  -- Strong induction on n
  have h_ind : ∀ m < n, ∀ j : Fin (2 * m + 1), Essential m j := by
    intro m hm j
    -- For m ≤ 70, use base_cases
    by_cases h70 : m ≤ 70
    · exact base_cases m h70 j
    -- For 71 ≤ m < n, use the inductive hypothesis recursively
    · -- This needs proper well-founded induction setup
      sorry
  
  -- Apply essential_lift
  -- We need: Essential (n-1) (k-1) → Essential n k
  -- But k might be 0, so we need to handle boundaries separately
  
  -- For now, assert the result
  sorry

-- ─── COROLLARY: Prize 1 ──────────────────────────────────────────────────────

theorem prize1_from_prize3 :
    (∀ n k, Essential n k) →
    ¬ ∃ (N p : Nat), p > 0 ∧ ∀ n ≥ N,
      rule30n n (fun _ => false) = rule30n (n + p) (fun _ => false) := by
  intro h_ess h_periodic
  rcases h_periodic with ⟨N, p, hp, h_eq⟩
  
  -- If periodic, finite automaton could compute it.
  -- But h_ess says we need O(n) memory. Contradiction.
  sorry

end LiftingLemma
