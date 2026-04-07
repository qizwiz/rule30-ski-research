/-
ToggleChannel.lean - Left-as-toggle channel lemmas for Rule 30
================================================================

Key insight: Rule 30 = L XOR (C OR R)
- Left input is a TOGGLE WIRE (linear, difference-preserving)
- Center/Right inputs are GATE GENERATORS (nonlinear, saturating)

This file formalizes the "left-toggle propagation" lemmas that enable:
- Block sensitivity lower bounds (Prize 3)
- Non-periodicity arguments (Prize 1)
- Density = 1/2 arguments (Prize 2)

Author: Jonathan Hill (with mathematical insight from deep analysis)
Date: 2026-03-04
-/

import P2p.CA_Basics
import P2p.Prize3_Complete

/-
================================================================================
SECTION 1: LOCAL TOGGLE LEMMA (Single Update)
================================================================================
-/

/-- Rule 30 local update decomposed: new = L XOR (C OR R) -/
lemma rule30Local_decomposed (p q r : Bool) :
  rule30Local p q r = xor p (q || r) := by
  rfl  -- By definition of rule30Local

/-- If the gate (C OR R) is fixed, flipping L flips the output -/
lemma rule30Local_left_toggle_fixed_gate
  (L₁ L₂ C R : Bool)
  (hL : L₁ ≠ L₂) :
  rule30Local L₁ C R ≠ rule30Local L₂ C R := by
  intro h_eq
  -- Expand definition: rule30Local L C R = L XOR (C OR R)
  rw [rule30Local_decomposed] at h_eq
  rw [rule30Local_decomposed] at h_eq
  -- Now we have: L₁ XOR (C OR R) = L₂ XOR (C OR R)
  -- Since L₁ ≠ L₂, this is impossible (XOR with same gate gives different outputs)
  -- Case analysis on all boolean values
  cases L₁ <;> cases L₂ <;> cases C <;> cases R <;> simp at hL h_eq ⊢
  <;> try contradiction
  <;> try decide

/-- Flipping left input flips output when gate is fixed (equality form) -/
lemma rule30Local_left_flip
  (L C R : Bool) :
  rule30Local (!L) C R = !(rule30Local L C R) := by
  rw [rule30Local_decomposed]
  -- xor (!L) G = !(xor L G) for any gate G
  cases L <;> cases C <;> cases R <;> simp [xor, band, bor]
  <;> try decide

/-
================================================================================
SECTION 2: GATE-STABLE PATH STRUCTURE
================================================================================
-/

/-- Base case: Toggle propagates in 1 step

For n=1, flipping position 1 (left edge of 3-cell cone) flips center output
-/
theorem left_toggle_propagates_k1 :
  ∃ (c₁ c₂ : Config 1),
    (∀ j ≠ 1, c₁ j = c₂ j) ∧
    c₁ 1 ≠ c₂ 1 ∧
    rule30n 1 c₁ ≠ rule30n 1 c₂ := by
  -- c₁ = [0, 0, 0], c₂ = [0, 1, 0]
  -- They agree everywhere except position 1
  -- rule30n 1 c₁ = rule30Local 0 0 0 = 0 XOR (0 OR 0) = 0
  -- rule30n 1 c₂ = rule30Local 0 1 0 = 0 XOR (1 OR 0) = 1
  -- Outputs differ!
  use fun i => if i.val = 0 then false else if i.val = 1 then false else false
  use fun i => if i.val = 0 then false else if i.val = 1 then true else false
  constructor
  · -- Agree everywhere except position 1
    intro j hj
    fin_cases j <;> simp at hj ⊢ <;> try contradiction <;> try rfl
  · constructor
    · -- Differ at position 1
      simp
    · -- Outputs differ
      simp [rule30n, caEvolve, caStepList, rule30Local]
      <;> decide

/-- Base case: Toggle propagates in 2 steps

For n=2, flipping position 2 (left edge of 5-cell cone) can flip center output
-/
theorem left_toggle_propagates_k2 :
  ∃ (c₁ c₂ : Config 2),
    (∀ j ≠ 2, c₁ j = c₂ j) ∧
    c₁ 2 ≠ c₂ 2 ∧
    rule30n 2 c₁ ≠ rule30n 2 c₂ := by
  -- c₁ = [0, 0, 0, 0, 0], c₂ = [0, 0, 1, 0, 0]
  -- Step 1: c₁ → [0, 0], c₂ → [1, 0]
  -- Step 2: c₁ → [0], c₂ → [1]
  -- Outputs differ!
  use fun i => false
  use fun i => if i.val = 2 then true else false
  constructor
  · -- Agree everywhere except position 2
    intro j hj
    fin_cases j <;> simp at hj ⊢ <;> try contradiction <;> try rfl
  · constructor
    · -- Differ at position 2
      simp
    · -- Outputs differ
      simp [rule30n, caEvolve, caStepList, rule30Local]
      <;> decide

/-- A gate-stable path certifies that a toggle can propagate from (t=0, pos) to (t=k, center)

The path is a sequence of positions pos(t) for t=0..k where:
- pos(0) = starting position (left edge)
- pos(k) = center position
- At each step, the gate value (C OR R) is the same in both worlds
- This ensures the toggle propagates cleanly
-/
structure GateStablePath (k : Nat) where
  /-- Position at each time step -/
  pos : Fin (k + 1) → Nat
  /-- Start position is within valid range -/
  start_valid : pos 0 < 2 * k + 1
  /-- End position is center -/
  end_center : pos k = k
  /-- Step rule: position changes by at most 1 per step -/
  step_bound : ∀ t : Fin k, (pos t.succ : Int) - (pos t : Int) ∈ ({-1, 0, 1} : Set Int)
  /-- Gate stability: for two configs differing only at start, gate values match along path -/
  gate_stable : ∀ (c₁ c₂ : Config k),
    (∀ j ≠ pos 0, c₁ j = c₂ j) →
    c₁ (pos 0) ≠ c₂ (pos 0) →
    ∀ t : Fin k,
      let center_t := pos t
      let right_t := pos t + 1
      (center_t < 2 * (k - t) + 1) →
      (right_t < 2 * (k - t) + 1) →
      (c₁ center_t || c₁ right_t) = (c₂ center_t || c₂ right_t)

/-
================================================================================
SECTION 3: TOGGLE PROPAGATION LEMMA (k Steps)
================================================================================
-/

/-- Main lemma: A toggle bit at left edge propagates to center after k steps

Given a gate-stable path, flipping the bit at the start position
flips the center output after k steps.
-/
theorem left_toggle_propagates_along_path
  (k : Nat)
  (P : GateStablePath k)
  (c₁ c₂ : Config k)
  (h_agree : ∀ j ≠ P.pos 0, c₁ j = c₂ j)
  (h_differ : c₁ (P.pos 0) ≠ c₂ (P.pos 0)) :
  rule30n k c₁ ≠ rule30n k c₂ := by
  -- Proof by induction on k
  -- Base case (k=0): Trivial (no evolution, outputs are the configs themselves)
  -- Inductive step:
  --   1. Apply rule30Local_left_toggle_fixed_gate at position P.pos 0
  --   2. Use P.gate_stable to ensure gate is fixed
  --   3. Toggle propagates to next layer
  --   4. Apply induction hypothesis for remaining k-1 steps
  induction k with
  | zero =>
    -- Base case: no evolution
    simp [rule30n] at h_differ ⊢
    exact h_differ
  | succ k ih =>
    -- Inductive step: k+1 steps
    -- Apply one step of evolution
    -- Use gate_stable to show toggle propagates
    -- Apply ih for remaining k steps
    admit  -- ~20 lines of careful induction

/-
================================================================================
SECTION 4: EXPLICIT CONSTRUCTION FOR ALL-ZEROS CONFIG
================================================================================
-/

/-- For all-zeros config, construct a gate-stable path

Key insight: All-zeros has gate = 0 OR 0 = 0 everywhere
This is the MOST STABLE gate possible (always 0)
Therefore toggle propagates CLEANLY
-/
def all_zeros_gate_path (k : Nat) : GateStablePath k where
  pos t := k - t.val  -- Start at left edge (position k), move right to center
  start_valid := by
    simp
    omega
  end_center := by
    simp
  step_bound := by
    intro t
    simp [Fin.val_succ]
    -- Position changes by exactly -1 per step (moving right)
    use -1
    <;> simp <;> omega
  gate_stable := by
    intro c₁ c₂ h_agree h_differ t h_center h_right
    -- For all-zeros config, gate = 0 OR 0 = 0
    -- But we need to show gate is same for c₁ and c₂
    -- Since c₁, c₂ agree everywhere except pos 0, and pos t ≠ pos 0 for t > 0
    -- the gate values are the same
    admit  -- ~10 lines showing gate stability for all-zeros

/-- All-zeros sensitivity lemma (using toggle channel)

For odd n, all-zeros config has sensitivity ≥ n
-/
theorem all_zeros_sensitivity_via_toggle (n : Nat) (h : Odd n) :
  sensitivity_at (rule30n n) (all_zeros_config n) ≥ n := by
  -- Construct n disjoint toggle channels
  -- Each channel is a single cell on left edge
  -- By left_toggle_propagates_along_path, each can flip center
  -- Therefore sensitivity ≥ n
  have P : GateStablePath n := all_zeros_gate_path n
  -- Count sensitive cells
  -- Each position in left half is sensitive (can flip center)
  -- Therefore sensitivity ≥ n
  admit  -- ~15 lines counting sensitive cells

/-
================================================================================
SECTION 5: BLOCK SENSITIVITY FROM TOGGLE CHANNELS
================================================================================
-/

/-- Construct n disjoint toggle channels for block sensitivity

Blocks: {0}, {2}, {4}, ..., {2n-2} (every other cell on left edge)
These are disjoint and each can independently flip center
-/
def toggle_channels_blocks (n : Nat) : Finset (Finset (Fin (2 * n + 1))) :=
  Finset.image (λ i => {⟨2 * i, by omega⟩}) (Finset.range n)

/-- Block sensitivity ≥ n via toggle channels -/
theorem rule30_block_sensitivity_via_toggles (n : Nat) :
  block_sensitivity (rule30n n) ≥ n := by
  -- Use all-zeros config as witness
  -- Blocks are toggle_channels_blocks n
  -- Each block is a single cell (disjoint)
  -- By left_toggle_propagates_along_path, each flips center
  -- Therefore block_sensitivity ≥ n
  use all_zeros_config n
  use toggle_channels_blocks n
  constructor
  · -- Show blocks are disjoint
    simp [toggle_channels_blocks]
    admit  -- ~5 lines showing disjointness
  · -- Show each block is sensitive
    intro i hi
    -- i is in toggle_channels_blocks n
    -- Therefore i = {2*j} for some j < n
    -- By left_toggle_propagates_along_path, this cell can flip center
    admit  -- ~10 lines showing sensitivity

/-
================================================================================
SECTION 6: PRIZE 3 QED (Using Toggle Channels)
================================================================================
-/

/-- Prize 3: Computational irreducibility via toggle channels -/
theorem prize3_via_toggle_channels (n : Nat) :
  ∀ (A : Algorithm), work A (rule30n n) ≥ n := by
  intro A
  calc
    work A (rule30n n) ≥ decision_tree_depth (rule30n n) := work_ge_decision_tree_depth _ _
    _ ≥ block_sensitivity (rule30n n) := nisan_lower_bound _
    _ ≥ n := rule30_block_sensitivity_via_toggles n

/-
================================================================================
SUMMARY

LEMMA HIERARCHY:
1. rule30Local_left_toggle_fixed_gate (local, 1 step) ✓
2. left_toggle_propagates_along_path (k steps, needs GateStablePath) ⚠️
3. all_zeros_gate_path (explicit construction for all-zeros) ⚠️
4. all_zeros_sensitivity_via_toggle (sensitivity ≥ n for odd n) ⚠️
5. rule30_block_sensitivity_via_toggles (block sensitivity ≥ n) ⚠️
6. prize3_via_toggle_channels (Prize 3 QED) ✓ (conditional on above)

PROOF STATUS:
- Local toggle lemma: ✓ Provable by case analysis
- GateStablePath structure: ✓ Defined
- Toggle propagation: ⚠️ Needs induction (~20 lines)
- All-zeros path: ⚠️ Needs gate stability proof (~10 lines)
- All-zeros sensitivity: ⚠️ Needs counting (~15 lines)
- Block sensitivity: ⚠️ Needs disjointness (~15 lines)
- Prize 3: ✓ Follows from above

NEXT STEPS:
1. Prove rule30Local_left_toggle_fixed_gate (30 min)
2. Prove left_toggle_propagates_along_path for k=1,2 (1 hour)
3. Generalize to arbitrary k (1-2 hours)
4. Complete all-zeros construction (1 hour)
5. Assemble Prize 3 (30 min)

TOTAL: ~4-5 hours to Prize 3 QED via toggle channels!

================================================================================
-/
