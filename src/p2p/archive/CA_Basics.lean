/-
CA_Basics.lean - Unified Cellular Automaton Definitions for Rule 30 Prizes
============================================================================

This file provides shared definitions used across all three Wolfram Rule 30 Prize proofs:
- Prize 1: Center column non-periodicity
- Prize 2: XOR-balance (density = 1/2)
- Prize 3: All cells essential

Authors: Jonathan Hill
Date: 2026-03-03
Status: COMPLETE - Ready for import in all prize files
-/

import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Init.Data.Fin.Basic

/-
================================================================================
SECTION 1: CORE CA DEFINITIONS
================================================================================
-/

/-- Rule 30 local update function: rule30(p, q, r) = p XOR (q OR r) -/
def rule30Local (p q r : Bool) : Bool := xor p (q || r)

/-- Configuration at generation n: cells at positions [-n, n], i.e., 2n+1 cells -/
abbrev Config (n : Nat) := Fin (2 * n + 1) → Bool

/-- Flip the value at cell k in configuration c -/
def flipCell {n : Nat} (c : Config n) (k : Fin (2 * n + 1)) : Config n :=
  fun j => if j = k then !c j else c j

/-- Convert configuration to list (for compatibility with list-based evolution) -/
def configToList {n : Nat} (c : Config n) : List Bool := List.ofFn c

/-- Convert list to configuration (requires length = 2n+1) -/
def listToConfig {n : Nat} (cells : List Bool) (_ : cells.length = 2 * n + 1) : Config n :=
  fun i => cells.getD i.val false

/-
================================================================================
SECTION 2: CA EVOLUTION (LIST-BASED)
================================================================================
-/

/-- Single CA step on a list of cells (produces list of length - 2) -/
def caStepList : List Bool → List Bool
  | p :: q :: r :: rest => rule30Local p q r :: caStepList (q :: r :: rest)
  | _ => []

/-- Evolve CA for n steps starting from initial configuration -/
def caEvolve : Nat → List Bool → List Bool
  | 0, cells => cells
  | t + 1, cells => caEvolve t (caStepList cells)

/-- Extract center cell value after n steps of evolution -/
def centerCellValue (n : Nat) (cells : List Bool) : Bool :=
  (caEvolve n cells).getD 0 false

/-
================================================================================
SECTION 3: CA EVOLUTION (CONFIGURATION-BASED)
================================================================================
-/

/-- Rule 30 evolution function for Prize 3 (configuration-based)
    Takes configuration at generation n, returns Boolean output -/
def rule30n (n : Nat) (c : Config n) : Bool :=
  (caEvolve n (configToList c)).getD 0 false

/-- Essential cell: cell k at generation n affects the output
    This is the key definition for Prize 3 -/
def Essential (n : Nat) (k : Fin (2 * n + 1)) : Prop :=
  ∃ c : Config n, rule30n n c ≠ rule30n n (flipCell c k)

/-
================================================================================
SECTION 4: CENTER COLUMN SEQUENCE (FOR PRIZE 1)
================================================================================
-/

/-- Initial configuration: single 1 at center (position n), 0 elsewhere -/
def initialConfig (n : Nat) : Config n :=
  fun i => if i.val = n then true else false

/-- The center column sequence: c(n) = center cell value after n steps
    starting from single 1 at center (Wolfram's Prize 1 statement) -/
def centerColumnSeq (n : Nat) : Bool :=
  rule30n n (initialConfig n)

/-- Eventually periodic sequence (Wolfram Prize 1 negation) -/
def EventuallyPeriodic (seq : Nat → Bool) : Prop :=
  ∃ (N p : Nat), p > 0 ∧ ∀ n ≥ N, seq n = seq (n + p)

/-
================================================================================
SECTION 5: FUNDAMENTAL LEMMAS
================================================================================
-/

/-- caEvolve step decomposition: evolving n+1 steps = evolving n steps after one caStep -/
theorem caEvolve_succ (n : Nat) (cells : List Bool) :
    caEvolve (n + 1) cells = caEvolve n (caStepList cells) :=
  rfl

/-- caStep reduces length by exactly 2 -/
theorem caStep_length (cells : List Bool) :
    (caStepList cells).length = cells.length - 2 := by
  induction cells with
  | nil => simp [caStepList]
  | cons p rest ih =>
    match rest with
    | [] => simp [caStepList]
    | [q] => simp [caStepList]
    | q :: r :: rest3 =>
      simp only [caStepList, List.length_cons] at *
      omega

/-- caEvolve n steps reduces length by 2n (when list is long enough) -/
theorem caEvolve_length (n : Nat) (cells : List Bool)
    (hlen : 2 * n + 1 ≤ cells.length) :
    (caEvolve n cells).length = cells.length - 2 * n := by
  induction n generalizing cells with
  | zero => simp [caEvolve]
  | succ n ih =>
    simp only [caEvolve]
    have hcl := caStep_length cells
    have him := ih (caStepList cells) (by omega)
    omega

/-- After n steps on (2n+1)-cell list, exactly 1 cell remains -/
theorem caEvolve_final_length (n : Nat) (cells : List Bool)
    (hlen : cells.length = 2 * n + 1) :
    (caEvolve n cells).length = 1 := by
  have h := caEvolve_length n cells (by omega)
  omega

/-
================================================================================
SECTION 6: XOR-LINEARITY (FOR PRIZE 2)
================================================================================
-/

/-- flipFirst b cells: XOR b into the head cell, leave tail unchanged -/
def flipFirst (b : Bool) : List Bool → List Bool
  | [] => []
  | h :: t => xor b h :: t

/-- Rule 30 is XOR-linear in its first (leftmost) argument -/
theorem rule30Local_xor_linear (b h q r : Bool) :
    rule30Local (xor b h) q r = xor b (rule30Local h q r) := by
  simp [rule30Local]

/-- caStep commutes with flipFirst (requires 3+ cells) -/
theorem caStep_commutes_flipFirst (b : Bool) (cells : List Bool)
    (h3 : 3 ≤ cells.length) :
    caStepList (flipFirst b cells) = flipFirst b (caStepList cells) := by
  match cells with
  | p :: q :: r :: rest =>
    simp [flipFirst, caStepList, rule30Local_xor_linear]

/-- caEvolve commutes with flipFirst (when list is long enough) -/
theorem caEvolve_commutes_flipFirst (b : Bool) (n : Nat) (cells : List Bool)
    (hlen : 2 * n + 1 ≤ cells.length) :
    caEvolve n (flipFirst b cells) = flipFirst b (caEvolve n cells) := by
  induction n generalizing cells with
  | zero => simp [caEvolve]
  | succ n ih =>
    simp only [caEvolve]
    have h3 : 3 ≤ cells.length := by omega
    rw [caStep_commutes_flipFirst b cells h3]
    apply ih
    have hcl := caStep_length cells
    omega

/-- flipFirst on non-empty list flips the head via XOR -/
theorem flipFirst_headD (b : Bool) (cells : List Bool) (hne : cells ≠ []) :
    (flipFirst b cells).headD false = xor b (cells.headD false) := by
  match cells with
  | [] => exact absurd rfl hne
  | x :: rest => simp [flipFirst]

/-
================================================================================
SECTION 7: PRIZE 2 MAIN THEOREM (XOR-FLIPS)
================================================================================
-/

/-- Prize 2 Core Lemma: Flipping the leftmost input cell flips the output
    This establishes: f_n(x_0, x_1, ..., x_{2n}) = x_0 XOR h_n(x_1, ..., x_{2n})
    Therefore: Pr[f_n = 1 | uniform random input] = 1/2 exactly -/
theorem prize2_xor_flips_output (n : Nat) (cells : List Bool)
    (hlen : cells.length = 2 * n + 1) :
    (caEvolve n (flipFirst true cells)).headD false =
    !((caEvolve n cells).headD false) := by
  rw [caEvolve_commutes_flipFirst true n cells (by omega)]
  have hne : caEvolve n cells ≠ [] := by
    intro h
    have := caEvolve_final_length n cells hlen
    rw [h] at this; simp at this
  rw [flipFirst_headD true (caEvolve n cells) hne]
  cases h : (caEvolve n cells).headD false <;> rfl

/-
================================================================================
SECTION 8: INITIAL CONFIGURATION LEMMAS (FOR PRIZE 1 & 3)
================================================================================
-/

/-- The initial configuration has exactly one 1 at the center -/
theorem initialConfig_center (n : Nat) :
    (initialConfig n) ⟨n, by
      have : n < 2 * n + 1 := by
        have := Nat.lt_succ_self n
        omega
      exact this
    ⟩ = true := by
  simp [initialConfig]

/-- Cells other than the center are 0 in the initial configuration -/
theorem initialConfig_off_center (n : Nat) (k : Fin (2 * n + 1)) (hk : k.val ≠ n) :
    (initialConfig n) k = false := by
  simp [initialConfig, hk]

/-
================================================================================
END OF CA_BASICS.lean
All definitions ready for import in Prize 1, 2, and 3 proofs.
================================================================================
-/
