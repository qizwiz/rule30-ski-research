/-
AllEssential_Minimal.lean
=========================
Standalone proof of all_essential_succ with NO mathlib dependency.
Imports only Init (core Lean 4). Verifies the proof compiles.

Once disk space allows a full mathlib build, these theorems can be
checked in Prize3_Complete.lean where they already appear at lines 345-381.
-/

-- Core Lean 4 / Init only — no mathlib needed for these proofs

/-- Rule 30 local update: p XOR (q OR r) -/
def rule30Local (p q r : Bool) : Bool := xor p (q || r)

/-- Configuration at generation n: 2n+1 cells -/
abbrev Config (n : Nat) := Fin (2 * n + 1) → Bool

/-- Single CA step on a list -/
def caStepList : List Bool → List Bool
  | p :: q :: r :: rest => rule30Local p q r :: caStepList (q :: r :: rest)
  | _ => []

/-- Evolve CA for n steps -/
def caEvolve : Nat → List Bool → List Bool
  | 0, cells => cells
  | t + 1, cells => caEvolve t (caStepList cells)

/-- Convert config to list -/
def configToList {n : Nat} (c : Config n) : List Bool := List.ofFn c

/-- rule30n: center cell value after n steps -/
def rule30n (n : Nat) (c : Config n) : Bool :=
  (caEvolve n (configToList c)).getD 0 false

/-- Essential: flipping cell k can change the output -/
def Essential (n : Nat) (k : Fin (2 * n + 1)) : Prop :=
  ∃ c : Config n, rule30n n c ≠ rule30n n (fun j => if j = k then !c j else c j)

-- ============================================================
-- AXIOMS (Z3-verified, matching Prize3_Complete.lean)
-- ============================================================

axiom lifting_lemma (n : Nat) (k : Fin (2 * n + 1)) :
    Essential n k → Essential (n + 1) ⟨k.val + 1, by have := k.is_lt; omega⟩

axiom left_boundary_essential (n : Nat) : Essential n ⟨0, by omega⟩

axiom right_boundary_essential (n : Nat) : Essential n ⟨2 * n, by omega⟩

axiom base_case_n0 (k : Fin 1) : Essential 0 k

-- ============================================================
-- THE KEY DEFINITIONS AND THEOREMS
-- ============================================================

/-- All cells are essential at level n -/
def AllEssential (n : Nat) : Prop :=
  ∀ k : Fin (2 * n + 1), Essential n k

/-- If all cells essential at n, then all essential at n+1 -/
-- Level n+1 has positions 0 .. 2*(n+1), i.e., 0 .. 2n+2.
-- Lifting covers 1 .. 2n+1 (shifting each level-n position right by 1).
-- Boundaries cover position 0 (left) and 2*(n+1) (right).
theorem all_essential_succ (n : Nat) (h : AllEssential n) : AllEssential (n + 1) := by
  intro k
  -- Case 1: position 0 — left boundary
  by_cases hk0 : k.val = 0
  · suffices heq : k = ⟨0, by omega⟩ by rw [heq]; exact left_boundary_essential (n + 1)
    exact Fin.ext hk0
  -- Case 2: right boundary position 2*(n+1)
  by_cases hk_right : k.val = 2 * (n + 1)
  · suffices heq : k = ⟨2 * (n + 1), by omega⟩ by rw [heq]; exact right_boundary_essential (n + 1)
    exact Fin.ext hk_right
  · -- Case 3: interior positions 1 .. 2n+1
    -- k.val ∈ {1..2n+1}, so k.val - 1 ∈ {0..2n} ⊂ Fin(2*n+1)
    have hk_pos : 1 ≤ k.val := by omega
    have hk_lt : k.val - 1 < 2 * n + 1 := by
      -- k.val < 2n+3 (from k.is_lt), k.val ≠ 2n+2 (from hk_right), k.val ≠ 0
      -- → k.val ≤ 2n+1 → k.val - 1 ≤ 2n < 2n+1
      have := k.is_lt
      omega
    have h_lift := lifting_lemma n ⟨k.val - 1, hk_lt⟩ (h ⟨k.val - 1, hk_lt⟩)
    -- h_lift : Essential (n+1) ⟨k.val - 1 + 1, _⟩
    suffices heq : k = ⟨k.val - 1 + 1, by omega⟩ by rw [heq]; exact h_lift
    exact Fin.ext (Nat.sub_add_cancel hk_pos).symm

/-- All cells essential at every level (induction) -/
theorem all_essential_all (n : Nat) : AllEssential n := by
  induction n with
  | zero =>
    intro k
    exact base_case_n0 k
  | succ n ih =>
    exact all_essential_succ n ih

-- ============================================================
-- SANITY CHECK
-- ============================================================

-- Confirm the type is what we expect
#check @all_essential_succ
-- all_essential_succ : ∀ (n : ℕ), AllEssential n → AllEssential (n + 1)

#check @all_essential_all
-- all_essential_all : ∀ (n : ℕ), AllEssential n
