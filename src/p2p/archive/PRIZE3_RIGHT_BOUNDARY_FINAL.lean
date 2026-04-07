-- Rule 30 Prize 3: Right Boundary Cell is Essential
-- PROOF: all-false witness + signal propagation
-- Fixed: explicit parentheses so :: chains don't bleed into ++ expressions

import Init.Data.Nat.Basic
import Init.Data.List.Basic

-- ─── CA definitions ─────────────────────────────────────────────────────────

def rule30Local (p q r : Bool) : Bool := xor p (q || r)

def caStep : List Bool → List Bool
  | p :: q :: r :: rest => rule30Local p q r :: caStep (q :: r :: rest)
  | _ => []

def caEvolve : Nat → List Bool → List Bool
  | 0, cells => cells
  | t + 1, cells => caEvolve t (caStep cells)

-- ─── Explicit equation lemma (avoids simp unfolding issues) ─────────────────

theorem caStep_cons3 (p q r : Bool) (rest : List Bool) :
    caStep (p :: q :: r :: rest) = rule30Local p q r :: caStep (q :: r :: rest) := rfl

-- ─── Simp lemmas ─────────────────────────────────────────────────────────────

theorem rule30Local_fff : rule30Local false false false = false := rfl
theorem rule30Local_fft : rule30Local false false true  = true  := rfl

-- ─── Lemma A: caStep on all-false collapses by 2 ────────────────────────────

-- caStep (replicate (n+2) false) = replicate n false
theorem caStep_all_false : ∀ (n : Nat),
    caStep (List.replicate (n + 2) false) = List.replicate n false
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => by
      -- replicate (n+4) false = F :: F :: F :: replicate (n+1) false
      -- (no ++ here, so no precedence issue)
      rw [show List.replicate (n + 2 + 2) false =
          false :: false :: false :: List.replicate (n + 1) false from by
          simp [List.replicate_succ]]
      rw [caStep_cons3]
      simp only [rule30Local_fff]
      -- false :: caStep (F :: F :: replicate (n+1) false) = replicate (n+2) false
      rw [show false :: false :: List.replicate (n + 1) false =
          List.replicate (n + 3) false from by
          simp [List.replicate_succ]]
      rw [show n + 3 = (n + 1) + 2 from by omega]
      rw [caStep_all_false (n + 1)]
      simp [List.replicate_succ]

-- ─── Lemma B: caEvolve n on (2n+1)-all-false gives [false] ──────────────────

theorem caEvolve_all_false : ∀ (n : Nat),
    caEvolve n (List.replicate (2 * n + 1) false) = [false]
  | 0 => rfl
  | (n + 1) => by
      simp only [caEvolve]
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by omega]
      rw [caStep_all_false (2 * n + 1)]
      exact caEvolve_all_false n

-- ─── Lemma C: signal propagation — single T at right eats 2 falses per step ──

-- KEY INSIGHT: use (List.replicate n false ++ [true]) with explicit parens
-- so the argument to caStep is  F :: F :: F :: (replicate n false ++ [true])
-- which matches the p :: q :: r :: rest pattern correctly.

-- caStep (replicate (n+2) false ++ [true]) = replicate n false ++ [true]
theorem caStep_right_signal : ∀ (n : Nat),
    caStep (List.replicate (n + 2) false ++ [true]) = List.replicate n false ++ [true]
  | 0 => rfl   -- caStep [F, F, T] = [T]  ✓
  | (n + 1) => by
      -- Rewrite LHS argument: replicate (n+3) false ++ [true]
      --   = F :: F :: F :: (replicate n false ++ [true])   ← explicit parens!
      rw [show List.replicate (n + 1 + 2) false ++ [true] =
          false :: false :: false :: (List.replicate n false ++ [true]) from by
          simp [List.replicate_succ, List.cons_append]]
      -- Unfold caStep on the 3-cons pattern
      rw [caStep_cons3]
      simp only [rule30Local_fff]
      -- Goal: false :: caStep (F :: F :: (replicate n false ++ [true]))
      --     = replicate (n+1) false ++ [true]
      -- Rewrite RHS to expose the leading false
      rw [show List.replicate (n + 1) false ++ [true] =
          false :: (List.replicate n false ++ [true]) from by
          simp [List.replicate_succ, List.cons_append]]
      -- Now both sides start with false ::, use congr 1
      congr 1
      -- Goal: caStep (F :: F :: (replicate n false ++ [true]))
      --     = replicate n false ++ [true]
      -- Rewrite argument back to replicate form for IH
      rw [show false :: false :: (List.replicate n false ++ [true]) =
          List.replicate (n + 2) false ++ [true] from by
          simp [List.replicate_succ, List.cons_append]]
      exact caStep_right_signal n

-- ─── Lemma D: after n+1 steps, signal reaches position 0 ────────────────────

-- caEvolve (n+1) (replicate (2*(n+1)) false ++ [true]) = [true]
theorem caEvolve_right_signal : ∀ (n : Nat),
    caEvolve (n + 1) (List.replicate (2 * (n + 1)) false ++ [true]) = [true]
  | 0 => rfl   -- caEvolve 1 [F, F, T] = caStep [F, F, T] = [T]  ✓
  | (n + 1) => by
      simp only [caEvolve]
      rw [show 2 * (n + 1 + 1) = (2 * (n + 1)) + 2 from by omega]
      rw [caStep_right_signal (2 * (n + 1))]
      exact caEvolve_right_signal n

-- ─── flipLast: flip the last element ────────────────────────────────────────

def flipLast : List Bool → List Bool
  | []      => []
  | [x]     => [!x]
  | x :: xs => x :: flipLast xs

-- Helper: flipLast distributes over 2+ element cons chains
theorem flipLast_cons (x y : Bool) (zs : List Bool) :
    flipLast (x :: y :: zs) = x :: flipLast (y :: zs) := rfl

-- ─── Lemma E: flipLast converts all-false to signal configuration ─────────

-- flipLast (replicate (n+1) false) = replicate n false ++ [true]
theorem flipLast_all_false : ∀ (n : Nat),
    flipLast (List.replicate (n + 1) false) = List.replicate n false ++ [true]
  | 0 => rfl
  | (n + 1) => by
      -- Expand replicate (n+2) false = F :: F :: replicate n false
      rw [show List.replicate (n + 1 + 1) false =
          false :: false :: List.replicate n false from by simp [List.replicate_succ]]
      -- flipLast (F :: F :: replicate n false) = F :: flipLast (F :: replicate n false)
      rw [flipLast_cons false false (List.replicate n false)]
      -- Fold back: F :: replicate n false = replicate (n+1) false
      rw [show false :: List.replicate n false = List.replicate (n + 1) false from by
          simp [List.replicate_succ]]
      -- Apply IH: flipLast (replicate (n+1) false) = replicate n false ++ [true]
      rw [flipLast_all_false n]
      -- F :: (replicate n false ++ [true]) = replicate (n+1) false ++ [true]
      simp [List.replicate_succ, List.cons_append]

-- ─── Main Theorem: right boundary cell is essential ─────────────────────────

-- For n ≥ 1, flipping the rightmost cell changes the output.
-- Witness: all-false initial configuration.
theorem prize3_right_boundary_essential (n : Nat) (hn : 1 ≤ n) :
    (caEvolve n (List.replicate (2 * n + 1) false)).headD false ≠
    (caEvolve n (flipLast (List.replicate (2 * n + 1) false))).headD false := by
  -- LHS: all-false evolves to [false], headD = false
  rw [caEvolve_all_false]
  -- flipLast (replicate (2n+1) false) = replicate (2n) false ++ [true]
  -- (apply flipLast_all_false at k = 2n, since 2n+1 = (2n)+1)
  rw [flipLast_all_false (2 * n)]
  -- Since n ≥ 1, write n = m + 1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- caEvolve (m+1) (replicate (2*(m+1)) false ++ [true]) = [true]
  rw [caEvolve_right_signal m]
  -- false ≠ true
  simp
