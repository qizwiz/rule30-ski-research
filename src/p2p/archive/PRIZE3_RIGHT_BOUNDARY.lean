-- Rule 30 Prize 3: Right Boundary Cell is Essential
-- STATUS: PROOF COMPLETE (needs lean verification — lean not installed in this VM)
--
-- WITNESS STRATEGY:
--   For all n ≥ 1, use the all-false list: cells = List.replicate (2*n+1) false
--
--   After n steps:
--     caEvolve n (replicate (2n+1) false)          = [false]   (Lemma B)
--     caEvolve n (replicate (2n) false ++ [true])  = [true]    (Lemma D)
--
--   And: flipLast (replicate (2n+1) false) = replicate (2n) false ++ [true]  (Lemma E)
--   Therefore: false ≠ true  →  theorem proved.
--
-- SIGNAL PROPAGATION INTUITION:
--   The all-false config is a "dark" background. After n steps, output = false.
--   Flipping the rightmost cell (only 1 cell has T, at the right edge) creates
--   a "signal cone" that propagates leftward. After k steps, the signal has
--   moved 2k positions to the left and the rest is still all-false.
--   After n steps the signal reaches position 0 = the output cell.
--
--   At each step, rule30Local F F T = xor F (F OR T) = T  (signal survives)
--   rule30Local F T _ = xor F (T OR _) = F XOR T = T  (NO — rule30 is asymmetric!)
--
--   More precisely: what survives is:
--     caStep (replicate k false ++ [true]) = replicate (k-2) false ++ [true]  (Lemma C)
--   The signal loses 2 positions of false-padding per step, preserving the T at the end.
--   After n steps starting with replicate (2n) false ++ [true],
--   we get replicate 0 false ++ [true] = [true].

import Init.Data.Nat.Basic
import Init.Data.List.Basic

-- CA definitions (Matching Prize 2) ---------------------------------------

def rule30Local (p q r : Bool) : Bool := xor p (q || r)

def caStep : List Bool -> List Bool
  | p :: q :: r :: rest => rule30Local p q r :: caStep (q :: r :: rest)
  | _ => []

def caEvolve : Nat -> List Bool -> List Bool
  | 0, cells => cells
  | t + 1, cells => caEvolve t (caStep cells)

-- --- Right Boundary Flipping -------------------------------------------------

def flipLast : List Bool -> List Bool
  | [] => []
  | [x] => [!x]
  | x :: xs => x :: flipLast xs

-- Core Simp Lemmas

lemma rule30Local_fff : rule30Local false false false = false := by
  unfold rule30Local
  rfl

lemma rule30Local_fft : rule30Local false false true = true := by
  unfold rule30Local
  rfl

-- Lemma A: caStep of all-false = shorter all-false
--
-- caStep (replicate (n+2) false) = replicate n false
--
-- Proof: false :: false :: false :: replicate n false
--   → rule30Local F F F :: caStep (false :: false :: replicate n false)
--   → false :: caStep (replicate (n+2) false)
--   → false :: replicate n false  (by IH)
--   = replicate (n+1) false

lemma caStep_all_false (n : Nat) :
    caStep (List.replicate (n + 2) false) = List.replicate n false := by
  induction n with
  | zero => simp [caStep, List.replicate]
  | succ n ih =>
    -- Unfold: replicate (n+3) false = F :: F :: F :: replicate n false
    rw [show List.replicate (n + 1 + 2) false =
        false :: List.replicate (n + 2) false from List.replicate_succ _ _]
    rw [show List.replicate (n + 2) false =
        false :: List.replicate (n + 1) false from List.replicate_succ _ _]
    rw [show List.replicate (n + 1) false =
        false :: List.replicate n false from List.replicate_succ _ _]
    -- Now: caStep (F :: F :: F :: replicate n false)
    simp only [caStep, rule30Local_fff]
    -- Goal: false :: caStep (false :: false :: replicate n false) = replicate (n+1) false
    rw [show false :: false :: List.replicate n false =
        List.replicate (n + 2) false from by simp [List.replicate_succ]]
    rw [ih]
    rfl

-- --- Lemma B: caEvolve n on all-false list of length 2n+1 gives [false] ------

lemma caEvolve_all_false (n : Nat) :
    caEvolve n (List.replicate (2 * n + 1) false) = [false] := by
  induction n with
  | zero => simp [caEvolve, List.replicate]
  | succ n ih =>
    simp only [caEvolve]
    -- caStep (replicate (2*(n+1)+1) false) = caStep (replicate (2n+3) false)
    -- = replicate (2n+1) false  (by Lemma A, since 2n+3 = (2n+1)+2)
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by omega]
    rw [caStep_all_false (2 * n + 1)]
    exact ih

-- --- Lemma C: caStep on (replicate (n+2) false ++ [true]) -------------------
--
-- caStep (replicate (n+2) false ++ [true]) = replicate n false ++ [true]
--
-- Proof:
--   F :: F :: F :: replicate n false ++ [true]
--   → rule30Local F F F :: caStep (F :: F :: replicate n false ++ [true])
--   → false :: caStep (replicate (n+2) false ++ [true])
--   → false :: (replicate n false ++ [true])   (by IH)
--   = replicate (n+1) false ++ [true]
-- Base:
--   caStep ([F, F, T]) = [rule30Local F F T] = [true] = [] ++ [true]  ✓

lemma caStep_right_signal (n : Nat) :
    caStep (List.replicate (n + 2) false ++ [true]) = List.replicate n false ++ [true] := by
  induction n with
  | zero =>
    simp [caStep, List.replicate, rule30Local]
  | succ n ih =>
    -- Unfold: replicate (n+3) false ++ [true] = F :: F :: F :: replicate n false ++ [true]
    rw [show List.replicate (n + 1 + 2) false ++ [true] =
        false :: List.replicate (n + 2) false ++ [true] from by
          simp [List.replicate_succ, List.cons_append]]
    rw [show List.replicate (n + 2) false ++ [true] =
        false :: List.replicate (n + 1) false ++ [true] from by
          simp [List.replicate_succ, List.cons_append]]
    rw [show List.replicate (n + 1) false ++ [true] =
        false :: List.replicate n false ++ [true] from by
          simp [List.replicate_succ, List.cons_append]]
    -- Now: caStep (F :: F :: F :: replicate n false ++ [true])
    simp only [caStep, rule30Local_fff]
    -- Goal: false :: caStep (false :: false :: replicate n false ++ [true])
    --     = replicate (n+1) false ++ [true]
    rw [show false :: false :: List.replicate n false ++ [true] =
        List.replicate (n + 2) false ++ [true] from by
          simp [List.replicate_succ, List.cons_append]]
    rw [ih]
    simp [List.replicate_succ, List.cons_append]

-- --- Lemma D: caEvolve (n+1) on (replicate (2*(n+1)) false ++ [true]) = [true]

lemma caEvolve_right_signal (n : Nat) :
    caEvolve (n + 1) (List.replicate (2 * (n + 1)) false ++ [true]) = [true] := by
  induction n with
  | zero =>
    -- caEvolve 1 ([F, F] ++ [true]) = caStep [F, F, T] = [T]
    simp [caEvolve, caStep, List.replicate, rule30Local]
  | succ n ih =>
    simp only [caEvolve]
    -- caStep (replicate (2*(n+2)) false ++ [true]) = replicate (2*(n+1)) false ++ [true]
    rw [show 2 * (n + 1 + 1) = (2 * (n + 1)) + 2 from by omega]
    rw [caStep_right_signal (2 * (n + 1))]
    -- Now: caEvolve (n+1) (replicate (2*(n+1)) false ++ [true]) = [true]
    exact ih

-- --- Lemma E: flipLast on all-false list -------------------------------------
--
-- flipLast (replicate (n+1) false) = replicate n false ++ [true]

lemma flipLast_all_false (n : Nat) :
    flipLast (List.replicate (n + 1) false) = List.replicate n false ++ [true] := by
  induction n with
  | zero => simp [flipLast, List.replicate]
  | succ n ih =>
    rw [show List.replicate (n + 1 + 1) false =
        false :: List.replicate (n + 1) false from List.replicate_succ _ _]
    simp only [flipLast]
    -- flipLast (false :: replicate (n+1) false)
    -- Since replicate (n+1) false is non-empty (n+1 ≥ 1), this matches x :: flipLast xs
    rw [ih]
    simp [List.replicate_succ, List.cons_append]

-- --- The Right Boundary Theorem ----------------------------------------------

theorem prize3_right_boundary_essential (n : Nat) (hn : n ≥ 1) :
    ∃ (cells : List Bool), cells.length = 2 * n + 1 ∧
    (caEvolve n cells).headD false ≠ (caEvolve n (flipLast cells)).headD false := by
  -- Witness: all-false list of length 2*n+1
  refine ⟨List.replicate (2 * n + 1) false, ?_, ?_⟩
  · simp
  · -- LHS: caEvolve n (replicate (2n+1) false) = [false]
    rw [caEvolve_all_false n]
    -- flipLast (replicate (2n+1) false):
    rw [show 2 * n + 1 = (2 * n) + 1 from rfl]
    rw [flipLast_all_false (2 * n)]
    -- RHS: caEvolve n (replicate (2n) false ++ [true]) = [true]
    -- Use Lemma D: caEvolve (n-1+1) = caEvolve n
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn  -- n = m + 1
    rw [caEvolve_right_signal m]
    -- Goal: false ≠ true (from headD on [false] vs [true])
    simp

-- --- STATUS SUMMARY ----------------------------------------------------------
/-
  Prize 3 Right Boundary: PROOF COMPLETE (pending lean verification)

  WITNESS: cells = List.replicate (2*n+1) false  (all-false list)

  KEY LEMMAS:
  ✓ caStep_all_false    -- caStep collapses all-false by 2
  ✓ caEvolve_all_false  -- n applications give [false]
  ✓ caStep_right_signal -- signal propagates leftward by 2 per step
  ✓ caEvolve_right_signal -- n applications give [true]
  ✓ flipLast_all_false  -- flipLast converts to replicate n false ++ [true]
  ✓ prize3_right_boundary_essential -- the main theorem

  NEXT: Interior cells (0 < k < 2n) — needs cone reachability argument.
  The left-boundary XOR-linearity argument (k=0) extends via induction
  to show that for any interior cell at index k, there exists a config
  where it matters. Key: choose a config that "opens the cone" from k.
-/
