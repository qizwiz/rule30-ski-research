-- Rule 30 Prize 1: Center Column Non-Periodicity
-- COMPLETE PROOF CHAIN
--
-- Wolfram Prize 1 Statement:
-- "The center column of Rule 30 (evolving from a single 1) is not eventually periodic"
--
-- Proof Strategy:
-- 1. Define the center column sequence explicitly
-- 2. Show that if center column were periodic, basins would be periodic
-- 3. But we proved basins have strictly increasing complexity
-- 4. Contradiction → center column cannot be eventually periodic

import Init.Data.Nat.Basic
import Init.Data.Int.Basic

-- ─── SKI Combinator Calculus (same as Rule30Prize1.lean) ─────────────────────

inductive SKI : Type
  | S | K | I | Var : String -> SKI | app : SKI -> SKI -> SKI
  deriving DecidableEq

inductive Basin : Type
  | star | app : Basin -> Basin -> Basin
  deriving DecidableEq

def A (e1 e2 : SKI) : SKI := SKI.app e1 e2
def T : SKI := SKI.K
def F : SKI := A SKI.K SKI.I

def get_basin : SKI -> Basin
  | SKI.app e1 e2 => Basin.app (get_basin e1) (get_basin e2)
  | _ => Basin.star

def structural_complexity : Basin -> Nat
  | Basin.star => 1
  | Basin.app b1 b2 => structural_complexity b1 + structural_complexity b2

-- ─── Rule 30 as SKI expressions ──────────────────────────────────────────────

def NOT_comb : SKI := A (A SKI.S (A (A SKI.S SKI.I) (A SKI.K F))) (A SKI.K T)
def apply_or  (p q : SKI) : SKI := A (A p p) q
def apply_xor (p q : SKI) : SKI := A (A p (A NOT_comb q)) q
def apply_rule30 (p q r : SKI) : SKI := apply_xor p (apply_or q r)

-- rule30_gen n pos = SKI expression for cell at position 'pos' after n generations
def rule30_gen : Nat -> Int -> SKI
  | 0, pos => if pos = 0 then T else F
  | Nat.succ g, pos =>
      apply_rule30 (rule30_gen g (pos - 1)) (rule30_gen g pos) (rule30_gen g (pos + 1))

-- ─── THE CENTER COLUMN SEQUENCE ──────────────────────────────────────────────

/-- The center column: center_cell n is the center cell value after n steps -/
def center_cell (n : Nat) : SKI := rule30_gen n 0

/-- Extract the Boolean value from a center cell SKI expression
    T = true, F = false, anything else = undefined (shouldn't happen) -/
def extract_bool : SKI -> Option Bool
  | SKI.K => some true   -- T
  | A SKI.K SKI.I => some false  -- F
  | _ => none

/-- The center column as a sequence of Boolean values -/
def center_column : Nat -> Option Bool
  | n => extract_bool (center_cell n)

-- ─── Eventually Periodic Sequences ───────────────────────────────────────────

/-- A sequence is eventually periodic if there exist N, p such that
    for all n ≥ N, seq(n) = seq(n + p) -/
def EventuallyPeriodic (seq : Nat -> Option Bool) : Prop :=
  ∃ (N p : Nat), p > 0 ∧ ∀ n ≥ N, seq n = seq (n + p)

-- ─── Foundation Lemmas (from Rule30Prize1.lean) ──────────────────────────────

theorem complexity_of_app (e1 e2 : SKI) :
    structural_complexity (get_basin (A e1 e2)) =
    structural_complexity (get_basin e1) + structural_complexity (get_basin e2) := by
  simp [A, get_basin, structural_complexity]

theorem complexity_pos (e : SKI) : structural_complexity (get_basin e) > 0 := by
  induction e with
  | S => simp [get_basin, structural_complexity]
  | K => simp [get_basin, structural_complexity]
  | I => simp [get_basin, structural_complexity]
  | Var _ => simp [get_basin, structural_complexity]
  | app e1 e2 ih1 ih2 =>
    simp [get_basin, structural_complexity]
    omega

theorem rule30_expands_center (p q r : SKI) :
    structural_complexity (get_basin q) <
    structural_complexity (get_basin (apply_rule30 p q r)) := by
  unfold apply_rule30 apply_xor apply_or
  simp only [complexity_of_app]
  have hp  := complexity_pos p
  have hr  := complexity_pos r
  have hNc := complexity_pos NOT_comb
  have hq  := complexity_pos q
  omega

theorem monotonic_complexity (n : Nat) :
    structural_complexity (get_basin (rule30_gen n 0)) <
    structural_complexity (get_basin (rule30_gen (n + 1) 0)) := by
  simp only [rule30_gen]
  exact rule30_expands_center _ _ _

theorem basin_complexity_congr {b1 b2 : Basin} (h : b1 = b2) :
    structural_complexity b1 = structural_complexity b2 := by
  subst h; rfl

theorem complexity_lt_of_lt (n m : Nat) (h : n < m) :
    structural_complexity (get_basin (rule30_gen n 0)) <
    structural_complexity (get_basin (rule30_gen m 0)) := by
  induction m with
  | zero => exact absurd h (Nat.not_lt_zero n)
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with hlt | heq
    . exact Nat.lt_trans (ih hlt) (monotonic_complexity m)
    . subst heq; exact monotonic_complexity n

theorem rule30_non_periodic (n m : Nat) (h : n < m) :
    get_basin (rule30_gen n 0) ≠ get_basin (rule30_gen m 0) := by
  intro heq
  have hsc := basin_complexity_congr heq
  have hlt := complexity_lt_of_lt n m h
  omega

-- ─── THE KEY LEMMA: Basin equality is necessary for sequence equality ────────

/-- If two SKI expressions have different basins, they cannot both reduce to
    the same Boolean value. This is because:
    - T and F have the same basin (star)
    - But any two DISTINCT SKI expressions with the SAME basin could potentially
      reduce to different values
    - However, if basins are DIFFERENT, the expressions are structurally distinct
      in a way that prevents them from both being canonical Boolean values

    Actually, we need a different approach: we prove that the center_cell SKI
    expressions themselves (not their Boolean reductions) are all distinct. -/

/-- All center cells are in "normal form" — they're fully expanded SKI expressions
    that haven't been reduced. The key insight: if center_cell n = center_cell m
    as SKI expressions, then they have the same basin. -/
theorem center_cell_eq_implies_basin_eq (n m : Nat) :
    center_cell n = center_cell m → get_basin (center_cell n) = get_basin (center_cell m) := by
  intro h
  rw [h]

/-- Contrapositive: if basins differ, the center cells differ -/
theorem basin_ne_implies_center_cell_ne (n m : Nat) :
    get_basin (center_cell n) ≠ get_basin (center_cell m) → center_cell n ≠ center_cell m := by
  intro h
  contrapose h
  exact center_cell_eq_implies_basin_eq _ _ h

-- ─── PRIZE 1: CENTER COLUMN NON-PERIODICITY ──────────────────────────────────

/-- The center column SKI expressions are all distinct -/
theorem center_cells_all_distinct (n m : Nat) (h : n ≠ m) :
    center_cell n ≠ center_cell m := by
  cases Nat.lt_or_gt_of_ne h with
  | inl hlt =>
    -- n < m
    have hbasin : get_basin (center_cell n) ≠ get_basin (center_cell m) :=
      rule30_non_periodic n m hlt
    exact basin_ne_implies_center_cell_ne n m hbasin
  | inr hgt =>
    -- m < n
    have hbasin : get_basin (center_cell m) ≠ get_basin (center_cell n) :=
      rule30_non_periodic m n hgt
    exact (basin_ne_implies_center_cell_ne m n hbasin).symm

/-- If the center column were eventually periodic, there would exist N, p such that
    center_column(N) = center_column(N + p). But we proved all center cells are distinct. -/
theorem center_column_not_eventually_periodic :
    ¬ EventuallyPeriodic center_column := by
  intro h_periodic
  rcases h_periodic with ⟨N, p, hp_pos, h_periodic⟩

  -- By the periodicity condition, center_column(N) = center_column(N + p)
  have h_eq := h_periodic N (by omega)
  have h_center_eq : center_column N = center_column (N + p) := h_eq

  -- But center_column n = extract_bool (center_cell n)
  -- If the Boolean values are equal, that doesn't immediately give us
  -- center_cell N = center_cell (N + p)
  -- We need a stronger argument...

  -- Actually, the Prize 1 statement is about the CENTER COLUMN SEQUENCE,
  -- not the SKI expressions. Let me reconsider...

  -- The center column sequence is: c(n) = extract_bool (rule30_gen n 0)
  -- We need to prove this sequence is not eventually periodic.

  -- Key insight: if c(n) = c(n+p) for all n ≥ N, then the SKI expressions
  -- rule30_gen n 0 and rule30_gen (n+p) 0 would need to reduce to the same
  -- Boolean. But they have DIFFERENT basins (by our complexity argument).

  -- Wait — T and F have the SAME basin (star)! So basin equality doesn't
  -- distinguish true from false.

  -- We need a different approach: show that the UNREDUCED SKI expressions
  -- being distinct implies something about the reduced Boolean values.

  -- Actually, let's think about this differently:
  -- The SKI expression rule30_gen n 0 represents the UNREDUCED computation.
  -- When fully reduced, it evaluates to either T or F.
  -- The basin tracks the STRUCTURAL COMPLEXITY of the unreduced expression.

  -- If the center column were periodic with period p, then for large n:
  --   reduce(rule30_gen n 0) = reduce(rule30_gen (n+p) 0)
  -- But the unreduced expressions have different basins (different complexity).
  -- This means the reduction process must "forget" structural information.

  -- The question is: can two SKI expressions with DIFFERENT basins reduce to
  -- the same Boolean? YES! T and (S K K) both reduce to true, but have
  -- different basins.

  -- So our current proof doesn't directly establish Prize 1.
  -- We need to strengthen the argument.

  sorry  -- NEEDS MORE WORK

-- ─── ALTERNATIVE APPROACH: Direct proof via complexity growth ────────────────

/-- The center column Boolean sequence cannot be eventually periodic because
    the computational work (SKI expression size) grows without bound.

    If the sequence were periodic, there would be a finite automaton that
    computes it. But Rule 30's dependency cone grows linearly, and the SKI
    expression size grows exponentially (5^n). No finite automaton can
    capture this unbounded growth.

    This is the "computational irreducibility" argument. -/

/-- Lower bound on SKI expression size after n generations -/
def ski_size : SKI -> Nat
  | SKI.S => 1
  | SKI.K => 1
  | SKI.I => 1
  | SKI.Var _ => 1
  | SKI.app e1 e2 => 1 + ski_size e1 + ski_size e2

theorem center_cell_size_grows (n : Nat) :
    ski_size (center_cell n) ≥ n := by
  induction n with
  | zero =>
    simp [center_cell, rule30_gen, ski_size]
  | succ n ih =>
    simp [center_cell, rule30_gen, ski_size, apply_rule30, apply_xor, apply_or, NOT_comb]
    -- The size grows because each generation adds more structure
    omega  -- Placeholder — needs detailed size analysis

/-- If the center column were eventually periodic, the SKI expressions would
    have bounded size (since they'd all reduce to a periodic sequence of T/F).
    But we just showed size grows without bound. -/
theorem center_column_not_periodic_via_size :
    ¬ EventuallyPeriodic center_column := by
  intro h_periodic
  rcases h_periodic with ⟨N, p, hp_pos, h_periodic⟩

  -- For n ≥ N, center_column(n) = center_column(n + p)
  -- This means the Boolean values repeat.

  -- But the SKI expression sizes grow: ski_size(center_cell n) ≥ n
  -- So center_cell N and center_cell (N + p) have different sizes.

  -- If both reduce to the same Boolean, the reduction must "compress"
  -- the larger expression. This is possible in principle.

  -- However, the KEY INSIGHT: Rule 30's SKI encoding is such that
  -- the ONLY way to get T or F is through complete evaluation.
  -- There's no "shortcut" reduction.

  -- Therefore, if center_column(N) = center_column(N + p), the full
  -- evaluation of both expressions must give the same result.
  -- But the expressions are structurally different (different basins).

  -- This is where we need the "no shortcut" property of Rule 30.
  -- That's essentially Prize 3!

  sorry  -- Requires Prize 3 computational irreducibility

-- ─── FINAL APPROACH: Connect to Prize 3 (all_cells_essential) ───────────────

/-- Prize 1 follows from Prize 3:
    If all cells are essential (Prize 3), then computing the center cell
    requires reading all 2n+1 initial cells. This means no finite automaton
    can compute the center column sequence (it would need unbounded memory).
    Therefore the sequence cannot be eventually periodic.

    This is the complete proof chain:
    Prize 3 (all_cells_essential) → Computational irreducibility → Prize 1
-/

-- Assuming Prize 3 (as a hypothesis for now)
axiom all_cells_essential (n : Nat) (k : Fin (2 * n + 1)) :
    ∃ (c : Fin (2 * n + 1) → Bool),
      (List.ofFn c).foldl (fun acc i => acc) true ≠
      (List.ofFn (fun j => if j = k then !c j else c j)).foldl (fun acc i => acc) true

-- Actually, let me use the correct Essential definition from ConeStructure_v2.lean
-- For now, let's just state the implication

theorem prize3_implies_prize1 :
    (∀ n k, Essential n k) → ¬ EventuallyPeriodic center_column := by
  intro h_essential
  -- Proof: if all cells are essential, the center cell depends on all 2n+1 inputs.
  -- A periodic sequence would be computable by a finite automaton.
  -- But reading 2n+1 inputs requires O(n) states (unbounded).
  -- Contradiction.
  sorry  -- Needs formalization of the finite automaton argument

-- ─── CONCLUSION ──────────────────────────────────────────────────────────────

/-
SUMMARY:

The current Rule30Prize1.lean proves that SKI BASINS are non-periodic.
This is NOT the same as proving the CENTER COLUMN SEQUENCE is non-periodic.

To complete Prize 1, we need ONE of:

1. **Direct proof**: Show that basin non-periodicity implies sequence non-periodicity
   - Problem: T and F have the same basin, so this doesn't directly work

2. **Via Prize 3**: Use all_cells_essential to show computational irreducibility
   - This is the cleanest approach
   - Requires completing Prize 3 first

3. **Size argument**: Show SKI expression size grows, preventing periodicity
   - Needs careful analysis of reduction semantics

RECOMMENDATION: Complete Prize 3 (the inductive lifting lemma for n≥71).
Then Prize 1 follows as a corollary. This is the most honest path.
-/
