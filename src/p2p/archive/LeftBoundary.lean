/-
LeftBoundary.lean
=================
Proof that the left-boundary column L₇ in Rule 30 from a single spike at
position 0 is identically zero for all time t ≥ 0.

## Mathematical content

Left-boundary column: L_j(t) = R30(j − t, t).
Recurrence: L_j(t+1) = L_{j−2}(t) XOR (L_{j−1}(t) OR L_j(t)), boundary = 0.
Initial: L_0(0) = 1, L_j(0) = 0 (j ≥ 1).

8-step cascade:
  L₀ = 1 (const) → L₁ = 1 (forced) → L₂ = 0 (forced) → L₃ period-2
  → L₄ = 1 (absorbing) → L₅ = L₃ → L₆ = L₅ → L₇ = L₅ XOR L₆ = 0

The orbit reaches a period-2 cycle at t = 2:
  stateEven = (1, 1, 0, 0, 1, 0, 0, 0)   — even t ≥ 2
  stateOdd  = (1, 1, 0, 1, 1, 1, 1, 0)   — odd  t ≥ 3
Both have l7 = false.
-/

import P2p.Prize3_Complete
import P2p.CausalConeLemmas

namespace P2p

/-! ## State and evolution -/

/-- The 8 left-boundary columns L₀..L₇ at a given time step. -/
structure LBState where
  l0 : Bool
  l1 : Bool
  l2 : Bool
  l3 : Bool
  l4 : Bool
  l5 : Bool
  l6 : Bool
  l7 : Bool
  deriving DecidableEq, Repr

/-- Initial state: spike at position 0 (only L₀ = 1). -/
def lbInit : LBState :=
  { l0 := true,  l1 := false, l2 := false, l3 := false,
    l4 := false, l5 := false, l6 := false, l7 := false }

/-- One Rule 30 step on the left-boundary columns.
    Rule 30: next[i] = cell[i−1] XOR (cell[i] OR cell[i+1]).
    L_j(t+1) = L_{j−2}(t) XOR (L_{j−1}(t) OR L_j(t)), boundary L_{−1}=L_{−2}=0. -/
def lbStep (s : LBState) : LBState :=
  { l0 := s.l0,
    l1 := s.l0 || s.l1,
    l2 := s.l0 ^^ (s.l1 || s.l2),
    l3 := s.l1 ^^ (s.l2 || s.l3),
    l4 := s.l2 ^^ (s.l3 || s.l4),
    l5 := s.l3 ^^ (s.l4 || s.l5),
    l6 := s.l4 ^^ (s.l5 || s.l6),
    l7 := s.l5 ^^ (s.l6 || s.l7) }

/-- Left-boundary state after t steps from a single spike at position 0. -/
def lbEvol : Nat → LBState
  | 0     => lbInit
  | t + 1 => lbStep (lbEvol t)

/-- `lbEvol` step equation (for `rw`). -/
@[simp]
theorem lbEvol_succ (t : Nat) : lbEvol (t + 1) = lbStep (lbEvol t) := rfl

/-! ## Period-2 orbit -/

/-- The even-phase periodic state (t even ≥ 2). -/
def stateEven : LBState :=
  { l0 := true, l1 := true,  l2 := false, l3 := false,
    l4 := true, l5 := false, l6 := false, l7 := false }

/-- The odd-phase periodic state (t odd ≥ 3). -/
def stateOdd : LBState :=
  { l0 := true, l1 := true, l2 := false, l3 := true,
    l4 := true, l5 := true, l6 := true,  l7 := false }

/-- stateEven → stateOdd under one step. -/
theorem lbStep_stateEven : lbStep stateEven = stateOdd := by decide

/-- stateOdd → stateEven under one step. -/
theorem lbStep_stateOdd : lbStep stateOdd = stateEven := by decide

/-- The orbit enters the cycle at t = 2. -/
theorem lbEvol_2 : lbEvol 2 = stateEven := by native_decide

/-- The period-2 reduction: lbEvol(k + 4) = lbEvol(k + 2). -/
theorem lbEvol_period2 (k : Nat) : lbEvol (k + 4) = lbEvol (k + 2) := by
  induction k with
  | zero =>
    -- lbEvol 4 = lbEvol 2 (both equal stateEven)
    native_decide
  | succ n ih =>
    -- lbEvol (n + 5) = lbStep (lbEvol (n + 4))
    --                = lbStep (lbEvol (n + 2))    [by ih]
    --                = lbEvol (n + 3)
    have h5 : n + 1 + 4 = (n + 4) + 1 := by omega
    have h3 : n + 1 + 2 = (n + 2) + 1 := by omega
    rw [h5, lbEvol_succ, ih, ← lbEvol_succ, ← h3]

/-! ## Main theorem: L₇ = 0 for all t -/

/-- l7 = false in both periodic states. -/
theorem stateEven_l7 : stateEven.l7 = false := rfl
theorem stateOdd_l7  : stateOdd.l7  = false := rfl

/-- The left-boundary column L₇ is identically 0 for all t ≥ 0.
    Proof: by strong induction, reducing t ≥ 4 to t − 2 via the period-2 orbit. -/
theorem lbEvol_l7_zero (t : Nat) : (lbEvol t).l7 = false := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    match t with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => decide
    | t + 4 =>
      -- Reduce by period-2: lbEvol(t+4) = lbEvol(t+2)
      rw [lbEvol_period2 t]
      exact ih (t + 2) (by omega)

/-! ## Connection to the original f_center_prev_zero

`f_center_prev_zero` (LinearityCorridor.lean) uses the finite-tape caEvolve model:
  spike at position 2t in tape of width 4t+15, evolved t steps → position 7 = false.

The connection from `lbEvol_l7_zero` to caEvolve requires a causal-cone restriction
argument: position 7 at time t only depends on positions 7..7+2t, which are all
inside a large-enough tape.  This is deferred as a sorry pending the cone-restriction
formalization.
-/

/-- The finite-tape caEvolve at position 7 equals lbEvol's l7.
    **Proof deferred**: causal cone restriction argument needed. -/
theorem lbEvol_eq_caEvolve_pos7 (t : Nat) :
    (lbEvol t).l7 =
    (caEvolve t (spikeAtList (2 * t) (4 * t + 15))).getD 7 false := by
  sorry

/-- Anti-diagonal k=7: position 7 at time t is always false (f_center_prev_zero, all t).
    The mathematical content is fully proved via lbEvol_l7_zero.
    The Lean-tape-model bridge is the remaining sorry. -/
theorem f_center_prev_zero_all (t : Nat) :
    (caEvolve t (spikeAtList (2 * t) (4 * t + 15))).getD 7 false = false := by
  rw [← lbEvol_eq_caEvolve_pos7]
  exact lbEvol_l7_zero t

end P2p
