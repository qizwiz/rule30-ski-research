import Init.Data.Nat.Basic

/-
  Prize #3 formal track starter.
  This file contains minimal model primitives plus a first
  dependency-cone arithmetic lemma that we can build on.
-/

namespace Prize3

structure Model where
  work : Nat -> Nat

-- Width of the dependency cone at generation n
def coneWidth (n : Nat) : Nat := 2 * n + 1

-- Conservative proxy for information that must be resolved at generation n.
def requiredCells (n : Nat) : Nat := coneWidth n

-- First foundational fact: width is at least n+1.
-- This is intentionally simple, but nontrivial and reusable.
theorem coneWidth_ge_n_plus_one (n : Nat) : n + 1 ≤ coneWidth n := by
  unfold coneWidth
  have h0 : n ≤ n + n := Nat.le_add_right n n
  have h : n ≤ 2 * n := by
    rw [Nat.two_mul]
    exact h0
  simpa [Nat.succ_eq_add_one] using Nat.succ_le_succ h

-- Width is at least n (weaker form often useful for cost-transfer side conditions).
theorem coneWidth_ge_n (n : Nat) : n ≤ coneWidth n := by
  exact Nat.le_trans (Nat.le_succ n) (coneWidth_ge_n_plus_one n)

-- Width increase per generation is exactly 2.
theorem coneWidth_succ (n : Nat) : coneWidth (n + 1) = coneWidth n + 2 := by
  unfold coneWidth
  simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

-- Width is monotone in n.
theorem coneWidth_monotone (n : Nat) : coneWidth n ≤ coneWidth (n + 1) := by
  rw [coneWidth_succ]
  exact Nat.le_add_right (coneWidth n) 2

-- Width is always positive.
theorem coneWidth_pos (n : Nat) : 0 < coneWidth n := by
  unfold coneWidth
  exact Nat.succ_pos (2 * n)

-- Required-data proxy agrees definitionally with cone width.
theorem requiredCells_eq_coneWidth (n : Nat) : requiredCells n = coneWidth n := by
  rfl

-- Required-data proxy is at least linear in n.
theorem requiredCells_ge_n_plus_one (n : Nat) : n + 1 ≤ requiredCells n := by
  simpa [requiredCells] using coneWidth_ge_n_plus_one n

-- Required-data proxy is at least n.
theorem requiredCells_ge_n (n : Nat) : n ≤ requiredCells n := by
  simpa [requiredCells] using coneWidth_ge_n n

-- Required-data proxy is monotone in n.
theorem requiredCells_monotone (n : Nat) : requiredCells n ≤ requiredCells (n + 1) := by
  simpa [requiredCells] using coneWidth_monotone n

-- Required-data proxy grows by exactly 2 each generation.
theorem requiredCells_succ (n : Nat) : requiredCells (n + 1) = requiredCells n + 2 := by
  simpa [requiredCells] using coneWidth_succ n

-- Required-data proxy is always positive.
theorem requiredCells_pos (n : Nat) : 0 < requiredCells n := by
  simpa [requiredCells] using coneWidth_pos n

/-!
  Phase 3 bridge scaffold (claim-hygienic):
  These lemmas do not prove the Prize3 lower bound.
  They formalize a minimal observation/no-skip interface so the final
  exactness-to-work bridge can be discharged with explicit hypotheses.
-/

section BridgeScaffold

variable {State : Type}
variable (cell : State -> Nat -> Bool)

structure Algorithm (State : Type) where
  run : Nat -> State -> Bool
  observes : Nat -> Nat -> Prop

def agreesOnObserved (A : Algorithm State) (n : Nat) (s1 s2 : State) : Prop :=
  forall i, A.observes n i -> cell s1 i = cell s2 i

def exactFor (A : Algorithm State) (target : Nat -> State -> Bool) : Prop :=
  forall n s, A.run n s = target n s

def requiredAt (n i : Nat) : Prop :=
  i < requiredCells n

theorem requiredAt_iff (n i : Nat) : requiredAt n i ↔ i < requiredCells n := by
  rfl

-- If an algorithm only depends on observed units, and exactness can be broken
-- whenever a required unit is left unobserved, that required unit must be observed.
theorem must_observe_required
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness :
      forall n i,
        requiredAt n i ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2) :
    forall n i, requiredAt n i -> A.observes n i := by
  intro n i hReq
  by_cases hObs : A.observes n i
  · exact hObs
  · rcases h_witness n i hReq hObs with ⟨s1, s2, hAgree, hTargetNe⟩
    have hRunEq : A.run n s1 = A.run n s2 := h_obs_det n s1 s2 hAgree
    have hTargetEq : target n s1 = target n s2 := by
      rw [← h_exact n s1, ← h_exact n s2]
      exact hRunEq
    exact False.elim (hTargetNe hTargetEq)

-- Required index 0 is always present, useful as a base sanity check.
theorem requiredAt_zero (n : Nat) : requiredAt n 0 := by
  unfold requiredAt requiredCells coneWidth
  have hpos : 0 < 2 * n + 1 := Nat.succ_pos (2 * n)
  exact hpos

-- Any index up to n lies in the required interval [0, requiredCells n).
theorem requiredAt_of_le_n (n i : Nat) (h : i ≤ n) : requiredAt n i := by
  unfold requiredAt
  have hi_succ : i < n + 1 := Nat.lt_succ_of_le h
  exact Nat.lt_of_lt_of_le hi_succ (requiredCells_ge_n_plus_one n)

-- Any index strictly below n+1 is required at generation n.
theorem requiredAt_of_lt_n_plus_one (n i : Nat) (h : i < n + 1) : requiredAt n i := by
  unfold requiredAt
  exact Nat.lt_of_lt_of_le h (requiredCells_ge_n_plus_one n)

-- In particular, index n is always required.
theorem requiredAt_self (n : Nat) : requiredAt n n := by
  exact requiredAt_of_le_n n n (Nat.le_refl n)

-- Required indices remain required when advancing one generation.
theorem requiredAt_monotone_gen (n i : Nat) : requiredAt n i -> requiredAt (n + 1) i := by
  intro hReq
  unfold requiredAt at *
  exact Nat.lt_of_lt_of_le hReq (requiredCells_monotone n)

-- Minimal exactness-to-work bridge corollary at the base index.
theorem observes_zero_of_exact
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness :
      forall n i,
        requiredAt n i ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2) :
    forall n, A.observes n 0 := by
  intro n
  exact must_observe_required (cell := cell) A target h_obs_det h_exact h_witness n 0 (requiredAt_zero n)

-- General exactness-to-observation bridge on all required indices.
theorem observes_required_of_exact
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness :
      forall n i,
        requiredAt n i ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2) :
    forall n i, requiredAt n i -> A.observes n i := by
  exact must_observe_required (cell := cell) A target h_obs_det h_exact h_witness

-- Under the same hypotheses, exactness forces observation of every index i <= n.
theorem observes_prefix_of_exact
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness :
      forall n i,
        requiredAt n i ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2) :
    forall n i, i ≤ n -> A.observes n i := by
  intro n i hi
  exact must_observe_required (cell := cell) A target h_obs_det h_exact h_witness n i
    (requiredAt_of_le_n n i hi)

-- Exactness implies at least one required index is observed at each generation.
theorem exists_observed_required_of_exact
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness :
      forall n i,
        requiredAt n i ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2) :
    forall n, exists i, requiredAt n i /\ A.observes n i := by
  intro n
  refine ⟨0, requiredAt_zero n, ?_⟩
  exact observes_zero_of_exact (cell := cell) A target h_obs_det h_exact h_witness n

end BridgeScaffold

/-!
  Phase 4 pre-bridge (conditional cost transfer):
  These are purely conditional inequalities. They do not claim a Prize3
  lower bound unless a concrete accounting hypothesis is instantiated.
-/

section CostTransferScaffold

-- If work dominates requiredCells pointwise, linear lower bounds follow immediately.
theorem work_ge_requiredCells_implies_linear_plus_one
    (work : Nat -> Nat)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, n + 1 <= work n := by
  intro n
  exact Nat.le_trans (requiredCells_ge_n_plus_one n) (h_account n)

-- A weaker linear form (constant c = 1) from the same accounting hypothesis.
theorem work_ge_requiredCells_implies_linear
    (work : Nat -> Nat)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, n <= work n := by
  intro n
  exact Nat.le_trans (requiredCells_ge_n n) (h_account n)

-- Required indices are bounded by the cone interval's right endpoint proxy.
theorem requiredAt_le_two_mul (n i : Nat) (hReq : requiredAt n i) : i <= 2 * n := by
  unfold requiredAt requiredCells coneWidth at hReq
  have hSucc : i < Nat.succ (2 * n) := by
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using hReq
  exact Nat.lt_succ_iff.mp hSucc

end CostTransferScaffold

end Prize3
