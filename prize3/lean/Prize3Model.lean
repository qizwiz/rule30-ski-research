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

-- A required index is exactly an index in the interval [0, 2n].
theorem requiredAt_iff_le_two_mul (n i : Nat) : requiredAt n i ↔ i <= 2 * n := by
  unfold requiredAt requiredCells coneWidth
  have h : i < Nat.succ (2 * n) ↔ i <= 2 * n := Nat.lt_succ_iff
  simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

-- Any index up to the cone endpoint is required.
theorem requiredAt_of_le_two_mul (n i : Nat) (h : i <= 2 * n) : requiredAt n i := by
  exact (requiredAt_iff_le_two_mul n i).2 h

-- Next-generation required interval is exactly [0, 2n + 2].
theorem requiredAt_next_gen_iff_le_two_mul_add_two (n i : Nat) :
    requiredAt (n + 1) i ↔ i <= 2 * n + 2 := by
  calc
    requiredAt (n + 1) i ↔ i <= 2 * (n + 1) := requiredAt_iff_le_two_mul (n + 1) i
    _ ↔ i <= 2 * n + 2 := by
      simp [Nat.mul_add, Nat.add_comm]

-- Any index up to 2n+1 is required at generation n+1.
theorem requiredAt_of_le_two_mul_add_one_next_gen (n i : Nat) (h : i <= 2 * n + 1) :
    requiredAt (n + 1) i := by
  have h' : i <= 2 * n + 2 := Nat.le_trans h (Nat.le_succ (2 * n + 1))
  exact (requiredAt_next_gen_iff_le_two_mul_add_two n i).2 h'

-- Any index up to 2n+2 is required at generation n+1.
theorem requiredAt_of_le_two_mul_add_two_next_gen (n i : Nat) (h : i <= 2 * n + 2) :
    requiredAt (n + 1) i := by
  exact (requiredAt_next_gen_iff_le_two_mul_add_two n i).2 h

-- Right endpoint of the next-generation dependency interval is required.
theorem requiredAt_two_mul_add_two_next_gen (n : Nat) : requiredAt (n + 1) (2 * n + 2) := by
  exact requiredAt_of_le_two_mul_add_two_next_gen n (2 * n + 2) (Nat.le_refl (2 * n + 2))

-- Any index strictly beyond the next-generation endpoint is not required.
theorem not_requiredAt_of_two_mul_add_two_lt_next_gen (n i : Nat) (h : 2 * n + 2 < i) :
    ¬ requiredAt (n + 1) i := by
  intro hReq
  have hLe : i <= 2 * n + 2 := (requiredAt_next_gen_iff_le_two_mul_add_two n i).1 hReq
  exact Nat.not_lt_of_ge hLe h

-- First index after the n+1 dependency interval is not required.
theorem not_requiredAt_two_mul_add_three_next_gen (n : Nat) :
    ¬ requiredAt (n + 1) (2 * n + 3) := by
  exact not_requiredAt_of_two_mul_add_two_lt_next_gen n (2 * n + 3) (Nat.lt_succ_self (2 * n + 2))

-- Next-generation split: every index is either required at n+1 or beyond 2n+2.
theorem requiredAt_or_two_mul_add_two_lt_next_gen (n i : Nat) :
    requiredAt (n + 1) i ∨ 2 * n + 2 < i := by
  by_cases hReq : requiredAt (n + 1) i
  · exact Or.inl hReq
  · exact Or.inr (Nat.lt_of_not_ge (fun hLe => hReq ((requiredAt_next_gen_iff_le_two_mul_add_two n i).2 hLe)))

-- Next-generation complement form: outside required data is exactly beyond 2n+2.
theorem not_requiredAt_iff_two_mul_add_two_lt_next_gen (n i : Nat) :
    ¬ requiredAt (n + 1) i ↔ 2 * n + 2 < i := by
  constructor
  · intro hNotReq
    exact Nat.lt_of_not_ge
      (fun hLe => hNotReq ((requiredAt_next_gen_iff_le_two_mul_add_two n i).2 hLe))
  · intro hLt hReq
    exact Nat.not_lt_of_ge ((requiredAt_next_gen_iff_le_two_mul_add_two n i).1 hReq) hLt

-- Next-generation non-beyond-boundary form: not being beyond 2n+2 forces requiredness at n+1.
theorem requiredAt_of_not_two_mul_add_two_lt_next_gen (n i : Nat)
    (hNotLt : ¬ (2 * n + 2 < i)) : requiredAt (n + 1) i := by
  by_cases hReq : requiredAt (n + 1) i
  · exact hReq
  · exact False.elim (hNotLt ((not_requiredAt_iff_two_mul_add_two_lt_next_gen n i).1 hReq))

-- In particular, index n is always required.
theorem requiredAt_self (n : Nat) : requiredAt n n := by
  exact requiredAt_of_le_n n n (Nat.le_refl n)

-- Right endpoint of the dependency interval is required.
theorem requiredAt_two_mul (n : Nat) : requiredAt n (2 * n) := by
  exact (requiredAt_iff_le_two_mul n (2 * n)).2 (Nat.le_refl (2 * n))

-- First index after the dependency interval is not required.
theorem not_requiredAt_two_mul_succ (n : Nat) : ¬ requiredAt n (2 * n + 1) := by
  intro hReq
  have hLe : 2 * n + 1 <= 2 * n := (requiredAt_iff_le_two_mul n (2 * n + 1)).1 hReq
  exact Nat.not_succ_le_self (2 * n) hLe

-- Any index strictly beyond the cone endpoint is not required.
theorem not_requiredAt_of_two_mul_lt (n i : Nat) (h : 2 * n < i) : ¬ requiredAt n i := by
  intro hReq
  have hLe : i <= 2 * n := (requiredAt_iff_le_two_mul n i).1 hReq
  exact Nat.not_lt_of_ge hLe h

-- Complement form: an index is outside required data exactly when it is beyond 2n.
theorem not_requiredAt_iff_two_mul_lt (n i : Nat) : ¬ requiredAt n i ↔ 2 * n < i := by
  constructor
  · intro hNotReq
    apply Nat.lt_of_not_ge
    intro hLe
    exact hNotReq ((requiredAt_iff_le_two_mul n i).2 hLe)
  · intro hLt hReq
    have hLe : i <= 2 * n := (requiredAt_iff_le_two_mul n i).1 hReq
    exact Nat.not_lt_of_ge hLe hLt

-- Non-beyond-boundary form: not being beyond 2n forces requiredness at generation n.
theorem requiredAt_of_not_two_mul_lt (n i : Nat) (hNotLt : ¬ (2 * n < i)) : requiredAt n i := by
  by_cases hReq : requiredAt n i
  · exact hReq
  · exact False.elim (hNotLt ((not_requiredAt_iff_two_mul_lt n i).1 hReq))

-- Every index either lies in the required interval or is strictly beyond it.
theorem requiredAt_or_two_mul_lt (n i : Nat) : requiredAt n i ∨ 2 * n < i := by
  by_cases hReq : requiredAt n i
  · exact Or.inl hReq
  · exact Or.inr ((not_requiredAt_iff_two_mul_lt n i).1 hReq)

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

-- In particular, exactness forces observation of the center-prefix endpoint i = n.
theorem observes_self_of_exact
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
    forall n, A.observes n n := by
  intro n
  exact observes_prefix_of_exact (cell := cell) A target h_obs_det h_exact h_witness n n
    (Nat.le_refl n)

-- Exactness also forces observation across the full cone interval i <= 2n.
theorem observes_cone_interval_of_exact
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
    forall n i, i <= 2 * n -> A.observes n i := by
  intro n i hi
  exact must_observe_required (cell := cell) A target h_obs_det h_exact h_witness n i
    (requiredAt_of_le_two_mul n i hi)

-- If an index is required at generation n, exactness forces it observed at generation n+1 as well.
theorem observes_required_next_gen_of_exact
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
    forall n i, requiredAt n i -> A.observes (n + 1) i := by
  intro n i hReq
  exact must_observe_required (cell := cell) A target h_obs_det h_exact h_witness (n + 1) i
    (requiredAt_monotone_gen n i hReq)

-- Prefix form of next-generation forcing: every i <= n must be observed at generation n+1.
theorem observes_prefix_next_gen_of_exact
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
    forall n i, i <= n -> A.observes (n + 1) i := by
  intro n i hi
  exact observes_required_next_gen_of_exact (cell := cell) A target h_obs_det h_exact h_witness n i
    (requiredAt_of_le_n n i hi)

-- At generation n+1, exactness forces observation of index 2n+1.
theorem observes_two_mul_add_one_next_gen_of_exact
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
    forall n, A.observes (n + 1) (2 * n + 1) := by
  intro n
  exact must_observe_required (cell := cell) A target h_obs_det h_exact h_witness (n + 1) (2 * n + 1)
    (requiredAt_of_le_two_mul_add_one_next_gen n (2 * n + 1) (Nat.le_refl (2 * n + 1)))

-- In particular, exactness forces observation of the cone endpoint i = 2n.
theorem observes_two_mul_of_exact
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
    forall n, A.observes n (2 * n) := by
  intro n
  exact observes_cone_interval_of_exact (cell := cell) A target h_obs_det h_exact h_witness n (2 * n)
    (Nat.le_refl (2 * n))

-- Endpoint form at generation n+1, rewritten as 2n+2.
theorem observes_two_mul_add_two_next_gen_of_exact
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
    forall n, A.observes (n + 1) (2 * n + 2) := by
  intro n
  simpa [Nat.mul_add, Nat.add_comm]
    using observes_two_mul_of_exact (cell := cell) A target h_obs_det h_exact h_witness (n + 1)

-- At generation n+1, exactness forces observation over the full interval i <= 2n+2.
theorem observes_next_gen_interval_of_exact
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
    forall n i, i <= 2 * n + 2 -> A.observes (n + 1) i := by
  intro n i hi
  exact must_observe_required (cell := cell) A target h_obs_det h_exact h_witness (n + 1) i
    ((requiredAt_next_gen_iff_le_two_mul_add_two n i).2 hi)

-- Split form for witness case analysis: either an index is observed, or it lies beyond 2n.
theorem observes_or_two_mul_lt_of_exact
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
    forall n i, A.observes n i ∨ 2 * n < i := by
  intro n i
  rcases requiredAt_or_two_mul_lt n i with hReq | hLt
  · exact Or.inl (must_observe_required (cell := cell) A target h_obs_det h_exact h_witness n i hReq)
  · exact Or.inr hLt

-- Non-beyond-boundary form: if i is not strictly beyond 2n, exactness forces observation at n.
theorem observes_of_not_two_mul_lt_of_exact
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
    forall n i, ¬ (2 * n < i) -> A.observes n i := by
  intro n i hNotLt
  rcases observes_or_two_mul_lt_of_exact (cell := cell) A target h_obs_det h_exact h_witness n i with hObs | hLt
  · exact hObs
  · exact False.elim (hNotLt hLt)

-- Next-generation split corollary: exactness implies observed-or-beyond-(2n+2) at n+1.
theorem observes_or_two_mul_add_two_lt_next_gen_of_exact
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
    forall n i, A.observes (n + 1) i ∨ 2 * n + 2 < i := by
  intro n i
  simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using observes_or_two_mul_lt_of_exact (cell := cell) A target h_obs_det h_exact h_witness (n + 1) i

-- Next-generation non-beyond-boundary form: if i is not beyond 2n+2, exactness forces observation at n+1.
theorem observes_of_not_two_mul_add_two_lt_next_gen_of_exact
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
    forall n i, ¬ (2 * n + 2 < i) -> A.observes (n + 1) i := by
  intro n i hNotLt
  rcases observes_or_two_mul_add_two_lt_next_gen_of_exact
      (cell := cell) A target h_obs_det h_exact h_witness n i with hObs | hLt
  · exact hObs
  · exact False.elim (hNotLt hLt)

-- Contrapositive bridge form: under exactness hypotheses, unobserved implies not required.
theorem not_observes_implies_not_required_of_exact
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
    forall n i, ¬ (A.observes n i) -> ¬ requiredAt n i := by
  intro n i hNotObs hReq
  exact hNotObs
    (must_observe_required (cell := cell) A target h_obs_det h_exact h_witness n i hReq)

-- Split form in requiredness language: every index is observed or not required.
theorem observes_or_not_required_of_exact
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
    forall n i, A.observes n i ∨ ¬ requiredAt n i := by
  intro n i
  rcases observes_or_two_mul_lt_of_exact (cell := cell) A target h_obs_det h_exact h_witness n i with hObs | hLt
  · exact Or.inl hObs
  · exact Or.inr (not_requiredAt_of_two_mul_lt n i hLt)

-- Next-generation contrapositive form: unobserved at n+1 implies not required at n+1.
theorem not_observes_next_gen_implies_not_required_next_gen_of_exact
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
    forall n i, ¬ (A.observes (n + 1) i) -> ¬ requiredAt (n + 1) i := by
  intro n i hNotObs hReq
  exact hNotObs
    (must_observe_required (cell := cell) A target h_obs_det h_exact h_witness (n + 1) i hReq)

-- Next-generation split in requiredness language: every index at n+1 is observed or not required.
theorem observes_or_not_required_next_gen_of_exact
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
    forall n i, A.observes (n + 1) i ∨ ¬ requiredAt (n + 1) i := by
  intro n i
  rcases observes_or_two_mul_add_two_lt_next_gen_of_exact
      (cell := cell) A target h_obs_det h_exact h_witness n i with hObs | hLt
  · exact Or.inl hObs
  · exact Or.inr (not_requiredAt_of_two_mul_add_two_lt_next_gen n i hLt)

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

-- Under the same accounting hypothesis, work also dominates cone width directly.
theorem work_ge_requiredCells_implies_coneWidth
    (work : Nat -> Nat)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, coneWidth n <= work n := by
  intro n
  simpa [requiredCells] using h_account n

-- Expanded arithmetic form useful for explicit constant accounting.
theorem work_ge_requiredCells_implies_two_mul_plus_one
    (work : Nat -> Nat)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, 2 * n + 1 <= work n := by
  intro n
  simpa [coneWidth] using work_ge_requiredCells_implies_coneWidth work h_account n

-- A weaker but sometimes cleaner arithmetic form from the same accounting hypothesis.
theorem work_ge_requiredCells_implies_two_mul
    (work : Nat -> Nat)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, 2 * n <= work n := by
  intro n
  exact Nat.le_trans (Nat.le_succ (2 * n))
    (work_ge_requiredCells_implies_two_mul_plus_one work h_account n)

-- Required indices are bounded by the cone interval's right endpoint proxy.
theorem requiredAt_le_two_mul (n i : Nat) (hReq : requiredAt n i) : i <= 2 * n := by
  unfold requiredAt requiredCells coneWidth at hReq
  have hSucc : i < Nat.succ (2 * n) := by
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using hReq
  exact Nat.lt_succ_iff.mp hSucc

-- Conditional per-index transfer: any required index is bounded by work
-- once explicit accounting requiredCells n <= work n is supplied.
theorem work_ge_requiredCells_implies_requiredAt_le_work
    (work : Nat -> Nat)
    (h_account : forall n, requiredCells n <= work n) :
    forall n i, requiredAt n i -> i <= work n := by
  intro n i hReq
  exact Nat.le_trans (requiredAt_le_two_mul n i hReq)
    (work_ge_requiredCells_implies_two_mul work h_account n)

-- Next-generation arithmetic corollary under the same accounting hypothesis.
theorem work_ge_requiredCells_implies_two_mul_add_two_next_gen
    (work : Nat -> Nat)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, 2 * n + 2 <= work (n + 1) := by
  intro n
  have hStrong : 2 + 2 * n + 1 <= work (n + 1) := by
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using work_ge_requiredCells_implies_two_mul_plus_one work h_account (n + 1)
  have hStep : 2 * n + 2 <= 2 + 2 * n + 1 := by
    calc
      2 * n + 2 = 2 + 2 * n := by simp [Nat.add_comm]
      _ <= 2 + 2 * n + 1 := Nat.le_succ (2 + 2 * n)
  exact Nat.le_trans hStep hStrong

-- Next-generation per-index transfer (explicit n+1 form) for bridge composition.
theorem work_ge_requiredCells_implies_requiredAt_next_gen_le_work
    (work : Nat -> Nat)
    (h_account : forall n, requiredCells n <= work n) :
    forall n i, requiredAt (n + 1) i -> i <= work (n + 1) := by
  intro n i hReq
  exact work_ge_requiredCells_implies_requiredAt_le_work work h_account (n + 1) i hReq

end CostTransferScaffold

/-!
  Phase 5 composition scaffold:
  These lemmas only combine already-conditional bridge and accounting results.
  They remain conditional and do not claim a closed Prize3 lower bound.
-/

section BridgeCostComposition

variable {State : Type}
variable (cell : State -> Nat -> Bool)

-- Under exactness+witness hypotheses and explicit accounting, each required index
-- is both observed and bounded by work at generation n.
theorem required_observed_and_bounded_of_exact_and_accounting
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness :
      forall n i,
        requiredAt n i ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2)
    (h_account : forall n, requiredCells n <= work n) :
    forall n i, requiredAt n i -> (A.observes n i /\ i <= work n) := by
  intro n i hReq
  constructor
  · exact must_observe_required (cell := cell) A target h_obs_det h_exact h_witness n i hReq
  · exact work_ge_requiredCells_implies_requiredAt_le_work work h_account n i hReq

-- Next-generation form of the same composition lemma.
theorem required_observed_and_bounded_next_gen_of_exact_and_accounting
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness :
      forall n i,
        requiredAt n i ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2)
    (h_account : forall n, requiredCells n <= work n) :
    forall n i, requiredAt (n + 1) i -> (A.observes (n + 1) i /\ i <= work (n + 1)) := by
  intro n i hReq
  constructor
  · exact must_observe_required (cell := cell) A target h_obs_det h_exact h_witness (n + 1) i hReq
  · exact work_ge_requiredCells_implies_requiredAt_next_gen_le_work work h_account n i hReq

-- Endpoint specialization at generation n: index 2n is observed and work-bounded.
theorem endpoint_observed_and_bounded_of_exact_and_accounting
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness :
      forall n i,
        requiredAt n i ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, (A.observes n (2 * n) /\ 2 * n <= work n) := by
  intro n
  exact required_observed_and_bounded_of_exact_and_accounting
    (cell := cell) A target work h_obs_det h_exact h_witness h_account n (2 * n)
    (requiredAt_two_mul n)

-- Endpoint specialization at generation n+1: index 2n+2 is observed and work-bounded.
theorem endpoint_next_gen_observed_and_bounded_of_exact_and_accounting
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness :
      forall n i,
        requiredAt n i ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, (A.observes (n + 1) (2 * n + 2) /\ 2 * n + 2 <= work (n + 1)) := by
  intro n
  exact required_observed_and_bounded_next_gen_of_exact_and_accounting
    (cell := cell) A target work h_obs_det h_exact h_witness h_account n (2 * n + 2)
    (requiredAt_two_mul_add_two_next_gen n)

end BridgeCostComposition

end Prize3
