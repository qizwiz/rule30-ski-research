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

section Rule30WitnessScaffold

-- Concrete Rule 30 state container: cell values indexed by natural positions.
abbrev Rule30State : Type := Nat -> Bool

-- Concrete cell accessor for the bridge interface.
def rule30Cell (s : Rule30State) (i : Nat) : Bool := s i

-- Concrete center-target projection at generation n.
def rule30CenterTarget (trace : Nat -> Rule30State) (n : Nat) : Bool :=
  rule30Cell (trace n) n

-- One-step local Rule30 update used for concrete finite witness seeds.
def rule30Local (p q r : Bool) : Bool := p != (q || r)

-- Center after one Rule30 step from indices 0,1,2 of the initial slice.
def rule30CenterOneStep (s : Rule30State) : Bool :=
  rule30Local (rule30Cell s 0) (rule30Cell s 1) (rule30Cell s 2)

-- Center after two Rule30 steps from indices 0..4 of the initial slice.
def rule30CenterTwoStep (s : Rule30State) : Bool :=
  rule30Local
    (rule30Local (rule30Cell s 0) (rule30Cell s 1) (rule30Cell s 2))
    (rule30Local (rule30Cell s 1) (rule30Cell s 2) (rule30Cell s 3))
    (rule30Local (rule30Cell s 2) (rule30Cell s 3) (rule30Cell s 4))

-- Center after three Rule30 steps from indices 0..6 of the initial slice.
def rule30CenterThreeStep (s : Rule30State) : Bool :=
  rule30Local
    (rule30Local
      (rule30Local (rule30Cell s 0) (rule30Cell s 1) (rule30Cell s 2))
      (rule30Local (rule30Cell s 1) (rule30Cell s 2) (rule30Cell s 3))
      (rule30Local (rule30Cell s 2) (rule30Cell s 3) (rule30Cell s 4)))
    (rule30Local
      (rule30Local (rule30Cell s 1) (rule30Cell s 2) (rule30Cell s 3))
      (rule30Local (rule30Cell s 2) (rule30Cell s 3) (rule30Cell s 4))
      (rule30Local (rule30Cell s 3) (rule30Cell s 4) (rule30Cell s 5)))
    (rule30Local
      (rule30Local (rule30Cell s 2) (rule30Cell s 3) (rule30Cell s 4))
      (rule30Local (rule30Cell s 3) (rule30Cell s 4) (rule30Cell s 5))
      (rule30Local (rule30Cell s 4) (rule30Cell s 5) (rule30Cell s 6)))

-- Center after four Rule30 steps from indices 0..8 of the initial slice.
def rule30CenterFourStep (s : Rule30State) : Bool :=
  let a0 := rule30Local (rule30Cell s 0) (rule30Cell s 1) (rule30Cell s 2)
  let a1 := rule30Local (rule30Cell s 1) (rule30Cell s 2) (rule30Cell s 3)
  let a2 := rule30Local (rule30Cell s 2) (rule30Cell s 3) (rule30Cell s 4)
  let a3 := rule30Local (rule30Cell s 3) (rule30Cell s 4) (rule30Cell s 5)
  let a4 := rule30Local (rule30Cell s 4) (rule30Cell s 5) (rule30Cell s 6)
  let a5 := rule30Local (rule30Cell s 5) (rule30Cell s 6) (rule30Cell s 7)
  let a6 := rule30Local (rule30Cell s 6) (rule30Cell s 7) (rule30Cell s 8)
  let b0 := rule30Local a0 a1 a2
  let b1 := rule30Local a1 a2 a3
  let b2 := rule30Local a2 a3 a4
  let b3 := rule30Local a3 a4 a5
  let b4 := rule30Local a4 a5 a6
  let c0 := rule30Local b0 b1 b2
  let c1 := rule30Local b1 b2 b3
  let c2 := rule30Local b2 b3 b4
  rule30Local c0 c1 c2

-- Small-horizon center target dispatcher (n = 0..3).
def rule30CenterSmall (n : Nat) (s : Rule30State) : Bool :=
  match n with
  | 0 => rule30Cell s 0
  | 1 => rule30CenterOneStep s
  | 2 => rule30CenterTwoStep s
  | 3 => rule30CenterThreeStep s
  | 4 => rule30CenterFourStep s
  | _ => rule30Cell s n

-- Recursive center evaluator on a finite cone slice:
-- `n+1` depends on three shifted `n`-step center evaluations.
def rule30CenterRec : Nat -> Rule30State -> Bool
  | 0, s => rule30Cell s 0
  | Nat.succ k, s =>
      rule30Local
        (rule30CenterRec k s)
        (rule30CenterRec k (fun j => s (j + 1)))
        (rule30CenterRec k (fun j => s (j + 2)))

-- Pointwise bit flip on a full Rule30State.
def flipAtState (s : Rule30State) (i : Nat) : Rule30State :=
  fun j => if j = i then !(s j) else s j

-- Boolean-difference check for a fixed target function.
def diffCheck (f : Rule30State -> Bool) (i : Nat) (s : Rule30State) : Bool :=
  decide (f s ≠ f (flipAtState s i))

-- Essentiality via Boolean derivative witness.
def essentialByWitness (f : Rule30State -> Bool) (i : Nat) : Prop :=
  ∃ s, f s ≠ f (flipAtState s i)

theorem flipAtState_agree_except
    (s : Rule30State) (i j : Nat) (hj : j ≠ i) :
    rule30Cell s j = rule30Cell (flipAtState s i) j := by
  simp [rule30Cell, flipAtState, hj]

theorem pointwise_diff_witness_of_essentialByWitness
    (f : Rule30State -> Bool) (i : Nat)
    (hEss : essentialByWitness f i) :
    exists s1 s2,
      (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
      f s1 ≠ f s2 := by
  rcases hEss with ⟨s, hNe⟩
  refine ⟨s, flipAtState s i, ?_, hNe⟩
  intro j hj
  exact flipAtState_agree_except s i j hj

theorem essentialByWitness_iff_diffCheck_true
    (f : Rule30State -> Bool) (i : Nat) :
    essentialByWitness f i ↔ ∃ s, diffCheck f i s = true := by
  constructor
  · intro h
    rcases h with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    unfold diffCheck
    simpa [hs] using (show decide (f s ≠ f (flipAtState s i)) = true from by simp [hs])
  · intro h
    rcases h with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    unfold diffCheck at hs
    by_cases hDiff : f s ≠ f (flipAtState s i)
    · exact hDiff
    · simp [hDiff] at hs

-- 4D witness certificate: (n, i, x, check).
structure Rule30WitnessCert where
  n : Nat
  i : Nat
  x : Rule30State
  check : Bool

def rule30WitnessCertValid (c : Rule30WitnessCert) : Prop :=
  c.check = diffCheck (rule30CenterRec c.n) c.i c.x

theorem rule30WitnessCertValid_sound
    (c : Rule30WitnessCert)
    (hValid : rule30WitnessCertValid c)
    (hCheck : c.check = true) :
    rule30CenterRec c.n c.x ≠ rule30CenterRec c.n (flipAtState c.x c.i) := by
  unfold rule30WitnessCertValid at hValid
  rw [hValid] at hCheck
  unfold diffCheck at hCheck
  by_cases hDiff : rule30CenterRec c.n c.x ≠ rule30CenterRec c.n (flipAtState c.x c.i)
  · exact hDiff
  · simp [hDiff] at hCheck

theorem essentialByWitness_of_rule30WitnessCertValid_true
    (c : Rule30WitnessCert)
    (hValid : rule30WitnessCertValid c)
    (hCheck : c.check = true) :
    essentialByWitness (rule30CenterRec c.n) c.i := by
  refine ⟨c.x, ?_⟩
  exact rule30WitnessCertValid_sound c hValid hCheck

theorem rule30CenterRec_eq_small_0 (s : Rule30State) :
    rule30CenterRec 0 s = rule30CenterSmall 0 s := by
  rfl

theorem rule30CenterRec_eq_small_1 (s : Rule30State) :
    rule30CenterRec 1 s = rule30CenterSmall 1 s := by
  rfl

theorem rule30CenterRec_eq_small_2 (s : Rule30State) :
    rule30CenterRec 2 s = rule30CenterSmall 2 s := by
  rfl

theorem rule30CenterRec_eq_small_3 (s : Rule30State) :
    rule30CenterRec 3 s = rule30CenterSmall 3 s := by
  rfl

theorem rule30CenterRec_eq_small_4 (s : Rule30State) :
    rule30CenterRec 4 s = rule30CenterSmall 4 s := by
  rfl

theorem rule30CenterRec_eq_small_of_le_four (n : Nat) (hN : n <= 4) (s : Rule30State) :
    rule30CenterRec n s = rule30CenterSmall n s := by
  cases n with
  | zero =>
    simpa using rule30CenterRec_eq_small_0 s
  | succ n =>
    cases n with
    | zero =>
      simpa using rule30CenterRec_eq_small_1 s
    | succ n =>
      cases n with
      | zero =>
        simpa using rule30CenterRec_eq_small_2 s
      | succ n =>
        cases n with
        | zero =>
          simpa using rule30CenterRec_eq_small_3 s
        | succ n =>
          cases n with
          | zero =>
            simpa using rule30CenterRec_eq_small_4 s
          | succ n =>
            have hGt : 4 < Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))) := by simp
            exact False.elim (Nat.not_lt_of_ge hN hGt)

-- Single-index perturbation seed state.
def stateFlipAt (i : Nat) (b : Bool) : Rule30State :=
  fun j => if j = i then b else false

theorem stateFlipAt_agree_except (i j : Nat) (hj : j ≠ i) :
    rule30Cell (stateFlipAt i false) j = rule30Cell (stateFlipAt i true) j := by
  simp [rule30Cell, stateFlipAt, hj]

-- Override one index on top of an arbitrary base state.
def stateFlipAtOnBase (base : Rule30State) (i : Nat) (b : Bool) : Rule30State :=
  fun j => if j = i then b else base j

theorem stateFlipAtOnBase_agree_except
    (base : Rule30State) (i j : Nat) (b1 b2 : Bool) (hj : j ≠ i) :
    rule30Cell (stateFlipAtOnBase base i b1) j =
      rule30Cell (stateFlipAtOnBase base i b2) j := by
  simp [rule30Cell, stateFlipAtOnBase, hj]

theorem one_step_center_witness_i0 :
    exists s1 s2,
      (forall j, j ≠ 0 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterOneStep s1 ≠ rule30CenterOneStep s2 := by
  refine ⟨stateFlipAt 0 false, stateFlipAt 0 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 0 j hj
  · decide

theorem one_step_center_witness_i1 :
    exists s1 s2,
      (forall j, j ≠ 1 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterOneStep s1 ≠ rule30CenterOneStep s2 := by
  refine ⟨stateFlipAt 1 false, stateFlipAt 1 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 1 j hj
  · decide

theorem one_step_center_witness_i2 :
    exists s1 s2,
      (forall j, j ≠ 2 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterOneStep s1 ≠ rule30CenterOneStep s2 := by
  refine ⟨stateFlipAt 2 false, stateFlipAt 2 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 2 j hj
  · decide

-- Concrete one-step witness family across the full one-step required interval.
theorem one_step_center_witness_of_le_two (i : Nat) (hLe : i ≤ 2) :
    exists s1 s2,
      (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterOneStep s1 ≠ rule30CenterOneStep s2 := by
  cases i with
  | zero =>
    simpa using one_step_center_witness_i0
  | succ i =>
    cases i with
    | zero =>
      simpa using one_step_center_witness_i1
    | succ i =>
      cases i with
      | zero =>
        simpa using one_step_center_witness_i2
      | succ i =>
        have hGt : 2 < Nat.succ (Nat.succ (Nat.succ i)) := by
          simp
        exact False.elim (Nat.not_lt_of_ge hLe hGt)

-- Helper: full pointwise agreement implies bridge-form observed agreement.
theorem agreesOnObserved_of_pointwise_eq
    (A : Algorithm Rule30State)
    (n : Nat)
    (s1 s2 : Rule30State)
    (hEq : forall i, rule30Cell s1 i = rule30Cell s2 i) :
    agreesOnObserved rule30Cell A n s1 s2 := by
  intro i _hi
  exact hEq i

-- Bounded concrete witness adapter: if two states differ only at an unobserved
-- index i (within the 2n cone endpoint) and already separate the target output,
-- this yields the bridge witness form used by must_observe_required*.
theorem witness_le_two_mul_of_pointwise_diff
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          target n s1 ≠ target n s2) :
    forall n i,
      i <= 2 * n ->
      ¬ (A.observes n i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A n s1 s2 /\ target n s1 ≠ target n s2 := by
  intro n i hLe hNotObs
  rcases hConcrete n i hLe hNotObs with ⟨s1, s2, hEqExcept, hTargetNe⟩
  refine ⟨s1, s2, ?_, hTargetNe⟩
  intro j hObs
  exact hEqExcept j (by
    intro hji
    apply hNotObs
    simpa [hji] using hObs)

-- Center-target specialization of the bounded concrete witness adapter.
theorem witness_rule30_center_le_two_mul_of_pointwise_diff
    (A : Algorithm Rule30State)
    (hConcreteCenter :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n) :
    forall n i,
      i <= 2 * n ->
      ¬ (A.observes n i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A n s1 s2 /\ rule30Cell s1 n ≠ rule30Cell s2 n := by
  intro n i hLe hNotObs
  exact witness_le_two_mul_of_pointwise_diff
    A (fun k s => rule30Cell s k) hConcreteCenter n i hLe hNotObs

end Rule30WitnessScaffold

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

-- Concrete one-step h_witness seed in bridge form:
-- for each required index at n=1, produce agreeing-on-observed states with
-- different one-step center outputs.
theorem one_step_center_h_witness_seed
    (A : Algorithm Rule30State) :
    forall i,
      requiredAt 1 i ->
      ¬ (A.observes 1 i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A 1 s1 s2 /\ rule30CenterOneStep s1 ≠ rule30CenterOneStep s2 := by
  intro i hReq hNotObs
  have hLe : i <= 2 := by
    have hLe' : i <= 2 * 1 := (requiredAt_iff_le_two_mul 1 i).1 hReq
    simpa using hLe'
  rcases one_step_center_witness_of_le_two i hLe with ⟨s1, s2, hEqExcept, hNe⟩
  refine ⟨s1, s2, ?_, hNe⟩
  intro j hObs
  exact hEqExcept j (by
    intro hji
    apply hNotObs
    simpa [hji] using hObs)

-- Concrete zero-step h_witness seed in bridge form.
theorem zero_step_center_h_witness_seed
    (A : Algorithm Rule30State) :
    forall i,
      requiredAt 0 i ->
      ¬ (A.observes 0 i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A 0 s1 s2 /\ rule30Cell s1 0 ≠ rule30Cell s2 0 := by
  intro i hReq hNotObs
  have hi0 : i = 0 := by
    have hLe : i <= 2 * 0 := (requiredAt_iff_le_two_mul 0 i).1 hReq
    have : i = 0 := Nat.eq_zero_of_le_zero (by simpa using hLe)
    exact this
  subst hi0
  refine ⟨stateFlipAt 0 false, stateFlipAt 0 true, ?_, ?_⟩
  · intro j hObs
    exact stateFlipAt_agree_except 0 j (by
      intro hj0
      apply hNotObs
      simpa [hj0] using hObs)
  · decide

-- One-step center witness seed in explicit arithmetic form i <= 2.
theorem one_step_center_h_witness_seed_of_le_two
    (A : Algorithm Rule30State) :
    forall i,
      i <= 2 ->
      ¬ (A.observes 1 i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A 1 s1 s2 /\ rule30CenterOneStep s1 ≠ rule30CenterOneStep s2 := by
  intro i hLe hNotObs
  exact one_step_center_h_witness_seed A i
    ((requiredAt_iff_le_two_mul 1 i).2 (by simpa using hLe))
    hNotObs

-- Concrete two-step h_witness seed in bridge form at index i=0.
theorem two_step_center_h_witness_seed_i0
    (A : Algorithm Rule30State) :
    ¬ (A.observes 2 0) ->
    exists s1 s2,
      agreesOnObserved rule30Cell A 2 s1 s2 /\ rule30CenterTwoStep s1 ≠ rule30CenterTwoStep s2 := by
  intro hNotObs
  refine ⟨stateFlipAt 0 false, stateFlipAt 0 true, ?_, ?_⟩
  · intro j hObs
    exact stateFlipAt_agree_except 0 j (by
      intro hj0
      apply hNotObs
      simpa [hj0] using hObs)
  · decide

theorem two_step_center_witness_i1 :
    exists s1 s2,
      (forall j, j ≠ 1 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterTwoStep s1 ≠ rule30CenterTwoStep s2 := by
  let base : Rule30State := stateFlipAt 4 true
  refine ⟨stateFlipAtOnBase base 1 false, stateFlipAtOnBase base 1 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAtOnBase_agree_except base 1 j false true hj
  · decide

theorem two_step_center_witness_i2 :
    exists s1 s2,
      (forall j, j ≠ 2 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterTwoStep s1 ≠ rule30CenterTwoStep s2 := by
  let base : Rule30State := stateFlipAt 4 true
  refine ⟨stateFlipAtOnBase base 2 false, stateFlipAtOnBase base 2 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAtOnBase_agree_except base 2 j false true hj
  · decide

theorem two_step_center_witness_i3 :
    exists s1 s2,
      (forall j, j ≠ 3 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterTwoStep s1 ≠ rule30CenterTwoStep s2 := by
  refine ⟨stateFlipAt 3 false, stateFlipAt 3 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 3 j hj
  · decide

theorem two_step_center_witness_i4 :
    exists s1 s2,
      (forall j, j ≠ 4 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterTwoStep s1 ≠ rule30CenterTwoStep s2 := by
  refine ⟨stateFlipAt 4 false, stateFlipAt 4 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 4 j hj
  · decide

-- Concrete two-step witness family across the full two-step required interval.
theorem two_step_center_witness_of_le_four (i : Nat) (hLe : i ≤ 4) :
    exists s1 s2,
      (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterTwoStep s1 ≠ rule30CenterTwoStep s2 := by
  cases i with
  | zero =>
    refine ⟨stateFlipAt 0 false, stateFlipAt 0 true, ?_, ?_⟩
    · intro j hj
      exact stateFlipAt_agree_except 0 j hj
    · decide
  | succ i =>
    cases i with
    | zero =>
      simpa using two_step_center_witness_i1
    | succ i =>
      cases i with
      | zero =>
        simpa using two_step_center_witness_i2
      | succ i =>
        cases i with
        | zero =>
          simpa using two_step_center_witness_i3
        | succ i =>
          cases i with
          | zero =>
            simpa using two_step_center_witness_i4
          | succ i =>
            have hGt : 4 < Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ i)))) := by
              simp
            exact False.elim (Nat.not_lt_of_ge hLe hGt)

-- Concrete two-step h_witness seed in bridge form:
-- for each required index at n=2, produce agreeing-on-observed states with
-- different two-step center outputs.
theorem two_step_center_h_witness_seed
    (A : Algorithm Rule30State) :
    forall i,
      requiredAt 2 i ->
      ¬ (A.observes 2 i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A 2 s1 s2 /\ rule30CenterTwoStep s1 ≠ rule30CenterTwoStep s2 := by
  intro i hReq hNotObs
  have hLe : i ≤ 4 := by
    have hLe' : i <= 2 * 2 := (requiredAt_iff_le_two_mul 2 i).1 hReq
    simpa using hLe'
  rcases two_step_center_witness_of_le_four i hLe with ⟨s1, s2, hEqExcept, hNe⟩
  refine ⟨s1, s2, ?_, hNe⟩
  intro j hObs
  exact hEqExcept j (by
    intro hji
    apply hNotObs
    simpa [hji] using hObs)

-- Two-step center witness seed in explicit arithmetic form i <= 4.
theorem two_step_center_h_witness_seed_of_le_four
    (A : Algorithm Rule30State) :
    forall i,
      i <= 4 ->
      ¬ (A.observes 2 i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A 2 s1 s2 /\ rule30CenterTwoStep s1 ≠ rule30CenterTwoStep s2 := by
  intro i hLe hNotObs
  exact two_step_center_h_witness_seed A i
    ((requiredAt_iff_le_two_mul 2 i).2 (by simpa using hLe))
    hNotObs

theorem three_step_center_witness_i0 :
    exists s1 s2,
      (forall j, j ≠ 0 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterThreeStep s1 ≠ rule30CenterThreeStep s2 := by
  refine ⟨stateFlipAt 0 false, stateFlipAt 0 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 0 j hj
  · decide

theorem three_step_center_witness_i1 :
    exists s1 s2,
      (forall j, j ≠ 1 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterThreeStep s1 ≠ rule30CenterThreeStep s2 := by
  refine ⟨stateFlipAt 1 false, stateFlipAt 1 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 1 j hj
  · decide

theorem three_step_center_witness_i2 :
    exists s1 s2,
      (forall j, j ≠ 2 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterThreeStep s1 ≠ rule30CenterThreeStep s2 := by
  refine ⟨stateFlipAt 2 false, stateFlipAt 2 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 2 j hj
  · decide

theorem three_step_center_witness_i3 :
    exists s1 s2,
      (forall j, j ≠ 3 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterThreeStep s1 ≠ rule30CenterThreeStep s2 := by
  refine ⟨stateFlipAt 3 false, stateFlipAt 3 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 3 j hj
  · decide

theorem three_step_center_witness_i4 :
    exists s1 s2,
      (forall j, j ≠ 4 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterThreeStep s1 ≠ rule30CenterThreeStep s2 := by
  let base : Rule30State := stateFlipAt 6 true
  refine ⟨stateFlipAtOnBase base 4 false, stateFlipAtOnBase base 4 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAtOnBase_agree_except base 4 j false true hj
  · decide

theorem three_step_center_witness_i5 :
    exists s1 s2,
      (forall j, j ≠ 5 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterThreeStep s1 ≠ rule30CenterThreeStep s2 := by
  refine ⟨stateFlipAt 5 false, stateFlipAt 5 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 5 j hj
  · decide

theorem three_step_center_witness_i6 :
    exists s1 s2,
      (forall j, j ≠ 6 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterThreeStep s1 ≠ rule30CenterThreeStep s2 := by
  refine ⟨stateFlipAt 6 false, stateFlipAt 6 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 6 j hj
  · decide

-- Concrete three-step witness family across the full three-step required interval.
theorem three_step_center_witness_of_le_six (i : Nat) (hLe : i ≤ 6) :
    exists s1 s2,
      (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterThreeStep s1 ≠ rule30CenterThreeStep s2 := by
  cases i with
  | zero =>
    simpa using three_step_center_witness_i0
  | succ i =>
    cases i with
    | zero =>
      simpa using three_step_center_witness_i1
    | succ i =>
      cases i with
      | zero =>
        simpa using three_step_center_witness_i2
      | succ i =>
        cases i with
        | zero =>
          simpa using three_step_center_witness_i3
        | succ i =>
          cases i with
          | zero =>
            simpa using three_step_center_witness_i4
          | succ i =>
            cases i with
            | zero =>
              simpa using three_step_center_witness_i5
            | succ i =>
              cases i with
              | zero =>
                simpa using three_step_center_witness_i6
              | succ i =>
                have hGt : 6 < Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ i)))))) := by
                  simp
                exact False.elim (Nat.not_lt_of_ge hLe hGt)

-- Concrete three-step h_witness seed in bridge form:
-- for each required index at n=3, produce agreeing-on-observed states with
-- different three-step center outputs.
theorem three_step_center_h_witness_seed
    (A : Algorithm Rule30State) :
    forall i,
      requiredAt 3 i ->
      ¬ (A.observes 3 i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A 3 s1 s2 /\ rule30CenterThreeStep s1 ≠ rule30CenterThreeStep s2 := by
  intro i hReq hNotObs
  have hLe : i ≤ 6 := by
    have hLe' : i <= 2 * 3 := (requiredAt_iff_le_two_mul 3 i).1 hReq
    simpa using hLe'
  rcases three_step_center_witness_of_le_six i hLe with ⟨s1, s2, hEqExcept, hNe⟩
  refine ⟨s1, s2, ?_, hNe⟩
  intro j hObs
  exact hEqExcept j (by
    intro hji
    apply hNotObs
    simpa [hji] using hObs)

theorem four_step_center_witness_i0 :
    exists s1 s2,
      (forall j, j ≠ 0 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterFourStep s1 ≠ rule30CenterFourStep s2 := by
  refine ⟨stateFlipAt 0 false, stateFlipAt 0 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 0 j hj
  · decide

theorem four_step_center_witness_i1 :
    exists s1 s2,
      (forall j, j ≠ 1 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterFourStep s1 ≠ rule30CenterFourStep s2 := by
  let base : Rule30State := stateFlipAt 6 true
  refine ⟨stateFlipAtOnBase base 1 false, stateFlipAtOnBase base 1 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAtOnBase_agree_except base 1 j false true hj
  · decide

theorem four_step_center_witness_i2 :
    exists s1 s2,
      (forall j, j ≠ 2 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterFourStep s1 ≠ rule30CenterFourStep s2 := by
  let base : Rule30State := stateFlipAt 4 true
  refine ⟨stateFlipAtOnBase base 2 false, stateFlipAtOnBase base 2 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAtOnBase_agree_except base 2 j false true hj
  · decide

theorem four_step_center_witness_i3 :
    exists s1 s2,
      (forall j, j ≠ 3 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterFourStep s1 ≠ rule30CenterFourStep s2 := by
  let base : Rule30State := stateFlipAt 4 true
  refine ⟨stateFlipAtOnBase base 3 false, stateFlipAtOnBase base 3 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAtOnBase_agree_except base 3 j false true hj
  · decide

theorem four_step_center_witness_i4 :
    exists s1 s2,
      (forall j, j ≠ 4 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterFourStep s1 ≠ rule30CenterFourStep s2 := by
  refine ⟨stateFlipAt 4 false, stateFlipAt 4 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 4 j hj
  · decide

theorem four_step_center_witness_i5 :
    exists s1 s2,
      (forall j, j ≠ 5 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterFourStep s1 ≠ rule30CenterFourStep s2 := by
  let base : Rule30State := stateFlipAt 7 true
  refine ⟨stateFlipAtOnBase base 5 false, stateFlipAtOnBase base 5 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAtOnBase_agree_except base 5 j false true hj
  · decide

theorem four_step_center_witness_i6 :
    exists s1 s2,
      (forall j, j ≠ 6 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterFourStep s1 ≠ rule30CenterFourStep s2 := by
  let base : Rule30State := stateFlipAt 1 true
  refine ⟨stateFlipAtOnBase base 6 false, stateFlipAtOnBase base 6 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAtOnBase_agree_except base 6 j false true hj
  · decide

theorem four_step_center_witness_i7 :
    exists s1 s2,
      (forall j, j ≠ 7 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterFourStep s1 ≠ rule30CenterFourStep s2 := by
  refine ⟨stateFlipAt 7 false, stateFlipAt 7 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 7 j hj
  · decide

theorem four_step_center_witness_i8 :
    exists s1 s2,
      (forall j, j ≠ 8 -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterFourStep s1 ≠ rule30CenterFourStep s2 := by
  refine ⟨stateFlipAt 8 false, stateFlipAt 8 true, ?_, ?_⟩
  · intro j hj
    exact stateFlipAt_agree_except 8 j hj
  · decide

-- Concrete four-step witness family across the full four-step required interval.
theorem four_step_center_witness_of_le_eight (i : Nat) (hLe : i ≤ 8) :
    exists s1 s2,
      (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
      rule30CenterFourStep s1 ≠ rule30CenterFourStep s2 := by
  cases i with
  | zero =>
    simpa using four_step_center_witness_i0
  | succ i =>
    cases i with
    | zero =>
      simpa using four_step_center_witness_i1
    | succ i =>
      cases i with
      | zero =>
        simpa using four_step_center_witness_i2
      | succ i =>
        cases i with
        | zero =>
          simpa using four_step_center_witness_i3
        | succ i =>
          cases i with
          | zero =>
            simpa using four_step_center_witness_i4
          | succ i =>
            cases i with
            | zero =>
              simpa using four_step_center_witness_i5
            | succ i =>
              cases i with
              | zero =>
                simpa using four_step_center_witness_i6
              | succ i =>
                cases i with
                | zero =>
                  simpa using four_step_center_witness_i7
                | succ i =>
                  cases i with
                  | zero =>
                    simpa using four_step_center_witness_i8
                  | succ i =>
                    have hGt :
                        8 <
                          Nat.succ
                            (Nat.succ
                              (Nat.succ
                                (Nat.succ
                                  (Nat.succ
                                    (Nat.succ
                                      (Nat.succ
                                        (Nat.succ (Nat.succ i)))))))) := by
                      simp
                    exact False.elim (Nat.not_lt_of_ge hLe hGt)

-- Concrete four-step h_witness seed in bridge form.
theorem four_step_center_h_witness_seed
    (A : Algorithm Rule30State) :
    forall i,
      requiredAt 4 i ->
      ¬ (A.observes 4 i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A 4 s1 s2 /\ rule30CenterFourStep s1 ≠ rule30CenterFourStep s2 := by
  intro i hReq hNotObs
  have hLe : i ≤ 8 := by
    have hLe' : i <= 2 * 4 := (requiredAt_iff_le_two_mul 4 i).1 hReq
    simpa using hLe'
  rcases four_step_center_witness_of_le_eight i hLe with ⟨s1, s2, hEqExcept, hNe⟩
  refine ⟨s1, s2, ?_, hNe⟩
  intro j hObs
  exact hEqExcept j (by
    intro hji
    apply hNotObs
    simpa [hji] using hObs)

-- Uniform small-horizon witness constructor seed (n = 0..4).
theorem small_horizon_center_h_witness_seed_le_four
    (A : Algorithm Rule30State) :
    forall n i,
      n <= 4 ->
      requiredAt n i ->
      ¬ (A.observes n i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A n s1 s2 /\ rule30CenterSmall n s1 ≠ rule30CenterSmall n s2 := by
  intro n i hN hReq hNotObs
  cases n with
  | zero =>
    rcases zero_step_center_h_witness_seed A i hReq hNotObs with ⟨s1, s2, hAgree, hNe⟩
    exact ⟨s1, s2, hAgree, by simpa [rule30CenterSmall] using hNe⟩
  | succ n =>
    cases n with
    | zero =>
      rcases one_step_center_h_witness_seed A i hReq hNotObs with ⟨s1, s2, hAgree, hNe⟩
      exact ⟨s1, s2, hAgree, by simpa [rule30CenterSmall] using hNe⟩
    | succ n =>
      cases n with
      | zero =>
        rcases two_step_center_h_witness_seed A i hReq hNotObs with ⟨s1, s2, hAgree, hNe⟩
        exact ⟨s1, s2, hAgree, by simpa [rule30CenterSmall] using hNe⟩
      | succ n =>
        cases n with
        | zero =>
          rcases three_step_center_h_witness_seed A i hReq hNotObs with ⟨s1, s2, hAgree, hNe⟩
          exact ⟨s1, s2, hAgree, by simpa [rule30CenterSmall] using hNe⟩
        | succ n =>
          cases n with
          | zero =>
            rcases four_step_center_h_witness_seed A i hReq hNotObs with ⟨s1, s2, hAgree, hNe⟩
            exact ⟨s1, s2, hAgree, by simpa [rule30CenterSmall] using hNe⟩
          | succ n =>
            have hGt : 4 < Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))) := by simp
            exact False.elim (Nat.not_lt_of_ge hN hGt)

-- Small-horizon no-skip closure from exactness + observation determinism (`n <= 4`).
theorem observes_required_small_horizon_of_exact_le_four
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact_small :
      forall n, n <= 4 -> forall s, A.run n s = rule30CenterSmall n s) :
    forall n i, n <= 4 -> requiredAt n i -> A.observes n i := by
  intro n i hN hReq
  by_cases hObs : A.observes n i
  · exact hObs
  · rcases small_horizon_center_h_witness_seed_le_four A n i hN hReq hObs with ⟨s1, s2, hAgree, hNe⟩
    have hRunEq : A.run n s1 = A.run n s2 := h_obs_det n s1 s2 hAgree
    have hTargetEq : rule30CenterSmall n s1 = rule30CenterSmall n s2 := by
      rw [← h_exact_small n hN s1, ← h_exact_small n hN s2]
      exact hRunEq
    exact False.elim (hNe hTargetEq)

-- Rec-target variant of the uniform small-horizon witness constructor (`n <= 4`).
theorem small_horizon_center_h_witness_seed_rec_le_four
    (A : Algorithm Rule30State) :
    forall n i,
      n <= 4 ->
      requiredAt n i ->
      ¬ (A.observes n i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A n s1 s2 /\ rule30CenterRec n s1 ≠ rule30CenterRec n s2 := by
  intro n i hN hReq hNotObs
  rcases small_horizon_center_h_witness_seed_le_four A n i hN hReq hNotObs with
    ⟨s1, s2, hAgree, hNeSmall⟩
  refine ⟨s1, s2, hAgree, ?_⟩
  intro hEqRec
  apply hNeSmall
  rw [← rule30CenterRec_eq_small_of_le_four n hN s1, ← rule30CenterRec_eq_small_of_le_four n hN s2]
  exact hEqRec

-- Rec-target variant of small-horizon no-skip closure (`n <= 4`).
theorem observes_required_small_horizon_of_exact_rec_le_four
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact_rec_small :
      forall n, n <= 4 -> forall s, A.run n s = rule30CenterRec n s) :
    forall n i, n <= 4 -> requiredAt n i -> A.observes n i := by
  intro n i hN hReq
  by_cases hObs : A.observes n i
  · exact hObs
  · rcases small_horizon_center_h_witness_seed_rec_le_four A n i hN hReq hObs with
      ⟨s1, s2, hAgree, hNeRec⟩
    have hRunEq : A.run n s1 = A.run n s2 := h_obs_det n s1 s2 hAgree
    have hTargetEq : rule30CenterRec n s1 = rule30CenterRec n s2 := by
      rw [← h_exact_rec_small n hN s1, ← h_exact_rec_small n hN s2]
      exact hRunEq
    exact False.elim (hNeRec hTargetEq)

-- Uniform small-horizon witness constructor seed (n = 0..3).
theorem small_horizon_center_h_witness_seed
    (A : Algorithm Rule30State) :
    forall n i,
      n <= 3 ->
      requiredAt n i ->
      ¬ (A.observes n i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A n s1 s2 /\ rule30CenterSmall n s1 ≠ rule30CenterSmall n s2 := by
  intro n i hN hReq hNotObs
  cases n with
  | zero =>
    rcases zero_step_center_h_witness_seed A i hReq hNotObs with ⟨s1, s2, hAgree, hNe⟩
    exact ⟨s1, s2, hAgree, by simpa [rule30CenterSmall] using hNe⟩
  | succ n =>
    cases n with
    | zero =>
      rcases one_step_center_h_witness_seed A i hReq hNotObs with ⟨s1, s2, hAgree, hNe⟩
      exact ⟨s1, s2, hAgree, by simpa [rule30CenterSmall] using hNe⟩
    | succ n =>
      cases n with
      | zero =>
        rcases two_step_center_h_witness_seed A i hReq hNotObs with ⟨s1, s2, hAgree, hNe⟩
        exact ⟨s1, s2, hAgree, by simpa [rule30CenterSmall] using hNe⟩
      | succ n =>
        cases n with
        | zero =>
          rcases three_step_center_h_witness_seed A i hReq hNotObs with ⟨s1, s2, hAgree, hNe⟩
          exact ⟨s1, s2, hAgree, by simpa [rule30CenterSmall] using hNe⟩
        | succ n =>
          have hGt : 3 < Nat.succ (Nat.succ (Nat.succ (Nat.succ n))) := by simp
          exact False.elim (Nat.not_lt_of_ge hN hGt)

-- Small-horizon no-skip closure from exactness + observation determinism.
theorem observes_required_small_horizon_of_exact
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact_small :
      forall n, n <= 3 -> forall s, A.run n s = rule30CenterSmall n s) :
    forall n i, n <= 3 -> requiredAt n i -> A.observes n i := by
  intro n i hN hReq
  by_cases hObs : A.observes n i
  · exact hObs
  · rcases small_horizon_center_h_witness_seed A n i hN hReq hObs with ⟨s1, s2, hAgree, hNe⟩
    have hRunEq : A.run n s1 = A.run n s2 := h_obs_det n s1 s2 hAgree
    have hTargetEq : rule30CenterSmall n s1 = rule30CenterSmall n s2 := by
      rw [← h_exact_small n hN s1, ← h_exact_small n hN s2]
      exact hRunEq
    exact False.elim (hNe hTargetEq)

-- Per-generation Rule30 center witness predicate for bridge discharge.
def Rule30CenterWitnessAt
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (n : Nat) : Prop :=
  forall i,
    requiredAt n i ->
    ¬ (A.observes n i) ->
    exists s1 s2,
      agreesOnObserved rule30Cell A n s1 s2 /\ target n s1 ≠ target n s2

-- Small-horizon witness predicate instance for the concrete small target.
theorem rule30CenterWitnessAt_small_horizon
    (A : Algorithm Rule30State) :
    forall n, n <= 3 -> Rule30CenterWitnessAt A rule30CenterSmall n := by
  intro n hN i hReq hNotObs
  exact small_horizon_center_h_witness_seed A n i hN hReq hNotObs

-- Small-horizon witness predicate instance for the concrete small target (`n <= 4`).
theorem rule30CenterWitnessAt_small_horizon_le_four
    (A : Algorithm Rule30State) :
    forall n, n <= 4 -> Rule30CenterWitnessAt A rule30CenterSmall n := by
  intro n hN i hReq hNotObs
  exact small_horizon_center_h_witness_seed_le_four A n i hN hReq hNotObs

-- Induction scaffold:
-- if witnesses hold on small horizons and can be propagated one generation
-- from n to n+1 for n >= 3, then they hold for all n.
theorem rule30CenterWitnessAt_of_small_horizon_and_step
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (hBase : forall n, n <= 3 -> Rule30CenterWitnessAt A target n)
    (hStep :
      forall n,
        3 <= n ->
        Rule30CenterWitnessAt A target n ->
        Rule30CenterWitnessAt A target (n + 1)) :
    forall n, Rule30CenterWitnessAt A target n := by
  intro n
  induction n with
  | zero =>
    exact hBase 0 (by simp)
  | succ n ih =>
    by_cases hSmall : Nat.succ n <= 3
    · exact hBase (Nat.succ n) hSmall
    · have hGe3 : 3 <= n := by
        have hLt : 3 < Nat.succ n := Nat.lt_of_not_ge hSmall
        exact Nat.lt_succ_iff.mp hLt
      exact hStep n hGe3 ih

-- Variant of the induction scaffold with explicit base horizon `n <= 4`.
theorem rule30CenterWitnessAt_of_small_horizon_le_four_and_step
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (hBase : forall n, n <= 4 -> Rule30CenterWitnessAt A target n)
    (hStep :
      forall n,
        4 <= n ->
        Rule30CenterWitnessAt A target n ->
        Rule30CenterWitnessAt A target (n + 1)) :
    forall n, Rule30CenterWitnessAt A target n := by
  intro n
  induction n with
  | zero =>
    exact hBase 0 (by simp)
  | succ n ih =>
    by_cases hSmall : Nat.succ n <= 4
    · exact hBase (Nat.succ n) hSmall
    · have hGe4 : 4 <= n := by
        have hLt : 4 < Nat.succ n := Nat.lt_of_not_ge hSmall
        exact Nat.lt_succ_iff.mp hLt
      exact hStep n hGe4 ih

-- Bridge discharge from a full witness family.
theorem observes_required_of_rule30CenterWitnessAt
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (hWitness : forall n, Rule30CenterWitnessAt A target n) :
    forall n i, requiredAt n i -> A.observes n i := by
  intro n i hReq
  exact must_observe_required
    (cell := rule30Cell)
    A target h_obs_det h_exact
    (fun n i hReq' hNotObs => hWitness n i hReq' hNotObs)
    n i hReq

-- Step adapter:
-- if we can build next-generation pointwise-difference witnesses in arithmetic
-- form (`i <= 2*(n+1)`), we obtain the witness predicate at `n+1`.
theorem rule30CenterWitnessAt_next_gen_of_pointwise_diff
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (hConcreteNext :
      forall n i,
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          target (n + 1) s1 ≠ target (n + 1) s2) :
    forall n, Rule30CenterWitnessAt A target (n + 1) := by
  intro n i hReq hNotObs
  have hLe : i <= 2 * (n + 1) := (requiredAt_iff_le_two_mul (n + 1) i).1 hReq
  rcases hConcreteNext n i hLe hNotObs with ⟨s1, s2, hEqExcept, hNe⟩
  refine ⟨s1, s2, ?_, hNe⟩
  intro j hObs
  exact hEqExcept j (by
    intro hji
    apply hNotObs
    simpa [hji] using hObs)

-- Induction-step constructor:
-- combine a next-generation concrete witness builder with the generic scaffold.
theorem rule30CenterWitnessAt_step_of_pointwise_diff
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (hConcreteNext :
      forall n i,
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          target (n + 1) s1 ≠ target (n + 1) s2) :
    forall n,
      3 <= n ->
      Rule30CenterWitnessAt A target n ->
      Rule30CenterWitnessAt A target (n + 1) := by
  intro n _hGe _hPrev
  exact rule30CenterWitnessAt_next_gen_of_pointwise_diff A target hConcreteNext n

-- Full witness-family constructor from:
-- (1) explicit small-horizon base (`n <= 3`) and
-- (2) next-generation concrete pointwise-difference witnesses.
theorem rule30CenterWitnessAt_all_of_small_horizon_and_pointwise_next
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (hBase : forall n, n <= 3 -> Rule30CenterWitnessAt A target n)
    (hConcreteNext :
      forall n i,
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          target (n + 1) s1 ≠ target (n + 1) s2) :
    forall n, Rule30CenterWitnessAt A target n := by
  exact rule30CenterWitnessAt_of_small_horizon_and_step
    A target hBase
    (rule30CenterWitnessAt_step_of_pointwise_diff A target hConcreteNext)

-- Full witness-family constructor from:
-- (1) explicit small-horizon base (`n <= 4`) and
-- (2) next-generation concrete pointwise-difference witnesses.
theorem rule30CenterWitnessAt_all_of_small_horizon_le_four_and_pointwise_next
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (hBase : forall n, n <= 4 -> Rule30CenterWitnessAt A target n)
    (hConcreteNext :
      forall n i,
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          target (n + 1) s1 ≠ target (n + 1) s2) :
    forall n, Rule30CenterWitnessAt A target n := by
  exact rule30CenterWitnessAt_of_small_horizon_le_four_and_step
    A target hBase
    (fun n _hGe4 _hPrev =>
      rule30CenterWitnessAt_next_gen_of_pointwise_diff A target hConcreteNext n)

-- Full no-skip closure from the same two ingredients.
theorem observes_required_of_small_horizon_and_pointwise_next
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (hBase : forall n, n <= 3 -> Rule30CenterWitnessAt A target n)
    (hConcreteNext :
      forall n i,
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          target (n + 1) s1 ≠ target (n + 1) s2) :
    forall n i, requiredAt n i -> A.observes n i := by
  intro n i hReq
  exact observes_required_of_rule30CenterWitnessAt
    A target h_obs_det h_exact
    (rule30CenterWitnessAt_all_of_small_horizon_and_pointwise_next
      A target hBase hConcreteNext)
    n i hReq

-- Specialization with the concrete small-horizon base constructor.
theorem observes_required_of_rule30CenterSmall_base_and_pointwise_next
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A rule30CenterSmall)
    (hConcreteNext :
      forall n i,
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30CenterSmall (n + 1) s1 ≠ rule30CenterSmall (n + 1) s2) :
    forall n i, requiredAt n i -> A.observes n i := by
  intro n i hReq
  exact observes_required_of_small_horizon_and_pointwise_next
    A rule30CenterSmall h_obs_det h_exact
    (rule30CenterWitnessAt_small_horizon A) hConcreteNext
    n i hReq

-- Recursive-target full witness-family constructor from:
-- (1) rec-target small-horizon base (`n <= 4`) and
-- (2) recursive-target next-generation pointwise-difference witnesses.
theorem rule30CenterRec_witness_all_of_small_horizon_and_pointwise_next
    (A : Algorithm Rule30State)
    (hConcreteNextRec :
      forall n i,
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2) :
    forall n, Rule30CenterWitnessAt A rule30CenterRec n := by
  exact rule30CenterWitnessAt_all_of_small_horizon_le_four_and_pointwise_next
    A rule30CenterRec
    (fun n hN =>
      by
        intro i hReq hNotObs
        exact small_horizon_center_h_witness_seed_rec_le_four A n i hN hReq hNotObs)
    hConcreteNextRec

-- Recursive-target next-generation witness-family packaging from concrete
-- pointwise-difference witnesses at generation `n+1`.
theorem rule30CenterWitnessAt_next_gen_rule30CenterRec_of_pointwise_diff
    (A : Algorithm Rule30State)
    (hConcreteNextRec :
      forall n i,
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2) :
    forall n, Rule30CenterWitnessAt A rule30CenterRec (n + 1) := by
  exact rule30CenterWitnessAt_next_gen_of_pointwise_diff A rule30CenterRec hConcreteNextRec

-- Concrete recursive-target next-generation pointwise-difference witnesses
-- for bounded horizons (`n <= 3`), using explicit finite witness families.
theorem rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three
    (A : Algorithm Rule30State) :
    forall n i,
      n <= 3 ->
      i <= 2 * (n + 1) ->
      ¬ (A.observes (n + 1) i) ->
      exists s1 s2,
        (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
        rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2 := by
  intro n i hN hLe _hNotObs
  cases n with
  | zero =>
    have hLe2 : i <= 2 := by simpa using hLe
    rcases one_step_center_witness_of_le_two i hLe2 with ⟨s1, s2, hEqExcept, hNe⟩
    refine ⟨s1, s2, hEqExcept, ?_⟩
    simpa [rule30CenterRec_eq_small_1, rule30CenterSmall] using hNe
  | succ n =>
    cases n with
    | zero =>
      have hLe4 : i <= 4 := by simpa using hLe
      rcases two_step_center_witness_of_le_four i hLe4 with ⟨s1, s2, hEqExcept, hNe⟩
      refine ⟨s1, s2, hEqExcept, ?_⟩
      simpa [rule30CenterRec_eq_small_2, rule30CenterSmall] using hNe
    | succ n =>
      cases n with
      | zero =>
        have hLe6 : i <= 6 := by simpa using hLe
        rcases three_step_center_witness_of_le_six i hLe6 with ⟨s1, s2, hEqExcept, hNe⟩
        refine ⟨s1, s2, hEqExcept, ?_⟩
        simpa [rule30CenterRec_eq_small_3, rule30CenterSmall] using hNe
      | succ n =>
        cases n with
        | zero =>
          have hLe8 : i <= 8 := by simpa using hLe
          rcases four_step_center_witness_of_le_eight i hLe8 with ⟨s1, s2, hEqExcept, hNe⟩
          refine ⟨s1, s2, hEqExcept, ?_⟩
          simpa [rule30CenterRec_eq_small_4, rule30CenterSmall] using hNe
        | succ n =>
          have hNotGe : ¬ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n))) <= 3) := by simp
          exact False.elim (hNotGe hN)

-- Bounded recursive-target next-generation pointwise-difference witnesses
-- in explicit non-beyond-boundary form (`¬(2n+2 < i)`), for `n <= 3`.
theorem rule30CenterRec_next_gen_pointwise_diff_witness_not_two_mul_add_two_lt_of_le_three
    (A : Algorithm Rule30State) :
    forall n i,
      n <= 3 ->
      ¬ (2 * n + 2 < i) ->
      ¬ (A.observes (n + 1) i) ->
      exists s1 s2,
        (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
        rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2 := by
  intro n i hN hNotLt hNotObs
  have hLe' : i <= 2 * n + 2 := Nat.le_of_not_gt hNotLt
  have hLe : i <= 2 * (n + 1) := by simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm] using hLe'
  exact rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three A n i hN hLe hNotObs

-- Bounded recursive-target next-generation pointwise-difference witnesses
-- in required-interval form (`requiredAt (n+1) i`), for `n <= 3`.
theorem rule30CenterRec_next_gen_pointwise_diff_witness_requiredAt_of_le_three
    (A : Algorithm Rule30State) :
    forall n i,
      n <= 3 ->
      requiredAt (n + 1) i ->
      ¬ (A.observes (n + 1) i) ->
      exists s1 s2,
        (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
        rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2 := by
  intro n i hN hReq hNotObs
  have hLe : i <= 2 * (n + 1) := (requiredAt_iff_le_two_mul (n + 1) i).1 hReq
  exact rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three A n i hN hLe hNotObs

-- Package the bounded concrete recursive-target next-generation witness
-- constructor as a witness-family instance at generation `n+1` (`n <= 3`).
theorem rule30CenterWitnessAt_next_gen_rule30CenterRec_of_pointwise_diff_le_three
    (A : Algorithm Rule30State) :
    forall n,
      n <= 3 ->
      Rule30CenterWitnessAt A rule30CenterRec (n + 1) := by
  intro n hN i hReq hNotObs
  rcases rule30CenterRec_next_gen_pointwise_diff_witness_requiredAt_of_le_three
      A n i hN hReq hNotObs with
      ⟨s1, s2, hEqExcept, hNe⟩
  refine ⟨s1, s2, ?_, hNe⟩
  intro j hObs
  exact hEqExcept j (by
    intro hji
    apply hNotObs
    simpa [hji] using hObs)

-- Bounded next-generation no-skip closure (`n <= 3`) from the concrete
-- recursive-target witness constructor.
theorem observes_required_next_gen_rule30CenterRec_of_pointwise_diff_le_three
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact_rec : exactFor A rule30CenterRec) :
    forall n,
      n <= 3 ->
      forall i, requiredAt (n + 1) i -> A.observes (n + 1) i := by
  intro n hN i hReq
  by_cases hObs : A.observes (n + 1) i
  · exact hObs
  · rcases rule30CenterWitnessAt_next_gen_rule30CenterRec_of_pointwise_diff_le_three A n hN i hReq hObs with
      ⟨s1, s2, hAgree, hTargetNe⟩
    have hRunEq : A.run (n + 1) s1 = A.run (n + 1) s2 := h_obs_det (n + 1) s1 s2 hAgree
    have hTargetEq : rule30CenterRec (n + 1) s1 = rule30CenterRec (n + 1) s2 := by
      rw [← h_exact_rec (n + 1) s1, ← h_exact_rec (n + 1) s2]
      exact hRunEq
    exact False.elim (hTargetNe hTargetEq)

-- Bounded next-generation no-skip closure (`n <= 3`) in explicit
-- non-beyond-boundary form: `¬(2n+2 < i)` implies observation at `n+1`.
theorem observes_next_gen_of_not_two_mul_add_two_lt_rule30CenterRec_of_pointwise_diff_le_three
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact_rec : exactFor A rule30CenterRec) :
    forall n,
      n <= 3 ->
      forall i, ¬ (2 * n + 2 < i) -> A.observes (n + 1) i := by
  intro n hN i hNotLt
  by_cases hObs : A.observes (n + 1) i
  · exact hObs
  · rcases rule30CenterRec_next_gen_pointwise_diff_witness_not_two_mul_add_two_lt_of_le_three
      A n i hN hNotLt hObs with ⟨s1, s2, hEqExcept, hTargetNe⟩
    have hAgree : agreesOnObserved rule30Cell A (n + 1) s1 s2 := by
      intro j hObsJ
      exact hEqExcept j (by
        intro hji
        apply hObs
        simpa [hji] using hObsJ)
    have hRunEq : A.run (n + 1) s1 = A.run (n + 1) s2 := h_obs_det (n + 1) s1 s2 hAgree
    have hTargetEq : rule30CenterRec (n + 1) s1 = rule30CenterRec (n + 1) s2 := by
      rw [← h_exact_rec (n + 1) s1, ← h_exact_rec (n + 1) s2]
      exact hRunEq
    exact False.elim (hTargetNe hTargetEq)

-- Bridge adapter in explicit non-beyond-boundary form:
-- combine the bounded concrete witness constructor (`n <= 3`) with a tail
-- constructor (`3 < n`) to obtain a full next-generation witness family
-- stated as `¬(2n+2 < i)`.
theorem rule30CenterRec_next_gen_pointwise_diff_witness_not_two_mul_add_two_lt_of_le_three_or_gt_three
    (A : Algorithm Rule30State)
    (hTailNotTwoMulAddTwoLt :
      forall n i,
        3 < n ->
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2) :
    forall n i,
      ¬ (2 * n + 2 < i) ->
      ¬ (A.observes (n + 1) i) ->
      exists s1 s2,
        (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
        rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2 := by
  intro n i hNotLt hNotObs
  by_cases hN : n <= 3
  · exact rule30CenterRec_next_gen_pointwise_diff_witness_not_two_mul_add_two_lt_of_le_three
      A n i hN hNotLt hNotObs
  · exact hTailNotTwoMulAddTwoLt n i (Nat.lt_of_not_ge hN) hNotLt hNotObs

-- Tail-aware next-generation no-skip closure in explicit non-beyond-boundary
-- form: if `i` is not beyond `2n+2`, observation at generation `n+1` follows.
theorem observes_next_gen_of_not_two_mul_add_two_lt_rule30CenterRec_of_pointwise_diff_le_three_or_gt_three
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact_rec : exactFor A rule30CenterRec)
    (hTailNotTwoMulAddTwoLt :
      forall n i,
        3 < n ->
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2) :
    forall n i, ¬ (2 * n + 2 < i) -> A.observes (n + 1) i := by
  intro n i hNotLt
  by_cases hObs : A.observes (n + 1) i
  · exact hObs
  · rcases rule30CenterRec_next_gen_pointwise_diff_witness_not_two_mul_add_two_lt_of_le_three_or_gt_three
      A hTailNotTwoMulAddTwoLt n i hNotLt hObs with
      ⟨s1, s2, hEqExcept, hTargetNe⟩
    have hAgree : agreesOnObserved rule30Cell A (n + 1) s1 s2 := by
      intro j hObsJ
      exact hEqExcept j (by
        intro hji
        apply hObs
        simpa [hji] using hObsJ)
    have hRunEq : A.run (n + 1) s1 = A.run (n + 1) s2 := h_obs_det (n + 1) s1 s2 hAgree
    have hTargetEq : rule30CenterRec (n + 1) s1 = rule30CenterRec (n + 1) s2 := by
      rw [← h_exact_rec (n + 1) s1, ← h_exact_rec (n + 1) s2]
      exact hRunEq
    exact False.elim (hTargetNe hTargetEq)

-- Tail-aware next-generation no-skip closure in requiredAt form.
theorem observes_required_next_gen_rule30CenterRec_of_pointwise_diff_le_three_or_gt_three
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact_rec : exactFor A rule30CenterRec)
    (hTailNotTwoMulAddTwoLt :
      forall n i,
        3 < n ->
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2) :
    forall n i, requiredAt (n + 1) i -> A.observes (n + 1) i := by
  intro n i hReq
  have hLe : i ≤ 2 * n + 2 := by
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using ((requiredAt_iff_le_two_mul (n + 1) i).1 hReq)
  exact observes_next_gen_of_not_two_mul_add_two_lt_rule30CenterRec_of_pointwise_diff_le_three_or_gt_three
    A h_obs_det h_exact_rec hTailNotTwoMulAddTwoLt n i
    (Nat.not_lt_of_ge hLe)

-- Bridge adapter: combine the explicit bounded witness constructor (`n <= 3`)
-- with an abstract tail constructor (`3 < n`) to obtain a full next-generation
-- pointwise-difference witness family.
theorem rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three_or_gt_three
    (A : Algorithm Rule30State)
    (hTail :
      forall n i,
        3 < n ->
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2) :
    forall n i,
      i <= 2 * (n + 1) ->
      ¬ (A.observes (n + 1) i) ->
      exists s1 s2,
        (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
        rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2 := by
  intro n i hLe hNotObs
  by_cases hN : n <= 3
  · exact rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three A n i hN hLe hNotObs
  · exact hTail n i (Nat.lt_of_not_ge hN) hLe hNotObs

-- Tail-shape adapter:
-- convert explicit non-beyond-boundary tail witnesses (`¬(2n+2 < i)`) into
-- boundary-form tail witnesses (`i <= 2*(n+1)`).
theorem rule30CenterRec_tail_pointwise_diff_witness_of_tail_not_two_mul_add_two_lt
    (A : Algorithm Rule30State)
    (hTailNotTwoMulAddTwoLt :
      forall n i,
        3 < n ->
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2) :
    forall n i,
      3 < n ->
      i <= 2 * (n + 1) ->
      ¬ (A.observes (n + 1) i) ->
      exists s1 s2,
        (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
        rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2 := by
  intro n i hGt hLe hNotObs
  have hLe' : i <= 2 * n + 2 := by
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLe
  exact hTailNotTwoMulAddTwoLt n i hGt (Nat.not_lt_of_ge hLe') hNotObs

-- Tail adapter from essentiality witnesses to pointwise-difference witnesses.
theorem rule30CenterRec_tail_pointwise_diff_witness_of_tail_essentialByWitness
    (A : Algorithm Rule30State)
    (hTailEssential :
      forall n i,
        3 < n ->
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        essentialByWitness (rule30CenterRec (n + 1)) i) :
    forall n i,
      3 < n ->
      i <= 2 * (n + 1) ->
      ¬ (A.observes (n + 1) i) ->
      exists s1 s2,
        (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
        rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2 := by
  intro n i hGt hLe hNotObs
  exact pointwise_diff_witness_of_essentialByWitness
    (rule30CenterRec (n + 1)) i
    (hTailEssential n i hGt hLe hNotObs)

-- Tail adapter from certificate checks to pointwise-difference witnesses.
theorem rule30CenterRec_tail_pointwise_diff_witness_of_tail_cert
    (A : Algorithm Rule30State)
    (hTailCert :
      forall n i,
        3 < n ->
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        ∃ c : Rule30WitnessCert,
          c.n = n + 1 /\
          c.i = i /\
          rule30WitnessCertValid c /\
          c.check = true) :
    forall n i,
      3 < n ->
      i <= 2 * (n + 1) ->
      ¬ (A.observes (n + 1) i) ->
      exists s1 s2,
        (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
        rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2 := by
  intro n i hGt hLe hNotObs
  rcases hTailCert n i hGt hLe hNotObs with ⟨c, hCn, hCi, hValid, hCheck⟩
  have hEss : essentialByWitness (rule30CenterRec (n + 1)) i := by
    rw [← hCn, ← hCi]
    exact essentialByWitness_of_rule30WitnessCertValid_true c hValid hCheck
  exact pointwise_diff_witness_of_essentialByWitness
    (rule30CenterRec (n + 1)) i hEss

-- Full next-generation pointwise-difference witness family from:
-- bounded concrete construction (`n <= 3`) + certificate-checked tails (`3 < n`).
theorem rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three_or_tail_cert
    (A : Algorithm Rule30State)
    (hTailCert :
      forall n i,
        3 < n ->
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        ∃ c : Rule30WitnessCert,
          c.n = n + 1 /\
          c.i = i /\
          rule30WitnessCertValid c /\
          c.check = true) :
    forall n i,
      i <= 2 * (n + 1) ->
      ¬ (A.observes (n + 1) i) ->
      exists s1 s2,
        (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
        rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2 := by
  exact rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three_or_gt_three
    A (rule30CenterRec_tail_pointwise_diff_witness_of_tail_cert A hTailCert)

-- Recursive-target full no-skip closure from:
-- deterministic observed semantics + exactness to `rule30CenterRec`
-- + rec-target next-generation pointwise witnesses.
theorem observes_required_of_rule30CenterRec_base_and_pointwise_next
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact_rec : exactFor A rule30CenterRec)
    (hConcreteNextRec :
      forall n i,
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2) :
    forall n i, requiredAt n i -> A.observes n i := by
  intro n i hReq
  exact observes_required_of_rule30CenterWitnessAt
    A rule30CenterRec h_obs_det h_exact_rec
    (rule30CenterRec_witness_all_of_small_horizon_and_pointwise_next A hConcreteNextRec)
    n i hReq

-- Recursive-target full no-skip closure adapter that consumes:
-- (1) concrete bounded witness construction (`n <= 3`) and
-- (2) an explicit unbounded tail constructor (`3 < n`).
theorem observes_required_of_rule30CenterRec_base_and_tail_pointwise_next
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact_rec : exactFor A rule30CenterRec)
    (hTail :
      forall n i,
        3 < n ->
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2) :
    forall n i, requiredAt n i -> A.observes n i := by
  exact observes_required_of_rule30CenterRec_base_and_pointwise_next
    A h_obs_det h_exact_rec
    (rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three_or_gt_three A hTail)

-- Recursive-target full no-skip closure adapter for explicit non-beyond-boundary
-- tail hypotheses (`¬(2n+2 < i)`).
theorem observes_required_of_rule30CenterRec_base_and_tail_not_two_mul_add_two_lt
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact_rec : exactFor A rule30CenterRec)
    (hTailNotTwoMulAddTwoLt :
      forall n i,
        3 < n ->
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30CenterRec (n + 1) s1 ≠ rule30CenterRec (n + 1) s2) :
    forall n i, requiredAt n i -> A.observes n i := by
  exact observes_required_of_rule30CenterRec_base_and_tail_pointwise_next
    A h_obs_det h_exact_rec
    (rule30CenterRec_tail_pointwise_diff_witness_of_tail_not_two_mul_add_two_lt
      A hTailNotTwoMulAddTwoLt)

-- Recursive-target no-skip closure adapter for tail essentiality hypotheses.
theorem observes_required_of_rule30CenterRec_base_and_tail_essentialByWitness
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact_rec : exactFor A rule30CenterRec)
    (hTailEssential :
      forall n i,
        3 < n ->
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        essentialByWitness (rule30CenterRec (n + 1)) i) :
    forall n i, requiredAt n i -> A.observes n i := by
  exact observes_required_of_rule30CenterRec_base_and_tail_pointwise_next
    A h_obs_det h_exact_rec
    (rule30CenterRec_tail_pointwise_diff_witness_of_tail_essentialByWitness
      A hTailEssential)

-- Recursive-target no-skip closure adapter for certificate-checked tail hypotheses.
theorem observes_required_of_rule30CenterRec_base_and_tail_cert
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact_rec : exactFor A rule30CenterRec)
    (hTailCert :
      forall n i,
        3 < n ->
        i <= 2 * (n + 1) ->
        ¬ (A.observes (n + 1) i) ->
        ∃ c : Rule30WitnessCert,
          c.n = n + 1 /\
          c.i = i /\
          rule30WitnessCertValid c /\
          c.check = true) :
    forall n i, requiredAt n i -> A.observes n i := by
  exact observes_required_of_rule30CenterRec_base_and_pointwise_next
    A h_obs_det h_exact_rec
    (rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three_or_tail_cert A hTailCert)

-- Concrete n=2 bridge closure: the two-step witness seed forces observation
-- of every required index at generation 2 under local exactness/determinism.
theorem observes_required_at_two_of_two_step_center_seed
    (A : Algorithm Rule30State)
    (h_obs_det2 :
      forall s1 s2,
        agreesOnObserved rule30Cell A 2 s1 s2 -> A.run 2 s1 = A.run 2 s2)
    (h_exact2 : forall s, A.run 2 s = rule30CenterTwoStep s) :
    forall i, requiredAt 2 i -> A.observes 2 i := by
  intro i hReq
  by_cases hObs : A.observes 2 i
  · exact hObs
  · rcases two_step_center_h_witness_seed A i hReq hObs with ⟨s1, s2, hAgree, hTargetNe⟩
    have hRunEq : A.run 2 s1 = A.run 2 s2 := h_obs_det2 s1 s2 hAgree
    have hTargetEq : rule30CenterTwoStep s1 = rule30CenterTwoStep s2 := by
      rw [← h_exact2 s1, ← h_exact2 s2]
      exact hRunEq
    exact False.elim (hTargetNe hTargetEq)

-- Concrete n=3 bridge closure: the three-step witness seed forces observation
-- of every required index at generation 3 under local exactness/determinism.
theorem observes_required_at_three_of_three_step_center_seed
    (A : Algorithm Rule30State)
    (h_obs_det3 :
      forall s1 s2,
        agreesOnObserved rule30Cell A 3 s1 s2 -> A.run 3 s1 = A.run 3 s2)
    (h_exact3 : forall s, A.run 3 s = rule30CenterThreeStep s) :
    forall i, requiredAt 3 i -> A.observes 3 i := by
  intro i hReq
  by_cases hObs : A.observes 3 i
  · exact hObs
  · rcases three_step_center_h_witness_seed A i hReq hObs with ⟨s1, s2, hAgree, hTargetNe⟩
    have hRunEq : A.run 3 s1 = A.run 3 s2 := h_obs_det3 s1 s2 hAgree
    have hTargetEq : rule30CenterThreeStep s1 = rule30CenterThreeStep s2 := by
      rw [← h_exact3 s1, ← h_exact3 s2]
      exact hRunEq
    exact False.elim (hTargetNe hTargetEq)

-- Concrete n=4 bridge closure: the four-step witness seed forces observation
-- of every required index at generation 4 under local exactness/determinism.
theorem observes_required_at_four_of_four_step_center_seed
    (A : Algorithm Rule30State)
    (h_obs_det4 :
      forall s1 s2,
        agreesOnObserved rule30Cell A 4 s1 s2 -> A.run 4 s1 = A.run 4 s2)
    (h_exact4 : forall s, A.run 4 s = rule30CenterFourStep s) :
    forall i, requiredAt 4 i -> A.observes 4 i := by
  intro i hReq
  by_cases hObs : A.observes 4 i
  · exact hObs
  · rcases four_step_center_h_witness_seed A i hReq hObs with ⟨s1, s2, hAgree, hTargetNe⟩
    have hRunEq : A.run 4 s1 = A.run 4 s2 := h_obs_det4 s1 s2 hAgree
    have hTargetEq : rule30CenterFourStep s1 = rule30CenterFourStep s2 := by
      rw [← h_exact4 s1, ← h_exact4 s2]
      exact hRunEq
    exact False.elim (hTargetNe hTargetEq)

-- Center-target witness in direct requiredAt form (h_witness shape).
theorem witness_rule30_center_requiredAt_of_pointwise_diff
    (A : Algorithm Rule30State)
    (hConcreteCenter :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n) :
    forall n i,
      requiredAt n i ->
      ¬ (A.observes n i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A n s1 s2 /\ rule30Cell s1 n ≠ rule30Cell s2 n := by
  intro n i hReq hNotObs
  exact witness_rule30_center_le_two_mul_of_pointwise_diff A hConcreteCenter n i
    ((requiredAt_iff_le_two_mul n i).1 hReq) hNotObs

-- Package the direct requiredAt witness adapter as a per-generation witness family.
theorem rule30CenterWitnessAt_rule30_center_of_pointwise_diff
    (A : Algorithm Rule30State)
    (hConcreteCenter :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n) :
    forall n, Rule30CenterWitnessAt A (fun k s => rule30Cell s k) n := by
  intro n i hReq hNotObs
  exact witness_rule30_center_requiredAt_of_pointwise_diff A hConcreteCenter n i hReq hNotObs

-- Center-target witness in direct requiredAt form from non-beyond-boundary
-- concrete hypotheses (¬(2n < i)).
theorem witness_rule30_center_requiredAt_of_pointwise_diff_not_two_mul_lt
    (A : Algorithm Rule30State)
    (hConcreteCenterNotTwoMulLt :
      forall n i,
        ¬ (2 * n < i) ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n) :
    forall n i,
      requiredAt n i ->
      ¬ (A.observes n i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A n s1 s2 /\ rule30Cell s1 n ≠ rule30Cell s2 n := by
  intro n i hReq hNotObs
  exact witness_rule30_center_requiredAt_of_pointwise_diff
    A
    (fun n' i' hLe hNotObs' =>
      hConcreteCenterNotTwoMulLt n' i' (Nat.not_lt_of_ge hLe) hNotObs')
    n i hReq hNotObs

-- Package the non-beyond-boundary requiredAt witness adapter as a
-- per-generation witness family.
theorem rule30CenterWitnessAt_rule30_center_of_pointwise_diff_not_two_mul_lt
    (A : Algorithm Rule30State)
    (hConcreteCenterNotTwoMulLt :
      forall n i,
        ¬ (2 * n < i) ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n) :
    forall n, Rule30CenterWitnessAt A (fun k s => rule30Cell s k) n := by
  intro n i hReq hNotObs
  exact witness_rule30_center_requiredAt_of_pointwise_diff_not_two_mul_lt
    A hConcreteCenterNotTwoMulLt n i hReq hNotObs

-- Center-target witness in direct next-generation requiredAt form.
theorem witness_rule30_center_requiredAt_next_gen_of_pointwise_diff
    (A : Algorithm Rule30State)
    (hConcreteCenter :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n) :
    forall n i,
      requiredAt (n + 1) i ->
      ¬ (A.observes (n + 1) i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A (n + 1) s1 s2 /\ rule30Cell s1 (n + 1) ≠ rule30Cell s2 (n + 1) := by
  intro n i hReq hNotObs
  exact witness_rule30_center_requiredAt_of_pointwise_diff
    A hConcreteCenter (n + 1) i hReq hNotObs

-- Requiredness at generation n can be split into strict-prefix-or-endpoint form.
theorem requiredAt_iff_lt_two_mul_or_eq_two_mul (n i : Nat) :
    requiredAt n i ↔ i < 2 * n ∨ i = 2 * n := by
  constructor
  · intro hReq
    have hLe : i <= 2 * n := (requiredAt_iff_le_two_mul n i).1 hReq
    exact Nat.lt_or_eq_of_le hLe
  · intro hSplit
    rcases hSplit with hLt | hEq
    · exact (requiredAt_iff_le_two_mul n i).2 (Nat.le_of_lt hLt)
    · rw [hEq]
      exact (requiredAt_iff_le_two_mul n (2 * n)).2 (Nat.le_refl (2 * n))

-- Boundary-index witness adapter: discharge the bridge with the equivalent
-- arithmetic form i <= 2n instead of requiredAt n i.
theorem must_observe_required_of_le_two_mul_witness
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness_le_two_mul :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2) :
    forall n i, requiredAt n i -> A.observes n i := by
  intro n i hReq
  exact must_observe_required (cell := cell) A target h_obs_det h_exact
    (fun n i hReq' hNotObs =>
      h_witness_le_two_mul n i ((requiredAt_iff_le_two_mul n i).1 hReq') hNotObs)
    n i hReq

-- Rule30 concrete witness composition: a pointwise-difference witness at i <= 2n
-- is enough to discharge the required-index observation bridge directly.
theorem must_observe_required_rule30_of_pointwise_diff_witness
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          target n s1 ≠ target n s2) :
    forall n i, requiredAt n i -> A.observes n i := by
  intro n i hReq
  exact must_observe_required_of_le_two_mul_witness
    (cell := rule30Cell) A target h_obs_det h_exact
    (witness_le_two_mul_of_pointwise_diff A target hConcrete) n i hReq

-- Concrete center-slice specialization: exact center-cell target at generation n.
theorem must_observe_required_rule30_center_of_pointwise_diff_witness
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n) :
    forall n i, requiredAt n i -> A.observes n i := by
  intro n i hReq
  exact must_observe_required_rule30_of_pointwise_diff_witness
    A (fun n s => rule30Cell s n) h_obs_det h_exact hConcrete n i hReq

-- Rule30 next-generation no-skip composition: reuses the same concrete
-- pointwise-difference witness adapter at generation n+1.
theorem must_observe_required_next_gen_rule30_of_pointwise_diff_witness
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          target n s1 ≠ target n s2) :
    forall n i, requiredAt (n + 1) i -> A.observes (n + 1) i := by
  intro n i hReq
  exact must_observe_required_of_le_two_mul_witness
    (cell := rule30Cell) A target h_obs_det h_exact
    (witness_le_two_mul_of_pointwise_diff A target hConcrete) (n + 1) i hReq

-- Concrete center-slice specialization at generation n+1.
theorem must_observe_required_next_gen_rule30_center_of_pointwise_diff_witness
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n) :
    forall n i, requiredAt (n + 1) i -> A.observes (n + 1) i := by
  intro n i hReq
  exact must_observe_required_next_gen_rule30_of_pointwise_diff_witness
    A (fun n s => rule30Cell s n) h_obs_det h_exact hConcrete n i hReq

-- Rule30 no-skip adapter in non-beyond-boundary form at generation n.
theorem must_observe_of_not_two_mul_lt_rule30_of_pointwise_diff_witness
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          target n s1 ≠ target n s2) :
    forall n i, ¬ (2 * n < i) -> A.observes n i := by
  intro n i hNotLt
  have hReq : requiredAt n i := (requiredAt_iff_le_two_mul n i).2 (Nat.le_of_not_gt hNotLt)
  exact must_observe_required_rule30_of_pointwise_diff_witness
    A target h_obs_det h_exact hConcrete n i hReq

-- Concrete center-slice specialization of non-beyond-boundary no-skip at generation n.
theorem must_observe_of_not_two_mul_lt_rule30_center_of_pointwise_diff_witness
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n) :
    forall n i, ¬ (2 * n < i) -> A.observes n i := by
  intro n i hNotLt
  exact must_observe_of_not_two_mul_lt_rule30_of_pointwise_diff_witness
    A (fun n s => rule30Cell s n) h_obs_det h_exact hConcrete n i hNotLt

-- Rule30 no-skip adapter in non-beyond-boundary form at generation n+1.
theorem must_observe_next_gen_of_not_two_mul_add_two_lt_rule30_of_pointwise_diff_witness
    (A : Algorithm Rule30State)
    (target : Nat -> Rule30State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          target n s1 ≠ target n s2) :
    forall n i, ¬ (2 * n + 2 < i) -> A.observes (n + 1) i := by
  intro n i hNotLt
  have hLe' : i <= 2 * n + 2 := Nat.le_of_not_gt hNotLt
  have hLe : i <= 2 * (n + 1) := by
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLe'
  have hReq : requiredAt (n + 1) i := (requiredAt_iff_le_two_mul (n + 1) i).2 hLe
  exact must_observe_required_next_gen_rule30_of_pointwise_diff_witness
    A target h_obs_det h_exact hConcrete n i hReq

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

-- Next-generation corollary of the boundary-index witness adapter.
theorem must_observe_required_next_gen_of_le_two_mul_witness
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness_le_two_mul :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2) :
    forall n i, requiredAt (n + 1) i -> A.observes (n + 1) i := by
  intro n i hReq
  exact must_observe_required_of_le_two_mul_witness
    (cell := cell) A target h_obs_det h_exact h_witness_le_two_mul (n + 1) i hReq

-- Next-generation requiredness can be split into strict-prefix-or-endpoint form.
theorem requiredAt_next_gen_iff_lt_two_mul_add_two_or_eq_two_mul_add_two (n i : Nat) :
    requiredAt (n + 1) i ↔ i < 2 * n + 2 ∨ i = 2 * n + 2 := by
  constructor
  · intro hReq
    have hLe : i <= 2 * n + 2 := (requiredAt_next_gen_iff_le_two_mul_add_two n i).1 hReq
    exact Nat.lt_or_eq_of_le hLe
  · intro hSplit
    rcases hSplit with hLt | hEq
    · exact (requiredAt_next_gen_iff_le_two_mul_add_two n i).2 (Nat.le_of_lt hLt)
    · rw [hEq]
      exact (requiredAt_next_gen_iff_le_two_mul_add_two n (2 * n + 2)).2 (Nat.le_refl (2 * n + 2))

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

-- Next-generation requiredness is equivalent to not being beyond 2n+2.
theorem requiredAt_iff_not_two_mul_add_two_lt_next_gen (n i : Nat) :
    requiredAt (n + 1) i ↔ ¬ (2 * n + 2 < i) := by
  constructor
  · intro hReq hLt
    exact Nat.not_lt_of_ge ((requiredAt_next_gen_iff_le_two_mul_add_two n i).1 hReq) hLt
  · intro hNotLt
    exact requiredAt_of_not_two_mul_add_two_lt_next_gen n i hNotLt

-- Center-target witness in direct next-generation requiredAt form from
-- non-beyond-boundary concrete hypotheses (¬(2n+2 < i)).
theorem witness_rule30_center_requiredAt_next_gen_of_pointwise_diff_not_two_mul_add_two_lt
    (A : Algorithm Rule30State)
    (hConcreteCenterNotTwoMulAddTwoLt :
      forall n i,
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 (n + 1) ≠ rule30Cell s2 (n + 1)) :
    forall n i,
      requiredAt (n + 1) i ->
      ¬ (A.observes (n + 1) i) ->
      exists s1 s2,
        agreesOnObserved rule30Cell A (n + 1) s1 s2 /\
        rule30Cell s1 (n + 1) ≠ rule30Cell s2 (n + 1) := by
  intro n i hReq hNotObs
  rcases hConcreteCenterNotTwoMulAddTwoLt n i
      ((requiredAt_iff_not_two_mul_add_two_lt_next_gen n i).1 hReq) hNotObs with
      ⟨s1, s2, hEqExcept, hTargetNe⟩
  refine ⟨s1, s2, ?_, hTargetNe⟩
  intro j hObs
  exact hEqExcept j (by
    intro hji
    apply hNotObs
    simpa [hji] using hObs)

-- Package the next-generation non-beyond-boundary requiredAt witness adapter
-- as a per-generation witness family at index generation `n+1`.
theorem rule30CenterWitnessAt_next_gen_rule30_center_of_pointwise_diff_not_two_mul_add_two_lt
    (A : Algorithm Rule30State)
    (hConcreteCenterNotTwoMulAddTwoLt :
      forall n i,
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 (n + 1) ≠ rule30Cell s2 (n + 1)) :
    forall n, Rule30CenterWitnessAt A (fun k s => rule30Cell s k) (n + 1) := by
  intro n i hReq hNotObs
  exact witness_rule30_center_requiredAt_next_gen_of_pointwise_diff_not_two_mul_add_two_lt
    A hConcreteCenterNotTwoMulAddTwoLt n i hReq hNotObs

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

-- Requiredness is equivalent to not being beyond 2n.
theorem requiredAt_iff_not_two_mul_lt (n i : Nat) : requiredAt n i ↔ ¬ (2 * n < i) := by
  constructor
  · intro hReq hLt
    exact Nat.not_lt_of_ge ((requiredAt_iff_le_two_mul n i).1 hReq) hLt
  · intro hNotLt
    exact requiredAt_of_not_two_mul_lt n i hNotLt

-- Boundary-complement witness adapter: discharge the bridge using the equivalent
-- non-beyond-boundary form ¬(2n < i) instead of requiredAt n i.
theorem must_observe_required_of_not_two_mul_lt_witness
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness_not_two_mul_lt :
      forall n i,
        ¬ (2 * n < i) ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2) :
    forall n i, requiredAt n i -> A.observes n i := by
  intro n i hReq
  exact must_observe_required (cell := cell) A target h_obs_det h_exact
    (fun n' i' hReq' hNotObs =>
      h_witness_not_two_mul_lt n' i' ((requiredAt_iff_not_two_mul_lt n' i').1 hReq') hNotObs)
    n i hReq

-- Concrete Rule30 center-target no-skip composition from non-beyond-boundary
-- witness assumptions at generation n.
theorem must_observe_required_rule30_center_of_pointwise_diff_witness_not_two_mul_lt
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcreteCenterNotTwoMulLt :
      forall n i,
        ¬ (2 * n < i) ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n) :
    forall n i, requiredAt n i -> A.observes n i := by
  intro n i hReq
  exact must_observe_required (cell := rule30Cell) A (fun k s => rule30Cell s k) h_obs_det h_exact
    (witness_rule30_center_requiredAt_of_pointwise_diff_not_two_mul_lt A hConcreteCenterNotTwoMulLt)
    n i hReq

-- Next-generation corollary of the boundary-complement witness adapter.
theorem must_observe_required_next_gen_of_not_two_mul_lt_witness
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness_not_two_mul_lt :
      forall n i,
        ¬ (2 * n < i) ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          agreesOnObserved cell A n s1 s2 /\ target n s1 ≠ target n s2) :
    forall n i, requiredAt (n + 1) i -> A.observes (n + 1) i := by
  intro n i hReq
  exact must_observe_required_of_not_two_mul_lt_witness
    (cell := cell) A target h_obs_det h_exact h_witness_not_two_mul_lt (n + 1) i hReq

-- Next-generation boundary-complement adapter with a direct n+1 arithmetic shape:
-- witness obligations are stated as ¬(2n+2 < i), avoiding rewrites through 2*(n+1).
theorem must_observe_required_next_gen_of_not_two_mul_add_two_lt_witness
    (A : Algorithm State)
    (target : Nat -> State -> Bool)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A target)
    (h_witness_not_two_mul_add_two_lt :
      forall n i,
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          agreesOnObserved cell A (n + 1) s1 s2 /\ target (n + 1) s1 ≠ target (n + 1) s2) :
    forall n i, requiredAt (n + 1) i -> A.observes (n + 1) i := by
  intro n i hReq
  by_cases hObs : A.observes (n + 1) i
  · exact hObs
  · rcases h_witness_not_two_mul_add_two_lt n i
      ((requiredAt_iff_not_two_mul_add_two_lt_next_gen n i).1 hReq) hObs with
      ⟨s1, s2, hAgree, hTargetNe⟩
    have hRunEq : A.run (n + 1) s1 = A.run (n + 1) s2 := h_obs_det (n + 1) s1 s2 hAgree
    have hTargetEq : target (n + 1) s1 = target (n + 1) s2 := by
      rw [← h_exact (n + 1) s1, ← h_exact (n + 1) s2]
      exact hRunEq
    exact False.elim (hTargetNe hTargetEq)

-- Concrete center-slice next-generation no-skip in explicit non-beyond-boundary
-- form: witness assumptions are stated as ¬(2n+2 < i).
theorem must_observe_required_next_gen_rule30_center_of_pointwise_diff_witness_not_two_mul_add_two_lt
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcreteCenterNotTwoMulAddTwoLt :
      forall n i,
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 (n + 1) ≠ rule30Cell s2 (n + 1)) :
    forall n i, requiredAt (n + 1) i -> A.observes (n + 1) i := by
  intro n i hReq
  exact must_observe_required_next_gen_of_not_two_mul_add_two_lt_witness
    (cell := rule30Cell) A (fun k s => rule30Cell s k) h_obs_det h_exact
    (fun n' i' hNotLt hNotObs =>
      witness_rule30_center_requiredAt_next_gen_of_pointwise_diff_not_two_mul_add_two_lt
        A hConcreteCenterNotTwoMulAddTwoLt n' i'
        (requiredAt_of_not_two_mul_add_two_lt_next_gen n' i' hNotLt) hNotObs) n i hReq

-- Direct center-slice next-generation corollary in non-beyond-boundary form.
theorem must_observe_next_gen_of_not_two_mul_add_two_lt_rule30_center_of_pointwise_diff_witness
    (A : Algorithm Rule30State)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcreteCenterNotTwoMulAddTwoLt :
      forall n i,
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 (n + 1) ≠ rule30Cell s2 (n + 1)) :
    forall n i, ¬ (2 * n + 2 < i) -> A.observes (n + 1) i := by
  intro n i hNotLt
  exact must_observe_required_next_gen_rule30_center_of_pointwise_diff_witness_not_two_mul_add_two_lt
    A h_obs_det h_exact hConcreteCenterNotTwoMulAddTwoLt n i
    (requiredAt_of_not_two_mul_add_two_lt_next_gen n i hNotLt)

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

-- Arithmetic contrapositive form: unobserved at n implies index is beyond 2n.
theorem not_observes_implies_two_mul_lt_of_exact
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
    forall n i, ¬ (A.observes n i) -> 2 * n < i := by
  intro n i hNotObs
  exact (not_requiredAt_iff_two_mul_lt n i).1
    (not_observes_implies_not_required_of_exact
      (cell := cell) A target h_obs_det h_exact h_witness n i hNotObs)

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

-- Next-generation arithmetic contrapositive: unobserved at n+1 is beyond 2n+2.
theorem not_observes_next_gen_implies_two_mul_add_two_lt_next_gen_of_exact
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
    forall n i, ¬ (A.observes (n + 1) i) -> 2 * n + 2 < i := by
  intro n i hNotObs
  exact (not_requiredAt_iff_two_mul_add_two_lt_next_gen n i).1
    (not_observes_next_gen_implies_not_required_next_gen_of_exact
      (cell := cell) A target h_obs_det h_exact h_witness n i hNotObs)

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

-- Next-generation existence form: exactness also forces an observed required
-- index at generation n+1.
theorem exists_observed_required_next_gen_of_exact
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
    forall n, exists i, requiredAt (n + 1) i /\ A.observes (n + 1) i := by
  intro n
  refine ⟨2 * n + 2, requiredAt_two_mul_add_two_next_gen n, ?_⟩
  exact observes_two_mul_add_two_next_gen_of_exact (cell := cell) A target h_obs_det h_exact h_witness n

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

-- Immediate weakening of the next-generation endpoint bound.
theorem work_ge_requiredCells_implies_two_mul_add_one_next_gen
    (work : Nat -> Nat)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, 2 * n + 1 <= work (n + 1) := by
  intro n
  exact Nat.le_trans (Nat.le_succ (2 * n + 1))
    (work_ge_requiredCells_implies_two_mul_add_two_next_gen work h_account n)

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

-- Split+bound packaging at generation n: every index is observed or not required,
-- and required indices are explicitly bounded by work.
theorem observes_or_not_required_and_required_le_work_of_exact_and_accounting
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
    forall n i, (A.observes n i ∨ ¬ requiredAt n i) /\ (requiredAt n i -> i <= work n) := by
  intro n i
  constructor
  · exact observes_or_not_required_of_exact (cell := cell) A target h_obs_det h_exact h_witness n i
  · intro hReq
    exact work_ge_requiredCells_implies_requiredAt_le_work work h_account n i hReq

-- Next-generation split+bound packaging in explicit n+1 form.
theorem observes_or_not_required_next_gen_and_required_le_work_of_exact_and_accounting
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
    forall n i, (A.observes (n + 1) i ∨ ¬ requiredAt (n + 1) i) /\
      (requiredAt (n + 1) i -> i <= work (n + 1)) := by
  intro n i
  constructor
  · exact observes_or_not_required_next_gen_of_exact (cell := cell) A target h_obs_det h_exact h_witness n i
  · intro hReq
    exact work_ge_requiredCells_implies_requiredAt_next_gen_le_work work h_account n i hReq

-- Non-beyond-boundary adapter at generation n: if i is not beyond 2n,
-- exactness+witness+accounting force both observation and work bound.
theorem observed_and_bounded_of_not_two_mul_lt_of_exact_and_accounting
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
    forall n i, ¬ (2 * n < i) -> (A.observes n i /\ i <= work n) := by
  intro n i hNotLt
  exact required_observed_and_bounded_of_exact_and_accounting
    (cell := cell) A target work h_obs_det h_exact h_witness h_account n i
    (requiredAt_of_not_two_mul_lt n i hNotLt)

-- Non-beyond-boundary adapter at generation n+1 in explicit 2n+2 form.
theorem observed_and_bounded_of_not_two_mul_add_two_lt_next_gen_of_exact_and_accounting
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
    forall n i, ¬ (2 * n + 2 < i) -> (A.observes (n + 1) i /\ i <= work (n + 1)) := by
  intro n i hNotLt
  exact required_observed_and_bounded_next_gen_of_exact_and_accounting
    (cell := cell) A target work h_obs_det h_exact h_witness h_account n i
    (requiredAt_of_not_two_mul_add_two_lt_next_gen n i hNotLt)

-- Boundary-form adapter at generation n: i <= 2n gives observation and work bound.
theorem observed_and_bounded_of_le_two_mul_of_exact_and_accounting
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
    forall n i, i <= 2 * n -> (A.observes n i /\ i <= work n) := by
  intro n i hLe
  exact required_observed_and_bounded_of_exact_and_accounting
    (cell := cell) A target work h_obs_det h_exact h_witness h_account n i
    (requiredAt_of_le_two_mul n i hLe)

-- Concrete Rule30 center-target specialization of the n-generation boundary form:
-- if i <= 2n, exactness+witness+accounting force observation and work bound.
theorem observed_and_bounded_rule30_center_of_le_two_mul_of_pointwise_diff_witness_and_accounting
    (A : Algorithm Rule30State)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n)
    (h_account : forall n, requiredCells n <= work n) :
    forall n i, i <= 2 * n -> (A.observes n i /\ i <= work n) := by
  intro n i hLe
  exact observed_and_bounded_of_le_two_mul_of_exact_and_accounting
    (cell := rule30Cell) A (fun k s => rule30Cell s k) work h_obs_det h_exact
    (witness_rule30_center_requiredAt_of_pointwise_diff A hConcrete) h_account n i hLe

-- Concrete Rule30 center-target non-beyond-boundary specialization at generation n:
-- if i is not beyond 2n, exactness+witness+accounting force observation and work bound.
theorem observed_and_bounded_rule30_center_of_not_two_mul_lt_of_pointwise_diff_witness_and_accounting
    (A : Algorithm Rule30State)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcreteCenterNotTwoMulLt :
      forall n i,
        ¬ (2 * n < i) ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n)
    (h_account : forall n, requiredCells n <= work n) :
    forall n i, ¬ (2 * n < i) -> (A.observes n i /\ i <= work n) := by
  intro n i hNotLt
  have hReq : requiredAt n i := requiredAt_of_not_two_mul_lt n i hNotLt
  constructor
  · exact must_observe_required_rule30_center_of_pointwise_diff_witness_not_two_mul_lt
      A h_obs_det h_exact hConcreteCenterNotTwoMulLt n i hReq
  · exact work_ge_requiredCells_implies_requiredAt_le_work work h_account n i hReq

-- Boundary-form adapter at generation n+1: i <= 2n+2 gives observation and work bound.
theorem observed_and_bounded_next_gen_of_le_two_mul_add_two_of_exact_and_accounting
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
    forall n i, i <= 2 * n + 2 -> (A.observes (n + 1) i /\ i <= work (n + 1)) := by
  intro n i hLe
  exact required_observed_and_bounded_next_gen_of_exact_and_accounting
    (cell := cell) A target work h_obs_det h_exact h_witness h_account n i
    ((requiredAt_next_gen_iff_le_two_mul_add_two n i).2 hLe)

-- Concrete Rule30 center-target specialization of the next-generation boundary form:
-- if i <= 2n+2, exactness+witness+accounting force observation and work bound at n+1.
theorem observed_and_bounded_next_gen_rule30_center_of_le_two_mul_add_two_of_pointwise_diff_witness_and_accounting
    (A : Algorithm Rule30State)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n)
    (h_account : forall n, requiredCells n <= work n) :
    forall n i, i <= 2 * n + 2 -> (A.observes (n + 1) i /\ i <= work (n + 1)) := by
  intro n i hLe
  exact observed_and_bounded_next_gen_of_le_two_mul_add_two_of_exact_and_accounting
    (cell := rule30Cell) A (fun k s => rule30Cell s k) work h_obs_det h_exact
    (witness_rule30_center_requiredAt_of_pointwise_diff A hConcrete) h_account n i hLe

-- Concrete Rule30 center-target endpoint specialization at generation n+1.
theorem endpoint_next_gen_observed_and_bounded_rule30_center_of_pointwise_diff_witness_and_accounting
    (A : Algorithm Rule30State)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, (A.observes (n + 1) (2 * n + 2) /\ 2 * n + 2 <= work (n + 1)) := by
  intro n
  exact observed_and_bounded_next_gen_rule30_center_of_le_two_mul_add_two_of_pointwise_diff_witness_and_accounting
    A work h_obs_det h_exact hConcrete h_account n (2 * n + 2) (Nat.le_refl (2 * n + 2))

-- Concrete Rule30 center-target next-generation non-beyond-boundary specialization:
-- if i is not beyond 2n+2, exactness+witness+accounting force observation and work bound.
theorem observed_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting
    (A : Algorithm Rule30State)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcreteCenterNotTwoMulAddTwoLt :
      forall n i,
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 (n + 1) ≠ rule30Cell s2 (n + 1))
    (h_account : forall n, requiredCells n <= work n) :
    forall n i, ¬ (2 * n + 2 < i) -> (A.observes (n + 1) i /\ i <= work (n + 1)) := by
  intro n i hNotLt
  have hReq : requiredAt (n + 1) i := requiredAt_of_not_two_mul_add_two_lt_next_gen n i hNotLt
  constructor
  · exact must_observe_required_next_gen_rule30_center_of_pointwise_diff_witness_not_two_mul_add_two_lt
      A h_obs_det h_exact hConcreteCenterNotTwoMulAddTwoLt n i hReq
  · exact work_ge_requiredCells_implies_requiredAt_next_gen_le_work work h_account n i hReq

-- Concrete Rule30 center-target next-generation requiredness specialization:
-- requiredAt (n+1) i directly yields observation and work bound.
theorem observed_and_bounded_next_gen_rule30_center_of_requiredAt_of_pointwise_diff_witness_not_two_mul_add_two_lt_and_accounting
    (A : Algorithm Rule30State)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcreteCenterNotTwoMulAddTwoLt :
      forall n i,
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 (n + 1) ≠ rule30Cell s2 (n + 1))
    (h_account : forall n, requiredCells n <= work n) :
    forall n i, requiredAt (n + 1) i -> (A.observes (n + 1) i /\ i <= work (n + 1)) := by
  intro n i hReq
  exact observed_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting
    A work h_obs_det h_exact hConcreteCenterNotTwoMulAddTwoLt h_account n i
    ((requiredAt_iff_not_two_mul_add_two_lt_next_gen n i).1 hReq)

-- Concrete Rule30 center-target endpoint specialization at generation n+1
-- from the non-beyond-boundary witness form.
theorem endpoint_next_gen_observed_and_bounded_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting
    (A : Algorithm Rule30State)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcreteCenterNotTwoMulAddTwoLt :
      forall n i,
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 (n + 1) ≠ rule30Cell s2 (n + 1))
    (h_account : forall n, requiredCells n <= work n) :
    forall n, (A.observes (n + 1) (2 * n + 2) /\ 2 * n + 2 <= work (n + 1)) := by
  intro n
  exact observed_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting
    A work h_obs_det h_exact hConcreteCenterNotTwoMulAddTwoLt h_account n (2 * n + 2)
    (Nat.not_lt_of_ge (Nat.le_refl (2 * n + 2)))

-- Prefix adapter at generation n: i <= n gives observation and work bound.
theorem observed_and_bounded_of_le_n_of_exact_and_accounting
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
    forall n i, i <= n -> (A.observes n i /\ i <= work n) := by
  intro n i hLe
  exact required_observed_and_bounded_of_exact_and_accounting
    (cell := cell) A target work h_obs_det h_exact h_witness h_account n i
    (requiredAt_of_le_n n i hLe)

-- Prefix adapter at generation n+1: i <= n+1 gives observation and work bound.
theorem observed_and_bounded_next_gen_of_le_n_add_one_of_exact_and_accounting
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
    forall n i, i <= n + 1 -> (A.observes (n + 1) i /\ i <= work (n + 1)) := by
  intro n i hLe
  exact required_observed_and_bounded_next_gen_of_exact_and_accounting
    (cell := cell) A target work h_obs_det h_exact h_witness h_account n i
    (requiredAt_of_le_n (n + 1) i hLe)

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

-- Near-endpoint specialization at generation n+1: index 2n+1 is observed and work-bounded.
theorem near_endpoint_next_gen_observed_and_bounded_of_exact_and_accounting
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
    forall n, (A.observes (n + 1) (2 * n + 1) /\ 2 * n + 1 <= work (n + 1)) := by
  intro n
  exact required_observed_and_bounded_next_gen_of_exact_and_accounting
    (cell := cell) A target work h_obs_det h_exact h_witness h_account n (2 * n + 1)
    (requiredAt_of_le_two_mul_add_one_next_gen n (2 * n + 1) (Nat.le_refl (2 * n + 1)))

-- Left-endpoint specialization at generation n: index 0 is observed and work-bounded.
theorem left_endpoint_observed_and_bounded_of_exact_and_accounting
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
    forall n, (A.observes n 0 /\ 0 <= work n) := by
  intro n
  exact required_observed_and_bounded_of_exact_and_accounting
    (cell := cell) A target work h_obs_det h_exact h_witness h_account n 0 (requiredAt_zero n)

-- Left-endpoint specialization at generation n+1: index 0 is observed and work-bounded.
theorem left_endpoint_next_gen_observed_and_bounded_of_exact_and_accounting
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
    forall n, (A.observes (n + 1) 0 /\ 0 <= work (n + 1)) := by
  intro n
  exact required_observed_and_bounded_next_gen_of_exact_and_accounting
    (cell := cell) A target work h_obs_det h_exact h_witness h_account n 0 (requiredAt_zero (n + 1))

-- Existence packaging at generation n: at least one index is required, observed,
-- and bounded by work under the same conditional hypotheses.
theorem exists_observed_required_and_bounded_of_exact_and_accounting
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
    forall n, exists i, requiredAt n i /\ A.observes n i /\ i <= work n := by
  intro n
  refine ⟨0, requiredAt_zero n, ?_⟩
  constructor
  · exact must_observe_required (cell := cell) A target h_obs_det h_exact h_witness n 0 (requiredAt_zero n)
  · exact work_ge_requiredCells_implies_requiredAt_le_work work h_account n 0 (requiredAt_zero n)

-- Concrete Rule30 center-target existence packaging at generation n.
theorem exists_observed_required_and_bounded_rule30_center_of_pointwise_diff_witness_and_accounting
    (A : Algorithm Rule30State)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, exists i, requiredAt n i /\ A.observes n i /\ i <= work n := by
  intro n
  exact exists_observed_required_and_bounded_of_exact_and_accounting
    (cell := rule30Cell) A (fun k s => rule30Cell s k) work h_obs_det h_exact
    (witness_rule30_center_requiredAt_of_pointwise_diff A hConcrete) h_account n

-- Concrete Rule30 center-target existence packaging at generation n from
-- explicit non-beyond-boundary witness obligations.
theorem exists_observed_required_and_bounded_rule30_center_of_not_two_mul_lt_of_pointwise_diff_witness_and_accounting
    (A : Algorithm Rule30State)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcreteCenterNotTwoMulLt :
      forall n i,
        ¬ (2 * n < i) ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, exists i, requiredAt n i /\ A.observes n i /\ i <= work n := by
  intro n
  refine ⟨2 * n, (requiredAt_iff_le_two_mul n (2 * n)).2 (Nat.le_refl (2 * n)), ?_⟩
  exact observed_and_bounded_rule30_center_of_not_two_mul_lt_of_pointwise_diff_witness_and_accounting
    A work h_obs_det h_exact hConcreteCenterNotTwoMulLt h_account n (2 * n)
    (Nat.not_lt_of_ge (Nat.le_refl (2 * n)))

-- Concrete Rule30 center-target next-generation existence packaging.
theorem exists_observed_required_and_bounded_next_gen_rule30_center_of_pointwise_diff_witness_and_accounting
    (A : Algorithm Rule30State)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcrete :
      forall n i,
        i <= 2 * n ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n)
    (h_account : forall n, requiredCells n <= work n) :
    forall n, exists i, requiredAt (n + 1) i /\ A.observes (n + 1) i /\ i <= work (n + 1) := by
  intro n
  refine ⟨2 * n + 2, requiredAt_two_mul_add_two_next_gen n, ?_⟩
  constructor
  · exact must_observe_required_rule30_center_of_pointwise_diff_witness
      A h_obs_det h_exact hConcrete (n + 1) (2 * n + 2) (requiredAt_two_mul_add_two_next_gen n)
  · exact work_ge_requiredCells_implies_requiredAt_next_gen_le_work work h_account n
      (2 * n + 2) (requiredAt_two_mul_add_two_next_gen n)

-- Concrete Rule30 center-target next-generation existence packaging from
-- explicit non-beyond-boundary witness obligations.
theorem exists_observed_required_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting
    (A : Algorithm Rule30State)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcreteCenterNotTwoMulAddTwoLt :
      forall n i,
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 (n + 1) ≠ rule30Cell s2 (n + 1))
    (h_account : forall n, requiredCells n <= work n) :
    forall n, exists i, requiredAt (n + 1) i /\ A.observes (n + 1) i /\ i <= work (n + 1) := by
  intro n
  refine ⟨2 * n + 2, requiredAt_two_mul_add_two_next_gen n, ?_⟩
  exact endpoint_next_gen_observed_and_bounded_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting
    A work h_obs_det h_exact hConcreteCenterNotTwoMulAddTwoLt h_account n

-- Paired existence packaging across adjacent generations in non-beyond-boundary form:
-- one observed+bounded required index at generation n and one at generation n+1.
theorem exists_observed_and_bounded_rule30_center_pair_of_not_two_mul_lt_and_not_two_mul_add_two_lt
    (A : Algorithm Rule30State)
    (work : Nat -> Nat)
    (h_obs_det :
      forall n s1 s2, agreesOnObserved rule30Cell A n s1 s2 -> A.run n s1 = A.run n s2)
    (h_exact : exactFor A (fun n s => rule30Cell s n))
    (hConcreteCenterNotTwoMulLt :
      forall n i,
        ¬ (2 * n < i) ->
        ¬ (A.observes n i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 n ≠ rule30Cell s2 n)
    (hConcreteCenterNotTwoMulAddTwoLt :
      forall n i,
        ¬ (2 * n + 2 < i) ->
        ¬ (A.observes (n + 1) i) ->
        exists s1 s2,
          (forall j, j ≠ i -> rule30Cell s1 j = rule30Cell s2 j) /\
          rule30Cell s1 (n + 1) ≠ rule30Cell s2 (n + 1))
    (h_account : forall n, requiredCells n <= work n) :
    forall n,
      (exists i, requiredAt n i /\ A.observes n i /\ i <= work n) /\
      (exists i, requiredAt (n + 1) i /\ A.observes (n + 1) i /\ i <= work (n + 1)) := by
  intro n
  constructor
  · exact exists_observed_required_and_bounded_rule30_center_of_not_two_mul_lt_of_pointwise_diff_witness_and_accounting
      A work h_obs_det h_exact hConcreteCenterNotTwoMulLt h_account n
  · exact exists_observed_required_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting
      A work h_obs_det h_exact hConcreteCenterNotTwoMulAddTwoLt h_account n

-- Next-generation existence packaging: the same conditional structure at n+1.
theorem exists_observed_required_and_bounded_next_gen_of_exact_and_accounting
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
    forall n, exists i, requiredAt (n + 1) i /\ A.observes (n + 1) i /\ i <= work (n + 1) := by
  intro n
  refine ⟨2 * n + 2, requiredAt_two_mul_add_two_next_gen n, ?_⟩
  constructor
  · exact must_observe_required (cell := cell) A target h_obs_det h_exact h_witness
      (n + 1) (2 * n + 2) (requiredAt_two_mul_add_two_next_gen n)
  · exact work_ge_requiredCells_implies_requiredAt_next_gen_le_work work h_account n
      (2 * n + 2) (requiredAt_two_mul_add_two_next_gen n)

end BridgeCostComposition

end Prize3
