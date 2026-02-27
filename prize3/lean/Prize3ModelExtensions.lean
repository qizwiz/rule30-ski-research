import Prize3Model

namespace Prize3

-- Downstream packaging corollary at generation n: from required+observed+bounded
-- existence to observed+bounded existence under the same explicit hypotheses.
theorem exists_observed_and_bounded_rule30_center_of_not_two_mul_lt_of_pointwise_diff_witness_and_accounting
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
    forall n, exists i, A.observes n i /\ i <= work n := by
  intro n
  rcases exists_observed_required_and_bounded_rule30_center_of_not_two_mul_lt_of_pointwise_diff_witness_and_accounting
      A work h_obs_det h_exact hConcreteCenterNotTwoMulLt h_account n with
    ⟨i, _hReq, hObs, hBound⟩
  exact ⟨i, hObs, hBound⟩

-- Downstream packaging corollary at generation n+1 from the matching
-- explicit non-beyond-boundary witness obligations.
theorem exists_observed_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting
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
    forall n, exists i, A.observes (n + 1) i /\ i <= work (n + 1) := by
  intro n
  rcases exists_observed_required_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting
      A work h_obs_det h_exact hConcreteCenterNotTwoMulAddTwoLt h_account n with
    ⟨i, _hReq, hObs, hBound⟩
  exact ⟨i, hObs, hBound⟩

-- Combined packaging across consecutive generations under the same
-- explicit non-beyond-boundary witness and accounting hypotheses.
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
      (exists i, A.observes n i /\ i <= work n) /\
      (exists i, A.observes (n + 1) i /\ i <= work (n + 1)) := by
  intro n
  constructor
  · exact exists_observed_and_bounded_rule30_center_of_not_two_mul_lt_of_pointwise_diff_witness_and_accounting
      A work h_obs_det h_exact hConcreteCenterNotTwoMulLt h_account n
  · exact exists_observed_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting
      A work h_obs_det h_exact hConcreteCenterNotTwoMulAddTwoLt h_account n

end Prize3
