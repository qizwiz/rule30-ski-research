# Prize3 M4 Submission Gate (Claim-Hygienic)

Date: 2026-02-27

Purpose: keep M4 progress and external readiness aligned without overstating theorem status.

## Status Snapshot
- Gate status: not claim-ready for external theorem submission.
- Required external status line: "Prize3 lower-bound theorem is not yet proved in-repo."

## Claim Split (Strict)
- Proved (in-repo):
  - Frozen model and target statement (`prize3/model.md`, `prize3/statement.md`).
  - Foundation lemmas on cone/proxy growth and monotonicity (`prize3/lean/Prize3Model.lean`).
  - Conditional bridge lemmas under explicit hypotheses (`must_observe_required`, `observes_prefix_of_exact`, `observes_self_of_exact`).
  - Witness-induction scaffolds now include explicit small-horizon base through `n <= 4` (`rule30CenterWitnessAt_of_small_horizon_le_four_and_step`, `rule30CenterWitnessAt_all_of_small_horizon_le_four_and_pointwise_next`, `rule30CenterRec_witness_all_of_small_horizon_and_pointwise_next`), still conditional on next-generation concrete witness construction.
  - Witness-family packaging adapters and finite-certificate soundness bridges (`rule30CenterWitnessAt_next_gen_rule30CenterRec_of_pointwise_diff`, `rule30CenterWitnessAt_next_gen_rule30_center_of_pointwise_diff_not_two_mul_add_two_lt`, `essentialByWitness_iff_diffCheck_true`, `rule30WitnessCertValid_sound`) are formalized as support artifacts and do not by themselves close O2/O3.
  - Rule 30 concrete witness compositions and normalized adapters under explicit pointwise-difference witness hypotheses (`must_observe_required_rule30_of_pointwise_diff_witness`, `must_observe_required_rule30_center_of_pointwise_diff_witness_not_two_mul_lt`, `must_observe_required_next_gen_rule30_of_pointwise_diff_witness`, `must_observe_of_not_two_mul_lt_rule30_of_pointwise_diff_witness`, `must_observe_of_not_two_mul_lt_rule30_center_of_pointwise_diff_witness`, `must_observe_next_gen_of_not_two_mul_add_two_lt_rule30_of_pointwise_diff_witness`, `must_observe_required_next_gen_rule30_center_of_pointwise_diff_witness_not_two_mul_add_two_lt`).
  - Conditional cost-transfer lemmas under explicit accounting hypothesis.
  - Conditional exactness+accounting composition lemmas (`required_observed_and_bounded_of_exact_and_accounting`, `required_observed_and_bounded_next_gen_of_exact_and_accounting`) plus Rule 30 center-target next-generation specializations in boundary and non-beyond-boundary forms (`observed_and_bounded_next_gen_rule30_center_of_le_two_mul_add_two_of_pointwise_diff_witness_and_accounting`, `observed_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting`) and paired consecutive-generation existence packaging (`exists_observed_and_bounded_rule30_center_pair_of_not_two_mul_lt_and_not_two_mul_add_two_lt`).
- Empirical (not proof):
  - Repro/runtime checks and script outputs only.
  - No empirical estimate is used as a proof step for Prize3.
- Conjectural / pending:
  - Rule 30-specific witness construction for indistinguishability obligations.
  - Concrete no-skip and accounting instantiation sufficient to close `Work_A(n) = Omega(n)`.

## Blocking Obligations
1. Instantiate Rule 30 state/output model into the bridge hypotheses.
2. Prove witness obligations used by `must_observe_required` for the concrete model.
3. Connect observed required units to `Work_A(n)` with explicit accounting assumptions acceptable for `M_cone_exact`.
4. Compose the instantiated bridge into the final asymptotic statement.

## Acceptance Checklist Before External Theorem Claim
- [ ] Lean artifact includes closed Rule 30 witness obligations (not placeholders).
- [ ] No-skip and cost-transfer steps are instantiated without hidden assumptions.
- [ ] Independent review note exists with explicit objection list and dispositions.
- [ ] External docs include proved/empirical/conjectural split and required status line verbatim.
- [ ] External wording is checked against `prize3/external_claim_guardrails.md`.
