# Prize3 Submission Readiness (M4 Track)

Date: 2026-03-05

This note is for funding/outreach context only. It does not claim theorem completion.

## Claim Hygiene Snapshot
- Proved (in-repo):
  - Frozen model + statement (`prize3/model.md`, `prize3/statement.md`)
  - Foundational cone/proxy lemmas in Lean (`prize3/lean/Prize3Model.lean`)
  - Conditional no-skip scaffold (`must_observe_required`) plus boundary-witness adapter lemmas (`must_observe_required_of_le_two_mul_witness`, `must_observe_required_next_gen_of_le_two_mul_witness`, `must_observe_required_of_not_two_mul_lt_witness`, `must_observe_required_next_gen_of_not_two_mul_lt_witness`, `must_observe_required_next_gen_of_not_two_mul_add_two_lt_witness`) and support lemmas including `observes_self_of_exact` and `observes_two_mul_of_exact`
  - Rule 30 concrete witness compositions from pointwise-difference interface (`must_observe_required_rule30_of_pointwise_diff_witness`, `must_observe_required_next_gen_rule30_of_pointwise_diff_witness`) plus arithmetic-normalized adapters (`must_observe_of_not_two_mul_lt_rule30_of_pointwise_diff_witness`, `must_observe_of_not_two_mul_lt_rule30_center_of_pointwise_diff_witness`, `must_observe_next_gen_of_not_two_mul_add_two_lt_rule30_of_pointwise_diff_witness`)
  - Rule 30 center-target witness adapters (`witness_rule30_center_le_two_mul_of_pointwise_diff`, `witness_rule30_center_requiredAt_of_pointwise_diff`, `witness_rule30_center_requiredAt_of_pointwise_diff_not_two_mul_lt`, `witness_rule30_center_requiredAt_next_gen_of_pointwise_diff`, `witness_rule30_center_requiredAt_next_gen_of_pointwise_diff_not_two_mul_add_two_lt`) and center-target no-skip specializations (`must_observe_required_rule30_center_of_pointwise_diff_witness`, `must_observe_required_rule30_center_of_pointwise_diff_witness_not_two_mul_lt`, `must_observe_required_next_gen_rule30_center_of_pointwise_diff_witness`, `must_observe_required_next_gen_rule30_center_of_pointwise_diff_witness_not_two_mul_add_two_lt`)
  - Witness-family induction scaffolds with explicit small-horizon base through `n <= 4` (`rule30CenterWitnessAt_of_small_horizon_le_four_and_step`, `rule30CenterWitnessAt_all_of_small_horizon_le_four_and_pointwise_next`, `rule30CenterRec_witness_all_of_small_horizon_and_pointwise_next`), still conditional on next-generation concrete witness construction.
  - Witness-family packaging adapters (`rule30CenterWitnessAt_next_gen_rule30CenterRec_of_pointwise_diff`, `rule30CenterWitnessAt_next_gen_rule30_center_of_pointwise_diff_not_two_mul_add_two_lt`) and finite-certificate soundness bridges (`essentialByWitness_iff_diffCheck_true`, `rule30WitnessCertValid_sound`) are formalized support artifacts for witness bookkeeping.
  - Bounded recursive-target next-generation witness/no-skip closure is formalized for `n <= 3` in both boundary and non-beyond-boundary forms (`rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three`, `rule30CenterRec_next_gen_pointwise_diff_witness_not_two_mul_add_two_lt_of_le_three`, `rule30CenterWitnessAt_next_gen_rule30CenterRec_of_pointwise_diff_le_three`, `observes_required_next_gen_rule30CenterRec_of_pointwise_diff_le_three`, `observes_next_gen_of_not_two_mul_add_two_lt_rule30CenterRec_of_pointwise_diff_le_three`).
  - Tail-aware adapter composition is formalized: bounded witnesses plus a tail hypothesis (`3 < n`) assemble full next-generation witness/no-skip interfaces in both boundary and non-beyond-boundary forms, with explicit shape-conversion from `¬(2n+2 < i)` tails into boundary tails and from tail essentiality hypotheses into pointwise-difference tails (`flipAtState_agree_except`, `pointwise_diff_witness_of_essentialByWitness`, `rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three_or_gt_three`, `rule30CenterRec_next_gen_pointwise_diff_witness_not_two_mul_add_two_lt_of_le_three_or_gt_three`, `rule30CenterRec_tail_pointwise_diff_witness_of_tail_not_two_mul_add_two_lt`, `rule30CenterRec_tail_pointwise_diff_witness_of_tail_essentialByWitness`, `observes_required_of_rule30CenterRec_base_and_tail_pointwise_next`, `observes_required_of_rule30CenterRec_base_and_tail_not_two_mul_add_two_lt`, `observes_required_of_rule30CenterRec_base_and_tail_essentialByWitness`, `observes_required_next_gen_rule30CenterRec_of_pointwise_diff_le_three_or_gt_three`, `observes_next_gen_of_not_two_mul_add_two_lt_rule30CenterRec_of_pointwise_diff_le_three_or_gt_three`).
  - Next-generation observation corollaries under the same explicit hypotheses (`observes_required_next_gen_of_exact`, `observes_prefix_next_gen_of_exact`)
  - Next-generation boundary support/corollaries (`requiredAt_next_gen_iff_le_two_mul_add_two`, `requiredAt_of_le_two_mul_add_one_next_gen`, `observes_two_mul_add_one_next_gen_of_exact`, `observes_two_mul_add_two_next_gen_of_exact`)
  - Next-generation requiredness decomposition support (`requiredAt_next_gen_iff_lt_two_mul_add_two_or_eq_two_mul_add_two`) for explicit strict-prefix/endpoint witness-case splits at boundary `2n+2`
  - Generation-`n` requiredness decomposition support (`requiredAt_iff_lt_two_mul_or_eq_two_mul`) for explicit strict-prefix/endpoint witness-case splits at boundary `2n`
  - Next-generation split support/corollary (`not_requiredAt_of_two_mul_add_two_lt_next_gen`, `requiredAt_or_two_mul_add_two_lt_next_gen`, `not_requiredAt_iff_two_mul_add_two_lt_next_gen`, `observes_or_two_mul_add_two_lt_next_gen_of_exact`)
  - Next-generation full-interval observation corollary (`observes_next_gen_interval_of_exact`)
  - Next-generation endpoint helpers (`requiredAt_of_le_two_mul_add_two_next_gen`, `requiredAt_two_mul_add_two_next_gen`, `not_requiredAt_two_mul_add_three_next_gen`)
  - Required-interval split lemmas (`not_requiredAt_iff_two_mul_lt`, `requiredAt_or_two_mul_lt`) for witness case partitioning
  - Non-beyond-boundary requiredness lemmas (`requiredAt_of_not_two_mul_lt`, `requiredAt_of_not_two_mul_add_two_lt_next_gen`) for direct requiredness closure in both `n` and `n+1` boundary cases
  - Non-beyond-boundary requiredness equivalences (`requiredAt_iff_not_two_mul_lt`, `requiredAt_iff_not_two_mul_add_two_lt_next_gen`) for direct witness-goal normalization in both `n` and `n+1` boundary cases
  - Exactness split corollary (`observes_or_two_mul_lt_of_exact`) for claim-safe witness branching
  - Non-beyond-boundary observation corollaries (`observes_of_not_two_mul_lt_of_exact`, `observes_of_not_two_mul_add_two_lt_next_gen_of_exact`) for direct branch closure without extra arithmetic rewrites
  - Contrapositive observation/requiredness bridge lemmas (`not_observes_implies_not_required_of_exact`, `not_observes_next_gen_implies_not_required_next_gen_of_exact`) and arithmetic contrapositive boundary forms (`not_observes_implies_two_mul_lt_of_exact`, `not_observes_next_gen_implies_two_mul_add_two_lt_next_gen_of_exact`) under the same explicit hypotheses
  - Requiredness-language splits (`observes_or_not_required_of_exact`, `observes_or_not_required_next_gen_of_exact`) under the same explicit hypotheses
  - Existence corollaries (`exists_observed_required_of_exact`, `exists_observed_required_next_gen_of_exact`) under the same explicit hypotheses
  - Conditional cost-transfer scaffold (explicit accounting hypothesis), including per-index bounds `work_ge_requiredCells_implies_requiredAt_le_work`, `work_ge_requiredCells_implies_requiredAt_next_gen_le_work` and next-generation endpoint/near-endpoint bounds `work_ge_requiredCells_implies_two_mul_add_two_next_gen`, `work_ge_requiredCells_implies_two_mul_add_one_next_gen`
  - Conditional composition scaffold joining exactness+witness+accounting hypotheses (`required_observed_and_bounded_of_exact_and_accounting`, `required_observed_and_bounded_next_gen_of_exact_and_accounting`)
  - Split+bound conditional composition packaging (`observes_or_not_required_and_required_le_work_of_exact_and_accounting`, `observes_or_not_required_next_gen_and_required_le_work_of_exact_and_accounting`) so each index has observed-or-not-required status and each required index has an explicit work bound at `n` and `n+1`
  - Boundary-form conditional composition adapters (`observed_and_bounded_of_le_two_mul_of_exact_and_accounting`, `observed_and_bounded_next_gen_of_le_two_mul_add_two_of_exact_and_accounting`) for direct `i ≤ 2n` and `i ≤ 2n+2` closure at `n` and `n+1`
  - Rule 30 center-target specializations (`observed_and_bounded_rule30_center_of_le_two_mul_of_pointwise_diff_witness_and_accounting`, `observed_and_bounded_next_gen_rule30_center_of_le_two_mul_add_two_of_pointwise_diff_witness_and_accounting`, `observed_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting`) for direct `i ≤ 2n`, `i ≤ 2n+2`, and `¬(2n+2 < i)` observation+work-bound closure at generations `n` and `n+1` under explicit center-target witness/accounting hypotheses
  - Prefix-form conditional composition adapters (`observed_and_bounded_of_le_n_of_exact_and_accounting`, `observed_and_bounded_next_gen_of_le_n_add_one_of_exact_and_accounting`) for direct `i ≤ n` and `i ≤ n+1` closure at `n` and `n+1`
  - Non-beyond-boundary conditional composition adapters (`observed_and_bounded_of_not_two_mul_lt_of_exact_and_accounting`, `observed_and_bounded_of_not_two_mul_add_two_lt_next_gen_of_exact_and_accounting`) for direct arithmetic-form closure at `n` and `n+1`
  - Endpoint-specialized conditional composition corollaries (`left_endpoint_observed_and_bounded_of_exact_and_accounting`, `left_endpoint_next_gen_observed_and_bounded_of_exact_and_accounting`, `endpoint_observed_and_bounded_of_exact_and_accounting`, `endpoint_next_gen_observed_and_bounded_of_exact_and_accounting`, `near_endpoint_next_gen_observed_and_bounded_of_exact_and_accounting`)
  - Existence-form conditional composition corollaries (`exists_observed_required_and_bounded_of_exact_and_accounting`, `exists_observed_required_and_bounded_next_gen_of_exact_and_accounting`, `exists_observed_required_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting`, `exists_observed_and_bounded_rule30_center_pair_of_not_two_mul_lt_and_not_two_mul_add_two_lt`)
  - Phase 3 obligation matrix with explicit open/closed status (`prize3/phase3_obligation_matrix.md`)
- Empirical (not proof):
  - Repro/runtime checks only; no empirical estimate is used as a Prize3 proof step.
- Conjectural / open:
  - Unbounded (all-`n`) Rule 30-specific next-generation witness construction for indistinguishability obligations
  - Full exactness-to-work bridge instantiation for `Work_A(n) = Omega(n)`

## Readiness Gates
1. Required for theorem-claim-ready external submission:
   - Rule 30 witness obligations discharged in Lean-compatible form
   - No-skip instantiated for the concrete Rule 30 target
   - Cost accounting instantiated without extra hidden assumptions
   - Independent review pass logged with explicit objection list
2. Current gate status:
   - Not claim-ready (bridge instantiation remains open).

## Safe External Status Line
"Prize3 lower-bound theorem is not yet proved in-repo."
