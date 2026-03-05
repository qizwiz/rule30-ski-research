# Prize3 Phase 3 Obligation Matrix (M4)

Date: 2026-03-05

Purpose: track the exactness-bridge obligations needed before any lower-bound theorem claim.

## Claim Split
- Proved (in-repo):
  - Abstract no-skip bridge interface and logic in Lean:
    - `must_observe_required`
    - `must_observe_required_of_le_two_mul_witness`
    - `must_observe_required_next_gen_of_le_two_mul_witness`
    - `must_observe_required_of_not_two_mul_lt_witness`
    - `must_observe_required_next_gen_of_not_two_mul_lt_witness`
    - `must_observe_required_next_gen_of_not_two_mul_add_two_lt_witness`
    - `witness_rule30_center_le_two_mul_of_pointwise_diff`
    - `witness_rule30_center_requiredAt_of_pointwise_diff`
    - `witness_rule30_center_requiredAt_of_pointwise_diff_not_two_mul_lt`
    - `witness_rule30_center_requiredAt_next_gen_of_pointwise_diff`
    - `witness_rule30_center_requiredAt_next_gen_of_pointwise_diff_not_two_mul_add_two_lt`
    - `must_observe_required_rule30_of_pointwise_diff_witness`
    - `must_observe_required_rule30_center_of_pointwise_diff_witness`
    - `must_observe_required_rule30_center_of_pointwise_diff_witness_not_two_mul_lt`
    - `must_observe_required_next_gen_rule30_of_pointwise_diff_witness`
    - `must_observe_required_next_gen_rule30_center_of_pointwise_diff_witness`
    - `must_observe_required_next_gen_rule30_center_of_pointwise_diff_witness_not_two_mul_add_two_lt`
    - `must_observe_of_not_two_mul_lt_rule30_of_pointwise_diff_witness`
    - `must_observe_of_not_two_mul_lt_rule30_center_of_pointwise_diff_witness`
    - `must_observe_next_gen_of_not_two_mul_add_two_lt_rule30_of_pointwise_diff_witness`
    - `observes_prefix_of_exact`
    - `observes_self_of_exact`
    - `observes_cone_interval_of_exact`
    - `observes_two_mul_of_exact`
    - `observes_or_two_mul_lt_of_exact`
    - `observes_required_next_gen_of_exact`
    - `observes_prefix_next_gen_of_exact`
    - `observes_two_mul_add_one_next_gen_of_exact`
    - `observes_two_mul_add_two_next_gen_of_exact`
    - `rule30CenterWitnessAt_of_small_horizon_le_four_and_step`
    - `rule30CenterWitnessAt_all_of_small_horizon_le_four_and_pointwise_next`
    - `rule30CenterRec_witness_all_of_small_horizon_and_pointwise_next`
    - `rule30CenterWitnessAt_next_gen_rule30CenterRec_of_pointwise_diff`
    - `rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three`
    - `rule30CenterWitnessAt_next_gen_rule30CenterRec_of_pointwise_diff_le_three`
    - `observes_required_next_gen_rule30CenterRec_of_pointwise_diff_le_three`
    - `rule30CenterWitnessAt_next_gen_rule30_center_of_pointwise_diff_not_two_mul_add_two_lt`
    - `essentialByWitness_iff_diffCheck_true`
    - `rule30WitnessCertValid_sound`
  - Required-interval arithmetic support:
    - `requiredAt_iff_le_two_mul`
    - `requiredAt_iff_lt_two_mul_or_eq_two_mul`
    - `requiredAt_of_le_two_mul`
    - `not_requiredAt_iff_two_mul_lt`
    - `requiredAt_of_not_two_mul_lt`
    - `requiredAt_iff_not_two_mul_lt`
    - `requiredAt_or_two_mul_lt`
    - `requiredAt_two_mul`
    - `requiredAt_next_gen_iff_le_two_mul_add_two`
    - `requiredAt_next_gen_iff_lt_two_mul_add_two_or_eq_two_mul_add_two`
    - `requiredAt_of_le_two_mul_add_one_next_gen`
    - `requiredAt_of_le_two_mul_add_two_next_gen`
    - `requiredAt_two_mul_add_two_next_gen`
    - `not_requiredAt_two_mul_add_three_next_gen`
    - `not_requiredAt_of_two_mul_add_two_lt_next_gen`
    - `requiredAt_or_two_mul_add_two_lt_next_gen`
    - `not_requiredAt_iff_two_mul_add_two_lt_next_gen`
    - `requiredAt_of_not_two_mul_add_two_lt_next_gen`
    - `requiredAt_iff_not_two_mul_add_two_lt_next_gen`
    - `not_requiredAt_two_mul_succ`
    - `not_requiredAt_of_two_mul_lt`
    - `observes_next_gen_interval_of_exact`
    - `observes_or_two_mul_add_two_lt_next_gen_of_exact`
    - `observes_of_not_two_mul_lt_of_exact`
    - `observes_of_not_two_mul_add_two_lt_next_gen_of_exact`
    - `not_observes_implies_not_required_of_exact`
    - `not_observes_next_gen_implies_not_required_next_gen_of_exact`
    - `not_observes_implies_two_mul_lt_of_exact`
    - `not_observes_next_gen_implies_two_mul_add_two_lt_next_gen_of_exact`
    - `observes_or_not_required_of_exact`
    - `observes_or_not_required_next_gen_of_exact`
    - `exists_observed_required_of_exact`
    - `exists_observed_required_next_gen_of_exact`
    - `exists_observed_required_and_bounded_rule30_center_of_not_two_mul_lt_of_pointwise_diff_witness_and_accounting`
    - `exists_observed_required_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting`
    - `exists_observed_and_bounded_rule30_center_pair_of_not_two_mul_lt_and_not_two_mul_add_two_lt`
- Empirical (not proof):
  - Repro logs and runtime checks only.
  - Multi-lens finite-horizon artifacts:
    - `research/lens_attack/results_n6.json`
    - `research/lens_attack/summary_n6.md`
    - `research/lens_attack/witness_catalog_n7.json`
    - `research/lens_attack/witness_catalog_n7.md`
    - `research/lens_attack/adversarial_findings_n6.md`
- Conjectural / pending:
  - Global (unbounded-horizon) Rule 30 next-generation witness-construction lemmas that instantiate `hConcreteNextRec` / `h_witness`.
  - Concrete accounting bridge from observed required units to `work` (combined conditional composition lemmas now exist, but concrete Rule 30 instantiation remains open).

## Obligation Matrix
| ID | Obligation | Status | Evidence / Artifact | Notes |
|---|---|---|---|---|
| O1 | Concrete Rule 30 state/output model for bridge section | Open | `prize3/rule30_witness_obligations.md` | Must be Lean-compatible and deterministic. |
| O2 | Rule 30 indistinguishability witness discharging `h_witness` | Open | `prize3/lean/Prize3Model.lean` (interface + adapters) | Small-horizon witness seeds and induction scaffolds cover base construction through `n <= 4`; bounded next-generation recursive-target witness construction is now proved for `n <= 3`, while unbounded next-generation witness construction remains open. |
| O3 | No-skip instantiated for concrete Rule 30 target | Open | Follows from O2 + existing bridge lemmas | Bounded next-generation concrete recursive-target no-skip closure is now proved for `n <= 3`; full all-`n` instantiation remains open pending O2 unbounded closure. |
| O4 | Accounting transfer: observed required units -> `Work_A(n)` | Open | `work_ge_requiredCells_implies_requiredAt_le_work`, `work_ge_requiredCells_implies_requiredAt_next_gen_le_work`, `required_observed_and_bounded_of_exact_and_accounting`, `required_observed_and_bounded_next_gen_of_exact_and_accounting`, `observes_or_not_required_and_required_le_work_of_exact_and_accounting`, `observes_or_not_required_next_gen_and_required_le_work_of_exact_and_accounting`, `observed_and_bounded_of_le_two_mul_of_exact_and_accounting`, `observed_and_bounded_rule30_center_of_le_two_mul_of_pointwise_diff_witness_and_accounting`, `observed_and_bounded_rule30_center_of_not_two_mul_lt_of_pointwise_diff_witness_and_accounting`, `observed_and_bounded_next_gen_of_le_two_mul_add_two_of_exact_and_accounting`, `observed_and_bounded_next_gen_rule30_center_of_le_two_mul_add_two_of_pointwise_diff_witness_and_accounting`, `observed_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting`, `observed_and_bounded_of_le_n_of_exact_and_accounting`, `observed_and_bounded_next_gen_of_le_n_add_one_of_exact_and_accounting`, `observed_and_bounded_of_not_two_mul_lt_of_exact_and_accounting`, `observed_and_bounded_of_not_two_mul_add_two_lt_next_gen_of_exact_and_accounting`, `left_endpoint_observed_and_bounded_of_exact_and_accounting`, `left_endpoint_next_gen_observed_and_bounded_of_exact_and_accounting`, `endpoint_observed_and_bounded_of_exact_and_accounting`, `endpoint_next_gen_observed_and_bounded_of_exact_and_accounting`, `near_endpoint_next_gen_observed_and_bounded_of_exact_and_accounting`, `exists_observed_required_and_bounded_rule30_center_of_not_two_mul_lt_of_pointwise_diff_witness_and_accounting`, `work_ge_requiredCells_implies_two_mul_add_two_next_gen`, `work_ge_requiredCells_implies_two_mul_add_one_next_gen` + prior cost-transfer scaffold in `prize3/lean/Prize3Model.lean` | Composition lemmas now combine exactness+witness+accounting hypotheses, including observed-or-not-required split+bound packaging, boundary-form, prefix-form, non-beyond-boundary adapters, and Rule 30 center-target specializations at generation `n` and at generation `n+1` in both boundary and non-beyond-boundary forms; concrete full Rule 30 instantiation is still missing. |
| O5 | Composition to final asymptotic theorem statement | Open | `prize3/statement.md` | Blocked on O2-O4. |

## Immediate Unblocked Next Steps
1. Extend `rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three` from bounded `n <= 3` to an unbounded concrete next-generation constructor for `hConcreteNextRec`.
2. Compose the resulting unbounded constructor through `rule30CenterRec_witness_all_of_small_horizon_and_pointwise_next` to close O2 witness-family construction.
3. Lift `observes_required_next_gen_rule30CenterRec_of_pointwise_diff_le_three` from bounded `n <= 3` to all `n`, then tighten O3/O4 composition notes without upgrading theorem status.
