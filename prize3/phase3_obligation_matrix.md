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
    - `rule30CenterRec_next_gen_pointwise_diff_witness_not_two_mul_add_two_lt_of_le_three`
    - `rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three_or_gt_three`
    - `rule30CenterRec_next_gen_pointwise_diff_witness_not_two_mul_add_two_lt_of_le_three_or_gt_three`
    - `rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three_or_tail_cert`
    - `rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three_or_tail_cert_not_two_mul_add_two_lt`
    - `rule30CenterRec_tail_pointwise_diff_witness_of_tail_not_two_mul_add_two_lt`
    - `rule30CenterWitnessAt_next_gen_rule30CenterRec_of_pointwise_diff_le_three`
    - `observes_required_next_gen_rule30CenterRec_of_pointwise_diff_le_three`
    - `observes_next_gen_of_not_two_mul_add_two_lt_rule30CenterRec_of_pointwise_diff_le_three`
    - `observes_next_gen_of_not_two_mul_add_two_lt_rule30CenterRec_of_pointwise_diff_le_three_or_gt_three`
    - `observes_required_next_gen_rule30CenterRec_of_pointwise_diff_le_three_or_gt_three`
    - `observes_required_of_rule30CenterRec_base_and_tail_pointwise_next`
    - `observes_required_of_rule30CenterRec_base_and_tail_not_two_mul_add_two_lt`
    - `rule30CenterWitnessAt_next_gen_rule30_center_of_pointwise_diff_not_two_mul_add_two_lt`
    - `flipAtState_agree_except`
    - `pointwise_diff_witness_of_essentialByWitness`
    - `essentialByWitness_iff_diffCheck_true`
    - `rule30WitnessCertValid_sound`
    - `essentialByWitness_of_rule30WitnessCertValid_true`
    - `rule30CenterRec_tail_pointwise_diff_witness_of_tail_essentialByWitness`
    - `rule30CenterRec_tail_pointwise_diff_witness_of_tail_cert`
    - `rule30CenterRec_tail_pointwise_diff_witness_of_tail_cert_not_two_mul_add_two_lt`
    - `observes_required_of_rule30CenterRec_base_and_tail_essentialByWitness`
    - `observes_required_of_rule30CenterRec_base_and_tail_cert`
    - `observes_required_of_rule30CenterRec_base_and_tail_cert_not_two_mul_add_two_lt`
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
| O2 | Rule 30 indistinguishability witness discharging `h_witness` | Open | `prize3/lean/Prize3Model.lean` (interface + adapters) | Small-horizon witness seeds and induction scaffolds cover base construction through `n <= 4`; bounded next-generation recursive-target witness construction is proved for `n <= 3` in both boundary (`i <= 2*(n+1)`) and non-beyond-boundary (`¬(2n+2 < i)`) forms. Proved tail-aware adapters now exist in both shapes, plus shape-conversion adapters from explicit non-beyond-boundary tails (`rule30CenterRec_tail_pointwise_diff_witness_of_tail_not_two_mul_add_two_lt`), from tail essentiality hypotheses (`rule30CenterRec_tail_pointwise_diff_witness_of_tail_essentialByWitness`), and from tail certificate-check hypotheses in both boundary and non-beyond-boundary forms (`rule30CenterRec_tail_pointwise_diff_witness_of_tail_cert`, `rule30CenterRec_tail_pointwise_diff_witness_of_tail_cert_not_two_mul_add_two_lt`) into boundary tails expected by full witness packaging. Certificate-tail hypotheses can now be lifted directly to a full next-generation pointwise witness family from either certificate shape (`rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three_or_tail_cert`, `rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three_or_tail_cert_not_two_mul_add_two_lt`). The concrete unbounded tail constructor itself remains open. |
| O3 | No-skip instantiated for concrete Rule 30 target | Open | Follows from O2 + existing bridge lemmas | Bounded next-generation concrete recursive-target no-skip closure is proved for `n <= 3` in both requiredAt and direct non-beyond-boundary (`¬(2n+2 < i)`) forms. Proved downstream tail-aware adapters now cover requiredAt and non-beyond-boundary next-generation forms and compose to full requiredAt closure from either tail shape (`observes_required_of_rule30CenterRec_base_and_tail_pointwise_next`, `observes_required_of_rule30CenterRec_base_and_tail_not_two_mul_add_two_lt`, `observes_required_of_rule30CenterRec_base_and_tail_essentialByWitness`, `observes_required_of_rule30CenterRec_base_and_tail_cert`, `observes_required_of_rule30CenterRec_base_and_tail_cert_not_two_mul_add_two_lt`, `observes_required_next_gen_rule30CenterRec_of_pointwise_diff_le_three_or_gt_three`, `observes_next_gen_of_not_two_mul_add_two_lt_rule30CenterRec_of_pointwise_diff_le_three_or_gt_three`), with certificate-tail consumers now covering both boundary and non-beyond-boundary certificate shapes. All-`n` closure still reduces to the same open O2 tail witness obligation (`3 < n`). |
| O4 | Accounting transfer: observed required units -> `Work_A(n)` | Open | `work_ge_requiredCells_implies_requiredAt_le_work`, `work_ge_requiredCells_implies_requiredAt_next_gen_le_work`, `required_observed_and_bounded_of_exact_and_accounting`, `required_observed_and_bounded_next_gen_of_exact_and_accounting`, `observes_or_not_required_and_required_le_work_of_exact_and_accounting`, `observes_or_not_required_next_gen_and_required_le_work_of_exact_and_accounting`, `observed_and_bounded_of_le_two_mul_of_exact_and_accounting`, `observed_and_bounded_rule30_center_of_le_two_mul_of_pointwise_diff_witness_and_accounting`, `observed_and_bounded_rule30_center_of_not_two_mul_lt_of_pointwise_diff_witness_and_accounting`, `observed_and_bounded_next_gen_of_le_two_mul_add_two_of_exact_and_accounting`, `observed_and_bounded_next_gen_rule30_center_of_le_two_mul_add_two_of_pointwise_diff_witness_and_accounting`, `observed_and_bounded_next_gen_rule30_center_of_not_two_mul_add_two_lt_of_pointwise_diff_witness_and_accounting`, `observed_and_bounded_of_le_n_of_exact_and_accounting`, `observed_and_bounded_next_gen_of_le_n_add_one_of_exact_and_accounting`, `observed_and_bounded_of_not_two_mul_lt_of_exact_and_accounting`, `observed_and_bounded_of_not_two_mul_add_two_lt_next_gen_of_exact_and_accounting`, `left_endpoint_observed_and_bounded_of_exact_and_accounting`, `left_endpoint_next_gen_observed_and_bounded_of_exact_and_accounting`, `endpoint_observed_and_bounded_of_exact_and_accounting`, `endpoint_next_gen_observed_and_bounded_of_exact_and_accounting`, `near_endpoint_next_gen_observed_and_bounded_of_exact_and_accounting`, `exists_observed_required_and_bounded_rule30_center_of_not_two_mul_lt_of_pointwise_diff_witness_and_accounting`, `work_ge_requiredCells_implies_two_mul_add_two_next_gen`, `work_ge_requiredCells_implies_two_mul_add_one_next_gen` + prior cost-transfer scaffold in `prize3/lean/Prize3Model.lean` | Composition lemmas now combine exactness+witness+accounting hypotheses, including observed-or-not-required split+bound packaging, boundary-form, prefix-form, non-beyond-boundary adapters, and Rule 30 center-target specializations at generation `n` and at generation `n+1` in both boundary and non-beyond-boundary forms; concrete full Rule 30 instantiation is still missing. |
| O5 | Composition to final asymptotic theorem statement | Open | `prize3/statement.md` | Blocked on O2-O4. |

## Immediate Unblocked Next Steps
1. Construct a concrete unbounded tail witness lemma for `3 < n` in the shape required by `rule30CenterRec_next_gen_pointwise_diff_witness_of_le_three_or_gt_three` (direct pointwise, essentiality, or certificate-check shape).
2. Instantiate a tail-aware no-skip adapter (`observes_required_of_rule30CenterRec_base_and_tail_pointwise_next` or `observes_required_of_rule30CenterRec_base_and_tail_cert`) with that concrete tail witness constructor.
3. Keep O2/O3 marked open until the tail witness constructor is machine-checked and connected through the existing adapters.
