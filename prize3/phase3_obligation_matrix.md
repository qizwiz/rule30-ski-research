# Prize3 Phase 3 Obligation Matrix (M4)

Date: 2026-02-26

Purpose: track the exactness-bridge obligations needed before any lower-bound theorem claim.

## Claim Split
- Proved (in-repo):
  - Abstract no-skip bridge interface and logic in Lean:
    - `must_observe_required`
    - `observes_prefix_of_exact`
    - `observes_self_of_exact`
    - `observes_cone_interval_of_exact`
    - `observes_two_mul_of_exact`
    - `observes_or_two_mul_lt_of_exact`
    - `observes_required_next_gen_of_exact`
    - `observes_prefix_next_gen_of_exact`
    - `observes_two_mul_add_one_next_gen_of_exact`
    - `observes_two_mul_add_two_next_gen_of_exact`
  - Required-interval arithmetic support:
    - `requiredAt_iff_le_two_mul`
    - `requiredAt_of_le_two_mul`
    - `not_requiredAt_iff_two_mul_lt`
    - `requiredAt_of_not_two_mul_lt`
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
- Empirical (not proof):
  - Repro logs and runtime checks only.
- Conjectural / pending:
  - Rule 30 witness-construction lemmas that instantiate `h_witness`.
  - Concrete accounting bridge from observed required units to `work` (combined conditional composition lemmas now exist, but concrete Rule 30 instantiation remains open).

## Obligation Matrix
| ID | Obligation | Status | Evidence / Artifact | Notes |
|---|---|---|---|---|
| O1 | Concrete Rule 30 state/output model for bridge section | Open | `prize3/rule30_witness_obligations.md` | Must be Lean-compatible and deterministic. |
| O2 | Rule 30 indistinguishability witness discharging `h_witness` | Open | `prize3/lean/Prize3Model.lean` (interface only) | Highest-risk technical gap. |
| O3 | No-skip instantiated for concrete Rule 30 target | Open | Follows from O2 + existing bridge lemmas | Currently only abstractly proved. |
| O4 | Accounting transfer: observed required units -> `Work_A(n)` | Open | `work_ge_requiredCells_implies_requiredAt_le_work`, `work_ge_requiredCells_implies_requiredAt_next_gen_le_work`, `required_observed_and_bounded_of_exact_and_accounting`, `required_observed_and_bounded_next_gen_of_exact_and_accounting`, `endpoint_observed_and_bounded_of_exact_and_accounting`, `endpoint_next_gen_observed_and_bounded_of_exact_and_accounting`, `near_endpoint_next_gen_observed_and_bounded_of_exact_and_accounting`, `work_ge_requiredCells_implies_two_mul_add_two_next_gen`, `work_ge_requiredCells_implies_two_mul_add_one_next_gen` + prior cost-transfer scaffold in `prize3/lean/Prize3Model.lean` | Composition lemmas now combine exactness+witness+accounting hypotheses, including endpoint and near-endpoint corollaries at generation `n+1`; concrete Rule 30 instantiation is still missing. |
| O5 | Composition to final asymptotic theorem statement | Open | `prize3/statement.md` | Blocked on O2-O4. |

## Immediate Unblocked Next Steps
1. Introduce a finite-slice Rule 30 state type for generation `n`.
2. Define concrete target function for center-cell exactness on that state.
3. Prove one-index perturbation witness lemma at `i <= 2n`.
4. Map perturbation witness into the `h_witness` hypothesis form used in Lean.
