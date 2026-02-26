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
  - Required-interval arithmetic support:
    - `requiredAt_iff_le_two_mul`
    - `requiredAt_of_le_two_mul`
    - `requiredAt_two_mul`
    - `not_requiredAt_two_mul_succ`
    - `not_requiredAt_of_two_mul_lt`
- Empirical (not proof):
  - Repro logs and runtime checks only.
- Conjectural / pending:
  - Rule 30 witness-construction lemmas that instantiate `h_witness`.
  - Concrete accounting bridge from observed required units to `work`.

## Obligation Matrix
| ID | Obligation | Status | Evidence / Artifact | Notes |
|---|---|---|---|---|
| O1 | Concrete Rule 30 state/output model for bridge section | Open | `prize3/rule30_witness_obligations.md` | Must be Lean-compatible and deterministic. |
| O2 | Rule 30 indistinguishability witness discharging `h_witness` | Open | `prize3/lean/Prize3Model.lean` (interface only) | Highest-risk technical gap. |
| O3 | No-skip instantiated for concrete Rule 30 target | Open | Follows from O2 + existing bridge lemmas | Currently only abstractly proved. |
| O4 | Accounting transfer: observed required units -> `Work_A(n)` | Open | Cost-transfer scaffold already present | Must avoid hidden assumptions. |
| O5 | Composition to final asymptotic theorem statement | Open | `prize3/statement.md` | Blocked on O2-O4. |

## Immediate Unblocked Next Steps
1. Introduce a finite-slice Rule 30 state type for generation `n`.
2. Define concrete target function for center-cell exactness on that state.
3. Prove one-index perturbation witness lemma at `i <= 2n`.
4. Map perturbation witness into the `h_witness` hypothesis form used in Lean.
