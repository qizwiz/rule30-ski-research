# Prize3 Exactness-to-Work Bridge Spec (M_cone_exact, draft v1)

Date: 2026-02-26

Purpose: freeze the missing Phase 3 bridge obligations in a Lean-ready form, without overstating proof status.

## Proved (in-repo)
- Arithmetic lower-bound scaffold for required dependency volume in `prize3/lean/Prize3Model.lean`:
  - `requiredCells_ge_n_plus_one`
  - `requiredCells_ge_n`
  - `requiredCells_succ`
  - `requiredCells_monotone`
- Conditional no-skip bridge scaffold in Lean (logic-level, hypothesis-explicit):
  - `must_observe_required`
  - `requiredAt_zero`
  - `requiredAt_iff_le_two_mul`
  - `requiredAt_two_mul`
  - `not_requiredAt_two_mul_succ`

## Empirical (not proof)
- None required for this bridge.
- Runtime tests/logs are only reproducibility checks.

## Conjectural / pending formalization
- Concrete Rule 30 state model for the abstract bridge interface (`State`, `cell`, and `target` instantiation).
- Indistinguishability witness construction specialized to Rule 30 center-cell exactness:
  - For any unobserved required index, construct two states that agree on observed units but force different exact outputs.
- Cost transfer lemma:
  - Worst-case `Work_A(n)` lower-bounds the number of resolved required units.

## Lean-ready theorem skeletons (draft)
1. `must_observe_required` (proved under explicit hypotheses)
2. Rule 30-specific witness lemma (pending)
3. `work_ge_requiredCells` (pending)
4. Final transfer: `Work_A(n) = Omega(n)` via `requiredCells_ge_n_plus_one` (pending)

## Blocker
- Need Rule 30-specific witness construction to discharge `h_witness` in `must_observe_required`.

## Immediate next step
- Instantiate the abstract bridge scaffold with a concrete Rule 30 center-cell target and prove the first witness lemma for small required indices.
