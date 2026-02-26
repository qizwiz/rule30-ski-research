# Prize3 Lower-Bound Core (M_cone_exact, draft v1)

Date: 2026-02-26

This note isolates the lower-bound core argument in a claim-hygienic way.

## Proved (in-repo artifacts)
- Model and target statement are frozen in:
  - `prize3/model.md`
  - `prize3/statement.md`
- Formalized width facts in Lean (`prize3/lean/Prize3Model.lean`):
  - `coneWidth_ge_n_plus_one`
  - `coneWidth_succ`
  - `coneWidth_monotone`
  - requirement-proxy lemmas on `requiredCells`
- Formalized conditional no-skip bridge skeleton in Lean:
  - `must_observe_required` (proved from explicit observation-determinism, exactness, and witness hypotheses)
  - `requiredAt_of_le_n` (proved: every `i ≤ n` lies in required interval under current proxy)
  - `requiredAt_iff_le_two_mul` (proved: required interval is exactly `0 ≤ i ≤ 2n`)
  - `requiredAt_of_le_two_mul` / `not_requiredAt_of_two_mul_lt` (proved: both inclusion and strict-outside exclusion at cone endpoint)
  - `requiredAt_two_mul` / `not_requiredAt_two_mul_succ` (proved boundary inclusions/exclusions)
  - `observes_prefix_of_exact` (proved: under scaffold hypotheses, exactness forces observation of every `i ≤ n`)
  - `observes_self_of_exact` (proved corollary: under same hypotheses, exactness forces observation of index `n`)
- Formalized conditional cost-transfer scaffold in Lean:
  - `work_ge_requiredCells_implies_linear_plus_one`
  - `work_ge_requiredCells_implies_linear`
  - `work_ge_requiredCells_implies_coneWidth`
  - `work_ge_requiredCells_implies_two_mul_plus_one`
  - `requiredAt_le_two_mul`

## Empirical (not proof)
- No Prize3 lower-bound empirical estimate is treated as proof in this track.
- Runtime observations from scripts are used only for debugging and reproducibility checks.

## Conjectural / pending proof obligations
- Information-flow necessity:
  - For exact center-cell computation at generation `n`, all cells in the dependency interval are information-relevant under `M_cone_exact`.
- No-skip step:
  - Any always-correct deterministic algorithm in `M_cone_exact` must process at least a linear number of dependency-relevant units.
- Final theorem:
  - `Work_A(n) = Omega(n)` for all valid exact algorithms `A`.

## Core argument scaffold
1. Define required information volume `requiredCells n` as dependency-cone width proxy.
2. Prove `requiredCells n >= n + 1` (linear lower bound on required information volume).
3. Connect required information volume to minimum work under `M_cone_exact` exactness constraints.
4. Discharge constants/quantifiers to obtain asymptotic lower bound.

## Bridge obligations (Step 3 decomposition)
- Observation model:
  - Formalize what it means for an algorithm run to have "read/resolved" a dependency-relevant unit.
- Indistinguishability lemma:
  - If two initial slices agree on all observed units but differ on at least one unobserved required unit, exact output cannot be guaranteed for both.
- No-skip consequence:
  - Any always-correct deterministic algorithm must resolve every required unit in the worst case.
- Cost transfer:
  - Use unit-cost accounting to map resolved required units to `Work_A(n)` lower bound.

## Conditional theorem fragment (proved, not yet instantiated)
- If an accounting hypothesis `requiredCells n ≤ work n` is provided, Lean now proves:
  - `n + 1 ≤ work n`
  - `n ≤ work n`
- This is a scaffold result only. It does **not** discharge the Rule 30-specific witness/accounting obligations by itself.

## Current blocker
- Step 3 is only partially formalized: abstract bridge logic is proved, but Rule 30-specific indistinguishability witness lemmas are still missing.

## Immediate next steps
1. Instantiate the abstract bridge scaffold with a concrete Rule 30 state/output model.
2. Prove Rule 30-specific witness lemmas needed by `must_observe_required`.
3. Add cost-transfer lemmas linking observed required units to `Work_A(n)`.
