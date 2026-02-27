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
  - `must_observe_required_of_le_two_mul_witness` (proved adapter: boundary-form witness obligations `i ≤ 2n` discharge the same bridge goal)
  - `must_observe_required_next_gen_of_le_two_mul_witness` (proved next-generation corollary of the same boundary-form adapter)
  - `requiredAt_of_le_n` (proved: every `i ≤ n` lies in required interval under current proxy)
  - `requiredAt_iff_le_two_mul` (proved: required interval is exactly `0 ≤ i ≤ 2n`)
  - `requiredAt_of_le_two_mul` / `not_requiredAt_of_two_mul_lt` (proved: both inclusion and strict-outside exclusion at cone endpoint)
  - `not_requiredAt_iff_two_mul_lt` / `requiredAt_or_two_mul_lt` (proved: exact inside/outside partition at the `2n` boundary)
  - `requiredAt_of_not_two_mul_lt` (proved: non-beyond-boundary form yields direct requiredness at generation `n`)
  - `requiredAt_iff_not_two_mul_lt` (proved: requiredness at generation `n` is exactly the non-beyond-boundary condition `¬(2n < i)`)
  - `requiredAt_two_mul` / `not_requiredAt_two_mul_succ` (proved boundary inclusions/exclusions)
  - `observes_prefix_of_exact` (proved: under scaffold hypotheses, exactness forces observation of every `i ≤ n`)
  - `observes_self_of_exact` (proved corollary: under same hypotheses, exactness forces observation of index `n`)
  - `observes_cone_interval_of_exact` / `observes_two_mul_of_exact` (proved corollaries: under scaffold hypotheses, exactness forces observation over `i ≤ 2n`, including endpoint `i = 2n`)
  - `observes_required_next_gen_of_exact` / `observes_prefix_next_gen_of_exact` (proved: under same scaffold hypotheses, required/prefix indices at generation `n` are forced observed at generation `n+1`)
  - `requiredAt_next_gen_iff_le_two_mul_add_two` / `requiredAt_of_le_two_mul_add_one_next_gen` (proved: explicit `n+1` boundary characterization and inclusion up to `2n+1`)
  - `requiredAt_next_gen_iff_lt_two_mul_add_two_or_eq_two_mul_add_two` (proved: requiredness at generation `n+1` decomposes into strict-prefix or endpoint case at boundary `2n+2`)
  - `requiredAt_of_le_two_mul_add_two_next_gen` / `requiredAt_two_mul_add_two_next_gen` / `not_requiredAt_two_mul_add_three_next_gen` (proved: explicit `n+1` endpoint inclusion and first-outside exclusion)
  - `not_requiredAt_of_two_mul_add_two_lt_next_gen` / `requiredAt_or_two_mul_add_two_lt_next_gen` / `not_requiredAt_iff_two_mul_add_two_lt_next_gen` (proved: strict-outside exclusion and exact outside characterization for the `n+1` boundary `2n+2`)
  - `requiredAt_of_not_two_mul_add_two_lt_next_gen` (proved: non-beyond-boundary form yields direct requiredness at generation `n+1`)
  - `requiredAt_iff_not_two_mul_add_two_lt_next_gen` (proved: requiredness at generation `n+1` is exactly the non-beyond-boundary condition `¬(2n+2 < i)`)
  - `observes_two_mul_add_one_next_gen_of_exact` / `observes_two_mul_add_two_next_gen_of_exact` (proved: under same scaffold hypotheses, exactness forces observation at key `n+1` boundary points)
  - `observes_next_gen_interval_of_exact` (proved: under same scaffold hypotheses, exactness forces observation for every index `i ≤ 2n+2` at generation `n+1`)
  - `observes_or_two_mul_add_two_lt_next_gen_of_exact` (proved: under same scaffold hypotheses, exactness gives observed-or-beyond split at `n+1` boundary `2n+2`)
  - `observes_of_not_two_mul_lt_of_exact` / `observes_of_not_two_mul_add_two_lt_next_gen_of_exact` (proved: under same scaffold hypotheses, non-beyond-boundary form turns split lemmas into direct observation conclusions at `n` and `n+1`)
  - `not_observes_implies_not_required_of_exact` / `not_observes_next_gen_implies_not_required_next_gen_of_exact` (proved contrapositives: under same scaffold hypotheses, unobserved implies not-required at `n` and `n+1`)
  - `not_observes_implies_two_mul_lt_of_exact` / `not_observes_next_gen_implies_two_mul_add_two_lt_next_gen_of_exact` (proved arithmetic contrapositives: under same scaffold hypotheses, unobserved implies strictly beyond the cone boundary at `n` and `n+1`)
  - `observes_or_not_required_of_exact` / `observes_or_not_required_next_gen_of_exact` (proved: under same scaffold hypotheses, exactness yields observed-or-not-required split without arithmetic side condition at `n` and `n+1`)
  - `exists_observed_required_of_exact` / `exists_observed_required_next_gen_of_exact` (proved existence corollaries: under same scaffold hypotheses, exactness forces at least one required observed index at `n` and `n+1`)
- Formalized conditional cost-transfer scaffold in Lean:
  - `work_ge_requiredCells_implies_linear_plus_one`
  - `work_ge_requiredCells_implies_linear`
  - `work_ge_requiredCells_implies_coneWidth`
  - `work_ge_requiredCells_implies_two_mul_plus_one`
  - `work_ge_requiredCells_implies_two_mul`
  - `work_ge_requiredCells_implies_two_mul_add_two_next_gen`
  - `work_ge_requiredCells_implies_two_mul_add_one_next_gen`
  - `requiredAt_le_two_mul`
  - `work_ge_requiredCells_implies_requiredAt_le_work`
  - `work_ge_requiredCells_implies_requiredAt_next_gen_le_work`
  - `required_observed_and_bounded_of_exact_and_accounting`
  - `required_observed_and_bounded_next_gen_of_exact_and_accounting`
  - `endpoint_observed_and_bounded_of_exact_and_accounting` (proved: under the same scaffold hypotheses, exactness+accounting force observation and work-bound at endpoint `i = 2n`)
  - `endpoint_next_gen_observed_and_bounded_of_exact_and_accounting` (proved: under the same scaffold hypotheses, exactness+accounting force observation and work-bound at next-generation endpoint `i = 2n+2`)
  - `near_endpoint_next_gen_observed_and_bounded_of_exact_and_accounting` (proved: under the same scaffold hypotheses, exactness+accounting force observation and work-bound at near-endpoint `i = 2n+1` in generation `n+1`)
  - `exists_observed_required_and_bounded_of_exact_and_accounting` / `exists_observed_required_and_bounded_next_gen_of_exact_and_accounting` (proved existence packagings: under the same scaffold hypotheses, there exists at least one required index that is both observed and bounded by work at `n` and `n+1`)

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
- Obligation matrix status artifact:
  - `prize3/phase3_obligation_matrix.md` (tracks open/closed obligations O1-O5 with evidence references)
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
  - For every required index `i`, `i ≤ work n`
- This is a scaffold result only. It does **not** discharge the Rule 30-specific witness/accounting obligations by itself.

## Current blocker
- Step 3 is only partially formalized: abstract bridge logic is proved, but Rule 30-specific indistinguishability witness lemmas are still missing.

## Immediate next steps
1. Instantiate the abstract bridge scaffold with a concrete Rule 30 state/output model.
2. Prove Rule 30-specific witness lemmas needed by `must_observe_required`.
3. Add cost-transfer lemmas linking observed required units to `Work_A(n)`.
