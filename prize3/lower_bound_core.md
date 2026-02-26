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

## Current blocker
- Step 3 is not fully formalized yet: exactness-to-work bridge needs a precise adversarial or indistinguishability lemma in Lean.

## Immediate next steps
1. Introduce a formal notion of algorithm observation trace under `M_cone_exact`.
2. State and prove a no-skip lemma against exact correctness.
3. Refactor the final theorem statement into Lean-ready quantified form.
