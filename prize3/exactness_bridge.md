# Prize3 Exactness-to-Work Bridge Spec (M_cone_exact, draft v1)

Date: 2026-02-26

Purpose: freeze the missing Phase 3 bridge obligations in a Lean-ready form, without overstating proof status.

## Proved (in-repo)
- Arithmetic lower-bound scaffold for required dependency volume in `prize3/lean/Prize3Model.lean`:
  - `requiredCells_ge_n_plus_one`
  - `requiredCells_ge_n`
  - `requiredCells_succ`
  - `requiredCells_monotone`

## Empirical (not proof)
- None required for this bridge.
- Runtime tests/logs are only reproducibility checks.

## Conjectural / pending formalization
- Observation trace model for deterministic algorithms in `M_cone_exact`.
- Indistinguishability lemma:
  - If two inputs are equal on all observed required units and differ on an unobserved required unit, exact output cannot be guaranteed for both.
- No-skip lemma:
  - Any always-correct deterministic algorithm must resolve every required unit in the worst case.
- Cost transfer lemma:
  - Worst-case `Work_A(n)` lower-bounds the number of resolved required units.

## Lean-ready theorem skeletons (draft)
1. `unobserved_required_unit_breaks_exactness`
2. `exact_algorithm_reads_all_required`
3. `work_ge_requiredCells`
4. Final transfer: `Work_A(n) = Omega(n)` via `requiredCells_ge_n_plus_one`

## Blocker
- Need precise formal type for algorithm observation traces before proving indistinguishability.

## Immediate next step
- Introduce a minimal abstract `Observes A n i : Prop` interface in Lean and prove the first no-skip consequence against exactness.
