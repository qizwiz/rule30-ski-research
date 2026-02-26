# Rule30 Witness Obligations (Phase 3, M_cone_exact)

Date: 2026-02-26

Purpose: make the Rule 30-specific witness step explicit enough to execute in Lean without mixing proved statements with pending claims.

## Proved (in-repo now)
- Abstract bridge interface and logic skeleton in `prize3/lean/Prize3Model.lean`:
  - `must_observe_required`
  - `observes_required_of_exact`
  - `observes_prefix_of_exact`
- Required-set arithmetic/proxy facts:
  - `requiredCells_ge_n_plus_one`
  - `requiredAt_of_le_n`
  - `requiredAt_self`
  - `requiredAt_monotone_gen`

## Empirical (not proof)
- None used in this witness track.
- Runtime scripts and logs are reproducibility checks only.

## Conjectural / pending proof obligations
1. Concrete Rule 30 state model for the bridge interface.
2. Local-to-global center-cell dependence lemma for generation `n`.
3. Witness constructor:
   - Input: `requiredAt n i` and `¬ A.observes n i`.
   - Output: states `s1 s2` agreeing on observed indices with different exact target outputs.
4. Cost transfer from observed required indices to `Work_A(n)` lower bound.

## Lean task decomposition
1. Define a finite-slice state model `State_n` aligned to the dependency cone.
2. Define Rule 30 center-cell target `targetCenter : Nat -> State -> Bool`.
3. Prove a finite perturbation lemma at one required index.
4. Lift perturbation to an indistinguishability witness for `h_witness`.
5. Instantiate `must_observe_required` and derive a per-`n` minimum-observation bound.
6. Add `work_ge_observed` accounting axiom/lemma under `M_cone_exact`.
7. Conclude `Work_A(n) = Omega(n)` via `requiredCells_ge_n_plus_one`.

## Blocking assumptions (must be explicit in Lean)
- Deterministic run semantics for algorithms in `M_cone_exact`.
- Observation trace meaning: `A.observes n i` corresponds to actual resolved unit-cost work.
- Rule 30 update semantics over the finite slice are extension-consistent.

## Acceptance gate for Phase 3 completion
- A Rule 30-specific witness lemma discharges the `h_witness` premise for the instantiated model.
- A separate cost-transfer lemma is present and compile-checked.
- `prize3/statement.md` still marked unproved until Phase 4 theorem is closed.
