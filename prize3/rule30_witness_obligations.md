# Rule30 Witness Obligations (Phase 3, M_cone_exact)

Date: 2026-02-27

Purpose: make the Rule 30-specific witness step explicit enough to execute in Lean without mixing proved statements with pending claims.

## Proved (in-repo now)
- Abstract bridge interface and logic skeleton in `prize3/lean/Prize3Model.lean`:
  - `must_observe_required`
  - `observes_required_of_exact`
  - `observes_prefix_of_exact`
- Concrete one-step witness seeds in `prize3/lean/Prize3Model.lean`:
  - `one_step_center_witness_i0`
  - `one_step_center_witness_i1`
  - `one_step_center_witness_i2`
  - `one_step_center_witness_of_le_two`
  - `one_step_center_h_witness_seed`
- Concrete multi-step witness increment in `prize3/lean/Prize3Model.lean`:
  - `rule30CenterSmall` (small-horizon dispatcher, `n=0..4`)
  - `rule30CenterRec` (recursive center evaluator scaffold)
  - `rule30CenterRec_eq_small_of_le_four` (alignment lemma for `n <= 4`)
  - `zero_step_center_h_witness_seed`
  - `rule30CenterTwoStep`
  - `rule30CenterThreeStep`
  - `rule30CenterFourStep`
  - `two_step_center_witness_i1`
  - `two_step_center_witness_i2`
  - `two_step_center_witness_i3`
  - `two_step_center_witness_i4`
  - `two_step_center_witness_of_le_four`
  - `two_step_center_h_witness_seed_i0` (`n=2`, index `i=0`, bridge form)
  - `two_step_center_h_witness_seed` (`n=2`, full required interval)
  - `three_step_center_witness_i0..i6`
  - `three_step_center_witness_of_le_six`
  - `three_step_center_h_witness_seed` (`n=3`, full required interval)
  - `four_step_center_witness_i0..i8`
  - `four_step_center_witness_of_le_eight`
  - `four_step_center_h_witness_seed` (`n=4`, full required interval)
  - `small_horizon_center_h_witness_seed_le_four` (uniform `n <= 4` constructor)
  - `observes_required_small_horizon_of_exact_le_four` (uniform no-skip closure for `n <= 4`)
  - `small_horizon_center_h_witness_seed_rec_le_four` (rec-target constructor for `n <= 4`)
  - `observes_required_small_horizon_of_exact_rec_le_four` (rec-target no-skip closure for `n <= 4`)
  - `small_horizon_center_h_witness_seed` (uniform `n <= 3` constructor)
  - `observes_required_small_horizon_of_exact` (uniform no-skip closure for `n <= 3`)
  - `Rule30CenterWitnessAt` (per-generation witness predicate)
  - `rule30CenterWitnessAt_small_horizon` (base constructor for `n <= 3`)
  - `rule30CenterWitnessAt_small_horizon_le_four` (base constructor for `n <= 4`)
  - `rule30CenterWitnessAt_of_small_horizon_and_step` (induction scaffold)
  - `rule30CenterWitnessAt_of_small_horizon_le_four_and_step` (induction scaffold with explicit `n <= 4` base)
  - `observes_required_of_rule30CenterWitnessAt` (bridge discharge from witness family)
  - `rule30CenterWitnessAt_next_gen_of_pointwise_diff` (next-gen step adapter)
  - `rule30CenterWitnessAt_step_of_pointwise_diff` (induction-step constructor from concrete next-gen witnesses)
  - `rule30CenterWitnessAt_all_of_small_horizon_and_pointwise_next` (full witness-family constructor)
  - `rule30CenterWitnessAt_all_of_small_horizon_le_four_and_pointwise_next` (full witness-family constructor with explicit `n <= 4` base)
  - `observes_required_of_small_horizon_and_pointwise_next` (full no-skip closure from base+step inputs)
  - `observes_required_of_rule30CenterSmall_base_and_pointwise_next` (concrete-base specialization)
  - `rule30CenterRec_witness_all_of_small_horizon_and_pointwise_next` (rec-target full witness-family constructor)
  - `observes_required_of_rule30CenterRec_base_and_pointwise_next` (rec-target full no-skip closure)
- Required-set arithmetic/proxy facts:
  - `requiredCells_ge_n_plus_one`
  - `requiredAt_of_le_n`
  - `requiredAt_self`
  - `requiredAt_monotone_gen`

## Empirical (not proof)
- Sensitivity scan over finite horizons (`n = 1..7`) reports full input sensitivity for
  `f_n : {0,1}^{2n+1} -> {0,1}` (center cell after `n` steps):
  - command: `python3 scripts/rule30_sensitivity_scan.py --max-n 7`
  - log: `logs/repro/cycle-20260227-015603.md`
- Runtime scripts and logs are reproducibility checks only, not formal proof.

## Conjectural / pending proof obligations
1. Concrete Rule 30 state model for the bridge interface.
2. Local-to-global center-cell dependence lemma for generation `n`.
3. Witness constructor:
   - Input: `requiredAt n i` and `¬ A.observes n i`.
   - Output: states `s1 s2` agreeing on observed indices with different exact target outputs.
   - Status: instantiated with concrete seeds at `n=1`, `n=2`, `n=3`, and `n=4` over the full required intervals.
4. Cost transfer from observed required indices to `Work_A(n)` lower bound.

## Lean task decomposition
1. Define a finite-slice state model `State_n` aligned to the dependency cone.
2. Define Rule 30 center-cell target `targetCenter : Nat -> State -> Bool`.
3. Prove a finite perturbation lemma at one required index.
4. Lift perturbation to an indistinguishability witness for `h_witness`.
   - Scaffold now present: prove a propagation step
     `Rule30CenterWitnessAt n -> Rule30CenterWitnessAt (n+1)` and instantiate
     either `rule30CenterWitnessAt_of_small_horizon_and_step` (`n <= 3` base)
     or `rule30CenterWitnessAt_of_small_horizon_le_four_and_step` (`n <= 4` base).
   - Current bridge helper: if concrete next-gen pointwise witnesses are supplied in
     arithmetic form (`i <= 2*(n+1)`), the step constructor discharges this propagation.
5. Instantiate `must_observe_required` and derive a per-`n` minimum-observation bound.
   - Generic composition now present: base (`n <= 3` or `n <= 4`) + next-gen
     pointwise witnesses imply `forall n i, requiredAt n i -> A.observes n i`.
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
