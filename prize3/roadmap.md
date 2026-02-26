# Proof Roadmap (M_cone_exact, v1)

## Phase 1: Model and statement freeze
- [x] Freeze model in `prize3/model.md`.
- [x] Freeze theorem statement in `prize3/statement.md`.

## Phase 2: Foundation lemmas
- [x] `coneWidth_ge_n_plus_one`
Plain meaning: dependency cone width is already linear-scale.

- [x] `coneWidth_succ`
Plain meaning: each generation increases cone width by exactly 2.

- [x] `coneWidth_monotone`
Plain meaning: dependency cone width never decreases.

- [x] `requiredCells_succ`
Plain meaning: required-data proxy increases by exactly 2 each generation.

- [x] `requiredCells_pos`
Plain meaning: required-data proxy is always nonzero (base sanity for cost transfer).

## Phase 3: Information-flow lemmas
- [x] Formalize a first required-data proxy (`requiredCells n := coneWidth n`) in Lean.
- [x] Freeze exactness-to-work bridge obligations and theorem skeletons in `prize3/exactness_bridge.md`.
- [x] Freeze Rule 30 witness-obligation decomposition in `prize3/rule30_witness_obligations.md`.
- [x] Add abstract no-skip bridge lemma in Lean (`must_observe_required`) with explicit hypotheses.
- [x] Add prefix-observation bridge corollary in Lean (`observes_prefix_of_exact`) under scaffold hypotheses.
- [ ] Formalize what data is required to determine center cell at generation `n` (Rule 30-specific witness construction beyond proxy).
- [ ] Discharge no-skip for Rule 30 by proving witness obligations under `M_cone_exact`.

## Phase 4: Lower-bound core
- [x] Add conditional cost-transfer lemmas in Lean (`work_ge_requiredCells_implies_linear_plus_one`, `work_ge_requiredCells_implies_linear`) under explicit accounting hypothesis.
- [ ] Prove `Work_A(n) = Omega(n)` for every valid exact algorithm `A` in `M_cone_exact`.

## Validation command
- `lean prize3/lean/Prize3Model.lean`

## Deliverable gate
- No Prize #3 claim until Phase 4 is complete and reviewed.
