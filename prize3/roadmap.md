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

## Phase 3: Information-flow lemmas
- [ ] Formalize what data is required to determine center cell at generation `n`.
- [ ] Show exactness forbids skipping required dependency information under `M_cone_exact`.

## Phase 4: Lower-bound core
- [ ] Prove `Work_A(n) = Omega(n)` for every valid exact algorithm `A` in `M_cone_exact`.

## Validation command
- `lean prize3/lean/Prize3Model.lean`

## Deliverable gate
- No Prize #3 claim until Phase 4 is complete and reviewed.
