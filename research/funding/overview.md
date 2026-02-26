# Research Overview (One Page)

**Name:** Jonathan Hill
**Email:** jonathan.f.hill@gmail.com
**Handle:** @_qizwiz (qizwiz)
**Affiliation:** Independent Researcher

## Summary
This work introduces a canonical, graph-shared combinatory representation of Cellular Automata (Rule 30) using SKI calculus. The core idea is to translate local CA updates into SKI terms, evaluate the global dependency cone via hash-consed term-graph reduction, and analyze the resulting structural dynamics on the Tamari lattice. This yields a structurally tractable representation that replaces exponential AST growth with an empirically observed quadratic DAG growth, while preserving the semantics of the CA.

## Proven Result
- **Inter-Basin Theorem (Lean 4):** every SKI reduction step strictly changes the parenthetical skeleton (basin) of the expression. This establishes monotonic structural progression and rules out basin self-loops.

## Empirical Results
- **Quadratic-Scale Subterm Growth (Empirical):** direct construction of the Rule 30 center-cell dependency cone shows quadratic-scale growth in distinct subterms under maximal sharing over the measured range, versus exponential AST growth without sharing.
- **Basin Prefix Invariance:** observed prefix stability of basin skeletons for $N \ge 3$ (Basin Stabilization Conjecture).

## Why This Matters
This creates a bridge between CA dynamics and term-rewriting/associahedron geometry, enabling structural invariants and formal reasoning to be applied to systems traditionally studied only through simulation. It is a new coordinate system for cellular automata evolution.

## Roadmap (Near-Term)
1. **Formalize Basin Stabilization:** prove or refute the conjecture in Lean with a truncated basin operator.
2. **Geodesic Characterization:** test if reduction trajectories are geodesics in the Tamari lattice.
3. **Tight Complexity Bounds:** derive explicit constants for the $O(N^2)$ bound under hash-consed graph sharing.

## Prize3 Claim Snapshot (2026-02-26)
- **Proved (artifact-level):** frozen model + theorem statement + foundational cone/required-data proxy lemmas + conditional no-skip bridge scaffold (`must_observe_required`) + required-interval boundary lemmas (`requiredAt_iff_le_two_mul`, `requiredAt_two_mul`, `not_requiredAt_two_mul_succ`) + conditional cost-transfer scaffold (under explicit accounting hypothesis) in `prize3/` and `prize3/lean/Prize3Model.lean`.
- **Empirical (Prize3-specific):** none used as proof for the lower bound.
- **Conjectural / in-progress:** Rule 30-specific witness + concrete accounting instantiation still needed to complete `Work_A(n) = Omega(n)` in `M_cone_exact`.

## Submission-Readiness Gate (Prize3)
- **Gate status:** not claim-ready for a Prize3 lower-bound theorem submission.
- **Reason:** Phase 3 no-skip/exactness bridge is still open.
- **Required status line:** "Prize3 lower-bound theorem is not yet proved in-repo."
- **Safe external phrasing:** "Foundational artifacts and lemmas are in place; the final lower-bound bridge remains open."

## Artifacts
- Paper: `papers/rule30_rheology.canonical.pdf`
- Lean proof: `lean_proofs/InterBasin.lean`
- Reproducible scripts: `research/README.md`
