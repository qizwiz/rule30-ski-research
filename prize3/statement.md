# Target Statement (Frozen v1)

## Plain-language statement
Under model `M_cone_exact`, any always-correct algorithm for the Rule 30 center cell needs at least linear work as `n` grows.

## Formal target theorem (drafted for this cycle)
Let `A` be any deterministic algorithm in `M_cone_exact` that outputs the exact center-cell value `C(n)` for every `n`.
Then:

`Work_A(n) = Omega(n)`.

Equivalent quantified form:
There exist constants `c > 0` and `N0` such that for all `n >= N0`,

`Work_A(n) >= c * n`.

## Claim hygiene
- This theorem is **not proved yet** in this repository.
- Theorem progress is tracked through `prize3/roadmap.md` and `prize3/lean/` lemmas.
