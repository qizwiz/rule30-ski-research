# Computational Model (Frozen v1)

This file freezes the model used by the Prize #3 track.

## Name
`M_cone_exact`

## Input
- A natural number `n` in unary cost model terms.
- Fixed initial condition: Rule 30 with a single black cell at generation 0.

## Output
- The exact center-cell bit at generation `n`.

## Allowed operations
- Deterministic computation over finite data.
- Arithmetic and indexing on machine integers.
- Evaluation of Rule 30 local transition on triples `(left, center, right)`.
- Reuse/memoization of previously computed values.

## Unit-cost accounting
`Work_A(n)` counts:
- each Rule 30 local transition evaluation as 1 unit,
- each read/write of a computed cell value as 1 unit,
- arithmetic/index operations as O(1) each.

This is a standard RAM-style accounting for exact evaluation algorithms.

## Correctness requirement
Algorithm `A` is valid iff for every `n`, it outputs the exact center-cell bit `C(n)`.

## Scope
- Worst-case asymptotic lower bound over valid algorithms in `M_cone_exact`.
- No probabilistic error is allowed.
- No external oracle for `C(n)` is allowed.

## Current status
- Model is frozen for the current proof cycle.
- Future model revisions must increment version (`Frozen v2`, etc.) and justify changes.
