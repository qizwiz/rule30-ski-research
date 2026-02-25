# One‑Page Funding Pitch (Draft)

**Jonathan Hill** — Independent Researcher  \
**Email:** jonathan.f.hill@gmail.com  \
**X:** @_qizwiz (qizwiz)

## Problem
Rule 30 exhibits computational irreducibility. Traditional analysis is simulation‑only and offers little formal structure for reasoning about the dynamics. We need a representation that retains exact semantics while enabling structural invariants and formal proofs.

## Approach
I compile the local Rule 30 update rule into SKI combinators, then construct the global dependency cone as a **maximally shared term graph** (hash‑consed DAG). I analyze the resulting structure using **basin skeletons** (parenthetical shapes) that map onto the Tamari lattice. This creates a new coordinate system for CA evolution: **computation as structural rewriting**.

## Results
- **Formal proof (Lean 4):** Inter‑Basin Theorem — every SKI reduction step strictly changes the basin skeleton (no basin self‑loops).  
- **Empirical:** distinct subterms in the shared DAG show quadratic-scale growth over measured generations, vs. exponential AST growth without sharing.  
- **Conjecture:** basin prefix stabilization for Rule 30 center cell after $N \ge 3$.

## Why It Matters
This reframes Rule 30 from a black‑box dynamical system into a structured rewriting trajectory. It opens the door to formal invariants, new complexity bounds, and the possibility of geodesic interpretations on the Tamari lattice.

## Next Milestones (6–12 months)
1. **Formalize Basin Stabilization** in Lean using truncated basin operators.
2. **Geodesic Tests**: determine whether reduction paths are geodesics on Tamari.
3. **Tight Bounds**: derive explicit constants for the $O(N^2)$ growth under sharing.

## What Funding Enables
- Time for formalization + proof engineering
- Compute for larger CA runs
- Collaboration with rewriting systems / CA researchers

## Artifacts
- Canonical paper: `papers/rule30_rheology.canonical.pdf`
- Lean proof: `lean_proofs/InterBasin.lean`
- Repro scripts: `research/README.md`
