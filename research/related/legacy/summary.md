# Research Narrative (Legacy Summary)

This summary distills earlier informal work into a coherent narrative for current positioning.

## 1) Core Thesis Thread
- The research has consistently aimed to **turn structure into computation**: from SKI combinators and CA topology to executable knowledge and self-healing agent systems.
- Across systems, the pattern is the same: **define a formal skeleton**, then use that skeleton to drive dynamics or execution.

## 2) The Combinator / CA Line
- `ski-ca.tex` frames SKI reduction as a cellular automaton on negatively curved graphs.
- Key idea: S-reduction requires local neighborhood surplus, which appears only beyond a curvature threshold (branching >= 3).
- This earlier work sets up the present Rule 30/SKI pipeline as a natural extension: **structure matters, topology matters**, and formal reductions can be engineered.

## 3) Parenthetical / Basin Line
- `PARENTHETICAL_TEST.md` is an early operational testbed for recognizing parenthetical structure and executing it.
- This aligns directly with basin skeletons in the Rule 30 work: **parse structure, then run controlled evaluation**.

## 4) Executable Knowledge Line
- `SENTENCES_ARE_CODE.md` documents the Redis + Lisp pipeline turning conversation sentences into executable functions.
- The key insight: **knowledge is not only indexed; it is compiled and callable**.
- This line establishes practical infrastructure for formal semantics and execution, which complements the SKI/CA formalism.

## 5) Self-Healing / Agent Line
- `FULL_SYSTEM_DEMO.md`, `SELF_HEALING_SYSTEM_COMPLETE.md`, and `WHATS_NEXT.md` describe a full-stack system of hooks, MCP tools, Lisp restarts, and evolutionary fitness.
- The system is architected around **error detection, repair, and population-level resilience**.
- This is a structural analog to the rewriting dynamics in the CA work: **errors are reduced; structure is preserved**.

## 6) Convergence
The through-line is a research program that treats:
- **Structure as a substrate** (combinators, parenthetical skeletons, graph topology)
- **Execution as controlled rewriting** (SKI reduction, Lisp restarts, agent repair)
- **Scaling as sharing** (hash-consing, Redis-backed knowledge graphs, agent populations)

This positions the current Rule 30 work not as a one-off paper, but as a **coherent continuation** of a longer research arc about structural computation.
