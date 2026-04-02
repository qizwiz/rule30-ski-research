# arxiv Finds — Wolfram Prize 3 Relevance

Last updated: 2026-04-01 (loop-B5)

---

## Paper 1: Fast Simulation of Cellular Automata by Self-Composition
- **arxiv ID**: 2409.07065 (Sep 2024)
- **Authors**: (not extracted)
- **Relevant technique**: Self-composition to build a composite rule with radius ∝ log n, reducing simulation time from O(n²) to O(n²/log n) for generation n. Experimental results given for Rule 30.
- **Why it matters**: Establishes that Rule 30 center-cell computation has an upper bound of O(n²/log n) TIME complexity. Our Prize 3 proof gives Ω(n) QUERY complexity lower bound — these are orthogonal measures. The existence of this speedup does NOT conflict with our block-sensitivity result (query complexity lower bounds concern how many initial cells must be read, not how fast you compute once you know which cells to read). Also note: this computes the FULL row configuration, not just the center cell.
- **Verdict**: Relevant context (upper-bound landscape), NOT a threat to our proof, NOT directly usable in our proof.

---

## Paper 2: Descriptive Complexity of Sensitivity of Cellular Automata
- **arxiv ID**: 2504.05012 (Apr 2025, AUTOMATA 2025)
- **Authors**: Tom Favereau & Ville Salo
- **Relevant technique**: Classifies the computational complexity of determining whether a CA is sensitive to initial conditions (dynamical/topological sense). Result: 1D case is Π²₀-complete, 2D+ is Σ³₀-complete.
- **Why it matters**: Uses a DIFFERENT notion of "sensitivity" — topological sensitivity (EVERY cell is changed by SOME initial perturbation), not Boolean block sensitivity (which specific blocks affect which output). The two notions are orthogonal. Our proof uses block sensitivity of a specific Boolean function (rule30n n applied to a 2n+1-bit input), which is a finite, concrete object. This paper's sensitivity is about infinite-time CA behavior.
- **Verdict**: Not directly applicable. Confirms CA sensitivity is a rich topic but different branch.

---

## Paper 3: On Condensation of Block Sensitivity, Certificate Complexity and the AND/OR Decision Tree Complexity
- **arxiv ID**: 2602.01042 (Feb 2026)
- **Authors**: (not extracted)
- **Relevant technique**: Shows that block sensitivity does NOT condense under restrictions. Constructs a Boolean function with query complexity k where any restriction to O(k) variables has block sensitivity only O(k^(2/3)). Modified Rubinstein function.
- **Why it matters**: Uses exactly our complexity measures (block sensitivity, certificate complexity, query complexity). The result is an UPPER bound showing hardness does not always condense — opposite direction from what we need. Our proof directly constructs n disjoint sensitive blocks at position n, so we don't need to "condense" anything. However, this paper confirms block sensitivity is actively studied in 2026. The Rubinstein function construction might be relevant to how one builds witnesses for structured Boolean functions.
- **Verdict**: Same framework as ours, different direction. Monitor for technique transfer.

---

## Paper 4: Unpredictability and Computational Irreducibility
- **arxiv ID**: 1111.4121 (2011)
- **Authors**: Hervé Zwirn & Jean-Paul Delahaye
- **Relevant technique**: Formalizes "computational irreducibility" in the sense that no computation of the nth state of a computationally irreducible CA can be faster than simulation itself. Proves CI behavior → no algorithmic shortcut.
- **Why it matters**: Philosophical/conceptual overlap with Prize 3 (both aim to show Rule 30 requires Ω(n) work). However, this paper uses a SIMULATION TIME model (Turing machine), not QUERY complexity. The two notions of "computational effort" differ: query complexity asks which cells of the initial condition must be read; simulation time asks how many steps a TM needs. Zwirn/Delahaye's result (if applicable to Rule 30) would be in simulation time, which is weaker than our query-complexity claim in some senses (query complexity is actually a stronger statement — you must read Ω(n) cells regardless of how efficient your algorithm is once you know them).
- **Verdict**: Moral alignment, technical divergence. Their approach does not directly help close the remaining axioms.

---

## Paper 5: Rule 30: Solving the Chaos
- **arxiv ID**: 2207.13237 (Jul 2022)
- **Author**: Mayukhmali Das
- **Claims**: "Analytical solution to the Wolfram Alpha Rule 30 Problem 1" (which is: is the center column periodic?)
- **Why it matters**: If legitimate, would be huge. However: the paper is uncited, from a non-specialist, and the title phrasing ("Solving the Chaos") is non-standard. The abstract claims to address Problem 1 (periodicity), NOT Prize 3 (computational effort). If it claims the center column IS periodic, it would contradict our working assumption. If it claims NOT periodic, it would be consistent with our work.
- **Action needed**: Skeptically verify if this paper has been cited or refuted. The Wolfram Prize page (writings.stephenwolfram.com/2019/10/announcing-the-rule-30-prizes/) would list any verified solutions.
- **Verdict**: SUSPICIOUS — verify before spending effort.

---

## Summary for loop-A / proof work

**No direct technique transfer found** in this mining session. The relevant observation:

1. Query complexity (our framework) and simulation time complexity are orthogonal measures. The fast-simulation result (O(n²/log n) time) does not threaten our Ω(n) query lower bound.

2. The block sensitivity framework (2602.01042) is actively studied in 2026. No one has yet published a block sensitivity lower bound for cellular automaton functions specifically — our proof would be novel in this direction.

3. For closing the remaining axioms (m=4 Level 3+, m=22 period-131072), no arxiv papers found with applicable LFSR/algebraic techniques specific to nonlinear CA period proofs. The algebraic path remains internal to our project.

---

## Loop-B5 Mining Session — Algebraic Period Proofs for m=4/m=22

**Focus**: Can any known technique prove period bounds for center-column outputs of Rule 30
started from structured central initial configs (spike/twoSpike)? 14 papers surveyed.

---

### Paper 6: Local Nested Structure in Rule 30 (Rowland 2006)
- **Source**: Complex Systems 16 (2006) 239–258. Not on arxiv.
  PDF: https://ericrowland.github.io/papers/Local_nested_structure_in_rule_30.pdf
- **Key technique**: Right/left bijectivity of Rule 30. For left-justified Rule 30 (Rule 86),
  all columns are eventually periodic with period a power of 2 (Jen's Theorem 4, 1986).
  Rowland's Proposition 2: period of column m doubles exactly when column m−1 is eventually
  white and the column m−2 period block contains an odd number of black cells.
- **Relevance to m=22 period-131072**: Proves period-as-power-of-2 for Rule 30 columns/diagonals
  via bijectivity. BUT applies only to rightful initial conditions (left tail constant), not central
  initial conditions like twoSpike(34,22). Non-trivial adaptation needed.
- **Relevance to m=4 Level 3+ hierarchy**: Self-similar period-doubling in left diagonals is
  structurally analogous to the witness-width hierarchy (P=8,16,64,...,131072). Mechanism
  (bijectivity condition propagates left) may illuminate why the hierarchy exists.
- **Verdict: CONTEXT** — closest existing algebraic work on Rule 30 period doubling.
  Right family of ideas but does not directly transfer to central initial conditions.

### Paper 7: Global Properties of Cellular Automata (Jen 1986)
- **Source**: J. Statistical Physics 43 (1986) 219–242.
- **Key technique**: Theorem 4: eventual periodicity with period a power of 2 for columns
  of right-bijective rules from rightful initial conditions.
- **Verdict: CONTEXT** — foundational result underlying Rowland. Same limitation.

### Papers 8–14: NLFSR / nonlinear complexity / GF(2) period surveys
- arxiv:1005.2280 — embeds clock-controlled generators into linear CA; not Rule 30.
- arxiv:2602.01134 — characterizes sequences with high NFSR order; doesn't bound period.
- arxiv:2602.17148 — period proofs for Yang-Baxter CA over F_{2^n}; not Rule 30.
- arxiv:1108.3982 — renormalization of probabilistic CA; not algebraic period analysis.
- NLFSR construction papers — build maximal-period registers; opposite direction from bounding.
- arxiv:2404.16313, 2405.08479 — NFSR order / 2-adic complexity surveys; not period bounds.
- **All VERDICT: NOT RELEVANT**

---

## B5 Synthesis: Key Insight for Loop-A

**Jen-Rowland bijectivity is the right family of ideas for both open problems.**

The algebraic mechanism is: in the left-bijective form of Rule 30, the rightward causal
influence of any initial cell is strictly bounded. Once that cell's cone doesn't reach
a given column at time T, that column's value is determined by the LEFT boundary alone —
making the column output periodic with the same period as the left boundary dynamics.

**Adaptation needed for central initial conditions (twoSpike, spike):**
- In twoSpike(w, m), both tails are white after width w. The right-bijective argument
  applies to the right half; the left-bijective argument applies to the left half.
- The center-column output at time n' is the XOR of contributions from both cones.
- Once n' is large enough that twoSpike's support doesn't reach the boundary, the
  center output is determined by two "rightful-from-center" sub-problems.
- This is precisely the D-field / linearity corridor structure already in the proof!

**Implication**: The corridor proof (CausalConeLemmas.lean) IS the right adaptation of
Rowland/Jen to the central-initial-condition case. The remaining algebraic work (m=4
Level 3+, m=22 period-131072) is proving that the "nonlinear interaction term" I=F⊕G⊕1
vanishes outside the D-field support — which is what d_leftbound and nl_zero_when_both_zero
establish. The Lean proof structure already matches the right mathematical approach.

**No new technique found; algebraic barrier is confirmed genuine and unaddressed in literature.**
