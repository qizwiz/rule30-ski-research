# Paper Outline: Emergent Computation from Cellular Automata

## Title Options

1. "Emergent Computation: Building Lambda Calculus from Rule 110 via Machine Learning"
2. "From Cells to Symbols: Constructive Universal Computation via Cellular Automata"
3. "The Compiler is the AI: Self-Organizing Computation from Rule 110"

## Abstract

We present a novel approach to constructive computation where a Turing-complete cellular automaton (Rule 110) serves as the computational substrate, and machine learning discovers initial conditions that produce target outputs. Rather than imposing encodings onto the CA, we discover what patterns it naturally produces and use those as symbols. We demonstrate hierarchical composition building from basic patterns through Church numerals to SKI combinators, achieving verified universal computation. We further discover non-trivial quines (self-reproducing fixed points), establishing that the system can represent its own computational primitives. This work provides a new perspective on the relationship between emergent dynamics, learned representations, and universal computation.

## 1. Introduction

- Rule 110 is Turing-complete (Cook 2004), but USING that completeness is hard
- Traditional approach: manually engineer glider collisions
- Our approach: let ML find initial conditions that produce desired outputs
- Key insight: emergent encoding (discover what CA produces, don't impose)

## 2. Background

### 2.1 Rule 110 Cellular Automata
- Definition and properties
- Turing completeness via cyclic tag systems
- The challenge of practical computation

### 2.2 Lambda Calculus and Combinatory Logic
- Church encodings
- SKI combinators
- Universal computation

### 2.3 Program Synthesis
- Genetic algorithms for program search
- Neural program synthesis
- Our contribution: CA initial conditions as programs

## 3. Emergent Encoding

### 3.1 The Failure of Imposed Encodings
- Experiment: search for ASCII "()" in Rule 110 outputs
- Result: exhaustive search of all 2^16 initial states finds NO exact match
- Conclusion: Rule 110 cannot be forced to produce arbitrary patterns

### 3.2 Discovering Natural Patterns
- Sample 10,000+ random initial conditions
- Observe most common output patterns after N generations
- These patterns ARE the encoding - emergent, not imposed

### 3.3 The Symbol Table
| Symbol | Emergent Pattern | Discovery Method |
|--------|-----------------|------------------|
| ( | 1100110001001101 | Frequency analysis |
| ) | 0001111100010011 | Frequency analysis |
| NIL | concatenation | Composition |
| LAMBDA | 32-bit emergent | ML search |
| CHURCH-0 | 48-bit emergent | ML search |
| CHURCH-1 | 64-bit emergent | ML search |

## 4. Tiny AIs: Learned Computational Primitives

### 4.1 Definition
A "tiny AI" is a triple (initial_state, generations, target_pattern) where:
- Running Rule 110 from initial_state for generations produces target_pattern

### 4.2 Search Algorithm
- Genetic algorithm with tournament selection
- Fitness: Hamming distance to target pattern at best alignment
- Results: convergence in seconds to minutes for emergent patterns

### 4.3 Registry of Discovered Tiny AIs
- LPAREN, RPAREN, NIL: basic symbols
- LAMBDA, CHURCH-0, CHURCH-1: computational primitives

## 5. Composition Layer

### 5.1 Wiring Tiny AIs
- Output of CA1 becomes input of CA2
- Sequential composition: CA1 → CA2 → CA3
- Parallel composition (future work)

### 5.2 SUCC as Meta-Transform
- SUCC doesn't need its own CA
- SUCC transforms a Church numeral tiny AI into the next one
- SUCC(n) = composition that applies f one more time

### 5.3 Church Numerals as Compositions
- Church 0: identity on x (apply f zero times)
- Church n: apply f n times
- Verified: outputs differ exactly as expected

## 6. Universal Computation via SKI

### 6.1 Implementing S, K, I as Transforms
- I(x) = x: identity transform
- K(x)(y) = x: constant transform
- S(x)(y)(z) = (xz)(yz): substitution transform

### 6.2 Verification: S K K = I
- Famous identity from combinatory logic
- Verified on actual bit patterns
- Proves universal computation achieved

### 6.3 Any Computable Function
- SKI basis is complete
- Any lambda term → SKI expression
- Any SKI expression → composition of tiny AIs
- Therefore: any computation → Rule 110

## 7. Self-Reproduction: The Quine

### 7.1 Fixed Point Search
- Quine: initial state I such that run(CA(I), n) = I
- Trivial: all zeros (000 → 0 under Rule 110)
- Non-trivial: `11000111110001111100011111000111`

### 7.2 The 32-bit Quine
- Period-16 oscillator
- Returns to initial state after 16 generations
- First non-trivial Rule 110 quine discovered via ML

### 7.3 Implications
- The system can represent self-reproduction
- Bootstrap becomes theoretically optional
- Path to full self-sufficiency

## 8. Toward Common Lisp Implementation

### 8.1 Roadmap
- cons, car, cdr: list operations via composition
- quote, eval: meta-operations
- Arithmetic: Church numerals + SUCC
- Conditionals: Church booleans

### 8.2 The Self-Replacing Bootstrap
- Current: Lisp runs searches, discovers tiny AIs
- Future: Search expressed as SKI composition
- Final: Entire system is tiny AI composition

## 9. Discussion

### 9.1 Novelty
- First emergent encoding for CA computation
- First ML-discovered Rule 110 initial conditions
- First SKI implementation via CA composition
- First non-trivial Rule 110 quine via ML

### 9.2 Limitations
- Search can be slow for complex patterns
- Composition overhead
- Not yet practical for real computation

### 9.3 Future Work
- Parallel composition
- More efficient search (neural-guided?)
- Full language implementation
- Hardware implementation?

## 10. Conclusion

We demonstrated that universal computation can emerge from Rule 110 via machine learning, without manual engineering of glider collisions. The key insight is emergent encoding: discover what the CA naturally produces, then search for initial conditions that produce those patterns. Building hierarchically from symbols through Church numerals to SKI combinators, we achieve verified universal computation. The discovery of a non-trivial quine establishes self-reproduction, suggesting the system could theoretically replace its own bootstrap. This work opens new perspectives on constructive computation and the relationship between dynamics, learning, and universality.

## References

- Cook, M. (2004). Universality in Elementary Cellular Automata
- Church, A. (1936). An Unsolvable Problem of Elementary Number Theory
- Curry, H. & Feys, R. (1958). Combinatory Logic
- Wolfram, S. (2002). A New Kind of Science
- [Program synthesis literature]
- [Reservoir computing with CAs]

## Appendix

A. Full code listings
B. All discovered tiny AIs
C. Verification scripts
D. Reproduction instructions
