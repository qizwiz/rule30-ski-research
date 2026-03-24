# Bridge Attacks: Objections to the Current Bridge Argument
## Updated by the attacker loop

### Attack log

**Attack 0 (2026-03-24, iteration 0 — seed):**
The fundamental problem with all three candidate paths:

1. **Against path A (universal witness):**
   Rule 30 from a single black cell has a very specific structure — the
   evolution is deterministic and symmetric. There is no reason to expect
   that flipping EVERY position k would change s(n). In fact, positions far
   from the center (near k=0 or k=2n) likely have zero influence on e_n's
   evolution because the Rule 30 triangle from a single central black cell
   doesn't reach those positions in time n. Specifically: for k near the
   boundaries, the causal cone from position k may not overlap with the
   center column at generation n when starting from e_n (which is supported
   at position n only). This would mean e_n is NOT a universal witness,
   and path A fails.

   *** Counterexample candidate: k=0. Does flipping e_n[0] change s(n)?
   The single-black-cell evolution uses all 2n+1 cells; position 0 IS in
   the light cone and IS essential for general inputs. But for e_n specifically,
   the leftmost cell starts at 0 and Rule 30 at (0,0,0) = 0, so the left
   boundary evolves trivially. The question is whether that changes the center. ***

2. **Against path B (information-theoretic):**
   This is entirely conditional on Prize 1. If the center column turns out to
   be eventually periodic (which nobody has ruled out — Prize 1 just asks us
   to prove it isn't), then s(n) IS computable in O(log n) time and space.
   So path B gives a conditional result at best.

3. **Against path C (reduction):**
   The reduction "use M to compute rule30 on general inputs" doesn't obviously
   work. To compute rule30_n(c) for general c, you'd need to somehow "inject"
   c into the single-black-cell evolution, which requires a non-trivial
   encoding. There's no obvious way to do this.

   More specifically: the single-black-cell initial condition e_n has 1 set bit.
   A general input c has up to 2n+1 set bits. You can't reduce the general
   problem to instances of the fixed-input problem without fundamentally
   changing the structure.

---

**Attack 1 (2026-03-24, bridge_attack_1.py — DECISIVE):**

PATH A IS DEAD. e_n is NOT a universal witness.

Computed for n=1..25: for every n, there are many positions k where
flipping e_n[k] does NOT change rule30_n(e_n).

| n  | total positions | sensitive | non-sensitive (sample) |
|----|----------------|-----------|------------------------|
|  1 | 3              | 2         | [2]                    |
|  5 | 11             | 4         | [2,4,6,7,8,9,10]       |
| 10 | 21             | 8         | [1,2,3,4,6,7,10,...]   |
| 15 | 31             | 15        | [3,4,6,8,12,...]       |
| 20 | 41             | 21        | [1,3,7,8,10,...]       |
| 25 | 51             | 23        | [1,5,11,15,23,...]     |

The sensitive count grows roughly as ~n, not ~2n. So e_n witnesses
about HALF the positions, not all of them.

Implication: the bridge via "e_n is a universal witness" is closed.
Our all-cells-essential theorem uses a DIFFERENT witness c* for each
position k. The single-black-cell input e_n is not the universal witness.

The query complexity of rule30_n restricted to the specific input e_n
is at most ~n (since only ~n positions are sensitive). This is weaker
than 2n+1 for general inputs.

### Most promising remaining path (updated after Attack 1)
Direct computation: verify computationally whether e_n is a universal witness.
I.e., for small n, check: for each k in {0,...,2n}, does
   rule30_n(e_n) ≠ rule30_n(flip(e_n, k))?

If YES for all k and all tested n, that IS path A working — and it would be
a computational fact that could be formalized.

If NO for some k, the bridge via path A is closed.

This is directly testable. The attacker recommends: run this check for n=1..30
and report which positions are sensitive for the specific e_n input.

---

## Attack 2 (2026-03-24)

**Script**: `research/bridge_attack_2.py`

**Claim under attack**: "D(rule30_n) = 2n+1 (proved). Does this help Prize 3?"

**The compression argument**: If a TM with O(1) working tape computes s(n) for all n,
then s(n) is eventually periodic (a finite automaton on unary input computes only
eventually-periodic sequences). If s(n) is aperiodic, no O(1)-space TM computes it.

### Computational findings (n=0..1000)

**Bit string s(0)..s(50)**:
`110111001100010110010011101011100111010101100001100`

**Density**: 481/1001 = 0.4805 (close to 0.5, no drift across sub-ranges).

**Periodicity search**: No period T ≤ 200 found with any tail start n_0 ≤ 200.
Checked all (T, n_0) pairs over 1001 data points.

**Autocorrelation** (T=1..50): All |C(T)| < 0.1. Peak at T=19, C=+0.074.
No statistically significant periodicty signal.

**Run-length analysis**: 474 runs in 1001 values, max run = 10, avg = 2.11.
No long constant stretches; consistent with pseudo-random behavior.

**Simple patterns rejected**: not constant, not period-2, not s(n) = (n mod k) mod 2
for any k ∈ {2,3,4,5}.

### The fatal gap in the compression argument

The argument is **valid but only for the wrong model**:

**Unary input model (O(1) space = finite automaton)**:
- Argument: valid. If s(n) is aperiodic, O(1)-space TM cannot compute it.
- But this only shows s(n) requires Ω(log n) bits of memory — just to store n in binary.
- This is trivially true and says nothing useful about Prize 3.

**Binary input model (standard complexity theory)**:
- A TM reading n in binary uses O(log n) bits of input.
- O(log n) working space gives 2^(O(log n)) = poly(n) states.
- The "finite automaton = eventually-periodic" argument **fails completely**.
- Log-space TMs can compute many aperiodic sequences (e.g., parity of Hamming weight
  of n is NOT eventually periodic but IS computable in O(log n) space).
- No connection between "s(n) has no short period" and "s(n) needs super-log space".

**Why this matters for the bridge**:
- Prize 3 asks whether s(n) is computable in sub-polynomial space (binary model).
- To close Prize 3 via the bridge, you need: s(n) requires Ω(n^ε) space for some ε > 0.
- The query lower bound D(rule30_n) = 2n+1 cannot deliver this — it lives in the
  worst-case-input query model, not the fixed-input space model.
- A TM computing s(n) never queries a distribution of inputs; it runs on the fixed
  integer n and can evaluate rule30 directly without any oracle.

### Verdict

The compression attack is a red herring for Prize 3 in the binary input model.

| Model | Compression argument | Conclusion |
|-------|---------------------|------------|
| Unary, O(1) space | Valid | s(n) needs Ω(log n) bits — trivial |
| Binary, O(log n) space | Fails | No conclusion possible |
| Binary, O(1) space | Valid | Prize 3 would be trivially false anyway |

**The real gap remains unchanged**: query complexity lower bounds (worst-case input,
randomized access model) do not imply space lower bounds for a fixed specific sequence.
No known technique bridges these two models without additional structural assumptions
(e.g., "the sequence is hard for circuit complexity classes", which is itself open).

---

## Attack 3 (2026-03-24)

**Script**: `research/bridge_attack_3.py`

**Claim under attack**: "Is e_n ever a universal witness — sensitive at ALL 2n+1 positions?"

This is a finer-grained rerun of Attack 1 with full position-by-position detail for n=1..20,
plus structural observations about the sensitive set S_n.

### Computational findings (n=1..20)

| n  | s(n) | \|S_n\| | \|N_n\| | \|S_n\|/(2n+1) | universal? |
|----|------|---------|---------|----------------|------------|
|  1 |    1 |       2 |       1 |          0.667 | no         |
|  2 |    0 |       1 |       4 |          0.200 | no         |
|  3 |    1 |       2 |       5 |          0.286 | no         |
|  4 |    1 |       4 |       5 |          0.444 | no         |
|  5 |    1 |       4 |       7 |          0.364 | no         |
|  6 |    0 |       4 |       9 |          0.308 | no         |
|  7 |    0 |       5 |      10 |          0.333 | no         |
|  8 |    1 |       8 |       9 |          0.471 | no         |
|  9 |    1 |       7 |      12 |          0.368 | no         |
| 10 |    0 |       8 |      13 |          0.381 | no         |
| 11 |    0 |       8 |      15 |          0.348 | no         |
| 12 |    0 |      12 |      13 |          0.480 | no         |
| 13 |    1 |      11 |      16 |          0.407 | no         |
| 14 |    0 |      11 |      18 |          0.379 | no         |
| 15 |    1 |      15 |      16 |          0.484 | no         |
| 16 |    1 |      11 |      22 |          0.333 | no         |
| 17 |    0 |      11 |      24 |          0.314 | no         |
| 18 |    0 |      17 |      20 |          0.459 | no         |
| 19 |    1 |      16 |      23 |          0.410 | no         |
| 20 |    0 |      21 |      20 |          0.512 | no         |

**e_n is NEVER a universal witness for any n in 1..20. Path A is definitively closed.**

Linear fit: |S_n| ≈ 0.887·n − 0.416 (RMSE = 1.648). So roughly |S_n| ≈ n.

### Key structural findings

**1. k=0 (left boundary) is ALWAYS sensitive** for n=1..20.
  This is consistent with the left-permutivity proof: flipping the leftmost cell
  always propagates to the centre. This gives 1 provably-sensitive position, but
  it is not enough for the bridge.

**2. k=n (centre cell of e_n) is NOT always sensitive.**
  Sensitive at n ∈ {1,3,4,5,8,9,13,15,16,19} — exactly 10 out of 20.
  NOT sensitive at n ∈ {2,6,7,10,11,12,14,17,18,20} — also 10 out of 20.
  This is striking: the cell whose initial value IS the single set bit is not
  reliably influential on the final centre output. Flipping it (turning the initial
  configuration all-zeros) changes the output for only half of n values tested.

**3. k=2n (right boundary) is almost never sensitive.**
  Sensitive only at n=8 in the entire tested range. This confirms that the
  rightmost cell contributes almost nothing to the evolution from e_n — the
  information flow is predominantly leftward (consistent with Rule 30's
  left-permutive character).

**4. S_n is NEVER mirror-symmetric** for any n in 1..20.
  Although e_n is a perfectly symmetric initial condition (single centre bit),
  Rule 30 is not left-right symmetric (it is left-permutive, not bi-permutive),
  so the causal structure is asymmetric. The sensitive set inherits this
  asymmetry fully — there is no n where S_n = {2n−k : k ∈ S_n}.

**5. The non-sensitive positions are deep interior, not just boundary effects.**
  For example, at n=6: S_6 = {0,1,2,3}, N_6 = {4,5,6,7,8,9,10,11,12}.
  The entire right half of the tape (positions 4..12) is non-sensitive.
  This is not a boundary artefact — it reflects the real causal structure of
  Rule 30 from e_n: information propagates predominantly leftward.

**6. |S_n| fluctuates irregularly around n with no clean formula.**
  The ratio |S_n|/(2n+1) varies between 0.200 (n=2) and 0.512 (n=20).
  It is not monotone. There is no obvious arithmetic formula for |S_n|.

### Verdict

Attack 3 confirms and deepens Attack 1 with precise position-level data.

| Claim | Status |
|-------|--------|
| e_n is a universal witness | **FALSE** for all n=1..20 |
| k=0 always sensitive | **TRUE** (provable via left-permutivity) |
| k=2n always sensitive | **FALSE** (sensitive only at n=8 in tested range) |
| k=n (source bit) always sensitive | **FALSE** (sensitive for only ~50% of n) |
| S_n is mirror-symmetric | **FALSE** for all tested n |
| \|S_n\| ≈ n | **TRUE** with linear fit slope ≈ 0.887 |

**The most damaging finding for the bridge**: the centre cell (the only initially-set bit)
is itself non-sensitive for roughly half the tested values of n. This means
rule30_n(all-zeros) = rule30_n(e_n) for n ∈ {2,6,7,10,11,12,14,17,18,20}.
In other words, for these n, the entire initial condition is irrelevant — the same
output would emerge from a blank tape. Any bridge argument that treats e_n as
"the hard input" must contend with the fact that for many n, the canonical input
is no harder to evaluate than the all-zeros input (trivially 0 for all n).

**Implication for Path E (cone argument)**: The cone argument says information must
propagate from position n to position 0 in exactly n steps — a tight traversal.
But if flipping position n (the tip of the cone) doesn't change the output, the
"tight propagation" is irrelevant for those specific n. Path E cannot use e_n's
cone structure as a hardness argument without first explaining why the centre bit
is non-sensitive for ~half the n values.

**One genuine residual**: k=0 is provably always sensitive. This gives a 1-bit
lower bound on the information that any algorithm must use — it must at some point
"logically depend on" cell 0 of the initial configuration. But a 1-bit lower bound
is far from what Prize 3 requires (a super-linear time or space lower bound).

---

## Attack 4 (2026-03-24)

**Script**: `research/bridge_attack_4.py`

**Claims under attack**:
1. Path C: "If a fast algorithm for s(n) existed, we could use it to compute rule30_n(c) for general c." Is there any oracle reduction from general rule30_n queries to fixed-input s(n') values?
2. Path B (information-theoretic): Does s(n) have low complexity as a function of the *binary representation* of n? If s(n) is a low-degree polynomial over GF(2) in the bits of n, Prize 3 is likely false.

### Test A: Circuit depth lower bound (DAG critical path)

For each n=1..15, the computation of s(n) from scratch requires constructing the full Rule 30 DAG. Each cell at each time step requires 2 gate layers (1 OR gate, 1 XOR gate). The critical path to the output node at (time=n, position=n) is exactly **2n** gate layers.

| n  | s(n) | total_gates | cone_gates | crit_depth |
|----|------|-------------|------------|------------|
|  1 |    1 |           6 |          6 |          2 |
|  5 |    1 |         110 |         70 |         10 |
| 10 |    0 |         420 |        240 |         20 |
| 15 |    1 |         930 |        510 |         30 |

**Critical depth = 2n exactly.** This is provable from data-dependency: cell (t, i) can only be computed after cell (t-1, i-1), (t-1, i), and (t-1, i+1) are known. There is no "skip ahead" in the sequential DAG. Even within the light cone, 2n(n+2) gates are required — all Θ(n²) of them lie on mutually dependent paths.

**What this does and does NOT give:**
- It gives a genuine circuit *depth* lower bound of 2n for any circuit computing s(n) from the initial tape. This is a real lower bound, not a worst-case artefact.
- **The gap:** Prize 3 asks about TIME, not circuit depth. A TM reading n in binary (O(log n) bits of input) could in principle use an algebraic shortcut that doesn't follow the Rule 30 DAG at all. The 2n depth lower bound only applies to circuits that accept the 2n+1-bit tape as input — not to a TM that receives just the integer n.

**Verdict**: Test A gives a tight circuit depth lower bound (2n) for the tape-input model. It does NOT close Prize 3 because Prize 3 is about a TM taking n in binary. The depth bound is real but lives in the wrong model.

---

### Test B: ANF degree of s(n) as a function of bits(n)

The key question: is s(n) computable by a low-degree formula in the binary digits of n? We compute the ANF (algebraic normal form) of the boolean function n → s(n) over GF(2), treating the K-bit binary expansion of n as the input variables b_0, ..., b_{K-1}.

| K | range | ANF degree | #terms | max degree K | notes |
|---|-------|-----------|--------|--------------|-------|
| 2 |  0..3 |     2/2   |      3 | FULL         | `1 + b1 + b0*b1` |
| 3 |  0..7 |     3/3   |      4 | FULL         | `1 + b1 + b0*b1 + b0*b1*b2` |
| 4 | 0..15 |     4/4   |      9 | FULL         | 9-term degree-4 polynomial |
| 5 | 0..31 |     4/5   |     18 | **BELOW MAX** | degree 4 out of 5 |
| 6 | 0..63 |     6/6   |     29 | FULL         | unique degree-6 monomial |
| 7 |0..127 |     7/7   |     66 | FULL         | unique degree-7 monomial |

**Key findings:**

1. **At K=5 (n=0..31), degree is 4, not 5.** This is the one anomaly — for this 32-value window, s(n) happens to miss the highest degree. But at K=6 and K=7, degree bounces back to FULL. This is consistent with s(n) being a high-complexity function of bits(n) with no structural shortcut — the K=5 dip is a finite accident.

2. **At K=6 and K=7, degree = K with a UNIQUE highest-degree monomial.** A unique full-degree monomial is the hallmark of "maximally hard" boolean functions. It means the function cannot be decomposed into any lower-degree formula — the full conjunction of all K bits is necessary.

3. **The number of ANF terms grows rapidly**: 3, 4, 9, 18, 29, 66 — roughly doubling every two steps. This is consistent with exponential growth Θ(2^K) that would characterise a random-looking boolean function.

**What this means for Prize 3:**

This is the most important finding of Attack 4. The ANF analysis directly attacks the low-degree polynomial path:

- **If** s(n) were computable by a degree-d polynomial in bits(n) for some fixed d, then the ANF degree would be bounded by d for all K ≥ d. The data shows degree = K for K = 2, 3, 4, 6, 7. There is NO fixed-degree polynomial description.
- **Implication**: Any TM that computes s(n) from the binary representation of n cannot use a constant-depth circuit (AC0) or any circuit of depth o(log n). This is because: ANF degree K requires at least K levels of AND gates in any circuit.
- **The gap**: The ANF lower bound K = log₂(n) + 1 gives a circuit depth lower bound of Ω(log n) for computing s(n) from the bits of n. This is an improvement over "trivially Ω(1)" — but Prize 3 requires Ω(n) time, and Ω(log n) circuit depth does not rule out polynomial-time TMs.

**What this does NOT give**: A super-logarithmic lower bound for the sequential computation time from the bits of n. The ANF depth bound is a circuit lower bound, not a TM time lower bound.

---

### Test C: Oracle reduction from general rule30_n(c) to s(n') values

If rule30_n were GF(2)-linear, computing rule30_n(c) for general c would reduce trivially to a linear combination of s(n') = rule30_n(e_k) values. We test this linear approximation:

| n  | linear approx error rate |
|----|--------------------------|
|  1 |            0.44         |
|  2 |            0.40         |
|  3 |            0.42         |
|  5 |            0.48         |
|  8 |            0.52         |
| 10 |            0.50         |

**The error rate is approximately 0.5 (random) for all n ≥ 4.** The linear combination of fixed-input s(n') values reconstructs rule30_n(c) for general c no better than a coin flip. This quantifies exactly why Path C fails: Rule 30's nonlinear term (c AND r in each step) accumulates through n steps until the output is completely nonlinear in any fixed-input query basis.

**Formal statement of the obstruction to Path C**: Suppose A is an oracle TM that queries s(n_1), s(n_2), ..., s(n_T) (for any choice of n_1, ..., n_T depending on n) and from these produces rule30_n(c) for general c. Then A's output is a function of T bits, each drawn from the sequence s(·). But rule30_n(c) has Boolean circuit complexity Θ(n²) in its 2n+1 inputs — exponentially more than any polynomial number of queries to s(·) could provide. No oracle reduction of this form can work in polynomial query complexity.

**The caveat**: this argument uses circuit complexity of rule30_n as a function of ALL inputs, not just e_n. The fixed-input case is different — as emphasized in all prior attacks, s(n) is a CONSTANT as a function of n inputs, so its circuit complexity is O(1). The nonlinearity argument only shows that a GENERAL oracle reduction fails; it says nothing about whether some clever non-oracle algorithm might compute s(n) directly from n.

---

### Summary of Attack 4 findings

| Test | Finding | Impact on bridge |
|------|---------|-----------------|
| A (circuit depth) | Critical path depth = 2n, provable from DAG structure | Real lower bound but wrong model for Prize 3 |
| B (ANF in bits of n) | Degree = K (= log n + 1) for K = 2,3,4,6,7; unique full-degree monomial at K=6,7 | Closes the "low-degree polynomial in bits(n)" path. No shortcut formula exists. Gives Ω(log n) circuit depth lower bound (weak). |
| C (oracle reduction) | Linear approximation error ≈ 0.5 for all n ≥ 4 | Confirms nonlinearity makes Path C impossible via linear oracle reduction. Higher-order reductions face exponential blowup. |

### New obstruction identified: the model mismatch is structural, not accidental

All three attacks converge on the same fundamental obstacle: there are TWO different computational models at play.

1. **Tape-input model**: TM reads the 2n+1 initial cells of the tape. Lower bounds: query complexity 2n+1 (our theorem), circuit depth 2n (Test A). These are real and provable.

2. **Integer-input model**: TM reads the integer n in binary (O(log n) bits). s(n) is a fixed, deterministic sequence. Lower bounds: ANF degree = log n + 1 (Test B). This is far weaker.

The Prize 3 question lives entirely in model 2. Our theorem lives entirely in model 1. The bridge must cross from model 1 to model 2, and no currently known technique does this without either:
- Using aperiodicity of s(n) (Prize 1, unproved), or
- Proving that the integer-to-tape encoding forces the TM to "unfold" the full DAG.

**Path E (cone argument) is the only remaining candidate** that could force the unfolding — by arguing that the cone from t_n expands to fill the full tape in exactly n steps, and any shortcut computation must represent the full cone state. But the cone argument still needs to explain why the specific integer n cannot be used to "precompute" cone states more efficiently than step-by-step simulation.
