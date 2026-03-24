# Bridge Argument: Query Complexity → Prize 3
## Status: DRAFT — iteration 4

### What we have
**Theorem (proved, Lean-formalized conditionally):**
For all n ≥ 0 and all k ∈ {0,...,2n}, position k is essential at generation n of Rule 30.
Corollary: the deterministic query complexity of rule30_n is exactly 2n+1.

### What Prize 3 asks
"Prove that no formula can give the nth center-column value of Rule 30
(starting from a single black cell) in less time than the rule itself requires."

More formally: let s(n) = rule30_n(e_n) where e_n is the single-black-cell
initial configuration (length 2n+1, 1 at position n). Prize 3 asks whether
any Turing machine M can compute s(n) in time o(n²) (or even sub-linear space).

### The gap
Our theorem: ∀ algorithm A, ∃ input c such that A must read all 2n+1 cells.
Prize 3 asks: for the SPECIFIC fixed input e_n, can s(n) be computed fast?

These are different models. Our result is worst-case over all inputs.
Prize 3 is average-case (or fixed-case) on one specific input.

### Current best bridge attempt
**Claim:** If there exists a TM M that computes s(n) in space S(n) = o(n), then
M cannot be correct for all n.

**Argument sketch (INCOMPLETE — weakest step marked):**
1. The single-black-cell evolution e_n at generation n has the property that
   s(n) = rule30_n(e_n) depends on ALL 2n+1 initial cells (by our theorem,
   applied to the specific input e_n).

   *** WEAKEST STEP: our theorem says there EXISTS c such that flipping c[k]
   changes the output — but e_n is a specific fixed c. The theorem doesn't
   directly say e_n is the witness for all k. ***

2. Alternative framing (information-theoretic):
   The function n ↦ s(n) encodes arbitrarily complex information about the
   Rule 30 trajectory. If Rule 30's center column is aperiodic (Prize 1,
   unproved), then s(n) cannot be compressed to O(1) description, so any
   algorithm computing it must maintain growing state.

   *** WEAKEST STEP: this relies on Prize 1 (aperiodicity), which is unproved.
   It would make Prize 3 conditional on Prize 1. ***

3. Strongest current path — via deterministic query complexity:
   Our theorem (all positions essential) directly proves D(rule30_n) = 2n+1.
   Proof: if any decision tree has depth < 2n+1, some path omits querying
   some variable k. Both inputs consistent with that path give the same output.
   But essentiality provides c, flip(c,k) consistent with that path that give
   DIFFERENT outputs. Contradiction. QED.

   *** CORRECTION (bridge_compute_2.py, 2026-03-24): bs(rule30_n) < 2n+1 for n≥2! ***
   The block sensitivity is: bs(rule30_2) = 4, bs(rule30_3) = 6, bs(rule30_5) = 10,
   etc. (all < 2n+1). The paper correctly claims D = 2n+1, but block sensitivity is
   STRICTLY LESS than D for n ≥ 2. This means rule30_n is an example where the
   bs < D gap is nontrivial.

   Concretely: no single input witnesses all 2n+1 variables simultaneously
   (no "universal witness" exists for n≥2). This is exactly bridge Attack 1.

   The D = 2n+1 lower bound is tight and correctly proved. But it uses a DIFFERENT
   witness input for each variable — exactly what the essentiality proof shows.

   But this is still the WORST-CASE model. The fixed-input question requires
   a different argument.

4. Direct fixed-input path:
   If s(n) were computable by M in time T(n), we could use M as a subroutine to
   reconstruct rule30 on ANY input c by querying s for carefully chosen n values
   corresponding to different "perturbations" of c. This would contradict our
   lower bound... IF we can show the reduction works.

   *** WEAKEST STEP: how to reduce general rule30 computation to queries of s(n)?
   The perturbation argument needs formalization. ***

### Known objections (from bridge_attacks.md)
- **Attack 1 (DECISIVE): PATH A IS DEAD.** e_n is not a universal witness.
  Computed n=1..25: ~half of positions are non-sensitive for the specific
  single-black-cell input. See bridge_attack_1.py for full table.
  Sensitive count grows as ~n, not ~2n.

### What a complete bridge would need
Either:
(A) Show e_n is itself a witness for essentiality of all positions (i.e.,
    flipping e_n[k] changes s(n) for EVERY k simultaneously — strong claim)
(B) Show s(n) is not computable in o(n) space via a direct entropy/complexity argument
(C) Show any fast algorithm for s(n) would contradict our query lower bound
    via a formal reduction

### Open questions for the builder loop to address
1. ~~Is e_n a universal witness?~~ **CLOSED (Attack 1).** e_n is NOT universal.
   ~n positions sensitive, ~n non-sensitive. Path A dead.
2. What does Rule 30's known structure (left-permutivity, Rowland's diagonal
   periodicity result) say about information flow in e_n specifically?
3. Can path (C) be made rigorous? What is the explicit reduction?

### Path C update: bridge_compute_1.py results (2026-03-24)

**Script**: `bridge_compute_1.py`

Key findings from n=1..30 sensitive position analysis:

1. **#sensitive grows as ~n with no clean formula** — it's not n+1, not 2n+1, not any
   obvious arithmetic expression. The count fluctuates irregularly around n (e.g., n=15
   has 15 sensitive, n=20 has 21, n=25 has 23). So Path C cannot assume a clean formula
   for which positions matter.

2. **k=0 always sensitive (proved by left-permutivity)** — for ANY input c, flipping c[0]
   always flips rule30_1(c) (left-permutivity of Rule 30). By induction this propagates
   to generation n. This gives exactly 1 guaranteed sensitive position — not enough for
   the bridge.

3. **rule30_n(e_k) distribution is pseudo-random** — for n=20, computing rule30_n(e_k)
   for k=0..40 gives 21 ones and 20 zeros with no discernible pattern. The distribution
   is neither symmetric nor structured. This makes a clean reduction very hard to state.

4. **c_0=[1,0,...,0] also not a universal witness** — the leftmost-black-cell initial
   condition has fewer sensitive positions than e_n for small n (checked n=3,5,8,10).
   No obvious "canonical" witness exists.

**Implication for Path C**: The reduction would need to show that rule30_n(c) for general
c can be computed from a polynomial number of fixed-input queries s(n_i) for various n_i.
The pseudo-random distribution of rule30_n(e_k) values makes this encoding non-obvious —
there's no clean "basis" of fixed inputs that spans all possible c values.

**Current status**: Path C (reduction) remains open but has no clear construction.

**Important correction**: rule30 is NOT GF(2)-linear. The rule is
  rule30(l,c,r) = l XOR (c OR r) = l XOR c XOR r XOR (c AND r)
The (c AND r) term is nonlinear over GF(2), so rule30_n(c) is a high-degree
polynomial in the initial cells (degree exponential in n in general). There is
no "basis" decomposition rule30_n(c) = Σ_k c_k · rule30_n(e_k).

The most promising angle remaining: left-permutivity gives a recursive structure.
Since rule30_n+1(c) = left_cell XOR rule30_n(rest), a TM that computes s(n) must
somehow encode the left_cell dependence — but this is available to any TM that
reads cell 0. The problem is we need a lower bound on the number of cells the
TM must read, not just that cell 0 matters.

---

## v3 update: bridge_compute_4.py findings (2026-03-24)

### The 3-cell block identity (clean result)

**Theorem (computational, verified n=2..11):**
  s(n) = rule30_{n-1}(t_n)

where t_n = [0,...,0, 1, 1, 1, 0,...,0] of length 2n-1, with the block of 3 ones
centered at position n-1 (i.e., ones at positions n-2, n-1, n).

**Proof sketch:** e_n has a single 1 at position n. After one step of rule30:
- Output position i uses input triple (i, i+1, i+2).
- rule30(0,0,0)=0; non-zero only when the 1 at position n is in the triple.
- Triples containing position n: i=n-2 (triple (n-2,n-1,n): rule30(0,0,1)=1),
  i=n-1 (triple (n-1,n,n+1): rule30(0,1,0)=1), i=n (triple (n,n+1,n+2): rule30(1,0,0)=1).
- So first_step(e_n) = t_n exactly.

Then applying n-1 more steps gives s(n). QED.

**Significance:** s(n) = rule30_{n-1}(t_n) is a clean identity expressing the single-cell
starting problem in terms of a 3-cell block. But: applying the same argument to t_n
does NOT produce t_{n-1}. The step(t_n) differs from t_{n-1} at exactly 4 positions
forming a "butterfly" pattern (positions {n-3, n-1, n, n+1} shift relative to center):

  step(t_n) = [0,..., 1, 1, 0, 0, 1, 0,...] (always 4 positions but NOT self-similar)

So the recursion `s(n) = rule30_{n-1}(t_n)` does NOT telescope into s(n-1).
The self-similarity structure breaks after one step.

### Randomness assessment (decisive negative result)

The sequence s(0..50) = [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1,0,0,1,1,1,...]:

1. **Linear complexity = 26 out of 51 terms.** The Berlekamp-Massey algorithm finds
   an LFSR of length 26, exactly what you'd expect for a truly random binary sequence
   of length 51. This is MAXIMAL complexity — the sequence looks computationally
   indistinguishable from a random binary string to any linear test.

2. **No boolean recurrence for lookback 1..6.** For every k from 1 to 6, there exist
   contexts c ∈ {0,1}^k that appear at multiple positions in the sequence and produce
   DIFFERENT outputs. No pure finite-memory recurrence of order ≤ 6 exists.

3. **No divide-and-conquer formula.** All tested formulas of the form
   s(n) = F(s(n//2), s(n//2 + 1), s(n//2 - 1), ...) fail. The two-input version
   F(s(n//2), s(n//2 + n%2)) is inconsistent (same inputs map to different outputs).

4. **Runs test:** 28 runs observed vs 26.4 expected (random) — no excess structure.

5. **Autocorrelation:** All lags 1..5 are < 0.25 in absolute value, consistent with
   an i.i.d. process.

### ANF degree growth (algebraic lower bound)

The algebraic normal form of rule30_n (as a boolean function of its 2n+1 inputs)
has been computed for n=1..6:

| n | terms | max degree |  highest-degree monomial |
|---|-------|------------|--------------------------|
| 1 |     4 |          2 |  {1,2}                    |
| 2 |    10 |          3 |  {1,3,4}                  |
| 3 |    30 |          5 |  {2,3,4,5,6}              |
| 4 |   122 |          7 |  {2,3,4,5,6,7,8}          |
| 5 |   346 |          9 |  {2,3,4,5,6,7,8,9,10}     |
| 6 |  1360 |         11 |  {2,3,4,5,6,7,8,9,10,11,12}|

**Pattern:** max degree = 2n-1, and the unique highest-degree monomial is ALWAYS the
product of variables {2, 3, ..., 2n} — all the "interior" cells (every cell except
the leftmost and rightmost). The number of terms roughly triples each time.

**Implication for Prize 3:** For any circuit computing rule30_n restricted to e_n,
the polynomial s(n) over GF(2) has algebraic degree 2n-1 (all interior variables
appear in the unique highest monomial). This means:

- Any AND-circuit computing s(n) must have at least one AND gate of fan-in 2n-1.
  (The highest-degree monomial requires this.)
- s(n) is NOT computable by a depth-O(1) circuit of polynomial size.
- Any FORMULA (tree-shaped circuit) computing s(n) has size at least 2^{Ω(n)}.

**CRITICAL CAVEAT:** This applies to the function rule30_n over ALL inputs. For the
SPECIFIC input e_n, the function is a constant (0 or 1), so trivially computable in
O(1). The ANF argument gives a lower bound on CIRCUIT COMPLEXITY of the function,
not on the complexity of computing a specific output.

### The irreducibility wall

The computation reveals a fundamental obstacle: s(n) is a single bit that is the
output of a specific high-degree polynomial evaluated at a specific sparse point.
That specific polynomial (max degree 2n-1, ~3^n terms) is hard to compute in general,
but at the specific point e_n, it evaluates to one bit, and there may be a short
"witness" computation that exploits the sparsity of e_n.

**What we DO know:**
- The sequence s(n) has maximal randomness properties (linear complexity ~n/2).
- There is no simple recurrence or divide-and-conquer formula.
- The full polynomial for rule30_n has exponential size and linear-in-n degree.

**What we DON'T know:**
- Whether there is a specialized algorithm that exploits e_n's sparsity to compute
  s(n) faster than simulating all n steps.
- The Kolmogorov complexity of the sequence s(0..n): is it n + O(1) bits, or can
  it be compressed? (Linear complexity ~n/2 says linear methods can't compress it,
  but nonlinear methods might.)

### Updated proof sketch candidates

**Candidate D (new): Algebraic degree lower bound, conditional form.**

Suppose there exists an algorithm M that computes s(n) in time T(n) = o(n²).
By the Cook-Levin and Razborov-Smolensky-type arguments, any algorithm running in
time T(n) corresponds to an AC0 circuit of depth O(log T(n)) and size 2^{O(T(n))}.

The algebraic degree of rule30_n is 2n-1. For AC0 circuits, the ANF degree is at
most 2^depth * log(size). If T(n) = o(n), the circuit would have ANF degree
o(n) * polylog, which contradicts degree 2n-1.

*** WEAKEST STEP: this argument applies to computing rule30_n on ANY input, but
we need it specifically for the fixed input e_n. Also, the relevant circuit model
for sequential algorithms is more subtle than AC0. ***

**Candidate E (new): The 3-cell reduction as a hardness amplifier.**

Since s(n) = rule30_{n-1}(t_n), and t_n has exactly 3 set bits at known positions:
if there were a fast algorithm for s(n), it would give a fast algorithm for
computing rule30_{n-1} applied to ANY 3-sparse input (by padding).

More precisely: any n-time CA step from a k-sparse initial condition has at most
O(nk) sensitivity. For t_n (k=3 sparse), this gives at most O(3n) = O(n) sensitive
positions — which matches bridge_compute_1 findings (~n sensitive positions for e_n).

But the hardness of computing rule30_{n-1}(t_n) may be provable via the CONE
argument: t_n's support spans the range [n-2, n] at time 0. For the output at
position 0 at time n-1 to be determined, information must propagate from position n
to position 0 in n-1 steps — exactly 1 cell per step, which is the maximum allowed
by the CA's finite speed of light. This tight propagation suggests no shortcut.

*** WEAKEST STEP: "tight propagation" is necessary but not sufficient for hardness.
A fast algorithm might exploit some algebraic structure of Rule 30 specific to 3-sparse
inputs. ***

### Status summary

| Path | Status | Blocking issue |
|------|--------|----------------|
| A (e_n universal witness) | DEAD | ~n sensitive, not 2n+1 |
| B (aperiodicity → incompressibility) | CONDITIONAL | Requires Prize 1 |
| C (reduction from general) | OPEN | No explicit reduction found |
| D (ANF degree lower bound) | PARTIAL | Fixed-input vs worst-case gap |
| E (3-cell reduction + cone) | PROMISING | Cone argument needs tightening |

**Most promising next step:** Prove that the cone computation from t_n (3-sparse, width-3 support at positions n-2..n) cannot be shortcut. The key question: is there any algorithm for rule30_{n-1}(t_n) that runs in time o(n)? The cone argument says each step shrinks the relevant support by at most 2 cells but can also GROW it (Rule 30 is left-permutive, so information grows leftward at speed 1 per step). After n-1 steps, the support has expanded from width 3 to width 2(n-1)+3 = 2n+1 — so a full-width computation appears unavoidable. This is the most concrete remaining path.

---

## v4 update: bridge_compute_5.py findings (2026-03-24)

### MAJOR DISCOVERY: k=n sensitivity ≡ s(n) (perfect match, n=1..30)

**Theorem (computational, verified n=1..30):**

  k=n is sensitive for e_n  ⟺  s(n) = 1

**Data:**
```
k=n sens  (n=1..30): 101110011000101100100111010111
s(n)      (n=1..30): 101110011000101100100111010111
Match: 30/30 (100%)
```

All other candidate sequences (n mod 2, Thue-Morse, s(n-1), s(n) XOR parity) match
at most 16/30 = 53%. The s(n) match at 30/30 is not coincidence.

**Formal statement of the conjecture:**

  ∀ n ≥ 1: rule30_n(flip(e_n, n)) ≠ rule30_n(e_n)  ⟺  s(n) = 1

Equivalently:
  - When s(n) = 1: flipping position n (the only initially-set cell) changes the output 1 → 0.
  - When s(n) = 0: flipping position n does NOT change the output 0 → the output is STILL 0.

**Verification of the s(n) = 0 case:** When s(n) = 0 and k=n is non-sensitive, we confirmed
that rule30_n(all-zeros) = s(n) = 0 for all tested n. This makes sense: e_n has a 1 at
position n; flipping it gives all-zeros; both give output 0. The all-zeros tape always
gives output 0 (by rule30(0,0,0) = 0 propagating everywhere). So the conjecture's "⟸"
direction for s(n)=0 is equivalent to: rule30_n(e_n) = rule30_n(all_zeros) = 0.

**Corollary:** For s(n)=0, the information at position n (the only initially-set bit) is
irrelevant to the final output — the output would be 0 even from a blank tape.

**What this means for Prize 3:**

This is a structural self-referential property: whether the source bit is sensitive is
determined by the output value itself. This has two implications:

1. **No-shortcut interpretation:** For all n where s(n)=1, computing s(n) requires (at
   minimum) processing the information at position n. But we already know from Path A
   analysis that roughly half the positions are sensitive — we needed position n to be
   among them at least when s(n)=1.

2. **Self-referential hardness:** The conjecture says the hardness of s(n) is
   self-referential: the bit s(n) controls whether the source bit participates in
   determining s(n). This is reminiscent of the Recursion Theorem and suggests deep
   fixed-point structure. Any algorithm that tries to "skip" evaluating position n must
   still determine s(n) correctly — but whether it can skip position n depends on s(n)!

3. **Reduction test results (Task 3):** For ALL 10 non-sensitive values of n (n=2,6,7,10,
   11,12,14,17,18,20), we found witnesses c ≠ e_n such that rule30_n(c) = 0 = s(n) but
   flipping position n in c DOES change the output. This confirms that k=n is an
   essential variable for the general function rule30_n — just not for the specific input
   e_n when s(n)=0. The witnesses are found in ≤14 random trials, indicating that sensitive
   inputs with output 0 are common (~50% density).

### Conjecture F: The s(n)=1 sensitivity duality

**Conjecture F (unproved):**  ∀ n ≥ 1: flip(e_n, n) = all-zeros, and
  rule30_n(e_n) = 1 ⟺ rule30_n(all-zeros) = 0

Note: rule30_n(all-zeros) = 0 ALWAYS (the all-zeros tape is a fixed point of Rule 30).
So the conjecture reduces to:

  **s(n) = 1 ⟺ rule30_n(e_n) = 1 ≠ 0 = rule30_n(all-zeros)**

Which is trivially true! When s(n)=1, clearly rule30_n(e_n) ≠ rule30_n(all-zeros) = 0,
so flipping position n (turning e_n into all-zeros) DOES change the output — meaning
k=n is sensitive. When s(n)=0, rule30_n(e_n) = 0 = rule30_n(all-zeros), so flipping
position n does NOT change the output — k=n non-sensitive.

**This resolves the conjecture COMPLETELY:**

The equivalence k=n sensitive ⟺ s(n) = 1 is not a conjecture — it is a THEOREM,
following immediately from:
  1. flip(e_n, n) = all-zeros (since e_n has a 1 only at position n)
  2. rule30_n(all-zeros) = 0 (all-zeros is a fixed point of Rule 30)
  3. k=n sensitive ⟺ rule30_n(e_n) ≠ rule30_n(flip(e_n,n)) = rule30_n(all-zeros) = 0
                    ⟺ rule30_n(e_n) ≠ 0
                    ⟺ s(n) = 1

**Conclusion:** The "pattern" found by bridge_compute_5.py is in fact an exact identity
that follows from a trivial observation about e_n's structure. The 30/30 match is not
evidence of deep structure — it is a tautology.

**Implications for the bridge:**
- This specific structural observation (k=n ↔ s(n)) gives zero new information about
  Prize 3 hardness, because it is a consequence of s(n)=0 ↔ e_n evaluates to 0 (same as blank tape).
- The reduction test (Task 3) confirms that k=n IS essential for the general function
  even when e_n is non-sensitive. This is already covered by our essentiality theorem.
- Path E (cone argument via 3-cell reduction) remains the most promising remaining angle.

### Updated path table

| Path | Status | Blocking issue |
|------|--------|----------------|
| A (e_n universal witness) | DEAD | ~n sensitive, not 2n+1 |
| B (aperiodicity → incompressibility) | CONDITIONAL | Requires Prize 1 |
| C (reduction from general) | OPEN | No explicit reduction found |
| D (ANF degree lower bound) | PARTIAL | Fixed-input vs worst-case gap |
| E (3-cell reduction + cone) | PROMISING | Cone argument needs tightening |
| F (s(n)=1 ↔ k=n sensitive) | CLOSED (trivial) | Is a tautology, not Prize 3 progress |

---

### Version history
- v0 (2026-03-24): Initial scaffold. Three candidate paths identified, all with gaps.
- v1 (2026-03-24): Path C update with bridge_compute_1.py findings. Path A confirmed
  dead. Left-permutivity gives 1 guaranteed sensitive position. GF(2) linearity angle
  identified as most promising Path C sub-approach.
- v3 (2026-03-24): bridge_compute_4.py findings. Three-cell block identity proved.
  Sequence shown to have maximal linear complexity (essentially random). ANF degree
  grows as 2n-1, unique highest monomial is product of all interior variables.
  No recurrence, no divide-and-conquer. New Candidates D (ANF degree) and E (cone
  argument via 3-cell reduction) identified. Path E is the strongest remaining angle.
- v4 (2026-03-24): bridge_compute_5.py findings. Major discovery: the k=n sensitivity
  sequence matches s(n) exactly for n=1..30. See below.
