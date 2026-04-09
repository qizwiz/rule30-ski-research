# Lean Proof Template: `subcaseB_mgt38_witness`

**Date**: 2026-04-09  
**Branch**: autoresearch/mar20  
**Status**: Axiom — proof strategy under development

---

## Section 1: The Axiom

### Exact Lean Statement (SubcaseB_Firewall.lean:147–162)

```lean
axiom subcaseB_mgt38_witness
    (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1))
    (hm_even : m.val % 2 = 0)
    (hm_low : 1 ≤ m.val)
    (hm_ge40 : 40 ≤ m.val)
    (hm_ne_r : m.val ≠ 2 * n')
    (hm_not_rm : m.val ≠ 2 * (n' + 1) - 8)
    (hm_high : m.val + 1 < 2 * (n' + 1) + 1)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m)
```

### Mathematical English

Given any SubcaseB event — that is, any pair `(n', m)` with `n' ≥ 3087`, even `m ≥ 40`
(excluding the right-mirror position `m = 2*(n'+1)-8` and the right-edge position `m = 2*n'`),
where SubcaseB has fired (i.e. `F_m(n'+1) = false` and `G_{m,last}(n'+1) = true`) — there
exists a *parity-clean* initial configuration `c_n` on the `(n'+1)`-step tape such that:

1. All odd-indexed cells of `c_n` are zero (the "parity-clean" condition), AND
2. `c_n` is *sensitive* at position `m`: flipping bit `m` in `c_n` changes the center output.

In other words, sensitivity at `m` can always be witnessed by a parity-clean configuration,
even though `m`'s single-spike gives the wrong parity (SubcaseB case). The parity-clean
condition ensures the witness is compatible with the prize theorem's sensitivity argument.

---

## Section 2: Known Witness Data

The witness spike position `X` depends on `m`. Notation: `F_X(T) = FXFast X T`
(center after `T` steps from spike at `X`), `G_{X,m}(T) = GXmFast X m T`
(center from spikes at `X` and `m`). A witness at event `(n', T=n'+1)` satisfies
`G_{X,m}(T) ≠ F_X(T)`.

### Confirmed per-m witnesses (first SubcaseB events)

| m  | First SubcaseB n' | T = n'+1 | F_X(T) | G_{X,m}(T) | Best X | Status |
|----|-------------------|----------|--------|------------|--------|--------|
| 40 | 40983             | 40984    | 0      | 1          | **2**  | PROVED in Lean (G2mFast40_T40984) |
| 40 | 61459             | 61460    | 0      | 1          | **2**  | PROVED in Lean (G2mFast40_T61460) |
| 42 | 118804            | 118805   | 1      | 0          | **2**  | PROVED in Lean (G2mFast42_T118805) |
| 44 | 249877            | 249878   | 0      | 1          | **4**  | sorry in SubcaseB_X2_Core.lean (pending native_decide) |
| 46 | 106522            | 106523   | 1      | 0          | **2**  | PROVED in Lean (G2mFast46_T106523) |
| 48 | 262167            | 262168   | 1      | 0          | **6**  | sorry in SubcaseB_X2_Core.lean (pending native_decide) |

### X=2 failure cases

- `m=44, T=249878`: `G_{2,44}(T) = 0 = F_2(T)` — X=2 fails; X=4 witnesses.
- `m=48, T=262168`: `G_{2,48}(T) = 0 = F_2(T)` and `G_{4,48}(T) = 0 = F_4(T)` — X=2 and X=4 fail; X=6 witnesses.

### Period and LFSR data per m (from patterns.md)

| m  | G_{X,m} period P | LFSR L   | P−L    | Connection poly type         | SubcaseB residues/P |
|----|-----------------|----------|--------|------------------------------|---------------------|
| 40 | 2¹⁶ = 65536     | 57347    | 8189   | Complex (~32 nonzero)        | 2 ({40983, 61459})  |
| 42 | 2¹⁷ = 131072    | 122884   | 8188   | Complex (~32 nonzero)        | 1 ({118804})        |
| 44 | 2¹⁸ = 262144    | unknown  | —      | unknown                      | ≥1 ({249877})       |
| 46 | 2¹⁹ = 524288    | 262145   | 262143 | (1+x)^{262145} (4 nonzero)  | ≥1 ({106522})       |
| 48 | unknown          | unknown  | —      | unknown                      | ≥1 ({262167})       |

### Observed X(m) pattern

| m mod 8 | Representative m | Witness X |
|---------|-----------------|-----------|
| 0       | 40              | 2         |
| 2       | 42, 46          | 2         |
| 4       | 44              | 4         |
| 0 (again)| 48             | 6         |

The pattern in X does not reduce simply to `m mod 4` or `m mod 8`.
The failures of X=2 for `m=44` and `m=48` suggest X is determined by
the D-chain interaction depth, not by `m mod k` for any small k.

---

## Section 3: Proposed Proof Strategy

### Strategy A: Period cert + sensitivity_transfer (per m, finite reach)

**Mechanism**: `sensitivity_transfer` (SubcaseBPeriod.lean:450) takes:
1. A base witness: `G_{X,m}(n''+1) ≠ F_X(n''+1)` at some `n''` (proved by `native_decide`)
2. A spike period cert: `caEvolve P (spikeAtList X (2*P+2*X+1)) = spikeAtList X (2*X+1)`
3. A twoSpike period cert: `caEvolve P (twoSpikeList X m (2*P+2*(max X m)+1)) = twoSpikeList X m (2*(max X m)+1)`

And concludes the witness holds for all `n' = n'' + k*P`.

**For m=40**: Period P=65536. Two base witnesses proved. `G2m40_period_cert_arr` is in
`SubcaseB_X2_PeriodCerts.lean` (pending native_decide build, ~5-30 min).
Once the period cert is proved, `sensitivity_transfer` closes all n' ≡ {40983, 61459} (mod 65536).

**For m=42**: Period P=131072. One base witness proved. `G2m42_period_cert_arr` pending
(~20min–2hr native_decide). Once proved, covers all n' ≡ 118804 (mod 131072).

**For m=46**: Period P=524288. One base witness proved. Period cert too large for
Array Bool native_decide (~5–32hr estimate). Needs UInt64 approach or algebraic proof.

**For m=44 and m=48**: Base witnesses currently sorry'd in `SubcaseB_X2_Core.lean`,
waiting for heavy native_decide runs. Periods not yet determined.

**Feasibility by m**:
- m=40: FEASIBLE (period 2¹⁶, certs buildable in <1hr)
- m=42: FEASIBLE (period 2¹⁷, ~1-2hr)
- m=44: PARTIALLY FEASIBLE (base witness pending; period unknown)
- m=46: HARD (period 2¹⁹; cert too large for Array Bool)
- m=48: UNKNOWN (period unknown)
- m≥50: INFEASIBLE — first SubcaseB events are exponentially large (T ≈ 2^(3m/4)), making native_decide impossible

**Verdict**: Strategy A can close finitely many m values (likely m=40,42 in the
near term, possibly m=44 within days) but CANNOT close the axiom for infinite m.

---

### Strategy B: Algebraic LFSR proof for infinite families

**Core idea**: The active set {40, 42, 44, 46, 48, 50, ...} is infinite (all even m ≥ 40),
so a finite native_decide enumeration cannot suffice. We need to show algebraically that
for each active m, some X(m) witnesses all SubcaseB events.

**LFSR structure**: `G_{X,m}` and `F_X` are both LFSR sequences over GF(2) with
connection polynomials (1+x)^L. The interaction `I = F_X ⊕ G_{X,m} ⊕ 1` is also
a GF(2) linear recurrence. SubcaseB fires when `F_m = 0` and `G_{m,last} = 1`.
A witness X makes `F_X(T) ≠ G_{X,m}(T)` at such T.

**The algebraic question**: For each active m, does there exist an X such that
`I_{X,m}(T) = F_X(T) ⊕ G_{X,m}(T)` is `1` whenever SubcaseB fires?

This reduces to a divisibility question: the LFSR polynomial of `I_{X,m}` must
not be divisible by the LFSR polynomial of the SubcaseB indicator.

**Period-family structure**: The data suggests:
- Pairs (40,42), (44,46), (48,50), ... share LFSR structural class
- Within each pair, m≡2 (mod 4) takes X=2; m≡0 (mod 4) may need X=4 or higher
- The periods P(m) grow as 2^floor(m/2) (doubling per 2 units of m)

**Approach for Lean**:
1. Identify a finite set of LFSR "connection polynomial classes" (e.g. the
   pairs grouped by v_2(m/2) — 2-adic valuation)
2. For each class, prove algebraically (or via GF(2) polynomial arithmetic)
   that a fixed X witnesses all SubcaseB events in that class
3. Reduce "all m≥40" to finitely many class representatives

**Blockers**: The algebraic characterization of X(m) is currently empirical only.
The observed values X ∈ {2, 4, 6} suggest X = 2 * v_2(m/2 - 1) + 2 or similar,
but this formula is unverified beyond m=40,42,44,46,48.

---

### Strategy C: Inductive/diagonal argument

**Core idea**: Use the D-field diagonal recurrence
`D_k[t] = rule30(D_k[t-1], D_{k-1}[t-1], D_{k-2}[t-1])` with `D_0[t]=1`
to show: if X witnesses at (m, n'), then X' witnesses at (m+4, n'+something).

**D-field observation**: The D-field propagates "bottom-right" in the (m, step) plane.
Each increment of m by 2 shifts the interaction one position right. If the witness
at m is X=2 and the interaction shifts right by 2 per m increment, then X should
shift by 2 as well — consistent with the observed X(44)=4, X(48)=6 pattern.

**Proposed inductive step**: Prove a lemma of the form:
```
lemma witness_inductive_step (m X : Nat) (hm : even m) (hm_ge40 : m ≥ 40)
    (hwit : ∀ n', subcaseB_fires n' m → GXmFast X m (n'+1) ≠ FXFast X (n'+1)) :
    ∀ n', subcaseB_fires n' (m+4) →
          GXmFast (X+2) (m+4) (n'+1) ≠ FXFast (X+2) (n'+1)
```

**If provable**, this would give an inductive proof from 3 base cases (m=40: X=2,
m=42: X=2, m=44: X=4) covering all m≥40. Each base case requires only one
native_decide computation.

**Feasibility**: The inductive step is plausible from the D-field geometry but has
not been verified computationally for even one step (m=40 → m=44). This is the
highest-priority computation needed to evaluate Strategy C.

**Blockers**: The m=44 (X=4) to m=48 (X=6) transition needs the base witness for
m=44 confirmed first. The diagonal recurrence for X+2 shift needs algebraic proof.

---

## Section 4: Required Lean Lemmas

### For Strategy A (per-m, closes m=40,42 now)

**Dependency order**:

1. `G2m40_period_cert_arr` — `caEvolveArr 65536 (twoSpikeArr 2 40 131153) = twoSpikeArr 2 40 81`
   - Type: concrete equality
   - Proof method: `native_decide` (estimated 5-30 min)
   - Status: stated in `SubcaseB_X2_PeriodCerts.lean`, pending build

2. `G2m40_period_cert` — list-form period cert derived from above
   - Proof method: `congrArg Array.toList` + `simp`
   - Status: already written, just needs above

3. `subcaseB_m40_all_events` — for all n' ≡ {40983, 61459} (mod 65536) with n'≥3087,
   a parity-clean c_n witnesses sensitivity at m=40
   - Type: `∀ k, ∃ c_n, parity_clean c_n ∧ sensitive c_n 40`
   - Proof method: `sensitivity_transfer` from `G2mFast40_T40984` + period cert
   - Depends on: (1) and (2)

4. Analogous chain for m=42 (cert `G2m42_period_cert_arr`, period 131072, ~1-2hr)

5. **NOT feasible for m≥46 via this strategy** — period certs too large.

### For Strategy B (algebraic, needed for infinite m)

1. `lfsr_class_of_Gxm` (m : Nat) (hm_even : even m) (hm_ge40 : m ≥ 40) :
   characterize the connection polynomial of `G_{X(m), m}` in terms of m
   - Type: ∀ statement
   - Proof method: algebraic GF(2) argument; no native_decide
   - Unknown: the formula for the connection polynomial

2. `subcaseB_indicator_poly` (m : Nat) : characterize the LFSR polynomial of
   the SubcaseB indicator sequence `(F_m(T) = 0) ∧ (G_m(T) = 1)`
   - Proof method: algebraic; probably follows from Phi_3 fingerprint theory

3. `witness_divides_indicator` (m X : Nat) : the polynomial of `F_X ⊕ G_{X,m}`
   is NOT divisible by the SubcaseB indicator poly
   - Proof method: GF(2) polynomial non-divisibility; likely requires computer algebra

4. `subcaseB_mgt38_witness_algebraic` : the main axiom, proved from (1-3)
   - Proof method: combine LFSR non-divisibility with `sensitivity_transfer`

### For Strategy C (inductive)

1. `G_Xplus2_m_plus4_formula` : algebraic identity relating G_{X+2, m+4} to G_{X,m}
   via the D-field recurrence
   - Type: functional equation or period relationship
   - Proof method: D-field diagonal recurrence; needs new algebraic development

2. `witness_shift_lemma` : if X witnesses all SubcaseB events for m, then X+2
   witnesses all SubcaseB events for m+4
   - Depends on: (1)
   - Proof method: induction + (1)

3. Base cases (m=40: X=2, m=42: X=2, m=44: X=4) with period certs
   - Proof method: native_decide (as in Strategy A)

4. `subcaseB_mgt38_witness` from inductive chain on m mod 4
   - Proof method: combine (2) + (3) over mod-4 residue classes

---

## Section 5: Gap Analysis

### Unknown mathematics

1. **X(m) formula**: The mapping m → X(m) is known only for m ∈ {40,42,44,46,48}.
   The observed values {2,2,4,2,6} do not fit a simple formula. The hypothesis
   `X(m) = 2 * (1 + v_2(m/2 - 1))` needs computational verification for m≥50.

2. **Period of G_{X,m} for m≥44**: Only m=40,42,46 have confirmed periods.
   The period of `G_{4,44}` and `G_{6,48}` is unknown. The doubling law
   `P(m) = 2^(m/2)` is observed for X=2 sequences but may not hold for X=4,6.

3. **Inductive step validity**: Whether `G_{X+2, m+4}` witnesses when `G_{X,m}`
   witnesses has not been tested even computationally.

4. **Why X=2 fails for m=44,48**: The D-chain explanation predicts X=2 fails when
   the D-field "corridor" is not left-permutive for X=2 at position m. The exact
   algebraic condition for this failure is unknown.

### Required computational experiments (before Lean proof)

**Priority 1**: Verify X(m) for m = 50, 52, 54, 56 (first SubcaseB events).
This tests the X(m) formula hypothesis and is feasible with the existing C program.

**Priority 2**: Determine period of G_{4,44} and G_{6,48}.
Run LFSR analysis (Python numpy) on these sequences.

**Priority 3**: Test the inductive step: if X=4 witnesses for m=44 at n'=249877,
does X=6 witness for m=48 at the "corresponding" n'?
Compare with the actual first event for m=48 at n'=262167.

**Priority 4**: For m=46, explore whether a UInt64-based period cert is feasible
for P=524288 (the caEvolveU64 path exists in CA_ArrayDef.lean).

### Current blockers for near-term progress

1. **m=44,48 base witnesses**: `GXmFast 4 44 249878` and `GXmFast 6 48 262168`
   are sorry'd. These are the next native_decide computations to run.

2. **m=40 period cert**: `G2m40_period_cert_arr` is stated but needs the build
   to complete. ETA: 5-30 minutes once triggered.

3. **No algebraic characterization of X(m)**: Without knowing X(m) for large m,
   neither Strategy B nor Strategy C can be formalized.

### Assessment of proof paths

| Strategy | Closes axiom? | Timeline | Main risk |
|----------|--------------|----------|-----------|
| A (per-m native_decide) | NO — only finitely many m | Weeks | Periods too large for m≥50 |
| B (algebraic LFSR) | YES — if X(m) formula found | Months | Formula unknown; GF(2) proof hard |
| C (inductive diagonal) | YES — if inductive step holds | Weeks–months | Step validity unverified |

**Most promising near-term action**: Verify X(m) for m=50,52,54 computationally,
then determine whether X = 2*(m/4 mod 2 + 1) or some related formula.
If a modular formula exists, Strategy C becomes feasible with 2-4 base cases.
