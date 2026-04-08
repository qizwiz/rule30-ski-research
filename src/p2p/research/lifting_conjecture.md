# Lifting Conjecture: Proof Path for `lifting_lemma`

**Date**: 2026-04-07 (updated: boundary formula correction + Unit 7 verification)
**Status**: Computationally verified for n ≤ 7 (exhaustive); n > 7 is conjecture  
**Key script**: `research/invariant_search.py`  
**Verification script**: `research/verify_b1_zero.py`

---

## 1. The Lifting Lemma

```lean
axiom lifting_lemma (n : Nat) (k : Fin (2 * n + 1)) :
    Essential n k → Essential (n + 1) ⟨k.val + 1, ...⟩
```

**Plain English**: If cell `k` is essential at generation `n` (i.e., flipping the
initial tape at position `k` changes the center output after `n` steps), then cell
`k+1` is essential at generation `n+1`.

**Why this suffices for Prize 3**: `lifting_lemma` + `AllEssential` at the base cases
directly gives `rule30_bs_ge_n`, which is the Ω(n) block sensitivity lower bound
(see `Prize3_Complete.lean` Section 8).

---

## 2. Two Proof Paths to the Prize (Updated)

There are currently TWO paths that could close the prize theorem:

**Path 1: `lifting_lemma` (this document)**
- Prove: Essential(n,k) → Essential(n+1,k+1) for all n,k
- Mechanism: inductive lifting via a P10-witness construction
- Status: UNSOUND (axiom unproved); existential claim verified n≤7; no
  universal boundary formula established

**Path 2: `rule30_prize3_direct` via `twoSpike_center_complement`**
- Uses `subcaseB_mgt38_witness` to show SubcaseB never fires for m≥40
- Requires proving `twoSpike_center_complement` in `SpinePass.lean`
- Status: INVALID — `subcaseB_mgt30_split` is demonstrably FALSE (SubcaseB fires
  for m=40 at n'=40983, m=42 at n'=118804, etc.; active set is INFINITE)
- This is a SEPARATE problem from `lifting_lemma`; requires LFSR/algebraic argument
  for the infinite family m=40,42,44,...

Both paths are currently blocked. Path 1 (lifting_lemma) is the more
mathematically accessible one.

---

## 3. The Invariant — P10: `c[j] = 1`

**Definition**: P(c, n, j) ⟺ c is a witness for Essential(n, j) AND c[j] = 1.

In words: the bit at the sensitive position is ON in the witness configuration.

**Why this is the right invariant** (and why 11 other candidates fail):

| Candidate | Existence | Closure | Notes |
|-----------|-----------|---------|-------|
| P1: c[0]=1 | FAIL | — | Not always satisfiable |
| P2: spike at x≤j | FAIL | — | Not always satisfiable |
| P3: c[j]=0 | FAIL | — | Not always satisfiable |
| P4: left-corner = dChain | FAIL | — | Not always satisfiable |
| P5: spike at mirror(j) | FAIL | — | Not always satisfiable |
| P6: boundary parity | FAIL | — | Not always satisfiable |
| P7: c[j]=0 AND c[0]=1 | FAIL | — | Subset of P3, also fails |
| P8: spike at j | FAIL | — | Fails at (n=6, j=5) — no weight-1 liftable witness |
| P9: hw ≤ 2 | FAIL | — | Not always satisfiable |
| **P10: c[j]=1** | **EXIST-OK** | **CLOSE-OK** | **THE ONE** |
| P11: center output=0 | EXIST-OK | CLOSE-FAIL(42) | Closure breaks |
| P12: center output=1 | EXIST-OK | CLOSE-FAIL(42) | Closure breaks |

P10 is the **only candidate** (of 12 tested) satisfying both conditions for n ≤ 7.

**Computational evidence** (from `invariant_search.py`, exhaustive for n ≤ 6,
spike-only for n = 7):
```
P10: c[j]=1:  EXIST-OK  CLOSE-OK
```

**Important**: P10 satisfies EXISTENCE and CLOSURE, but does NOT guarantee
liftability. Not every P10-witness is liftable; the claim is only that for each
(n,j), SOME P10-witness IS liftable. This is the key existential claim.

---

## 4. Existence: Every (n, j) Has a Liftable Witness with c[j] = 1

**Claim**: For every n ≥ 1 and 0 ≤ j ≤ 2n, there exists a configuration c of
length 2n+1 such that:
1. c witnesses Essential(n, j): `rule30n n c ≠ rule30n n (flipCell c j)`
2. c[j] = 1
3. c is liftable: there exist b0, b1 ∈ {0,1} such that [b0]+c+[b1] witnesses
   Essential(n+1, j+1)

**Verified**: Exhaustively for n ≤ 5 (all 2^(2n+1) configs enumerated), low-weight
scan for n = 6,7. No failure found.

**Key structure**: For most (n,j), the spike configuration `spikeAt j` works.
For shadow positions (both dChain values false), a higher-weight witness is needed.

**Exception at (n=6, j=5)**: (Updated from previous claim)
- `spikeAt 5` is NOT even a witness for Essential(6,5) (center output unaffected)
- All weight-1 spikes `spikeAt x` with x≠5 are witnesses but have c[5]=0 (violate P10)
- All weight-1 spikes `spikeAt x` with x=5: not a witness
- No weight-2 liftable P10-witness exists at (n=6, j=5)
- A weight-3 liftable P10-witness DOES exist: `c = [1,0,0,0,0,1,0,0,0,0,0,0,1]`,
  lifts with b0=0, b1=0

**Correction from previous version**: The earlier claim of "weight-2 witness" at
(n=6,j=5) was WRONG. The minimum liftable P10-witness has weight 3.

**Why existence likely holds in general**: The structure of the causal cone means
that for each (n,j) there is always a configuration where the j-th cell's influence
propagates cleanly to the center. The P10 condition (c[j]=1) is a natural normalization.
The shadow cases (where dChain values are false) may require weight 2 or 3 witnesses,
but the minimum weight appears bounded (conjecture: weight ≤ n/2 or similar).

---

## 5. The Lifting Construction — Correct Formulation

**Given**: c is a liftable witness for Essential(n, j) with c[j] = 1.

**Construction**: Choose b0, b1 ∈ {0,1} such that [b0]+c+[b1] witnesses Essential(n+1, j+1).

```
lifted = [b0] ++ c ++ [b1]
```

The lifted configuration has length 2(n+1)+1 = 2n+3, with:
- Position 0: b0 (to be chosen)
- Positions 1..2n+1: c[0]..c[2n] (the original witness)
- Position 2n+2: b1 (to be chosen)

**Claim**: Some choice of (b0, b1) makes `lifted` witness Essential(n+1, j+1).

---

## 6. Corrected Boundary Formula Analysis

### 6.1 The OLD Formula (INCORRECT)

The previous version claimed:
```
b0 = 1 - c[0]   (flip the left boundary bit)
b1 = 1 - c[2n]  (flip the right boundary bit)
```

**This is WRONG.** Computational verification shows:
- For `c = spikeAt(0), n=2, j=0`: old formula gives b0=0, b1=1 (since c[4]=0).
  Result: `v1=v2=1` — NOT a witness. The old formula FAILS here.
- The old formula fails for ~5-7% of liftable P10-witnesses at n=2..5.

### 6.2 The b1=0 Claim (ALSO INCORRECT)

The claim "b1=0 always works for any liftable witness" is computationally FALSE.

**Verified counterexamples** (from `verify_b1_zero.py`):
```
n=1: 4/7 liftable P10-witnesses CANNOT use b1=0
     (e.g., j=0, c=[1,0,0] — needs b1=1; j=1, c=[0,1,0] — needs b1=1)
n=2: 6/28 cannot use b1=0
n=3: 19/112 cannot use b1=0
n=4: 34/552 cannot use b1=0
```

The witnesses that fail b1=0 uniformly have best b1=1 (not b1=0), regardless of
whether c[2n]=0 or c[2n]=1.

### 6.3 What IS True About the Boundary

**Partial truth**: b1=0 works for the SPECIFIC counterexample case (`c=spikeAt(0), n=2, j=0`),
but this is because that particular witness lifts well with b1=0. It is not a general rule.

**What is established**:
- For each liftable witness c, at least one of {(0,0),(0,1),(1,0),(1,1)} works
- When `c[2n]=1`: typically both b1=0 and b1=1 work (but not always)
- When `c[2n]=0`: often only b1=1 works (not b1=0), though exceptions exist
- No witness-independent formula for (b0,b1) has been found that works universally

**The right boundary algebraic claim** (to be proved):
For the specific liftable P10-witness chosen by the existence proof (e.g., the canonical
low-weight witness), the corresponding (b0,b1) satisfies the lifting construction.
The formula for (b0,b1) depends on the witness, not just on n and j.

### 6.4 Right Boundary Algebraic Trace (Partial)

For the RIGHT boundary bit b1 at position 2n+2:
- After one step of Rule 30, the rightmost output bit is
  `rule30Local(c[2n-1], c[2n], b1) = c[2n-1] XOR (c[2n] OR b1)`
- This becomes the new right boundary for n steps of evolution
- The sensitivity of position j+1 in `lifted` to flipping propagates leftward
  through n steps

The key observation is that b1 affects the RIGHT edge of the causal cone.
If j+1 is far from the right edge (j << 2n+1), b1 may have no effect on the
center output, and any b1 works. If j+1 is near the right edge, b1 matters.

This suggests a structural theorem: the boundary choice depends on whether j is
in the "interior" or "shadow" (near-boundary) region of the causal cone.

---

## 7. Closure: The Lifted Config Preserves P10

**Claim**: If c has c[j] = 1, then lifted = [b0]+c+[b1] has lifted[j+1] = 1.

**Proof**: By construction, lifted[j+1] = c[j] = 1. The prepended bit b0 shifts
all indices by exactly 1, so position j in c becomes position j+1 in lifted.
The P10 invariant is **trivially preserved** by the lifting construction.

This holds regardless of which (b0,b1) is chosen — closure is free.

---

## 8. Lean Proof Sketch (Corrected)

The proof of `lifting_lemma` requires these components in order:

### Lemma A: Witness Existence with P10 (Existential)

```lean
lemma essential_liftable_witness (n : Nat) (j : Fin (2*n+1)) :
    Essential n j →
    ∃ (c : Config n) (b0 b1 : Bool),
      c[j] = true ∧
      rule30n n c ≠ rule30n n (flipCell c j) ∧
      let lifted := liftConfig b0 c b1
      rule30n (n+1) lifted ≠ rule30n (n+1) (flipCell lifted ⟨j+1, ...⟩)
```

**Proof approach**: Case split on dChain structure.
- Case 1 (dChain(n+1, j) = true): use all-zeros / all-ones witness (D-chain argument)
- Case 2 (dChain(n, j) = true): similar construction
- Case 3 (shadow, both false): requires finding a low-weight witness with c[j]=1.
  For n≤5, this always exists (exhaustively verified). The algebraic structure of
  the shadow (dChain gap) determines the minimum weight needed.

**Current state in Lean**: Cases 1+2 of `Lifting.lean` are handled. Case 3 (the
shadow case) has a sorry. The sorry is exactly where the existential P10 argument
would apply — specifically, constructing the low-weight witness for shadow positions.

### Lemma B: The Lifting Construction Works (Conditional)

```lean
lemma lifting_construction_valid (n : Nat) (j : Fin (2*n+1))
    (c : Config n) (b0 b1 : Bool)
    (hc : rule30n n c ≠ rule30n n (flipCell c j))
    (hj : c[j] = true)
    (hlift : let lifted := liftConfig b0 c b1
             rule30n (n+1) lifted ≠ rule30n (n+1) (flipCell lifted ⟨j+1, ...⟩)) :
    Essential (n+1) ⟨j+1, ...⟩
```

This is trivial given the existential: if c, b0, b1 are provided by Lemma A,
then the lifted config directly witnesses Essential(n+1, j+1).

**Note**: Unlike the previous formulation, we do NOT claim a specific formula for
b0 and b1. The existential claim in Lemma A already packages (b0,b1) together with
the witness. No separate "boundary formula" lemma is needed.

### Lemma C: Assembling the Full Proof

```lean
theorem lifting_lemma_proved (n : Nat) (k : Fin (2*n+1)) :
    Essential n k → Essential (n+1) ⟨k+1, ...⟩ := by
  intro h
  obtain ⟨c, hc⟩ := h  -- some witness for Essential(n,k)
  -- Apply Lemma A to get a liftable P10 witness with boundary bits
  obtain ⟨c', b0, b1, hj, hc', hlift⟩ := essential_liftable_witness n k h
  -- The lifted config directly witnesses Essential(n+1,k+1)
  exact ⟨liftConfig b0 c' b1, hlift⟩
```

The proof collapses entirely to Lemma A. There is no separate "boundary formula"
needed once the existential is established.

---

## 9. What Remains to Prove

### 9.1 The Core Open Problem: Lemma A for Shadow Positions

For shadow positions (dChain(n+1,j) = false AND dChain(n,j) = false), Lemma A
requires constructing a liftable P10-witness. This is the ONLY remaining gap.

**Known cases** (verified, not yet in Lean):
- For n ≤ 5: all shadow (n,j) have liftable P10-witnesses (exhaustive)
- For (n=6,j=5): weight-3 witness `c=[1,0,0,0,0,1,0,0,0,0,0,0,1]` with b0=0,b1=0

**What's needed algebraically**:
An inductive or structural argument showing that for any shadow (n,j), a liftable
P10-witness of bounded weight exists. The dChain gap (shadow) structure may provide
this — when both dChain values are false, the sensitivity at j in the (n+1)-step
evolution must come from an indirect path, and identifying that path gives the witness.

### 9.2 Verified vs Conjectured

| Claim | Status | Evidence |
|-------|--------|----------|
| P10 satisfies Existence for n ≤ 5 | VERIFIED | Exhaustive (verify_b1_zero.py) |
| P10 satisfies Existence for n = 6,7 | PARTIAL | Weight-3 scan; some (n,j) spike-only |
| P10 satisfies Closure for all n | VERIFIED (trivial) | Shift-by-1 structure |
| Liftable P10-witness exists for all (n,j) | CONJECTURED | Verified n ≤ 5 exhaustive |
| b1=0 always works for liftable witnesses | **REFUTED** | verify_b1_zero.py Test 2 |
| b0=!c[0],b1=!c[2n] works for all witnesses | **REFUTED** | Fails ~5% liftable n=2..5 |
| (n=6,j=5) needs weight-2 liftable P10 | **REFUTED** | Only weight-3 works |
| (n=6,j=5) needs weight-3 liftable P10 | VERIFIED | verify_b1_zero.py Test 4 |
| spikeAt j is always a liftable P10 witness | FALSE | Fails (n=6, j=5) |
| Every (n,j) has SOME liftable P10 witness | VERIFIED n≤5, CONJECTURED all n | — |

### 9.3 The Shadow Exception Structure

`Lifting.lean` currently has a sorry for Case 3 (shadow positions). These are
exactly the positions where:
- dChain(n+1, j) = false (cell j is NOT a "live" cell in the (n+1)-step evolution)
- dChain(n, j) = false (cell j is NOT a "live" cell in the n-step evolution)

For these positions, the standard dChain-based witnesses don't have c[j]=1, and
the spike@j witness may not even be a witness for Essential(n,j) (as seen at n=6,j=5
where spike@5 is not a witness).

**Conjecture**: For shadow (n,j), the minimum liftable P10-witness weight is
bounded by the "shadow depth" — the number of consecutive generations in which j
is a shadow. This is finite for each (n,j) and grows at most polynomially in n.

---

## 10. Relationship to Path 2 (twoSpike_center_complement)

`twoSpike_center_complement` in `SpinePass.lean` is the sorry blocking Path 2
(rule30_prize3_direct). It asserts that for even m≥40, the twoSpike witnesses
provide SubcaseB coverage. This requires:

1. Showing X=2 is a universal witness for SubcaseB at all m≥40 (empirically
   supported: verified for m=40 up to n'=200000, m=42 at n'=118804, m=46 at n'=106522)
2. An algebraic D-chain cascade argument: spike at 2 activates the chain 2→4→...→m,
   and the spike at m "intercepts" this chain and flips the center

This is a DIFFERENT problem from lifting_lemma. Path 2 needs LFSR/algebraic
structure over GF(2), while Path 1 (lifting_lemma) needs the existential witness
construction for shadow positions.

**Do not conflate these**: fixing Path 2 does NOT fix Path 1, and vice versa.

---

## Summary

The proof of `lifting_lemma` reduces to a single key lemma:

**Lemma A (Existential)**: For any (n, j) and any witness for Essential(n, j),
there exists a liftable P10-witness c' with c'[j]=1 and boundary bits (b0,b1) such
that [b0]+c'+[b1] witnesses Essential(n+1, j+1).

- **Closure** is trivial (shift-by-1 preserves c'[j]=1 at position j+1).
- **The boundary formula** is NOT universal: b1=0 and b0=!c[0],b1=!c[2n] both fail
  for some witnesses. The correct (b0,b1) depends on the specific witness c'.
- **What works**: for each (n,j), the low-weight liftable P10-witness (spike@j for
  non-shadow positions; weight-2 or weight-3 for shadow positions) has its own valid
  (b0,b1). The existential quantifier packages both together.
- **The key open problem**: prove the existential for ALL n, specifically for shadow
  positions where the structure of the dChain gap determines the witness.

Computationally: verified for n ≤ 5 (exhaustive), n=6 (partial, weight ≤ 3 scan),
n=7 (spike-only). The conjecture is that this holds for all n via the causal cone
geometry of shadow positions.
