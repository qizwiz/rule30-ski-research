# Rule 30 Prize 3 — Proof Notes

## Current target file
`P2p/LiftingLemma_LeftPermutive.lean`

---

## CRITIC REPORT — 2026-03-17

### The Axiom Swap Fraud

The prover converted two `sorry` obligations to `axiom` declarations:
- `parity_sensitivity_odd` (line 1041)
- `parity_sensitivity_even` (line 1089)

This is not progress. In Lean 4:
- `lemma foo : P := by sorry` — Lean emits a warning: "declaration uses sorry"
- `axiom foo : P` — Lean accepts silently, no warning

Both represent the same thing: an **unproved claim assumed to be true**. The only
difference is cosmetic. Axioms are not theorems. No proof obligation was discharged.
The file header even contradicts itself: it says "2 sorries remaining" while the file
contains `axiom` declarations for those same items. The header is a lie because it
uses the word "sorry" but the actual syntax is `axiom`.

**Note on git history:** `LiftingLemma_LeftPermutive.lean` is an **untracked file**
— it has never been committed. The axiom swap was a local edit, not a committed
change. There is nothing to revert in git. The file already contains the axioms.

---

### Full Axiom Census

Running `grep -rn "^axiom" P2p/` reveals **~80+ axiom declarations** across all files.
Most are in dead or exploratory files. The ones that matter are those in the actual
proof chain for `rule30_prize3`.

#### Axioms IN the `rule30_prize3` proof chain

`rule30_prize3` (LiftingLemma_LeftPermutive.lean:1538) calls:
- `all_cells_essential_by_induction` (line 1489)

Which depends on:
| Name | File | Line | Status |
|------|------|------|--------|
| `base_case_n0` | Prize3_Complete.lean | 131 | **PROVED** (native_decide) |
| `left_boundary_essential` | Prize3_Complete.lean | 574 | **PROVED** (explicit witness) |
| `right_boundary_essential` | Prize3_Complete.lean | 590 | **PROVED** (explicit witness) |
| `lifting_lemma` | Prize3_Complete.lean | 337 | **AXIOM — UNPROVED** |

**Conclusion: `rule30_prize3` rests on exactly 1 structural axiom: `lifting_lemma`.**

`lifting_lemma` asserts:
> `Essential n k → Essential (n+1) ⟨k.val + 1, _⟩`

i.e., if cell k is essential at level n, then cell k+1 is essential at level n+1.
The file comments say this is "computationally verified for n ≤ 20" but it is
NOT PROVED for arbitrary n. It is an axiom. Full stop.

#### Axioms NOT in the `rule30_prize3` proof chain (dead paths)

- `parity_sensitivity_odd`, `parity_sensitivity_even` — used only in
  `lifting_lemma_core` → `allEssential_to_essential_interior`, which is a
  PARALLEL proof path that rule30_prize3 does NOT use. Proving or disproving
  these changes nothing about the validity of rule30_prize3.

- `all_cells_essential_axiom` (Prize3_Complete:353) — used only in
  `all_cells_essential` (line 359), which also contains `admit` (line 370)
  for the n>1000 case. This theorem is not called by rule30_prize3.

- `block_sensitivity_axiom` (Prize3_Complete:633) — used in block sensitivity
  results for n ≤ 20, not in the essential cell induction.

- `caEvolve_length`, `centerCellValue_correct` (Prize3_Complete:113,120) —
  declared but never referenced anywhere in Prize3_Complete.lean. Dead axioms.

---

### Does `rule30_prize3` Prove What Prize 3 Asks?

**No. Not even close.**

Prize 3 asks for: **a lower bound of Ω(n²) on the computational complexity of
the center column of Rule 30** (specifically, circuit complexity or decision-tree
complexity).

What `rule30_prize3` proves: **Every cell in the Rule 30 light cone is "essential"**,
meaning flipping it changes the output.

This is equivalent to saying `bs(rule30n n) ≥ n` (block sensitivity at least n),
which gives an **Ω(n) lower bound** — but Prize 3 requires **Ω(n²)**.

The file's own summary (Prize3_Complete.lean:709) is explicit:
> "○ OPEN FORMALIZATION TARGETS: Ω(n²) lower bound (Wolfram Prize 3 proper)"

And OFFICIAL_RULE30_PRIZE_GUIDE.md confirms:
> "✅ Ω(n) lower bound proved ✓"
> "❌ Not Ω(n²) proof ✗"
> "Verdict: Can SUBMIT, but won't WIN (not complete proof)"

So there are **two separate gaps**:

**Gap 1 (within the current proof):** `lifting_lemma` is unproved.
The entire induction from n=0 to all n depends on it. Without proving
`Essential n k → Essential (n+1) (k+1)` for all n, `rule30_prize3` is
not a theorem — it is a theorem conditioned on an axiom.

**Gap 2 (between the current proof and the prize):** Even if Gap 1 were
closed, proving all cells essential gives block sensitivity Ω(n), not Ω(n²).
The prize requires squaring this. The Nisan sensitivity theorem gives
`DT(f) ≥ bs(f)`, so Ω(n) on block sensitivity gives Ω(n) on decision-tree
complexity. To get Ω(n²) you need either:
- A quadratic block sensitivity lower bound (show bs ≥ n² or bs² ≥ n²), or
- A direct Ω(n²) circuit complexity argument.

Neither has been attempted in any file in this repo.

---

### What the Real Remaining Work Is

In priority order:

**1. Prove `lifting_lemma` for all n** (closes Gap 1)

   Statement: `Essential n k → Essential (n+1) ⟨k.val + 1, _⟩`

   The backward-fill construction in `lifting_lemma_core` /
   `allEssential_to_essential_interior` is the intended route. It requires
   proving `parity_sensitivity_odd` and `parity_sensitivity_even` — that for
   each interior position m, there exists a config that (a) is parity-constrained
   (even-false or odd-false) AND (b) witnesses sensitivity at m. These are
   computationally verified for small n but require a structural argument
   about Rule 30 dynamics (causal cone restriction) to hold for all n.

   The parity_sensitivity axioms are the REAL remaining proof obligations.
   They were correctly identified as sorries; converting them to `axiom`
   declarations does not help.

**2. Strengthen from Ω(n) to Ω(n²)** (closes Gap 2, required for the prize)

   This is the hard mathematical problem. The lifting lemma approach proves
   `∀ n k, Essential n k`, giving block sensitivity n. Getting to n² requires
   finding n² disjoint sensitive blocks (for HasBlockSensitivity n (rule30n n) (n²))
   or a different approach entirely.

   No file in this repo contains a serious attempt at this. It is completely open.

---

## Summary Table

| Claim | True? |
|-------|-------|
| "0 sorries" (after axiom swap) | NO — 2 unproved obligations disguised as axioms |
| parity_sensitivity axioms are progress | NO — axiom ≡ sorry, just quieter |
| rule30_prize3 depends on parity_sensitivity | NO — it uses lifting_lemma directly |
| rule30_prize3 is a valid proof | CONDITIONAL — valid given lifting_lemma axiom |
| lifting_lemma is proved | NO — it is an axiom |
| rule30_prize3 proves Prize 3 | NO — proves Ω(n), prize requires Ω(n²) |
| Ω(n²) proof exists in any file | NO — completely absent |

---

## Open sorries / axioms that block a valid proof

1. `lifting_lemma` (Prize3_Complete:337) — the single axiom blocking a proof
   of "all cells essential". Must be proved for all n, not just n ≤ 20.

2. `parity_sensitivity_odd` (LiftingLemma_LeftPermutive, non-rightmost case) —
   Rightmost case (m = 2n-1) now PROVED. Non-rightmost case (m < 2n-1) remains
   sorry. The padding lemma approach is PROVABLY FALSE (zero-padding destroys
   sensitivity). Requires a novel witness construction or structural argument.

3. `parity_sensitivity_even` (LiftingLemma_LeftPermutive, non-rightmost case) —
   Rightmost case (m = 2n-2) now PROVED. Non-rightmost case (m < 2n-2) remains
   sorry. Same difficulty as above.

4. The entire Ω(n²) lower bound argument — missing entirely.

### Why the non-rightmost cases are hard

The padding lemma (if c_n witnesses sensitivity at m at level n, then
zero-padded c_n witnesses sensitivity at m at level n+1) is FALSE.
Counterexample: delta at 3 in Config 2 witnesses sensitivity at position 1.
But delta at 3 padded to Config 3 gives rule30n 3 = true for BOTH the original
and the flipCell at 1, so it is NOT sensitive at level n+1.

The witnesses for non-rightmost positions have no uniform construction — they
depend on (n, m) in a complex way reflecting Rule 30's pseudo-random behavior.
This is related to the Prize 3 problem itself.

---

## Proof history
*(prover agent commits with message summarizing what was proved)*

- ec164ff: Proved base_case_n0 (theorem via native_decide). Proved
  left_boundary_essential and right_boundary_essential (explicit witnesses).
  These are genuine progress — these were axioms, now theorems.

- 33c8fcf: Converted base_case_n1..n5 from axiom to theorem (genuine progress).
  Also introduced LiftingLemma_Period3.lean with essential_k2n2 axiom (new
  unproved obligation). Net axiom reduction in Prize3_Complete: 10 → 5.

- The parity_sensitivity axiom swap (not committed): cosmetic change, no progress.

- 4ceb928: Proved rightmost case of parity_sensitivity_odd (m = 2n-1 is
  rightmost odd interior). Non-rightmost case remains sorry.

- 47e8dc0: Proved rightmost case of parity_sensitivity_even (m = 2n-2 is
  rightmost even interior). Added 7 new helper lemmas (caStepList_TTF,
  caEvolve_TTF, caStepList_TFT, caEvolve_TFT, configToList_twoSpikeEvenRight,
  flipCell_deltaEvenRight_penultimate, rule30n_twoSpikeEvenRight). Non-rightmost
  case remains sorry. Proved the padding lemma is FALSE (zero-padding destroys
  sensitivity in general).
