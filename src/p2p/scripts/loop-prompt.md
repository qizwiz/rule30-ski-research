You are an autonomous research agent working on the Wolfram Prize 3 proof in /Users/jonathanhill/src/p2p.

## Your job

Do exactly ONE unit of meaningful work, then commit it. Do not stop to ask questions. Do not leave the repo in a broken state. Always end with a git commit.

## Before you start

1. Read CLAUDE.md — ranked task list and current state.
2. Run `scripts/proof-gate check` to see obligation count and locations.
3. Run `git log --oneline -8` — don't repeat recent work.
4. Check running builds: `ps aux | grep "lake build" | grep -v grep`
5. Check rule30_meta output: `tail -5 /tmp/rule30_meta_output.txt 2>/dev/null`
6. Check CA_Array_residues: `tail -3 /tmp/ca_residues_build.log 2>/dev/null`

## LEAN PROBE TOOL (fast, ~15s, no full build needed)

```bash
cat > /tmp/probe.lean << 'EOF'
import P2p.CausalConeLemmas
import P2p.Prize3_Complete
namespace P2p
example : YOUR_CLAIM := by ?_
end P2p
EOF
lake env lean /tmp/probe.lean 2>&1 | grep -A 20 "unsolved goals\|⊢\|error"
```

## CURRENT STATE (loop79, 2026-04-01)

**5 obligations**:
1. `subcaseB_m4_ge3087` — axiom, main target (line 1139 SubcaseBPeriod.lean)
2. `subcaseB_resolution_ge3087` — master axiom (assembles sub-cases; closes when #1 closes)
3. `subcaseB_m22_l0_sorry` — line 2417 SubcaseBPeriod.lean (m=22 algebraic barrier)
4. `subcaseB_m28_residue_3class_proved` — axiom CA_Array.lean (CA_Array_residues building)
5. `subcaseB_m30_residue_unique_proved` — axiom CA_Array.lean (CA_Array_residues building)

**Recent loop progress**: loops 77/78/80 proved 3 mechanical m=4 mod64 sub-cases.
**The loop must now ALTERNATE between two tracks:**

---

## TRACK A: LINEARITY CORRIDOR (known proof path for m=4 axiom)

The algebraic proof of `subcaseB_m4_ge3087` decomposes into 4 Lean lemmas.
**WARNING**: The corridor was designed for the right-boundary family (m=2n'-6).
`f_center_prev_zero` does NOT hold for fixed m directly — it needs adaptation.
Treat all 4 lemmas as targets to attempt, not guarantees to close.

### Lemma A1: nl_zero_when_both_zero (TRIVIAL — try first)

```lean
lemma nl_zero_when_both_zero (a' b' : Bool) :
    (false || false) ^^ (a' || b') ^^ ((false ^^ a') || (false ^^ b')) = false := by
  cases a' <;> cases b' <;> decide
```

Add to SubcaseBPeriod.lean or new LinearityCorridor.lean. Probe it first.

### Lemma A2: hcone_left_edge (MEDIUM)

Spike at position `2*(n'+1)` after `n'` steps can't reach position `n'+1` (causality).
Check if CausalConeLemmas.lean already has a zero-outside-cone lemma.
If yes, hcone_left_edge may follow directly.

### Lemma A3: f_center_prev_zero (HARD — anti-diagonal)

R30(7-t, t) = 0 for ALL t in infinite Rule 30 from spike at 0.
Verified computationally t=0..2000. Unique zero anti-diagonal among k=0..12.

**Approach**: Try native_decide for finite t ≤ 150 on appropriately-sized finite tape.
This gets a partial Lean theorem even if the full induction is hard.

```python
# First verify the finite formulation matches:
# (caEvolve (t+1) (spikeAtList 0 (2*(t+1)+20))).getD (7-t) false = false
# Run this Python check before writing Lean:
```

### Lemma A4: d_leftbound (HARD — D-field support)

D-field min support ≥ center+2 at step T-1.
D first appears at step 4 at position ≥ 2n'-2.
Drift ≤ 1 per step → min_support at T-1 ≥ 2n'-2-(T-5) = n'+3-5 = ... verify arithmetic.
Python-verify this bound before attempting Lean.

---

## TRACK B: EXPLORATION (open questions, may reveal new proof angles)

**Why explore?** The corridor may need adaptation. Exploration finds either a better
path or confirms the corridor is the only one. Run one exploration task per 2 loop iterations.

### B1: D-field structure at Level 3+ (mod16384=5, the hard m=4 case)

The rule30_meta.py is running (PID varies, output at /tmp/rule30_meta_output.txt).
If it has output: extract D-field patterns at specific Level 3+ positions.
If NOT done: write a FOCUSED Python script that only checks n'≡5 mod 16384 positions
(e.g., n'=16389, 32773, 49157) and asks: what is the MINIMUM w at each? Is there a pattern?

```python
# Quick Level 3+ probe (runs in minutes, not hours):
for n_prime in [16389, 32773, 49157, 65541]:
    # find min_w at this specific n'
    # compare with prediction min_w ~ 2.5*log2(n')
```

### B2: Witness LFSR analysis

The SEQUENCE of which w values are witnesses at fixed n' (varying mod residue) has structure.
Run BM on the indicator sequence: for n' = 5, 13, 21, ..., 3093, ..., is_witness(n', w=6)?
What is the linear complexity? Does it match L=5 (the m=4 LFSR entry)?

```python
# Compute: for n' in SubcaseB positions, does w=6 witness? → binary sequence
# BM that sequence → compare with F-sequence LC=5
```

### B3: Prize 1+2+3 connection

Prize 1 (non-periodic center column) + Prize 2 (density → 1/2) + Prize 3 (Ω(n) complexity).
We know: F-sequence density = 1/2 exactly (proved). Does this connect to Prize 2?
Wolfram Prize 2: "Prove that the density of black cells in Rule 30 center column → 1/2."
Our F-sequence result says: F(n', m=4) = 0 exactly half the time. Is that Prize 2?
Investigate: is Prize 2 about the SAME sequence as our F-sequence, or something different?

```python
# Compute actual center-column density for rule30 from standard spike initial condition
# Compare with F-sequence density
# Are these the same object?
```

### B4: m=22 l≡0 sorry — algebraic angle

m=22 sorry at line 2417 needs P=131072 period certs (infeasible with native_decide).
Alternative: can we use the LFSR structure of twoSpike(34,22) directly?
BM on the twoSpike(34,22) center-output sequence → connection polynomial → algebraic period cert.
If connection poly has degree D, period ≤ 2^D. If D is small, algebraic cert is feasible.

---

## DECISION LOGIC FOR THIS LOOP

Look at `git log --oneline -3`:
- If last 2 commits were Track A → do Track B this time
- If last commit was Track B → do Track A this time
- If CA_Array_residues build just finished → integrate it FIRST (closes 2 free obligations)
- If rule30_meta.py has output → read it and commit the findings to research/findings.md

## BUILD RULES

- NEVER wait for a build interactively — always background: `nohup lake build ... > /tmp/build.log 2>&1 &`
- NEVER start parallel builds — check first with `ps aux | grep "lake build"`
- CA_Array.lean has a clean olean — do NOT rebuild unless integrating CA_Array_residues
- SubcaseBPeriod.lean has a clean olean — do NOT rebuild unless adding new lemmas

## COMMIT FORMAT

`loop<N>: <track>: <what you did>`

Examples:
- `loop81: corridor: prove nl_zero_when_both_zero`
- `loop82: explore: D-field Level3+ min_w scan confirms log(n') growth`
- `loop83: corridor: native_decide f_center_prev_zero t≤100`

Always increment N from the last commit's loop number.
