You are an autonomous research agent working on the Wolfram Prize 3 proof in /Users/jonathanhill/src/p2p.

## Your job

Do exactly ONE unit of meaningful work, then commit it. Do not stop to ask questions. Do not leave the repo in a broken state. Always end with a git commit.

---

## ⚠️ SELF-MODIFICATION RULES (read before anything else)

This file is self-modifying. You MAY update the TRACK A and TRACK B sections below
when you have concrete evidence. You MUST follow these safeguards:

**ALLOWED updates:**
- Mark a lemma/task as `✓ DONE` with the loop number that closed it
- Mark an approach as `✗ REFUTED` with the reason (cite evidence: script output, Lean error, etc.)
- Add a new exploration task to Track B when data suggests it
- Promote a Track B finding to Track A if it opens a proof path
- Update the "CURRENT STATE" section with new obligation counts or build status

**FORBIDDEN updates:**
- Never remove the `## ⚠️ SELF-MODIFICATION RULES` section
- Never remove the `## BUILD RULES` section
- Never remove the `## DECISION LOGIC` section
- Never change the COMMIT FORMAT
- Never update without a concrete reason (no speculative reshuffling)
- Never claim something is ✓ DONE unless `scripts/proof-gate check` confirms the count dropped
  OR the Lean probe returns clean output with no errors

**HOW TO UPDATE:**
1. Make your code/proof change first
2. Run verification (proof-gate check, lean probe, or Python output)
3. THEN edit this file to reflect what you learned
4. Stage BOTH the proof change AND the loop-prompt change in the same commit
5. Add `[prompt updated: reason]` to the commit message

---

## Before you start

1. Read CLAUDE.md — ranked task list and current state.
2. Run `scripts/proof-gate check` — note the count.
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

---

## CURRENT STATE (auto-updated by loop)

**Obligations**: 5 (as of loop80)
- `subcaseB_m4_ge3087` — axiom, line 1139 SubcaseBPeriod.lean — MAIN TARGET
- `subcaseB_resolution_ge3087` — master axiom, line 4893 — closes when m4 closes
- `subcaseB_m22_l0_sorry` — line 2417 — algebraic barrier (P=131072, infeasible native_decide)
- `subcaseB_m28_residue_3class_proved` — CA_Array.lean axiom — CA_Array_residues building
- `subcaseB_m30_residue_unique_proved` — CA_Array.lean axiom — CA_Array_residues building

**Build status**:
- SubcaseBPeriod.lean: ✓ clean olean (build9, loop72)
- CA_Array.lean: ✓ clean olean
- CA_Array_residues.lean: BUILDING at /tmp/ca_residues_build.log

**Recent work**: loops 77/78/80 proved 3 mechanical m=4 mod64 sub-cases (mod16=13, mod64=53, mod64=21)

---

## TRACK A: LINEARITY CORRIDOR (known proof path for m=4 axiom)

**⚠️ CAVEAT**: Corridor was designed for right-boundary family (m=2n'-6).
`f_center_prev_zero` does NOT hold for fixed m directly — needs adaptation.
Proceed but treat each lemma as a target to attempt, not a guarantee.

### A1: nl_zero_when_both_zero — STATUS: OPEN

```lean
lemma nl_zero_when_both_zero (a' b' : Bool) :
    (false || false) ^^ (a' || b') ^^ ((false ^^ a') || (false ^^ b')) = false := by
  cases a' <;> cases b' <;> decide
```
Pure truth-table. Try it with the probe tool first, then add to SubcaseBPeriod.lean.

### A2: hcone_left_edge — ✓ DONE (loop83)

Proved in LinearityCorridor.lean. Key insight: after n' steps the tape
(length 2*(n'+1)+1 = 2n'+3) has length exactly 3, so index n'+1 ≥ 3 is
out of bounds → getD returns false. Uses caEvolve_length_le + omega.
Holds for n' ≥ 2 (fails for n' = 1 which gives T=true).

### A3: f_center_prev_zero — STATUS: OPEN (hard, needs adaptation for fixed m)

R30(7-t, t) = 0 for all t in infinite Rule 30 from spike at 0.
Computationally verified t=0..2000. Unique zero anti-diagonal among k=0..12.

Step 1: Python-verify the finite-tape formulation matches:
`(caEvolve (t+1) (spikeAtList 0 (2*(t+1)+20))).getD (7-t) false = false`

Step 2: native_decide for t ≤ 100 as a finite stepping stone.

Step 3: Full induction (hard — parity argument applies to Rule 90 but Rule 30 needs more).

### A4: d_leftbound — STATUS: OPEN (hard)

D-field min support ≥ center+2 at step T-1.
Python-verify the bound before attempting Lean: check n'=8..100 that D[center+1]_{T-1}=0.

---

## TRACK B: EXPLORATION

Run one Track B task for every 2 Track A tasks. Rotate through open items.

### B1: D-field at Level 3+ (mod16384=5) — STATUS: OPEN

rule30_meta.py running at PID unknown, output /tmp/rule30_meta_output.txt.
If output exists: extract D-field patterns at Level 3+ positions.
If NOT done: write focused Python for ONLY n'≡5 mod 16384 positions (n'=16389, 32773, 49157):
- What is min_w at each?
- What is the D-field SHAPE (not just center value) at T-1?
- Does the D-field have a period at these positions?

### B2: Witness LFSR — STATUS: OPEN

For n' in SubcaseB positions (5,13,21,...), does w=6 witness? → binary sequence.
Run BM on that sequence. Compare LC with F-sequence LC=5.
Does the witness-existence sequence have the SAME connection polynomial as the F-sequence?
If yes: witnesses are algebraically tied to F=0, not independent → proof leverage.

### B3: Prize 2 connection — ✓ DONE (loop82)

**Finding**: NO connection between Prize 2 and Prize 3.
- F(n', m=4) is a simple **period-8 LFSR sequence** (`10110100` repeating), density exactly 1/2.
- Prize 2 center column (standard Rule 30 from spike at 0) is **aperiodic/complex**, no LFSR structure.
- No correlation above chance between Prize 2 center column and any F(n', m) for m=0..12.
- Prize 2 and Prize 3 are independent problems; our proof does NOT automatically prove Prize 2.
- Data written to research/findings.md "Track B3" section.

### B4: m=22 algebraic angle — STATUS: OPEN

twoSpike(34, 22) needs P=131072 — infeasible with native_decide.
Run BM on twoSpike(34,22) center-output sequence to find connection polynomial.
If degree D is small (say ≤ 20), an algebraic period cert is feasible.
Compare with twoSpike(40,22) and twoSpike(42,22).

---

## DECISION LOGIC

Check `git log --oneline -3`:
- If last ≥2 commits were Track A → do Track B this iteration
- If last commit was Track B → do Track A this iteration
- **ALWAYS first**: if CA_Array_residues build finished → integrate immediately (closes 2 free obligations)
- **ALWAYS first**: if rule30_meta.py has new output → read it, update findings.md, commit

---

## BUILD RULES (protected — never modify)

- NEVER wait for a build — background only: `nohup lake build ... > /tmp/build.log 2>&1 &`
- NEVER start parallel builds — check `ps aux | grep "lake build"` first
- CA_Array.lean has clean olean — do NOT rebuild unless integrating CA_Array_residues
- SubcaseBPeriod.lean has clean olean — do NOT rebuild unless adding proved lemmas

---

## COMMIT FORMAT (protected — never modify)

`loop<N>: <track>: <what you did> [prompt updated: <reason>]`

The `[prompt updated: reason]` suffix is ONLY added when this file was also changed.

Examples:
- `loop81: corridor: prove nl_zero_when_both_zero [prompt updated: A1 marked done]`
- `loop82: explore: D-field Level3+ min_w scan [prompt updated: B1 finding added]`
- `loop83: corridor: native_decide f_center_prev_zero t≤100`

Always increment N from the last commit's loop number.

---

## SELF-MODIFICATION CHANGELOG

| Loop | Change | Reason |
|------|--------|--------|
| 79   | Created Track A + Track B structure | Session: corridor + exploration both needed |
| 79   | Added self-modification rules | User instruction: loop should improve itself |
| 82   | B3 marked ✓ DONE | Python verified: Prize 2 ≠ F(n',m), F(n',4) period=8 |
| 83   | A2 marked ✓ DONE | hcone_left_edge proved: tape-runs-out argument (len=3, idx≥3 OOB) |
