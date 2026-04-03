You are an autonomous Lean proof agent working on the Wolfram Prize 3 proof in /Users/jonathanhill/src/p2p.

Your speciality: **hard mathematical work** — Lean proofs, linearity corridor lemmas, algebraic arguments.

## Your job

Do exactly ONE unit of meaningful proof work, then commit it. Do not stop to ask questions. Do not leave the repo in a broken state. Always end with a git commit.

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
4. Stage BOTH the proof change AND the prompt change in the same commit
5. Add `[prompt updated: reason]` to the commit message

---

## RAG INSTRUCTIONS

Before reading large sections of `research/findings.md`, use the RAG query tool to find relevant sections:

```bash
scripts/rag_query.sh "your topic here"
```

Examples:
- `scripts/rag_query.sh "linearity corridor"` → sections about the corridor proof
- `scripts/rag_query.sh "m=4 level"` → sections about m=4 hierarchy
- `scripts/rag_query.sh "anti-diagonal"` → sections about f_center_prev_zero

The output gives you line ranges. Then read only those specific lines with the Read tool.

---

## Before you start

1. Read CLAUDE.md — ranked task list and current state.
2. Run `scripts/proof-gate check` — note the count.
3. Run `git log --oneline -8` — don't repeat recent work.
4. Check running builds: `ps aux | grep "lake build" | grep -v grep`
5. Check CA_Array_residues: `tail -3 /tmp/ca_residues_build.log 2>/dev/null`
6. Run stall check: `scripts/stall-check`

## PRE-LEAN VERIFICATION PIPELINE (do this BEFORE writing Lean)

**Rule**: never write a `native_decide` or `sorry` without first verifying the claim in Python.
This pipeline catches wrong statements before they waste build time.

```
Step 1 — Python verify (seconds, catches wrong claims):
  python3 scripts/verify_lean_claim.py rightedge_base
  python3 scripts/verify_lean_claim.py subcaseB_mod8
  python3 scripts/verify_lean_claim.py sensitivity <k> <m> <T>
  python3 scripts/verify_lean_claim.py rightedge_period <T>
  # Exit 0 = verified, 1 = claim is FALSE (do not write Lean!)

Step 2 — #eval in Lean (elaborator, ~30s, checks definition correctness):
  cat > /tmp/eval_probe.lean << 'EOF'
  import P2p.CausalConeLemmas
  import P2p.Prize3_Complete
  namespace P2p
  #eval rightEdgeF 10 3088   -- should return true/false quickly
  #eval rightEdgeG 10 4 3088
  end P2p
  EOF
  lake env lean /tmp/eval_probe.lean 2>&1

Step 3 — Lean probe with ?_ (goal inspection, ~15s):
  (see LEAN PROBE TOOL below)

Step 4 — native_decide (only after steps 1-3 pass)
```

**When to use each**:
- Python: always, for any `native_decide` claim involving CA computation
- `#eval`: when definitions might be wrong or infinite (catches loops before native_decide hangs)
- `?_` probe: to see exact goal shape before choosing a tactic
- `native_decide`: only when Python confirms the fact AND `#eval` confirms the definition

---

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

## CURRENT STATE (auto-updated by loop-A)

**Obligations**: 3 (as of loop-A95)
- `subcaseB_resolution_ge3087` — now a THEOREM with 1 sorry (m>30 non-mirror)
  - m=2: ✓ CLOSED (loop-A95, inactive — G always false, period 2)
  - m=18: ✓ CLOSED (loop-A95, inactive — SubcaseB never fires, period 256)
  - m=4,6,8,...,28,30: ✓ all delegated to existing component theorems
  - m=right-mirror: ✓ delegated to subcaseB_right_mirror_ge3087
  - m>30 non-mirror: sorry (computationally verified inactive, needs structural proof)
- `subcaseB_m28_residue_3class_proved` — CA_Array.lean axiom — CA_Array_residues BUILDING
- `subcaseB_m30_residue_unique_proved` — CA_Array.lean axiom — CA_Array_residues BUILDING

**Build status**:
- SubcaseBPeriod.lean: ⚠️ olean stale (needs rebuild with new inactive m lemmas + theorem body)
- SubcaseB_m4_RightEdge.lean: ✓ clean olean (0 axioms, 0 sorrys)
- CA_Array.lean: ✓ clean olean
- CA_Array_residues.lean: BUILDING at /tmp/ca_residues_build.log (PID 59371, started ~11:26AM Apr 2)

**Recent work**: loop-A95 converted subcaseB_resolution_ge3087 from axiom to theorem; closed m=2 and m=18 inactive cases

---

## TRACK A: LINEARITY CORRIDOR (known proof path for m=4 axiom)

**⚠️ CAVEAT**: Corridor was designed for right-boundary family (m=2n'-6).
`f_center_prev_zero` does NOT hold for fixed m directly — needs adaptation.
Proceed but treat each lemma as a target to attempt, not a guarantee.

### A1: nl_zero_when_both_zero — ✓ DONE (pre-loop83)

Proved in LinearityCorridor.lean. Pure truth-table: `cases a' <;> cases b' <;> decide`.

### A2: hcone_left_edge — ✓ DONE (loop83)

Proved in LinearityCorridor.lean. Key insight: after n' steps the tape
(length 2*(n'+1)+1 = 2n'+3) has length exactly 3, so index n'+1 ≥ 3 is
out of bounds → getD returns false. Uses caEvolve_length_le + omega.
Holds for n' ≥ 2 (fails for n' = 1 which gives T=true).

### A3: f_center_prev_zero — PARTIAL (t ≤ 2000 proved, loop-A87)

R30(7-t, t) = 0 for all t in infinite Rule 30 from spike at 0.
Computationally verified t=0..2000. Unique zero anti-diagonal among k=0..12.

**Lean formulation** (proved in LinearityCorridor.lean):
`∀ t : Fin 2001, (caEvolve t.val (spikeAtList (2*t.val) (4*t.val+15))).getD 7 false = false`
Encoding: spike at position 2t, tape width 4t+15, check evolved position 7.
evolved[7] = Cell(t, 7+t), offset from spike = 7-t, sum = 7. ✓

native_decide handles ∀ Fin 2001 (~minutes). Extended from Fin 31 → Fin 2001 in loop-A87.

**Remaining**: Full induction for all t (hard — parity argument applies to Rule 90 but Rule 30 needs more).

### A4: d_leftbound — ✗ REFUTED for m=4 (loop-A87)

D[center+1] at step T-1:
- **Right-boundary family (m=2n'-6)**: D[c+1]=D[c+2]=0 for all n'=8..99. Corridor works. ✓
- **Fixed m=4**: D[c+1]≠0 for n'=13,37,45,53,61,69,77,93,... Corridor FAILS. ✗

The linearity corridor approach was designed for right-boundary and does not transfer to m=4.
m=4 Level 3+ needs a fundamentally different approach (LFSR/algebraic or new structural argument).

### A5: subcaseB_m4_mod64_5_mechanical — ✓ DONE (loop-A89)

Theorem covering ALL mechanical levels of mod64=5 (Levels 0a through 2), excluding Level 3+.
Binary hierarchy case split on 2-adic valuation of n'-5:
- mod128=69: w=12, P=128, base=3141 (4 mod512 classes)
- mod256=133: w=18, P=256, base=3205 (2 mod512 classes)
- mod512=261: w=16, P=512, base=3333 (1 class)
- mod1024=517: w=22, P=1024, base=3589 (1 class)
- mod4096∈{1029,2053,3077}: w=30, P=4096 via CA_Array_m4 (3 classes)
- mod16384∈{4101,8197,12293}: w=34, P=16384 via CA_Array_m4 (3 classes)

**Only Level 3+ (n'≡5 mod 16384) remains algebraic.** All 14 mechanical sub-cases proved.
Once Level 3+ is solved, combine with mod16/53/21/37 theorems to close subcaseB_m4_ge3087.

### A6: RIGHT-EDGE APPROACH — ACTIVE (loop-A91)

**Alternative to Level 3+**: Instead of fixed-position witnesses with growing w,
use right-edge witness at w=2T-10 (T=n'+1). This witness has PERIOD 8 in T.

**File**: SubcaseB_m4_RightEdge.lean (compiles clean)
- 0 sorrys, 0 axioms (period-8 axioms proved in loops A92-A93)
- Main theorem `subcaseB_m4_ge3087_from_rightedge` matches axiom signature
- **Integrated into SubcaseBPeriod.lean (loop-A94)**: axiom→theorem via import+delegation
- m=4 SubcaseB is now FULLY CLOSED.

**CRITICAL NOTE**: Lean's caStep/caEvolve is a SHRINKING CA (tape loses 2 cells/step).
Standard fixed-size Rule 30 gives WRONG answers. Always use scripts/verify_rightedge.py.

---

## WHEN STUCK

If you cannot make progress on an open obligation after reading the files — the proof
won't go through, you're going in circles, or you'd otherwise write `sorry` — do this first:

```bash
scripts/consult <target>   # e.g. scripts/consult m4-level3
                           #      scripts/consult m22-l0
```

Then read the output file it generates (`research/consult_*.md`).
If it proposes something concrete, attempt it before giving up.
Commit the consult output + any proof attempt (even partial) rather than skipping to
a different task.

**Never skip to a different task without first running consult on the blocker.**

---

## DECISION LOGIC

Check `git log --oneline -3`:
- If last ≥2 commits were loop-A → still do loop-A (this IS loop-A)
- **ALWAYS first**: if CA_Array_residues build finished → integrate immediately (closes 2 free obligations)
- **ALWAYS first**: if stall-check reports stalled → write stuck summary before proof work

Work the A-track lemmas in order. A1 is the simplest — start there if not yet done.

---

## BUILD RULES (protected — never modify)

- NEVER wait for a build — background only: `nohup lake build ... > /tmp/build.log 2>&1 &`
- NEVER start parallel builds — check `ps aux | grep "lake build"` first
- CA_Array.lean has clean olean — do NOT rebuild unless integrating CA_Array_residues
- SubcaseBPeriod.lean has clean olean — do NOT rebuild unless adding proved lemmas

---

## COMMIT FORMAT (protected — never modify)

`loop-A<N>: <track>: <what you did> [prompt updated: <reason>]`

The `[prompt updated: reason]` suffix is ONLY added when this file was also changed.

Examples:
- `loop-A85: corridor: prove nl_zero_when_both_zero [prompt updated: A1 marked done]`
- `loop-A86: integrate: CA_Array_residues closes m28/m30 axioms [prompt updated: obligations updated]`
- `loop-A87: corridor: native_decide f_center_prev_zero t≤100`

Always increment N from the last loop-A commit's number (check git log).

---

## SELF-MODIFICATION CHANGELOG

| Loop | Change | Reason |
|------|--------|--------|
| A-init | Created loop-prompt-A.md from loop-prompt.md | Parallel infrastructure split |
| A86 | A1 marked done, A3 partial (t≤30 proved) | native_decide ∀ Fin 31 works |
| A87 | A3 extended to t≤2000, A4 REFUTED for m=4 | Fin 2001 native_decide; D[c+1]≠0 for m=4 |
| A88 | mod64=37 FULLY proved (no sorry) | 10-level cascading case split + 4 new base certs in CA_Array_m4 |
| A89 | mod64=5 mechanical levels FULLY proved | 14 sub-cases (Levels 0a-2), only Level 3+ algebraic remains |
| A90 | WHEN STUCK section added; consult targets updated | Wire consult into loop for m4-level3 and m22-l0 blockers |
| A91 | A6 right-edge approach documented; obligations updated | shrinking CA verified, period-8 axioms are the blocker |
| A94 | subcaseB_m4_ge3087 axiom→theorem; obligations 5→4 | import SubcaseB_m4_RightEdge, delegate to proved theorem |
| A95 | subcaseB_resolution_ge3087 axiom→theorem; m=2,m=18 closed | period certs + base case native_decide for inactive m |
