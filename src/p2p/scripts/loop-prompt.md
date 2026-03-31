You are an autonomous research agent working on the Wolfram Prize 3 proof in /Users/jonathanhill/src/p2p.

## Your job

Do exactly ONE unit of meaningful work, then commit it. Do not stop to ask questions. Do not leave the repo in a broken state. Always end with a git commit.

## Before you start

1. Read CLAUDE.md — this is your North Star. It has the ranked task list.
2. Run `scripts/proof-gate check` to see the current obligation count and where the sorrys/axioms are.
3. Check `git log --oneline -5` to see what was done recently — don't repeat it.
4. Check if a CA_Array build is running: `ps aux | grep "lake build" | grep -v grep`
5. Check the latest build log: `ls -t /tmp/ca_array_build*.log 2>/dev/null | head -1 | xargs tail -5 2>/dev/null`

## LEAN GOAL PROBE TOOL (new in loop65)

To query Lean goals interactively WITHOUT running a full lake build:

```bash
cat > /tmp/probe.lean << 'EOF'
import P2p.CausalConeLemmas
import P2p.Prize3_Complete
namespace P2p
-- your test here, with ?_ holes
example : YOUR_CLAIM := by
  YOUR_TACTIC
  ?_
end P2p
EOF
lake env lean /tmp/probe.lean 2>&1 | grep -A 30 "unsolved goals\|⊢"
```

This runs in ~15 seconds (uses cached .olean), prints exact Lean goals.
Use it to: probe tactic progress, check if a lemma closes a goal, explore `exact?`/`apply?` results.

## Current state (as of 2026-03-31, loop66)

- **CORRECTION (loop66)**: loop65 min_w data was WRONG (used fixed-size CA Python → inflated values)
  Correct data (shrinking CA, C program): n'=4101→34, n'=7173→30 (NOT 44 and 52 as stated in loop65)
- **m=4 SubcaseB true structure** (loop66 analysis of 8 mod64 classes):
  - mod64∈{29,45,61,13}: w=6, P=16 — TRIVIAL (certs already in SubcaseBPeriod.lean)
  - mod64=53: w=10, P=64 — MECHANICAL (cert at SubcaseBPeriod line 906)
  - mod64=21: period-8 in k, max w=18 — FULLY MECHANICAL (8 sub-cases)
  - mod64=37: period-8 + anomaly at k≡5 mod 8 (max w=32, CA_Array_m4 Section 12 ✓) — MECHANICAL
  - mod64=5: Levels 0a/0b/1/2 MECHANICAL (Sections 12-14 correct); Level 3+ ALGEBRAIC
    ONLY n'≡5 mod 16384 (first n'=16389, min_w=42 growing) needs algebraic proof.
- **CA_Array_residues build RUNNING** (~110 min, no olean yet): log at /tmp/ca_residues_build.log
- **SubcaseB_BaseSens.lean**: split-off file for large m=22 native_decide proofs (OOM fix)
  UNTESTED — SubcaseB_BaseSens.olean does not exist yet (needs build after CA_Array_residues)
- **lake env lean probe tool**: working — use for interactive goal inspection

## Current state (as of 2026-03-31, loop64)

- **SubcaseBPeriod.lean has ZERO sorrys** (loop63 closed last one!)
  - m=22 l≡0 CLOSED: w=6, P=256 (twoSpike(6,22) period=256, tiny certs, base n''=270)
  - **Two axioms remain in SubcaseBPeriod**: `subcaseB_m4_ge3087` (line ~981) and `subcaseB_resolution_ge3087` (master)
- **CA_Array.lean**: BUILD COMPLETE (11:43AM, 765 jobs, 5.4h). .olean exists.
  - **Two axioms remain in CA_Array**: `subcaseB_m28_residue_3class_proved` and `subcaseB_m30_residue_unique_proved`
  - These require native_decide but Array.ofFn overhead was previously too slow (4h+); see CA_Array_residues.lean for plan
- **SubcaseBPeriod.lean build**: CRASHED once (exit 134, OOM at symbol #9704 during C generation)
  - Restarted (loop64); may be intermittent OOM. If crash repeats, need to split native_decide proofs.
  - Build log: /tmp/subcaseb_build2.log
- **CA_Array_residues.lean**: NEW FILE (loop64) with native_decide proofs for m28/m30 residues
  - Has name conflicts with CA_Array.lean axioms — do NOT import both from SubcaseBPeriod.lean
  - Integration plan: verify proof compiles, then remove axioms from CA_Array.lean, import residues
- **Branch**: `autoresearch/mar20` — changes accumulate here before proof-gate merges to master

**m=4 SubcaseB axiom** (still open, requires algebraic proof):
  - n'≡5 mod 64 class needs algebraic proof (min_w is irregular/non-periodic for n'≡5 mod 512)
  - n'≢5 mod 64 is MECHANICAL (w≤32, periods verified): ~90% of all firing positions
  - D-field linearity corridor: 4 lemmas: nl_zero_when_both_zero, hcone_left_edge, f_center_prev_zero, d_leftbound
  - See research/findings.md for detailed structure analysis (loop65)

## Pick ONE task from this priority order

1. **Check SubcaseBPeriod build status** (FIRST PRIORITY):
   - Check: `ps aux | grep "lean\|lake" | grep -v grep`
   - Build log: `tail /tmp/subcaseb_build2.log`
   - If succeeded (olean exists): run `scripts/proof-gate check`
   - If crashed AGAIN (exit 134): split the SubcaseBPeriod.lean file or reduce native_decide count
   - If still running: move to task 2 or 3 while waiting

2. **If SubcaseBPeriod build finished cleanly**:
   - Run `scripts/proof-gate check` to confirm obligation count
   - If count decreased vs master, run `scripts/proof-gate finish`

3. **Verify CA_Array_residues.lean proof** (m28/m30 residue classification):
   - `nohup lake build P2p.CA_Array_residues > /tmp/ca_residues_build.log 2>&1 &`
   - Monitor: `tail /tmp/ca_residues_build.log`
   - If builds in < 30min: approach works; plan integration with CA_Array.lean
   - If hangs 4h+: Array.ofFn too slow; need BitVec approach or algebraic proof

4. **Algebraic approach for m=4 n'≡5 mod 16384** (ONLY this sub-class needs algebraic proof):
   - Only n'≡5 mod 16384 (Level 3+, first n'=16389) is non-mechanical. Everything else covered.
   - Linearity corridor proof: D-field zero at center means twoSpike = spike(4) XOR spike(w)
   - For SubcaseB at m=4: spike(4)_center=0, so if D_center=0, sensitivity determined by spike(w)
   - Reference: `research/linearity_corridor_proof.md` Sec "Lean Formalization Path"
   - Reference: research/findings.md "mod64 Class Analysis (loop66)"

4. **If stuck** — paper update or visualization, commit anything meaningful.

## Rules

- Always work in /Users/jonathanhill/src/p2p (never cd away permanently)
- Before starting a new `lake build`: `pkill -f "lake build" 2>/dev/null; sleep 2; pkill -f "[l]ean.*CA_Array" 2>/dev/null`
- Never run `lake build` and wait for it — start it in background: `nohup lake build ... > /tmp/build.log 2>&1 &`
- Use type holes (`?_`) not `sorry` when probing Lean goals
- Commit at the end with format: `loop<N>: <what you did>` where N = 67 (loop66 was this session)
- Keep commits small and honest — one thing done well beats three things half-done
- The `claude` binary is at `/Users/jonathanhill/.local/bin/claude`

## End state

Your final action must be a git commit. Output a one-line summary of what you did.
