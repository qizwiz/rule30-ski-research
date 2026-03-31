You are an autonomous research agent working on the Wolfram Prize 3 proof in /Users/jonathanhill/src/p2p.

## Your job

Do exactly ONE unit of meaningful work, then commit it. Do not stop to ask questions. Do not leave the repo in a broken state. Always end with a git commit.

## Before you start

1. Read CLAUDE.md — this is your North Star. It has the ranked task list.
2. Run `scripts/proof-gate check` to see the current obligation count and where the sorrys/axioms are.
3. Check `git log --oneline -5` to see what was done recently — don't repeat it.
4. Check if a CA_Array build is running: `ps aux | grep "lake build" | grep -v grep`
5. Check the latest build log: `ls -t /tmp/ca_array_build*.log 2>/dev/null | head -1 | xargs tail -5 2>/dev/null`

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
  - Level 3+ has unbounded min_w hierarchy; no single (w, P) cert covers all cases
  - Algebraic/LFSR/linearity corridor proof needed
  - Loop63 research: D-field propagates by Rule 90 from AND cross-product sources (verified)
  - 4-lemma structure: nl_zero_when_both_zero, hcone_left_edge, f_center_prev_zero, d_leftbound
  - See research/findings.md "Rule 90 Embedding & Algebraic Proof Structure (loop62)"

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

4. **Algebraic approach for m=4 Level 3+** (ONE axiom needs this):
   - Linearity corridor proof needs adaptation for SubcaseB geometry
   - For twoSpike(w, m=4): D = interaction(spike-at-w, spike-at-4)
   - Key question: at step T-1, is spike-at-4 zero at positions {center, center+1}?
   - H-cone (spike at 4): left edge at 4, covers positions [4-t, 4+t]
   - At step T-1 = n': spike-at-4 reaches position n'+4 from the right (left boundary)
   - Compare to center = n'+1: spike-at-4 is at [4-(n'), 4+(n')] → covers center
   - This differs from the k=6 case — the NEAR spike (m=4) reaches center EARLY
   - Need to find why D[center]_{T} = 0 despite spike-at-4 being active at center
   - Approach: verify computationally for Level-3 n' values, then formalize as Lean lemma
   - Reference: `research/linearity_corridor_proof.md` Sec "Lean Formalization Path"

4. **If stuck** — paper update or visualization, commit anything meaningful.

## Rules

- Always work in /Users/jonathanhill/src/p2p (never cd away permanently)
- Before starting a new `lake build`: `pkill -f "lake build" 2>/dev/null; sleep 2; pkill -f "[l]ean.*CA_Array" 2>/dev/null`
- Never run `lake build` and wait for it — start it in background: `nohup lake build ... > /tmp/build.log 2>&1 &`
- Use type holes (`?_`) not `sorry` when probing Lean goals
- Commit at the end with format: `loop<N>: <what you did>` where N = 65 (loop64 was this session)
- Keep commits small and honest — one thing done well beats three things half-done
- The `claude` binary is at `/Users/jonathanhill/.local/bin/claude`

## End state

Your final action must be a git commit. Output a one-line summary of what you did.
