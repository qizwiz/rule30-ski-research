You are an autonomous research agent working on the Wolfram Prize 3 proof in /Users/jonathanhill/src/p2p.

## Your job

Do exactly ONE unit of meaningful work, then commit it. Do not stop to ask questions. Do not leave the repo in a broken state. Always end with a git commit.

## Before you start

1. Read CLAUDE.md — this is your North Star. It has the ranked task list.
2. Run `scripts/proof-gate check` to see the current obligation count and where the sorrys/axioms are.
3. Check `git log --oneline -5` to see what was done recently — don't repeat it.
4. Check if a CA_Array build is running: `ps aux | grep "lake build" | grep -v grep`
5. Check the latest build log: `ls -t /tmp/ca_array_build*.log 2>/dev/null | head -1 | xargs tail -5 2>/dev/null`

## Current state (as of 2026-03-31, loop61)

- **SubcaseBPeriod.lean has ONE sorry**: m=22 j≡1/l≡0 sub-case (n'=35598+65536s)
  - l≡1 sub-case IS proved: w=32, P=65536, base n''=2830.
  - l≡0: twoSpike(w,22) has period=131072 for all witnesses → INFEASIBLE for native_decide
  - **Both m=22 l≡0 and m=4 require ALGEBRAIC proof, not period certs**
- **Two axioms remain**: `subcaseB_m4_ge3087` (line ~981) and `subcaseB_resolution_ge3087` (master)
- **CA_Array_m4.lean BUILT** (loop60): 765 jobs, 2444s. Sections 12-14 verified (Levels 0-2).
- **CA_Array.lean**: STILL BUILDING (started 2:47AM, 165+ min CPU as of loop61). Imports needed by SubcaseBPeriod.
- **Branch**: `autoresearch/mar20` — changes accumulate here before proof-gate merges to master

**m=4 hierarchy (loop61 confirmed)**: Level 3+ fully requires algebraic proof.
  - Confirmed period data: spike(40)=65536, spike(42)=131072, twoSpike(42,4)=131072
  - Level 3 sensitivity: w=40 covers n'≡{32773,49157} mod 131072; w=42 covers n'≡{16389,65541} mod 131072
  - n'≡{81925,98309,114693} mod 131072 need w≥44 → tape 262K+, even larger than Section 11
  - ALL Level 3+ cases: native_decide infeasible (tape sizes 131K-262K+, 65536-131072+ steps)
  - Sections 12-14 in CA_Array_m4.lean close ALL levels up to Level 2. Level 3+ is the algebraic boundary.
  - See research/findings.md "m=4 Level 3 Period Measurements (loop61)" for full data.

**m=22 l≡0 (loop61 state)**: twoSpike(w,22) period=131072 for all witnesses.
  - Same scale issue: P=131072 cert requires tape=262K elements → infeasible
  - Algebraic approach needed: linearity corridor adapted for SubcaseB m=22 geometry.

## Pick ONE task from this priority order

1. **Wait for CA_Array build, then build SubcaseBPeriod** (FIRST PRIORITY):
   - Check: `ps aux | grep "lake build" | grep -v grep`
   - If CA_Array done (`tail /tmp/ca_array_build7.log` shows `Built P2p.CA_Array`):
     - Ensure no other lake build running, then:
     - `nohup lake build P2p.SubcaseBPeriod > /tmp/subcaseb_build.log 2>&1 &`
     - Wait 10s: `sleep 10 && tail /tmp/subcaseb_build.log`
   - If SubcaseBPeriod finishes: run `scripts/proof-gate check`
   - If obligation count decreased vs master: run `scripts/proof-gate finish`

2. **If SubcaseBPeriod build finished cleanly**:
   - Run `scripts/proof-gate check` to confirm obligation count
   - If count decreased vs master, run `scripts/proof-gate finish`

3. **Algebraic approach for m=4 Level 3+** (both sorrys need this):
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
- Commit at the end with format: `loop<N>: <what you did>` where N = last loop number + 1
- Keep commits small and honest — one thing done well beats three things half-done
- The `claude` binary is at `/Users/jonathanhill/.local/bin/claude`

## End state

Your final action must be a git commit. Output a one-line summary of what you did.
