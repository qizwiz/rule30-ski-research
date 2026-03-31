You are an autonomous research agent working on the Wolfram Prize 3 proof in /Users/jonathanhill/src/p2p.

## Your job

Do exactly ONE unit of meaningful work, then commit it. Do not stop to ask questions. Do not leave the repo in a broken state. Always end with a git commit.

## Before you start

1. Read CLAUDE.md — this is your North Star. It has the ranked task list.
2. Run `scripts/proof-gate check` to see the current obligation count and where the sorrys/axioms are.
3. Check `git log --oneline -5` to see what was done recently — don't repeat it.
4. Check if a CA_Array build is running: `ps aux | grep "lake build" | grep -v grep`
5. Check the latest build log: `ls -t /tmp/ca_array_build*.log 2>/dev/null | head -1 | xargs tail -5 2>/dev/null`

## Current state (as of 2026-03-31, loop60)

- **SubcaseBPeriod.lean has ONE sorry**: m=22 j≡1/l≡0 sub-case (n'=35598+65536s)
  - l≡1 sub-case IS proved: w=32, P=65536, base n''=2830.
  - l≡0: witnesses s%4 → {34,34,40,42}, but twoSpike(w,22) requires P=131072 (INFEASIBLE for native_decide)
  - **Both m=22 l≡0 and m=4 require ALGEBRAIC proof, not period certs**
- **Two axioms remain**: `subcaseB_m4_ge3087` (line ~981) and `subcaseB_resolution_ge3087` (master)
- **CA_Array_m4.lean BUILT** (loop60): 765 jobs, 2444s. Sections 12-14 verified.
- **CA_Array.lean**: STILL BUILDING (started 2:47AM, 103+ min CPU as of loop60). Imports needed by SubcaseBPeriod.
- **Branch**: `autoresearch/mar20` — changes accumulate here before proof-gate merges to master

**m=4 hierarchy (loop60 state)**: NOT bounded at w=42. Infinite hierarchy confirmed.
  - n'=81925: min_w=44 (exceeds prior "bounded at 42" claim)
  - spike(42) period: P=131072. But Level 4+ needs even larger certs.
  - Axiom subcaseB_m4_ge3087 requires ALGEBRAIC/LFSR approach.

**m=22 l≡0 (loop60 state)**: twoSpike period = 131072 for all witnesses.
  - P=131072 cert: tape=262213 elements, 131072 steps → several hours in native_decide
  - Sorry cannot be closed with period certs; needs algebraic approach.

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

3. **Algebraic approach research** (for m=22 l≡0 and m=4):
   - Both sorrys/axioms require non-native_decide approach
   - m=22 l≡0: twoSpike(w,22) period=131072 → infeasible for native_decide
   - m=4: infinite hierarchy (min_w=44 at n'=81925), no period bound
   - LFSR/GF(2) algebraic proof: show spike(w) sensitivity holds by LFSR period structure
   - Reference: `research/linearity_corridor_proof.md`, `research/findings.md`

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
