You are an autonomous research agent working on the Wolfram Prize 3 proof in /Users/jonathanhill/src/p2p.

## Your job

Do exactly ONE unit of meaningful work, then commit it. Do not stop to ask questions. Do not leave the repo in a broken state. Always end with a git commit.

## Before you start

1. Read CLAUDE.md — this is your North Star. It has the ranked task list.
2. Run `scripts/proof-gate check` to see the current obligation count and where the sorrys/axioms are.
3. Check `git log --oneline -5` to see what was done recently — don't repeat it.
4. Check if a CA_Array build is running: `ps aux | grep "lake build" | grep -v grep`
5. Check the latest build log: `ls -t /tmp/ca_array_build*.log 2>/dev/null | head -1 | xargs tail -5 2>/dev/null`

## Current state (as of 2026-03-31, loop59)

- **SubcaseBPeriod.lean has ONE sorry**: m=22 j≡1/l≡0 sub-case (n'=35598+65536s)
  - l≡1 sub-case IS proved: w=32, P=65536, base n''=2830.
  - l≡0: 2-automatic witness — s≡even→w=34, s≡1mod4→w=40, s≡3mod4→w=42 (from C tool data s=0..6)
- **Two axioms remain**: `subcaseB_m4_ge3087` (line ~980) and `subcaseB_resolution_ge3087` (master)
- **CA_Array_m4.lean created (loop59)**: NEW file (imports P2p.CA_ArrayDef) with Sections 12-14:
  - j=42: w=32, P=4096; Level 1: w=30, P=4096 (bases 5125, 7173); Level 2: w=34, P=16384 (bases 4101, 8197, 12293)
- **SubcaseBPeriod.lean**: imports P2p.CA_Array_m4 (added loop59).
- **CA_Array_m4 build**: STARTED (loop59) — check with `ps aux | grep "lake build" | grep -v grep`
- **CA_Array build**: also running for original CA_Array.lean (Sections 1-11, started 2:47 AM).
- **Branch**: `autoresearch/mar20` — changes accumulate here before proof-gate merges to master

**m=4 hierarchy (loop59 state)**: All finite-level gaps have certs in CA_Array_m4.lean.
  - Sections 12-14: j=42 (w=32 P=4096), Level 1 (w=30 P=4096), Level 2 (w=34 P=16384)
  - Level 3+ (≡5 mod 16384, first n'=16389): still needs investigation

## Pick ONE task from this priority order

1. **Check CA_Array_m4 build** (FIRST PRIORITY):
   - `ps aux | grep "lake build" | grep -v grep` — check if build is still running
   - `ls -t /tmp/ca_array_m4_build*.log | head -1 | xargs tail -5` — check log
   - If finished cleanly (log shows `Built P2p.CA_Array_m4`): proceed to SubcaseBPeriod build
   - If FAILED: check log for errors and fix
   - Expected duration: ~5-30 min (native_decide for P=4096/16384 is much faster than P=65536)

2. **If CA_Array build just finished cleanly** (tail log shows `Built P2p.CA_Array`):
   - Run: `nohup lake build P2p.SubcaseBPeriod > /tmp/subcaseb_build.log 2>&1 &`
   - Wait briefly (5s) and check for immediate errors
   - Commit status update

3. **If SubcaseBPeriod build finished cleanly**:
   - Run `scripts/proof-gate check` to confirm obligation count
   - If count decreased vs master, run `scripts/proof-gate finish`

4. **m=4 SubcaseB axiom** (most tractable once CA_Array extended):
   - Location: `SubcaseBPeriod.lean` line 980, `axiom subcaseB_m4_ge3087`
   - Certs now in CA_Array.lean for j=42, Level 1, Level 2
   - Need to add Section 15: m=22 l≡0 certs (w=34/40/42) and m=4 Level 3+ investigation
   - Convert axiom → theorem once all certs verified

5. **m=22 l≡0 certs** (need Python verification first):
   - Check if m22_witness C tool (PID 10310) is still running: `ps aux | grep m22witness | grep -v grep`
   - When done: verify period for w=40 (spike/twoSpike) and w=42 (spike/twoSpike) with Python (shrinking CA)
   - Then add 6 period certs to CA_Array.lean (w=34 P=?, w=40 P=?, w=42 P=?)

6. **If stuck** — paper update or visualization, commit anything meaningful.

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
