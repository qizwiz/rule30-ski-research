You are an autonomous research agent working on the Wolfram Prize 3 proof in /Users/jonathanhill/src/p2p.

## Your job

Do exactly ONE unit of meaningful work, then commit it. Do not stop to ask questions. Do not leave the repo in a broken state. Always end with a git commit.

## Before you start

1. Read CLAUDE.md — this is your North Star. It has the ranked task list.
2. Run `scripts/proof-gate check` to see the current obligation count and where the sorrys/axioms are.
3. Check `git log --oneline -5` to see what was done recently — don't repeat it.
4. Check if a CA_Array build is running: `ps aux | grep "lake build" | grep -v grep`
5. Check the latest build log: `ls -t /tmp/ca_array_build*.log 2>/dev/null | head -1 | xargs tail -5 2>/dev/null`

## Current state (as of 2026-03-31)

- **SubcaseBPeriod.lean has ONE sorry**: m=22 j≡1/l≡0 sub-case (n'=35598+65536s)
  - l≡1 sub-case IS proved: w=32, P=65536, base n''=2830. Loop57 claim of "zero sorrys" was wrong.
  - loop57 P=4096 cert for l≡0 was mathematically wrong (w=32 not sensitive at n'=35598)
- **Two axioms remain**: `subcaseB_m4_ge3087` (line ~980) and `subcaseB_resolution_ge3087` (master)
- **CA_Array build**: may be running (check with ps aux); Sections 5-11 included.
- **Branch**: `autoresearch/mar20` — changes accumulate here before proof-gate merges to master

**CORRECTION (2026-03-31)**: The "linearity corridor" approach in loop-prompt and CLAUDE.md
for m=22 l≡0 is WRONG. `f_center_prev_zero` (lemma 3 in linearity_corridor_proof.md) holds
only for spike at position 2n'-6 (scaling), NOT for fixed m=22. For fixed m=22, F[center][T-1]
is frequently nonzero (verified for n'=22..100). The corridor proof does not close this sorry.

**NEW FINDING on m=22 l≡0**: No fixed w works for all n'=35598+65536*s:
  s=0: min_w=34 ✓  |  s=1: min_w=40 (w=34 fails)  |  s=2: min_w=34 ✓  |  s=3: min_w=42 (w=34 fails)
min_w is NOT a pure function of v₂(s). The problem needs a new approach (see findings.md).

## Pick ONE task from this priority order

1. **If a CA_Array build is running** — check its tail log. If still running, work on:
   - Extend D-field witness map for m=22 l≡0: understand why min_w varies non-simply
     Run: `python3 scripts/visualize_subcase.py 35598 22 60` (generates D-field figs)
     Then: compile/run `/tmp/m22_witness` style C tool to characterize min_w pattern
   - Or: start m=4 strong induction Lean skeleton (see Priority 4 below)

2. **If CA_Array build just finished cleanly** (tail log shows `Built P2p.CA_Array`):
   - Run: `nohup lake build P2p.SubcaseBPeriod > /tmp/subcaseb_build.log 2>&1 &`
   - Wait briefly (5s) and check for immediate errors
   - Commit status update

3. **If SubcaseBPeriod build finished cleanly**:
   - Run `scripts/proof-gate check` to confirm obligation count
   - If count decreased vs master, run `scripts/proof-gate finish`
   - Then proceed to Priority 4

4. **m=4 SubcaseB axiom** (most tractable remaining work):
   - Location: `SubcaseBPeriod.lean` line 980, `axiom subcaseB_m4_ge3087`
   - Approach: strong induction on v₂(n'-5) — termination guaranteed since n'=5 < 3087
   - For n'≡13 mod 16 (not ≡5 mod 32): w=6, period=16 — direct cert, provable
   - For n'≡5 mod 32 (not ≡5 mod 64): w=10, period=64 — direct cert
   - For deeper tiers: recurse on the unique n'≡5 mod 2^k sub-class
   - DO NOT use linearity corridor approach (f_center_prev_zero is WRONG for fixed m=4)
   - Start: `?_` holes in Lean to probe the goal type, then fill tier by tier

5. **m=22 l≡0 investigation** (research task):
   - No fixed witness w works; min_w varies (see findings.md)
   - Hypothesis: look for a witness w that depends on n' algebraically (not fixed)
   - Run: extend C witness tool to n'≤600000 and characterize min_w(s) for s=0..8
   - Update research/findings.md with pattern discovered

6. **If stuck** — computational experiment or paper update, commit anything meaningful.

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
