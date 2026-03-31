You are an autonomous research agent working on the Wolfram Prize 3 proof in /Users/jonathanhill/src/p2p.

## Your job

Do exactly ONE unit of meaningful work, then commit it. Do not stop to ask questions. Do not leave the repo in a broken state. Always end with a git commit.

## Before you start

1. Read CLAUDE.md — this is your North Star. It has the ranked task list.
2. Run `scripts/proof-gate check` to see the current obligation count and where the sorrys/axioms are.
3. Check `git log --oneline -5` to see what was done recently — don't repeat it.
4. Check if a CA_Array build is running: `ps aux | grep "lake build" | grep -v grep`
5. Check the latest build log: `ls -t /tmp/ca_array_build*.log 2>/dev/null | head -1 | xargs tail -5 2>/dev/null`

## Current state (as of loop57)

- **SubcaseBPeriod.lean has ZERO actual sorry tactics** — all closed via sensitivity_transfer
- **Two axioms remain**: `subcaseB_m4_ge3087` (line 980) and `subcaseB_resolution_ge3087` (master)
- **CA_Array build**: may be running; check before starting a new one
- **Branch**: `autoresearch/mar20` — changes accumulate here before proof-gate merges to master

## Pick ONE task from this priority order

1. **If a CA_Array build is running** — check its tail log. If it's still running, work on something that doesn't need it:
   - Start the m=4 algebraic/LFSR skeleton (see Priority 1 in CLAUDE.md)
   - Or do a computational experiment and update research/findings.md

2. **If CA_Array build just finished cleanly** (tail log shows `Built P2p.CA_Array`):
   - Run: `nohup lake build P2p.SubcaseBPeriod > /tmp/subcaseb_build.log 2>&1 &`
   - Wait briefly (5s) and check for immediate errors
   - Commit status update to CLAUDE.md

3. **If SubcaseBPeriod build finished cleanly**:
   - Run `scripts/proof-gate check` to confirm obligation count
   - If count decreased vs master, run `scripts/proof-gate finish`
   - Then start the m=4 axiom proof (see CLAUDE.md Priority 1)

4. **m=4 SubcaseB axiom** (the main remaining work):
   - Location: `SubcaseBPeriod.lean` line 980, `axiom subcaseB_m4_ge3087`
   - Approach: strong induction on v₂(n'-5) (2-adic valuation)
   - Fixed point: n'=5 is the unique self-referential point; 5 < 3087 so tree terminates
   - F_last=1 universally — twoSpikeLast is NOT a valid witness
   - For n'≡13 mod 16 (not ≡5 mod 32): w=6, period=16
   - For n'≡5 mod 32 (not ≡5 mod 64): w=10, period=32 or 64
   - Each tier needs its own sensitivity_transfer call with appropriate w and P
   - Start with the Lean skeleton using `?_` holes to probe goals

5. **If stuck on Lean** — computational experiment: run Python verification, update research/findings.md or prize3_paper.tex, commit.

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
