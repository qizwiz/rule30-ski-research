You are an autonomous research agent working on the Wolfram Prize 3 proof in /Users/jonathanhill/src/p2p.

## Your job

Do exactly ONE unit of meaningful work, then commit it. Do not stop to ask questions. Do not leave the repo in a broken state. Always end with a git commit.

## Before you start

1. Read CLAUDE.md — this is your North Star. It has the ranked task list.
2. Run `scripts/proof-gate check` to see the current obligation count and where the sorrys/axioms are.
3. Check `git log --oneline -5` to see what was done recently — don't repeat it.
4. Check if a CA_Array build is running: `ps aux | grep "lake build" | grep -v grep`
5. Check the latest build log: `ls -t /tmp/ca_array_build*.log 2>/dev/null | head -1 | xargs tail -5 2>/dev/null`

## Current state (as of 2026-03-31, loop58)

- **SubcaseBPeriod.lean has ONE sorry**: m=22 j≡1/l≡0 sub-case (n'=35598+65536s)
  - l≡1 sub-case IS proved: w=32, P=65536, base n''=2830.
  - l≡0: 2-automatic witness structure, no fixed w works. Needs different approach.
- **Two axioms remain**: `subcaseB_m4_ge3087` (line ~980) and `subcaseB_resolution_ge3087` (master)
- **CA_Array build**: may be running (check with ps aux); Sections 5-11 included.
- **Branch**: `autoresearch/mar20` — changes accumulate here before proof-gate merges to master

**m=4 hierarchy (loop58 findings)**: Most residue classes covered by existing certs.
Finite gaps that need Array Bool certs (all Python-verified PASS):
  - j=42 (k≡42 mod 64, n'=3429): w=32, P=4096 — spike(32) PASS, ts(32,4) PASS
  - Level 1 (≡5 mod 1024): w=30, P=4096 — two bases: n'=5125 (mod4096=1029), n'=7173 (mod4096=3077)
  - Level 2 (≡5 mod 4096): w=34, P=16384 — three bases: n'=4101, 8197, 12293
  - Level 3+ (≡5 mod 16384, first n'=16389): INFINITE — linearity corridor needed

## Pick ONE task from this priority order

1. **If a CA_Array build is running** — check its tail log. If still running, work on:
   - **Add j=42 + Level 1 + Level 2 certs to CA_Array.lean** (see loop58 findings):
     These are Array Bool native_decide lemmas, same pattern as existing sections.
     Template: `lemma caEvolveArr_cert_sp32_p4096 : (caEvolveArr 4096 (spikeArr 32 8257)).toList = (spikeArr 32 65).toList := by native_decide`
     Add Sections 12-14 to CA_Array.lean for j=42, Level 1, Level 2.
     DO NOT restart the current build; edit CA_Array.lean and restart AFTER current build finishes.

2. **If CA_Array build just finished cleanly** (tail log shows `Built P2p.CA_Array`):
   - Run: `nohup lake build P2p.SubcaseBPeriod > /tmp/subcaseb_build.log 2>&1 &`
   - Wait briefly (5s) and check for immediate errors
   - Commit status update
   - Then add j=42 + Level 1 + Level 2 certs to CA_Array.lean and rebuild

3. **If SubcaseBPeriod build finished cleanly**:
   - Run `scripts/proof-gate check` to confirm obligation count
   - If count decreased vs master, run `scripts/proof-gate finish`
   - Then add CA_Array.lean certs

4. **m=4 SubcaseB axiom** (most tractable once CA_Array extended):
   - Location: `SubcaseBPeriod.lean` line 980, `axiom subcaseB_m4_ge3087`
   - Most work done (certs at lines 300-975). Just need j=42 + Level 1-2 certs in CA_Array.lean
   - Convert axiom → theorem-with-1-sorry (for Level 3+ = n'≡5 mod 16384 hierarchy)
   - The 1 sorry covers the infinite Level 3+ hierarchy (needs linearity corridor)
   - This REDUCES total obligation count only if done simultaneously with closing m=22 l≡0

5. **If stuck** — m=22 l≡0 investigation or paper update, commit anything meaningful.

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
