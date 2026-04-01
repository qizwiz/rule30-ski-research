You are an autonomous research agent working on the Wolfram Prize 3 proof in /Users/jonathanhill/src/p2p.

## Your job

Do exactly ONE unit of meaningful work, then commit it. Do not stop to ask questions. Do not leave the repo in a broken state. Always end with a git commit.

## Before you start

1. Read CLAUDE.md — this is your North Star. It has the ranked task list.
2. Run `scripts/proof-gate check` to see the current obligation count and where the sorrys/axioms are.
3. Check `git log --oneline -5` to see what was done recently — don't repeat it.
4. Check if a build is running: `ps aux | grep "lake build" | grep -v grep`
5. Check the latest build log: `ls -t /tmp/ca_array_build*.log /tmp/ca_residues_build.log /tmp/subcaseb_build*.log 2>/dev/null | head -1 | xargs tail -5 2>/dev/null`

## LEAN GOAL PROBE TOOL

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

This runs in ~15 seconds (uses cached .olean). Use it to probe tactic progress.

## Current state (as of 2026-04-01, loop79)

- **5 obligations remain** (down from ~50+):
  1. `subcaseB_m4_ge3087` (axiom) — the algebraic case, MAIN TARGET
  2. `subcaseB_resolution_ge3087` (master axiom) — assembles all sub-cases; will become theorem once (1) is closed
  3. `subcaseB_m28_residue_3class_proved` (axiom in CA_Array.lean)
  4. `subcaseB_m30_residue_unique_proved` (axiom in CA_Array.lean)
  5. `subcaseB_right_mirror_ge3087` — follows from left-boundary symmetry

- **SubcaseBPeriod.lean build9**: CLEAN OLEAN (succeeded ~5:30AM April 1)
- **CA_Array_residues.lean build**: RUNNING at /tmp/ca_residues_build.log (closes obligations 3+4)
- **CA_Array.lean**: CLEAN OLEAN (exists). Do NOT rebuild unless necessary.

## THE TARGET: Linearity corridor proof for subcaseB_m4_ge3087

The algebraic proof of `subcaseB_m4_ge3087` decomposes into 4 Lean lemmas.
**Work on these in order — each one builds on the previous.**

### Lemma 1: nl_zero_when_both_zero (TRIVIAL — do this first)

**Statement**: `NL(0, 0, a', b') = 0` for all `a', b' : Bool`
where `NL(l, c, l', c') = (l OR c) XOR (l' OR c') XOR ((l XOR l') OR (c XOR c'))`

This is a pure truth-table check. Provable by `decide` in Lean.

**File to add it to**: `P2p/SubcaseBPeriod.lean` (or a new `P2p/LinearityCorridor.lean`)

**Lean sketch**:
```lean
lemma nl_zero_when_both_zero (a' b' : Bool) :
    (false || false) ^^ (a' || b') ^^ ((false ^^ a') || (false ^^ b')) = false := by
  cases a' <;> cases b' <;> decide
```

### Lemma 2: hcone_left_edge (MEDIUM — do this second)

**Statement**: For any `n' ≥ 1`, the H-cone spike at position `2*(n'+1)`
after `n'` steps cannot reach position `n'+1` (causality bound).

Equivalently: `(caEvolve (n'+1) (spikeAtList (2*(n'+1)) (2*(n'+1)+1))).getD (n'+1) false = false`

Actually: H_{n'}[n'+1] = 0. The spike is at position 2n'+2 on a tape of size 2n'+3.
After n' steps, causal cone reaches at most position 2n'+2 - n' = n'+2. So position n'+1 is
just OUTSIDE the cone. This should follow from the general causal cone lemma in CausalConeLemmas.lean.

Check if `CausalConeLemmas.lean` has a lemma about cells outside the cone always being 0.

### Lemma 3: f_center_prev_zero (HARD — anti-diagonal zero)

**Statement**: In infinite Rule 30 from spike at position 0,
the cell at position `7 - t` at time `t` is always 0:
`∀ t : Nat, R30_infinite_spike0_at t (7 - t) = false`

**Why it's true** (from findings.md):
- Rule 90: anti-diagonal i+t=7 is odd → C(t, (7-2t)/2) = 0 mod 2 (fractional index)
  Actually: R90(i,t) = 0 when i+t is odd (parity). i+t=7 always odd → R90=0.
- Rule 30 = Rule 90 XOR correction term (c AND NOT r)
- The correction term ALSO vanishes on anti-diagonal 7 by the cascade proof:
  s[0]=1 always, s[1] period-2, s[2]=s[1], s[3] period-4;
  the fold line hits s[2t-7] at time t at zero phase

**Lean approach**:
Option A (easy first step): native_decide for t ≤ 200 using finite tape.
  - Translate to: `∀ t ≤ 200, (caEvolve (t+1) (spikeAtList 0 (2*t+1+20))).getD (7-t) false = false`
  - Note: need tape large enough that boundary doesn't interfere

Option B (algebraic): Prove R30(i,t) = 0 for i+t odd by induction on t.
  - Base: R30(i,0) = (i=0). At t=0, only position 0 is 1. If i+0=7, i=7≠0, so R30=0. ✓
  - Step: R30(i, t+1) = rule30(R30(i-1,t), R30(i,t), R30(i+1,t))
    If i+t+1 is odd, then (i-1)+t, i+t, (i+1)+t have parities: (even, odd, even).
    By induction: R30(i,t)=0 (i+t odd). R30(i-1,t) and R30(i+1,t) might be nonzero.
    rule30(a, 0, b) = a XOR (0 OR b) = a XOR b
    So R30(i,t+1) = R30(i-1,t) XOR R30(i+1,t)... which is NOT necessarily 0!
    This means the anti-diagonal zero is NOT from simple parity — it's deeper.

  Actually the parity argument works for POSITION parity (i.e., position i and time t having
  opposite parities makes the cell 0). Let me verify:
  - i+t=7 means if t is even, i is odd; if t is odd, i is even.
  - rule30(l,c,r): if positions l,c,r alternate even/odd, does a parity argument apply?

  The REAL approach: write a Python script to verify the induction base and extract the
  pattern, then encode as native_decide proof for finite bound.

**Try Option A first**: Write the native_decide verification for t ≤ 100, check it compiles.

### Lemma 4: d_leftbound (HARD — support bound)

**Statement**: The D-field's minimum support at time T-1 is ≥ center+2.
Equivalently: `D[n'+1]_{T-1} = 0` and `D[n']_{T-1} = 0` where n' is the center index.

This follows from: D first appears at step 4, at position ≥ 2n'-2. The drift per step is at
most 1 cell toward center. After T-4 more steps, min_support ≥ 2n'-2 - (T-4) = 2n'-2 - n'-3 = n'-5.
Wait — need to re-verify this bound. Check `research/findings.md` section "Causal cone D-field".

## CA_Array_residues: check and integrate if done

```bash
tail -20 /tmp/ca_residues_build.log
ls -la .lake/build/lib/P2p/CA_Array_residues.olean 2>/dev/null
```

If build succeeded:
1. Verify the theorems it exports match what CA_Array.lean expects
2. Add `import P2p.CA_Array_residues` to CA_Array.lean
3. Remove the 2 axioms from CA_Array.lean (replace with the imported theorems)
4. Rebuild CA_Array.lean to confirm
5. Run proof-gate check

## rule30_meta.py: check if done

```bash
ls -la /tmp/rule30_meta.png && echo "done" || echo "still running"
```

If done: read its output, extract any structural insight about the D-field pattern,
update research/findings.md.

## Priority order for this loop

1. **Check CA_Array_residues build** — if done, integrate (closes 2 axioms)
2. **Attempt nl_zero_when_both_zero** in Lean — trivial, just do it
3. **Attempt hcone_left_edge** in Lean — check if CausalConeLemmas has what we need
4. **Python verification of anti-diagonal zero for t ≤ 500** — confirm the claim,
   understand WHICH cells neighboring the anti-diagonal are nonzero (this reveals
   the induction structure)
5. **Attempt f_center_prev_zero via native_decide** for finite t ≤ 100
6. **Check rule30_meta.py** output if done
7. **Paper/findings update** — document whatever you learn

## Rules

- Always work in /Users/jonathanhill/src/p2p (never cd away permanently)
- Before starting a new `lake build`: `pkill -f "lake build" 2>/dev/null; sleep 2`
- Never run `lake build` and wait for it — start in background: `nohup lake build ... > /tmp/build.log 2>&1 &`
- Use type holes (`?_`) not `sorry` when probing Lean goals
- Commit at the end with format: `loop<N>: <what you did>` where N increments from 79
- Keep commits small and honest

## End state

Your final action must be a git commit. Output a one-line summary of what you did.
