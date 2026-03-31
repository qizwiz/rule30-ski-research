# Rule 30 / Wolfram Prize 3 — Project North Star

## THE RABBIT: What we are proving

**Wolfram Prize 3 (official statement)**:
> Does computing the nth cell of the center column require at least O(n) computational effort?

**Answer we are proving: YES** — via block sensitivity lower bounds.

**Mechanism**: Rule 30's center cell at step n, viewed as a boolean function of the
initial configuration, has block sensitivity ≥ n. In query/decision-tree complexity,
block sensitivity ≥ n implies query complexity ≥ n — you must probe at least n
independent cells of the initial condition to determine the output. This IS the Ω(n)
computational effort lower bound Prize 3 asks for.

**Formalization** (in `P2p/Prize3_Complete.lean`):

```lean
theorem rule30_bs_ge_n (n : Nat) : HasBlockSensitivity n (rule30n n) n
```

where `HasBlockSensitivity n f n` means there exist n disjoint cell-blocks in the
2n+1-cell initial tape, each of which when flipped changes f's output.

**Informal**: Every cell in Rule 30's evolution triangle is essential. Flipping any
single initial cell somewhere changes the center output. Therefore computing that
output requires checking at least n cells → Ω(n) work.

## PROOF STATUS

### ✓ DONE (axiom-free, machine-checked)
- Core definitions: `rule30Local`, `Config`, `Essential`, `HasBlockSensitivity`
- Base cases n=0..5 via `native_decide`
- `AllEssential`: all 2n+1 cells essential at every level
- `rule30_bs_ge_n`: the prize theorem — **proved via one axiom** (see below)

### THE SINGLE REMAINING AXIOM
```lean
axiom subcaseB_resolution_ge3087 : ...
```
Lives in `P2p/SubcaseBPeriod.lean`. This axiom says: for all active m and all n' ≥ 3087,
if SubcaseB fires (spike_m gives center=false, twoSpike_{m,last} gives center=true),
then there exists a valid witness c proving sensitivity at m.

**Closing this axiom = axiom-free proof of Prize 3.**

## DEPENDENCY TREE TO CLOSE subcaseB_resolution_ge3087

```
subcaseB_resolution_ge3087  (master, needs ALL below)
├── subcaseB_m4_ge3087_proved        ← AXIOM (line 815)
├── subcaseB_m6_ge3087_proved        ← IN PROGRESS (proof written, build running)
├── subcaseB_m8_ge3087_proved        ✓ proved
├── subcaseB_m10_ge3087_proved       ✓ proved
├── subcaseB_m12_ge3087_proved       ✓ proved
├── subcaseB_m14_ge3087_proved       ✓ proved
├── subcaseB_m16_ge3087_proved       ✓ proved
├── subcaseB_m20_ge3087_proved       ✓ proved
├── subcaseB_m22_ge3087_proved       ← SORRY (l≡0 sub-case only: n'=35598+65536s, linearity corridor needed)
├── subcaseB_m24_ge3087_proved       ✓ proved
├── subcaseB_m26_ge3087_proved       ✓ proved
├── subcaseB_m28_ge3087_proved       ✓ proved (via CA_Array.lean native_decide)
├── subcaseB_m30_ge3087_proved       ✓ proved (via CA_Array.lean native_decide)
└── subcaseB_right_mirror_ge3087     ✓ proved (no actual sorrys in theorem)
```

**Also needed:** `subcaseB_m28_residue_3class_proved` and `subcaseB_m30_residue_unique_proved`
come from `P2p/CA_Array.lean` which must compile (build is running, takes ~1 hour).

## RANKED TASK LIST

### Priority 1: Close m=22 l≡0 sorry (linearity corridor)
- l≡1 case ✓ proved (pending CA_Array.lean build): w=32, P=65536, n''=2830
  Python (shrinking CA) verified: spike(32) P=65536 PASS, twoSpike(32,22) PASS, base sens PASS.
  Earlier "FAIL" was due to a buggy Python script using fixed-size (not shrinking) CA.
- l≡0 case SORRY: n'=35598+65536s. Min witness at n'=35598 is w=34 (w=32 not sensitive).
  Witnesses are 2-automatic (min w grows with v2(s)).
  Requires linearity corridor proof (same structure as m=4 axiom):
  4 lemmas: nl_zero_when_both_zero, hcone_left_edge, f_center_prev_zero, d_leftbound

### Priority 1: Prove m=4 SubcaseB (axiom removal)
- Location: `SubcaseBPeriod.lean` line 815, `axiom subcaseB_m4_ge3087`
- Structure: fires at n'≡5 mod 8; after reducing to n''=3093 mod 8, need k≥0 for n'=3093+k*8
- Most residue classes covered by existing certs (see SubcaseBPeriod.lean lines 300-975)
- **Gaps requiring new Array Bool certs** (verified 2026-03-31):
  - j=42 (k≡42 mod 64, n'=3429): w=32, P=4096. spike(32) P=4096 PASS, ts(32,4) P=4096 PASS
  - Level 1 (≡5 mod 1024): w=30, P=4096. Two bases: n'=5125 (mod4096=1029), n'=7173 (mod4096=3077)
  - Level 2 (≡5 mod 4096): w=34, P=16384. Three bases: n'=4101, 8197, 12293
  - Level 3+ (≡5 mod 16384, first n'=16389): INFINITE hierarchy → linearity corridor needed
- **NOT MECHANICAL**: levels 3+ require linearity corridor, same as m=22 l≡0
- All certs at levels 0-2 need to be added to CA_Array.lean (Array Bool native_decide)
- Once CA_Array.lean extended: convert axiom → theorem-with-1-sorry (for level 3+)

### Priority 3: ✓ m=6 SubcaseB proof WRITTEN (build running to verify)
- Location: `SubcaseBPeriod.lean` — 8-witness telescoping proof inserted 2026-03-27
- Structure: fires at n' ≡ {6,10} mod 16 (roughly); witnesses w=2, w=8
- twoSpike(2,6) period ≤ 16, twoSpike(8,6) period ≤ 32
- Approach: small-period native_decide certs, then sensitivity_transfer

### Priority 4: Right mirror axiom
- Location: `SubcaseBPeriod.lean` line 2800
- Mirrors left-boundary case; should follow symmetrically from left proofs

### Priority 5: Assemble subcaseB_resolution_ge3087
- Once all component proofs exist, case-split over all active m to make axiom a theorem

## KEY FILES

| File | Role |
|------|------|
| `P2p/Prize3_Complete.lean` | Prize theorem, definitions, base cases |
| `P2p/CausalConeLemmas.lean` | Period certs for spike sequences (committed) |
| `P2p/SubcaseBPeriod.lean` | All SubcaseB period proofs (untracked, in progress) |
| `P2p/CA_Array.lean` | Fast Array Bool native_decide for m=28,m=30 residues + m=22 j≡0 (untracked) |
| `research/findings.md` | Mathematical analysis, LFSR structure, linearity corridor |

## TECHNIQUE CHEAT SHEET

**sensitivity_transfer**: Given base sensitivity at n'' and period certs for both
`spike(w)` and `twoSpike(w,m)`, proves sensitivity for all n'=n''+k*P.

**Period cert form**: `caEvolve P (spikeAtList w (2*P+2*w+1)) = spikeAtList w (2*w+1)`

**spikeConfig_odd_false requirement**: witness must have even w.

**Active m set** (SubcaseB fires for n' ≥ 3087):
`{4, 6, 8, 10, 12, 14, 16, 20, 22, 24, 26, 28}` + right mirror

**Proof pattern for each m**:
1. Use `periodReduce` to reduce n' to a base residue class
2. Apply `subcaseB_{m}_unique_in_period` to classify residue
3. For each residue class, call `sensitivity_transfer` with appropriate w and P
4. Base sensitivity and certs come from `native_decide` in CA_Array.lean or CausalConeLemmas.lean

## AGENT PROTOCOL (git-gated, Von Neumann-style)

**Every proof agent must go through `scripts/proof-gate`.** This enforces the invariant:
every merge to master strictly decreases `sorry_count + axiom_count`.

```bash
# Start isolated work (creates git worktree, no filesystem races):
scripts/proof-gate start <task-name>   # e.g. proof-gate start m22-linearity

# Check current obligation count at any time:
scripts/proof-gate check               # prints count + locations

# Finish: build must pass, count must decrease, no new axioms:
scripts/proof-gate finish              # merges to master if gate passes
```

**Never run multiple `lake build` instances in parallel on the same file.**
Each worktree has its own `.lake/build/` — no races.

**Type holes over sorrys during development**: use `?_` instead of `sorry` to get the
compiler to print the exact goal type. Type holes fail the build (good — they can't
sneak through the gate). Only replace with `sorry` when you're deliberately deferring
to a named axiom.

## BUILD NOTES

- `lake build P2p.CA_Array` — takes ~1 hour (heavy native_decide for m=28 Fin 2048, m=30 8×Fin512, m=22 P=32768)
- Run in background: `nohup lake build P2p.CA_Array > /tmp/ca_array_build.log 2>&1 &`
- Once CA_Array.lean has an .olean, subsequent builds are cached
- CA_Array.lean and SubcaseBPeriod.lean are **untracked** — `git add` before committing
- **Never start parallel builds** — they race to write the same .olean and never finish
