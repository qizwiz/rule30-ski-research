# FINDINGS: Decisive local-null experiment — THE RULING

Date: 2026-07-08. Pre-registration v2 (module docstring of `decisive_localnull_2026-07-08.py`,
written before any decisive data existed). Run on rule30box, 09:39–10:04 box time (~25 min,
12 workers), 504 run rows + 168 graph rows, 0 errors, 0 censoring. Mac copies
checksum-verified against the box (`decisive_results_2026-07-08.csv` md5 `e58e82410f0e...`).

**Every headline number below was independently recomputed from the raw CSV rows**
(`decisive_results_2026-07-08.csv`, `decisive_graphs_2026-07-08.csv`) — not read off the
analyzer — including geo-means, fresh 10k-bootstrap CIs, per-seed win counts, turnover,
Spearman, and the price tables. All agree with `decisive_analysis_FULL_2026-07-08.txt`
to displayed precision. Validity gates re-verified raw: V0 reproduction vs
`robust_runs.csv` 216/216 exact; 168/168 graphs connected; max curved edge drift 0.238%;
0/504 rows censored at either tolerance; landmark cell (seed 30, N=225, heat) reproduces
digit-for-digit (flat=689, curved=89).

## THE RULING — Q-LOCAL (primary, pre-registered): **[L2] THE COEVOLUTION LOOP DOES REAL WORK**

Curved decisively beats the move-matched local-random null on BOTH registered readouts,
at every size, both matched algorithms, **96/96 per-seed wins**, meeting the registered
STRONG form (CI-lo(R) > 2.0 at every side):

| N | R = rounds(localrand)/rounds(curved), heat | pushsum | L = λ₂(curved)/λ₂(localrand) |
|---|---|---|---|
| 225  | 11.70 [9.80, 13.82] | 9.26 [7.57, 10.81] | 13.54 [11.14, 15.95] |
| 484  | 15.58 [12.84, 18.71] | 12.56 [9.86, 15.96] | 17.94 [15.45, 20.84] |
| 1024 (decisive) | **21.98 [19.29, 24.89]** | **17.98 [16.64, 19.53]** | **24.40 [22.31, 26.84]** |
| 4096 (blind consistency) | **49.86 [44.44, 55.75]** | **39.16 [30.45, 47.11]** | **61.73 [57.66, 66.21]** |

(geo-mean of paired per-seed ratios, 12 seeds, eps=1e-3; 10k-bootstrap 95% CI. eps=1e-6
is stronger still: R6 heat = 24.2 @1024, 59.4 @4096 — not a tolerance artifact.)

- The null is not budget-starved: **B1 alibi PASSES** — localrand add-turnover is
  81/85/84/86% of curved's at N=225/484/1024/4096 (gate ≥60%).
- The null isn't merely weaker — it's **useless**: localrand vs flat = 0.75/0.78/0.86/0.82x
  (heat), 0.72–0.92x (pushsum) — random local rewiring of the same move type, budget,
  locality radius and bridge protection is *slightly slower than the untouched grid*
  (6/96 per-seed wins). λ₂(localrand) sits *below* λ₂(flat) at every size
  (e.g. 0.000529 vs 0.000617 at N=4096); max_deg stays 8.6–11.2 while curved grows
  hubs to 90.8 → 519.8.
- Worst single seed across all 96 pairs: R = 3.65. There is no overlap anywhere.

**Attribution answer: the traffic signal earns its place.** Deleting only the signal
(keeping every other ingredient of the coevolution loop) destroys the entire effect.
The claim does NOT collapse to "any local rewiring delocalizes" — random local rewiring
delocalizes nothing.

## Q-SCALE — the N=4096 blind probe

- **S1 CONTINUES**: heat curved-vs-flat @4096 = **41.01x [33.54, 48.25]** (registered
  prediction ~38x [26, 55]; continue-gate ≥28.5, kill-gate <14.2). Pushsum 36.17x
  [28.77, 43.17] (predicted ~31x). 4-point log-log exponent **0.540** (pushsum 0.588),
  inside the registered [0.35, 0.65] band — the "~N^0.5" wording survives.
- **S2 DOES NOT WIDEN — prediction MISSED**: heat rounds(shuffled)/rounds(curved) @4096
  = **0.62 [0.55, 0.70]** vs gap-fit prediction 0.35 [0.22, 0.48] (widen-gate CI-hi<0.52).
  Observed CI is disjoint *above* the predicted band, and CI-lo (0.55) sits above the
  N=1024 value (0.52): the curved-vs-shuffled deficit *narrowed slightly* instead of
  widening. Shuffled still beats curved (0.62 < 1) — but the λ₂-power-law extrapolation
  (curved ~N^-0.55) over-predicted curved's decay: observed mean λ₂(curved)@4096 =
  0.0329 vs ~0.023 extrapolated. The per-family power-law fits are not trustworthy
  for extrapolation; the *rank ordering* is (Spearman below).
- **S3 persists**: gossip curved-vs-flat @4096 = 0.64x [0.52, 0.78] — the mismatch
  (hub-throttling) penalty holds at scale, though it softened from 0.40x @1024.
- Gap-governs, tightest yet: Spearman ρ(log rounds, log λ₂) = **−0.990** (heat) /
  **−0.991** (pushsum) across all 168 (side, seed, family) runs, localrand included.

## Q-COST — the priced verdict

price-A (total work = rounds × 2|E|; edge budgets matched) ≈ the rounds ratio — the
matched win survives trivially. The registered question is **price-B (port-limited:
rounds × max_deg)**:

| price-B vs flat (heat) | N=225 | N=484 | N=1024 | N=4096 |
|---|---|---|---|---|
| curved    | 0.40 [0.35,0.45] | 0.38 [0.33,0.44] | 0.29 [0.26,0.34] | **0.35 [0.30,0.40]** |
| localrand | 0.35 | 0.34 | 0.34 | 0.29 |
| shuffled  | — | — | — | 0.56 [0.46,0.70] |
| rreg4     | — | — | — | **138.41 [114, 161]** |

- **C1 replication PASS**: ada's disclosed flip reproduces exactly (0.40/0.38/0.29).
- **C2 FAILS** (as registered): the ">3x cost-adjusted survival" gate fails at every
  size — under port-limited accounting curved *inverts*, **0/96 per-seed wins**
  (heat+pushsum, all sides). The blind N=4096 cell = **0.346 [0.298, 0.405]**: above
  the trend-gate (<0.29), so the deterioration **BREAKS TREND** — the price-B penalty
  plateaus (0.29 → 0.35) rather than continuing to worsen. Still a loss.
- **C3 anchor PASS**: rreg4 price-B (138.41) == its rounds ratio (138.41) exactly at
  4096 (max_deg 4 = flat's 4) — no join bug.
- **C4**: localrand price-B ≈ 0.29–0.35, i.e. ~0.36–0.47x of its own rounds ratio —
  the predicted mild max_deg≈10 penalty, as registered.
- FINDINGS_curvature_compute.md line ~91 ("cost accounting would shrink, not flip,
  the matched win") is **RETRACTED** — it flips, everywhere, 0/96.

## The landmark statement (rewritten — pre-committed wording, L2 + cost-flip branch)

> **A globally-informed traffic signal actuated through local moves grows hub-mediated,
> delocalized wiring that a hub-exploiting matched algorithm uses 8.7–41x over flat
> (rounds, growing ~N^0.54) — an effect a move-matched local-random null cannot produce
> (localrand ≤ flat at every size; deleting only the traffic signal deletes the whole
> effect, 96/96) — BUT the win exists only while hub bandwidth is free: under
> port-limited accounting it inverts (0.24–0.40x, 0/96 per-seed wins), and a
> degree-preserving shuffle of curved's own edges beats the coevolved placement at
> N≥484 (0.62x at N=4096). The resource is the traffic-manufactured degree sequence,
> not curvature and not expansion.**

**"Expander-grade" is retracted UNCONDITIONALLY** (pre-registered wording commitment;
Thomas + Ada's contradiction flag was correct). The data concur: λ₂(curved) decays with
N (0.114 → 0.033); shuffled (0.62x rounds) and rreg4 (138x vs curved's 41x, and rreg4
keeps its full win under BOTH prices) both beat curved. Curved's win is against flat
and against the local-random null — never against expanders.

*Interpretation (ada's morphogenesis framing, labeled as such): the coevolution loop is
a morphogen — traffic gradients tell a local growth process where to build transport
hubs. What it grows is vasculature (a hub backbone), not an expander; vasculature is
exactly what a port-limited node can't afford.*

## What remains open (registered follow-ups, predictions on record)

1. **ada — degree-capped traffic coevolution** (cap 8–12, rounds 14/50/200). Her
   prediction: it DIES (~80%) — delocalization rides on hub-ballooning. This is now THE
   question: is the traffic signal's real work anything more than knowing where to grow
   hubs? Headroom if she's wrong: a capped coevolution keeping its rounds-win would be
   priced-win 4.4/6.1/9.5x.
2. **hopfield — factorial** {traffic, random} × {closure, degree-neutral local 2-swap},
   all capped, anchor rreg-CAP, readout = λ₂ RATE vs cumulative move budget. His
   prediction: traffic-swap beats random-swap on rate (~55–60%).
3. **thomas — random-walk-visit signal null**, only with a walk-LENGTH axis.
4. The S2 model miss: per-family λ₂ power-law fits over-predict curved's decay —
   don't extrapolate them again; any future scale claim needs the run, not the fit.
5. Unchanged caveats from the robustness sweep: one construction recipe (α=0.5,
   14 rounds), one task family (diffusive averaging), one baseline geometry (2D grid),
   Gromov-δ sampled not exact, no Ollivier-Ricci.

## Artifacts

- `decisive_results_2026-07-08.csv` (504 rows), `decisive_graphs_2026-07-08.csv` (168 rows)
- `decisive_analysis_FULL_2026-07-08.txt` (analyzer verdict, exit 0),
  `decisive_analysis_phase1_2026-07-08.txt`, `decisive_2026-07-08.log`,
  `decisive_config_2026-07-08.json`
- `decisive_localnull_2026-07-08.py` (pre-registration v2 + sweep + analyzer; selftest 24/24)
- Box mirror `rule30box:~/src/cdc-lab/`; re-run verdict:
  `ssh rule30box 'cd src/cdc-lab && ~/cdc-env/bin/python decisive_localnull_2026-07-08.py --analyze'`
- Supersedes the landmark paragraph of `FINDINGS_curvature_compute.md` (2026-07-08,
  robustness sweep), whose "expander-grade" wording and "shrink, not flip" cost claim
  are retracted above.
