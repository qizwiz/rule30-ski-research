# FINDINGS: "Curvature as a computational resource" — robustness sweep verdict

> **SUPERSEDED (2026-07-08, decisive local-null run): see `FINDINGS_decisive_localnull.md`.**
> "Expander-grade" is RETRACTED (unconditional pre-registered wording commitment), and the
> line-91 claim that cost accounting "would shrink, not flip" the matched win is RETRACTED
> (it flips: price-B 0.24–0.40x, 0/96 per-seed wins). The traffic-attribution question this
> file left open is now ANSWERED: curved beats the move-matched local-random null 22x @1024
> / 50x @4096 (rounds) and 24x/62x (lambda2) — the coevolution loop does real work.

Date: 2026-07-08. Sweep ran on rule30box (06:48–06:56 UTC, ~8 min, 432/432 cells, zero
censoring); verdict reproduced identically on the Mac from transferred CSVs (analyze
exit 0), and every headline number below was independently recomputed from the raw
`robust_runs.csv` / `robust_graphs.csv` (not just read off the analyzer output).

## The landmark statement (post-sweep, honest wording)

> **Local traffic-driven coevolution of a flat grid buys delocalized, expander-grade
> wiring that a geometry-matched algorithm exploits 9–19x over flat (growing with N,
> ~N^0.5), while a geometry-mismatched algorithm on the same graph gets nothing — it
> gets 2–2.5x SLOWER than flat.**

Per the pre-registered R3 reading, the earlier framing "curvature per se is the
resource" is **dropped**: degree-preserving shuffles and plain 4-regular expanders
match or beat the coevolved geometry for the matched algorithms. What survives, and is
robust across 3 sizes x 12 seeds x 2 tolerances x 2 matched algorithms with zero
exceptions, is:

1. **Curved >> flat when matched** (R1 PASS): heat diffusion geo-mean speedup 8.7x
   (N=225) → 12.2x → 19.0x (N=1024); push-sum 6.7x → 9.9x → 15.6x. All 95% CI lower
   bounds >> 1.5; **72/72 per-seed paired cells are wins** (worst single seed: 3.2x).
2. **Mismatch penalty reproduces** (R2 PASS): Metropolis gossip on the SAME curved
   graphs is 0.40–0.50x — slower than flat — at every size; **0/36 per-seed wins**
   (best single seed 0.92x). The gossip CI upper bound (0.51–0.63) sits far below the
   heat CI lower bound (7.4–17.2) at every size.
3. **The normalized-Laplacian gap governs** (R4 PASS): Spearman rho(log rounds,
   log lambda2) = −0.962 (heat, 144 runs) and −0.961 (push-sum). Quantitatively, the
   gap ratio lambda2(curved)/lambda2(flat) scales as N^+0.48 and the observed heat
   speedup scales as N^+0.51 — the mechanism closes.

The original 2026-07-07 landmark point (flat=570, curved=83, 6.9x, seed 30, N=225;
`results_compute_matched_2026-07-08.txt`) reproduces inside the sweep with paired x0
as flat=689 / curved=89 = 7.7x — consistent with the seed-30 draw sitting slightly
below the N=225 geo-mean of 8.7x.

## Evidence table 1 — paired speedup vs flat, eps=1e-3 (geo-mean [bootstrap 95% CI] {per-seed min..max}, 12 seeds)

| algo    | family   | N=225 | N=484 | N=1024 |
|---------|----------|-------|-------|--------|
| heat    | curved   | 8.73x [7.40,10.03] {4.4..11.7} | 12.18x [10.36,14.20] {7.5..19.3} | 18.97x [17.17,21.14] {15.0..25.9} |
| heat    | shuffled | 9.18x [7.67,11.00] | 16.13x [14.21,18.29] | 36.22x [32.62,40.04] |
| heat    | rreg4    | 12.30x [11.44,13.19] | 22.94x [20.72,25.37] | 46.74x [43.71,50.04] |
| pushsum | curved   | 6.65x [5.68,7.49] {3.2..8.2} | 9.87x [8.21,11.88] {6.3..15.4} | 15.62x [14.24,17.13] {12.6..19.7} |
| pushsum | shuffled | 6.84x [5.66,8.23] | 12.33x [10.83,13.79] | 25.88x [23.45,28.42] |
| pushsum | rreg4    | 12.89x [12.09,13.78] | 23.93x [21.50,26.58] | 48.00x [44.59,51.43] |
| gossip  | curved   | 0.47x [0.38,0.60] {0.25..0.91} | 0.50x [0.40,0.63] {0.27..0.86} | 0.40x [0.32,0.51] {0.19..0.92} |
| gossip  | shuffled | 0.63x [0.48,0.84] | 0.91x [0.66,1.24] | 0.87x [0.70,1.07] |
| gossip  | rreg4    | 13.45x [12.60,14.38] | 24.64x [22.08,27.37] | 48.93x [45.34,52.42] |

eps=1e-6 numbers are uniformly slightly HIGHER for the matched algos (heat curved
9.4/13.6/20.1x) and unchanged in sign for gossip (0.46/0.54/0.44x) — the effect is not
a tolerance artifact. Full tables: `results_robustness/robust_verdict_2026-07-08.txt`.

## Evidence table 2 — R3 controls (rounds_control / rounds_curved, eps3; <1 means control is FASTER)

| contrast | N=225 | N=484 | N=1024 |
|----------|-------|-------|--------|
| heat: curved vs shuffled | 0.95 [0.75,1.18] (tie) | 0.76 [0.66,0.85] | 0.52 [0.46,0.59] |
| heat: curved vs rreg4    | 0.71 [0.60,0.81] | 0.53 [0.46,0.60] | 0.41 [0.36,0.46] |
| pushsum: curved vs shuffled | 0.97 [0.77,1.22] (tie) | 0.80 [0.69,0.93] | 0.60 [0.55,0.67] |
| pushsum: curved vs rreg4    | 0.52 [0.43,0.59] | 0.41 [0.35,0.48] | 0.33 [0.30,0.35] |

The honest-risk branch of the pre-registration fired, sharper than predicted: curved ~
shuffled at N=225, but curved is strictly SLOWER than both controls at N=484/1024.
Spectral explanation (fit from `robust_graphs.csv` means): lambda2(flat) ~ N^−1.04,
lambda2(curved) ~ N^−0.55, lambda2(shuffled) ~ N^−0.18, lambda2(rreg4) ~ N^−0.04. The
coevolved family is **not** a true expander family — its gap decays; the speedup over
flat grows only because the grid's gap decays faster. Hub placement by local traffic
costs gap at scale relative to its own degree-preserving shuffle.

Note on gossip vs rreg4 (13–49x): the mismatch penalty is specifically a HUB penalty —
Metropolis weights throttle high-degree nodes (max_deg ≈ 91/137/270 on curved vs 4 on
flat/rreg4). Gossip is fine on a degree-flat expander; it dies on the hubby coevolved
graph. "Mismatch" = algorithm weighting vs degree structure, not grid vs non-grid.

## Validity (R0 PASS)

- Edge budget held: max curved-vs-flat edge drift 0.24% (bound 5%).
- All 144 graphs connected; 0 of 432 runs censored at maxr=40000 (eps3 and eps6).
- Pairing: one x0 per (side, seed) shared across all families/algos — all ratios paired.
- Script `sweep_curvature_robustness.py` sha-identical to designer's
  `robustness_sweep.py`; box selftest 14/14 pre-launch.

## Honest caveats — what was NOT tested

- **Round-cost accounting**: rounds are counted, not per-node work. Total messages per
  round = 2|E| is matched across families, but hub nodes do O(deg) work per round
  (max_deg up to ~270 on curved). A max-node-load or wall-clock-per-round-adjusted
  comparison was not run; it would shrink (not flip) the matched-algo win.
- **One construction recipe**: coevolve(alpha=0.5, 14 rounds, traffic ∝ N) only. No
  ablation of coevolution parameters; no test of whether MORE coevolution rounds close
  the gap to shuffled at large N.
- **One task family**: consensus/averaging (diffusive). Nothing non-diffusive was
  tested (shortest path, search, load balancing, epidemics).
- **One baseline geometry**: 2D grid. No 3D lattice, no other flat starts.
- **One mismatched algorithm**: Metropolis gossip. Other naive nulls (uniform-weight
  synchronous averaging, asynchronous gossip) untested.
- **Scale ceiling N=1024**: growth trend (N^0.51) is a 3-point fit; extrapolation
  unproven, and the decaying curved gap (N^−0.55) predicts the curved-vs-shuffled
  deficit WIDENS with N.
- **Curvature was never isolated as a variable**: Gromov delta/diam drops for curved
  (0.35 → 0.10–0.15) but shuffled shows nearly the same drop — hyperbolicity here is a
  byproduct of delocalized wiring, and delta_max is a 4000-quadruple sample, an
  estimate. No Ollivier-Ricci computed. This is why the curvature framing is dropped,
  not merely soft-pedaled.

## Next falsification

The surviving claim's load-bearing word is **LOCAL**: "local traffic-driven
coevolution buys expander-grade mixing." The shuffled control is a GLOBAL
randomization, so it cannot tell us whether the traffic signal matters.

1. **Local-null control (the sharp test)**: rerun the sweep adding a family
   `local-random` = same rewiring budget and same locality radius as coevolve, but
   edges rewired at random (no traffic signal). Pre-register: if local-random matches
   curved on lambda2 and rounds, the traffic-driven selection does nothing and the
   claim collapses to "any local rewiring with hub formation delocalizes"; if curved
   beats local-random, the coevolution loop is doing real work.
2. **Scale probe N=4096 (side 64)**: does heat curved-vs-flat continue ~N^0.5 and does
   curved-vs-shuffled continue to widen (prediction from the gap fits: ratio ~0.35)?
3. **Cost-adjusted verdict**: recompute R1/R2 in units of max-node-load x rounds; the
   matched win should survive at >3x — if it doesn't, hubs are buying speedup with
   unpaid bandwidth.

## Artifacts

- `results_robustness/robust_runs.csv` (432 rows), `robust_graphs.csv` (144 rows),
  `robust_config.json`, `robust_verdict_2026-07-08.txt` (exit 0), `sweep_2026-07-08.log`
- `results_compute_matched_2026-07-08.txt` (original landmark point, box run)
- `sweep_curvature_robustness.py` (the sweep + pre-registered analyzer)
- Box copies kept at `rule30box:~/src/cdc-lab/`; nothing left running on the box.
