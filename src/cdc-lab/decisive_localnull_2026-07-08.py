#!/usr/bin/env python3
"""CDC-lab DECISIVE EXPERIMENT -- PRE-REGISTRATION v2 (2026-07-08).

v1 written 02:37 (Q-LOCAL + Q-SCALE). v2 amendment written the same morning,
BEFORE ANY DECISIVE DATA EXISTS (verified: no decisive_results_*.csv anywhere),
adding the third pre-registered component (Q-COST), gossip, turnover
instrumentation, a side-64 maxr that cannot censor (extrapolated worst cell
gossip/curved eps6 ~80k rounds; maxr=200000), and lambda2 into the Q-LOCAL
collapse criterion. Nothing in the v1 decision rules was weakened.

=============================================================================
CLAIM UNDER TEST (FINDINGS_curvature_compute.md, post-robustness-sweep):
  "LOCAL traffic-driven coevolution of a flat grid buys delocalized,
   expander-grade wiring that a geometry-matched algorithm exploits 9-19x
   over flat (growing ~N^0.5)."
Load-bearing word: LOCAL(+traffic-driven). The shuffled control is GLOBAL, so
it cannot test whether the traffic signal matters. This experiment settles the
attribution question.

WORDING COMMITMENT, UNCONDITIONAL: "expander-grade" is retracted from the
landmark REGARDLESS of outcome (Thomas + Ada both flagged the internal
contradiction: FINDINGS line 11 "expander-grade" vs line 69 "not a true
expander family"; lambda2(curved) ~ N^-0.55 is not an expander family).

SOCIETY DELIBERATION HONORED (nerve-forum #curvature-compute, 02:19-02:31):
  - thomas: committed the null design = MOVE-MATCHED local-random rewiring
    (identical move type / schedule / bridge protection; traffic signal
    replaced by uniform randomness). build_localrand below IS that design,
    promoted unchanged from his N=225 pilot into the full pre-registered
    sweep, as he and hopfield both demanded. His turnover instrumentation
    (budget-starvation alibi) is promoted too (moves_add / moves_rm columns).
  - ada: found the cost verdict FLIPS on the existing CSVs. Disclosed below;
    Q-COST at sides<=32 is therefore a REPLICATION gate, not a blind test.
  - hopfield: replicated the flip; demanded locrand at full scale before any
    FINDINGS rewrite ("this project already got burned at N=225") -> locrand
    runs at ALL sides including 64. His and ada's degree-capped factorial is
    a REGISTERED FOLLOW-UP (below), not folded into this experiment.

DISCLOSURE OF PRIOR PEEKS (what is confirmatory vs blind):
  - thomas's pilot (N=225, seeds 30-35): locrand heat 0.70x vs flat,
    lambda2 0.008 (< flat 0.012), max_deg 7-10, turnover 81% of curved's.
    => Q-LOCAL at N=225 is CONFIRMATORY. N=484, N=1024, N=4096 are BLIND.
  - ada/hopfield cost flip (from existing CSVs, verified independently by the
    designer of this file before registration): price-B heat curved vs flat =
    0.40x / 0.38x / 0.29x at N=225/484/1024, 0/36 per-seed wins; pushsum
    0.30/0.31/0.24; gossip 0.02/0.02/0.01; rreg4 keeps its FULL win under
    both prices (max_deg 4 = flat's 4). => Q-COST at sides<=32 is
    REPLICATION. Q-COST at N=4096 and all locrand cost cells are BLIND.
  - everything at N=4096 is BLIND (no run of any kind has been done there).

=============================================================================
Q-LOCAL -- the attribution question (DECISIVE).
Family `localrand` = coevolve's move structure, budget, locality radius, 14
rounds, bridge protection -- every traffic-informed choice replaced by a
uniform-random one; NO traffic simulated. The only deleted ingredient is the
signal.

Primary readout (per side, per matched algo in {heat, pushsum}, eps=1e-3):
paired per-seed ratio R = rounds(localrand)/rounds(curved), geo-mean +
10k-bootstrap 95% CI (the sweep's exact statistic). Secondary mechanism
readout: paired per-seed ratio L = lambda2(curved)/lambda2(localrand),
geo-mean + CI. Decisive side = N=1024 (largest phase-1), with a REGISTERED
CONSISTENCY CHECK at N=4096: if the N=1024 verdict and the N=4096 CI
disagree in direction, N=4096 GOVERNS (this project was burned at small N
once already; R3 tie at 225 became a strict loss at 484+).

  L2 "the coevolution loop does real work" (attribution SURVIVES):
      CI-lo(R) > 1.0 at N=1024 for BOTH matched algos AND geo-mean R >= 1.5
      for heat at N=1024. Strong form (registered, expected from the pilot):
      CI-lo(R) > 2.0 at every side for both matched algos.
  L1 "claim collapses to 'any local rewiring delocalizes'" (attribution
      FALSIFIED): CI(R) spans 1.0 at N=1024 (either matched algo, without
      the other showing CI-lo>1) AND CI(L) spans or sits below 1.0 (the
      task-specified rounds-AND-lambda2 conjunction). Rounds-tie with a
      clear lambda2 separation (or vice versa) = MIXED: no collapse may be
      declared; investigate the readout/mechanism mismatch first.
  L3 "traffic selection is actively HARMFUL vs random local rewiring":
      CI-hi(R) < 1.0 at N=1024 for both matched algos.
  B1 budget-starvation alibi (gate on declaring L1): locrand mean add-
      turnover must be >= 60% of curved's at that side (pilot: 81%).
      If turnover < 60%, L1 may NOT be declared from this run; a budget-
      matched follow-up (retry adds until landed, capped attempts) is the
      pre-committed next step instead.

Registered predictions (from the pilot + gap fits; point [band]):
  R(heat, N=225) ~ 12x [6, 25] (pilot: 8.73/0.70). locrand-vs-flat <= 1.0x
  at every side (locrand does not even beat the grid). lambda2(localrand)
  stays below lambda2(flat); max_deg(localrand) stays O(10) at every side.

Q-SCALE -- the N=4096 probe (side 64; families flat/curved/shuffled/rreg4/
localrand; all BLIND).
  S1: heat curved-vs-flat geo-mean speedup at N=4096. Prediction from the
      N^0.51 fit: ~38x [26, 55]. "Growth continues" iff >= 28.5 (=1.5x the
      N=1024 value 19.0). KILL: < 14.2 (the sweep's own 0.75x decay rule) =
      the ~N^0.5 growth story dies. Secondary: pushsum ~31x [20, 48];
      4-point log-log fit exponent must stay in [0.35, 0.65] or the
      "~N^0.5" wording is dropped.
  S2: heat rounds(shuffled)/rounds(curved) at N=4096. Prediction from the
      gap fits (lambda2 curved ~N^-0.55, shuffled ~N^-0.18): ~0.35
      [0.22, 0.48]. "Deficit widens" iff CI-hi < 0.52 (the N=1024 value).
  S3 (reported): gossip curved-vs-flat stays < 1 at N=4096 (predict
      0.25-0.55) -- the R2 mismatch penalty persists at scale.

Q-COST -- the priced verdict (rounds are not free when hubs do O(deg) work).
Two prices, both registered so "cost-adjusted" is unambiguous:
  price-A (total work)    = rounds x 2|E|      (edge budget matched by R0,
                            so price-A ~ the rounds ratio; matched win
                            trivially survives; reported for completeness)
  price-B (port-limited / critical path) = rounds x max_deg  (a node is
                            hardware with finite ports; ada's accounting)
  C1 REPLICATION (disclosed): price-B heat/pushsum curved-vs-flat < 1 at
      every side <= 32, ~0.40/0.38/0.29 (heat). If this does NOT reproduce,
      HALT: reconcile code before interpreting anything.
  C2 THE TASK'S QUESTION: "does the matched win survive >3x cost-adjusted?"
      Gate: price-B geo-mean >= 3.0 at every side. REGISTERED EXPECTATION:
      FAIL (already known to fail at <=1024). The blind cell is N=4096:
      prediction price-B(heat, curved) ~0.22 [0.12, 0.35]; trend gate:
      < 0.29 (continues worsening). FINDINGS line ~91 ("would shrink, not
      flip") is ALREADY DEAD on the existing data and is retracted in the
      rewrite regardless.
  C3 ANCHOR / bug tripwire: rreg4 price-B == its rounds ratio (max_deg 4 =
      flat's 4) at every side where rreg4 runs; deviation = join bug.
  C4 BLIND: price-B for localrand (max_deg ~10 -> mild penalty ~2.5x,
      prediction: price-B(localrand) ~ 0.3x of its own rounds ratio).

=============================================================================
DECISION / WORDING MATRIX (the FINDINGS rewrite is pre-committed):
  L2 + cost flip confirmed -> landmark becomes: "A globally-informed traffic
    signal actuated through local moves grows hub-mediated delocalized wiring
    that a hub-exploiting matched algorithm uses 9-38x over flat (rounds,
    growing ~N^0.5) -- an effect a move-matched local-random null cannot
    produce (locrand <= flat) -- BUT the win exists only while hub bandwidth
    is free: under port-limited accounting it inverts (0.2-0.4x), and a
    degree-preserving shuffle matches or beats the coevolved placement at
    N>=484. The resource is the traffic-manufactured degree sequence, not
    curvature and not expansion." (Plus ada's morphogenesis framing as
    interpretation, clearly labeled as interpretation.)
  L1 (+B1 clean) -> the traffic attribution is FALSIFIED; landmark retracts
    to "any local rewiring of this budget delocalizes"; FINDINGS landmark
    paragraph replaced, pilot marked as non-replicating.
  L3 -> traffic is actively harmful; strongest retraction; investigate
    before publishing anything.
  S1-kill fires -> all "growing with N" language is removed everywhere.
  In every cell: "expander-grade" is removed; both prices are reported next
  to every headline speedup number from now on.

REGISTERED FOLLOW-UPS (not run here; predictions on the record):
  - ada: DEGREE-CAPPED traffic coevolution (cap 8-12, rounds 14/50/200).
    She predicts it DIES (~80%): delocalization rides on hub-ballooning.
  - hopfield: factorial {traffic, random} x {closure, degree-neutral local
    2-swap}, all capped, anchor rreg-CAP (rreg8 for cap 8), readout = RATE
    (lambda2 vs cumulative move budget), not endpoint. He predicts
    traffic-swap beats random-swap on rate (~55-60%). Headroom if a capped
    coevolution keeps its rounds-win: priced win 4.4/6.1/9.5x (cap 8).
  - thomas: random-WALK-visit signal null -- only with a walk-LENGTH axis
    (ada: stationary visits are degree-proportional = purely local).

VALIDITY GATES (all must pass or the analysis prints HALT and exits 1):
  V0 REPRODUCTION: flat/curved/gossip-inclusive cells at sides <= 32 must
     reproduce results_robustness/robust_runs.csv rounds EXACTLY (identical
     builders, seeds, x0 scheme => digit-for-digit or the environment
     drifted). Thomas's pilot gate, promoted.
  V1 = the sweep's R0: all graphs connected; curved edge drift <= 5%;
     <= 10% of non-flat cells censored at maxr (eps6). locrand eps6 cells at
     side 64 MAY censor (locrand is slow); eps3 is the primary readout and
     is safe by >5x margin. Censored numerators are kept at maxr (ratio
     becomes a conservative lower bound), censored denominators excluded --
     the sweep's exact convention.

DESIGN MATRIX (composes with the robustness sweep; nothing re-interpreted):
  phase 1: sides 15, 22, 32; families flat, curved, localrand
           (shuffled/rreg4 at these sides come from robust_*.csv -- same
           deterministic builders/seeds -- joined read-only in --analyze)
  phase 2: side 64; families flat, curved, shuffled, rreg4, localrand
  seeds 30..41 (12, incl. landmark seed 30); algos heat, pushsum, gossip;
  eps {1e-3, 1e-6}; maxr 40000 (sides<=32, = robust sweep) / 200000 (side
  64, non-censoring by >2x on the worst extrapolated cell); pairing: one x0
  per (side, seed) = default_rng([seed, side]) -- IDENTICAL to the sweep.
  ~756 run cells. Estimated wall: phase 1 ~10-20 min; phase 2 dominated by
  12 coevolve builds (~15-45 min each, parallelized over seeds) ~1-2 h on
  the box. Memory: <6 GB at 12 workers.

All kernels verbatim from sweep_curvature_robustness.py (the audited sweep);
new code paths: build_localrand (= thomas's pilot builder), move tallies
(additive counters, rng streams untouched -- selftest-checked), sparse
lambda2 for n>1500 (selftest-checked against dense), cost columns, the
seed-parallel driver.

OUTPUT (incremental, fsync per row, resume-safe):
  <outdir>/decisive_results_2026-07-08.csv   one row per (side,seed,family,algo)
  <outdir>/decisive_graphs_2026-07-08.csv    one row per (side,seed,family)
  <outdir>/decisive_config_2026-07-08.json   parameters
Log markers: "PHASE-1 COMPLETE" (Q-LOCAL answerable), "SWEEP COMPLETE".

USAGE (box: ~/cdc-env/bin/python; numpy/networkx/scipy only):
  python decisive_localnull_2026-07-08.py --selftest   # kernel checks, no CSVs
  python decisive_localnull_2026-07-08.py --quick      # smoke: side 10, 2 seeds
  python decisive_localnull_2026-07-08.py              # full run
  python decisive_localnull_2026-07-08.py --analyze    # pre-registered verdict
"""

import argparse
import csv
import json
import math
import multiprocessing as mp
import os
import random
import sys
import time

import numpy as np
import networkx as nx
import scipy.sparse as sp
from scipy.linalg import eigh
from scipy.sparse.linalg import eigsh
from scipy.sparse.csgraph import laplacian as csgraph_laplacian
from scipy.sparse.csgraph import shortest_path as csgraph_shortest_path
from scipy.stats import spearmanr

# ----------------------------------------------------------------------------- config
PHASE1_SIDES = [15, 22, 32]
PHASE2_SIDES = [64]
DEFAULT_SEEDS = list(range(30, 42))          # 12 seeds, includes landmark seed 30
MAXR_BY_SIDE = {64: 200000}                  # side-64 worst cell extrapolates ~80k
DEFAULT_MAXR = 40000                         # sides<=32: identical to robust sweep
ALPHA = 0.5
EPS_LIST = [1e-3, 1e-6]
FAMILIES_P1 = ["flat", "curved", "localrand"]
FAMILIES_P2 = ["flat", "curved", "shuffled", "rreg4", "localrand"]
ALGOS = ["heat", "pushsum", "gossip"]        # gossip needed for the R2-cost verdict
MATCHED_ALGOS = ["heat", "pushsum"]
DELTA_SAMPLES = 4000
NBOOT = 10000
DENSE_LAMBDA2_MAX_N = 1500                   # dense eigh below (== prior sweep), sparse above
DATE = "2026-07-08"

RUNS_FIELDS = ["side", "n", "seed", "family", "algo",
               "rounds_eps3", "conv_eps3", "rounds_eps6", "conv_eps6",
               "maxr", "alpha", "secs",
               "max_deg", "edges", "cost3_load", "cost6_load", "note"]
GRAPHS_FIELDS = ["side", "seed", "family", "nodes", "edges", "connected",
                 "mean_deg", "max_deg", "diam", "mean_path_len",
                 "gromov_delta_max", "delta_over_diam", "lambda2_norm",
                 "moves_add", "moves_rm", "build_secs", "note"]


def families_for(side):
    return FAMILIES_P2 if side in PHASE2_SIDES else FAMILIES_P1


def maxr_for(side, override=None):
    if override is not None:
        return override
    return MAXR_BY_SIDE.get(side, DEFAULT_MAXR)


def log(msg):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


# ------------------------------------------------------------------------ graph builds
def build_flat(side):
    return nx.convert_node_labels_to_integers(nx.grid_2d_graph(side, side))


def coevolve(G, rng, rounds=14, traffic=None, tally=None):
    """VERBATIM landmark construction (sweep_curvature_robustness.py coevolve).
    `tally` (optional dict) accumulates add/rm move counts WITHOUT touching the
    rng stream or the graph logic (selftest checks determinism is unchanged)."""
    G = G.copy()
    if traffic is None:
        traffic = int(round(1200 * G.number_of_nodes() / 225.0))
    for _ in range(rounds):
        eu = {tuple(sorted(e)): 0 for e in G.edges()}
        nu = {n: 0 for n in G}
        nd = list(G)
        for _ in range(traffic):
            s, t = rng.sample(nd, 2)
            try:
                p = nx.shortest_path(G, s, t)
            except nx.NetworkXNoPath:
                continue
            for a, b in zip(p, p[1:]):
                k = tuple(sorted((a, b)))
                eu[k] = eu.get(k, 0) + 1
            for x in p[1:-1]:
                nu[x] = nu.get(x, 0) + 1
        cong = sorted(nu, key=lambda x: -nu[x])[: max(1, len(G) // 15)]
        add = 0
        for x in cong:
            nb = sorted(G[x], key=lambda y: -eu.get(tuple(sorted((x, y))), 0))
            if len(nb) >= 2 and not G.has_edge(nb[0], nb[1]):
                G.add_edge(nb[0], nb[1])
                add += 1
        br = set(map(lambda e: tuple(sorted(e)), nx.bridges(G)))
        pr = sorted((k for k in eu if k not in br and G.has_edge(*k)),
                    key=lambda k: eu[k])
        rm = 0
        for k in pr[:add]:
            if k not in set(map(lambda e: tuple(sorted(e)), nx.bridges(G))):
                G.remove_edge(*k)
                rm += 1
        if tally is not None:
            tally["add"] = tally.get("add", 0) + add
            tally["rm"] = tally.get("rm", 0) + rm
    return G


def build_localrand(G, rng, rounds=14, tally=None):
    """THE LOCAL-RANDOM NULL (thomas's committed pilot design, promoted
    unchanged): coevolve's move structure, budget, and locality radius with
    every traffic-informed choice replaced by a uniform-random one; no traffic
    simulated. Mirrors coevolve line-by-line:
      congested-node pick  -> uniform-random node pick (same count max(1, N//15))
      top-2-traffic-neighbor edge add -> uniform-random neighbor-pair edge add
                                         (same distance-2 move in the CURRENT graph)
      least-used non-bridge deletions -> uniform-random non-bridge deletions
                                         (same count = successful adds, bridges
                                          re-checked before each removal)"""
    G = G.copy()
    for _ in range(rounds):
        nd = list(G)
        picks = rng.sample(nd, min(len(nd), max(1, len(G) // 15)))
        add = 0
        for x in picks:
            nb = list(G[x])
            if len(nb) >= 2:
                u, v = rng.sample(nb, 2)
                if not G.has_edge(u, v):
                    G.add_edge(u, v)
                    add += 1
        br = set(map(lambda e: tuple(sorted(e)), nx.bridges(G)))
        cand = [k for k in map(lambda e: tuple(sorted(e)), G.edges()) if k not in br]
        pr = rng.sample(cand, len(cand))     # random order (coevolve: traffic order)
        rm = 0
        for k in pr[:add]:
            if k not in set(map(lambda e: tuple(sorted(e)), nx.bridges(G))):
                G.remove_edge(*k)
                rm += 1
        if tally is not None:
            tally["add"] = tally.get("add", 0) + add
            tally["rm"] = tally.get("rm", 0) + rm
    return G


def build_shuffled(curved, seed):
    """VERBATIM: degree-preserving randomization of the curved graph."""
    E = curved.number_of_edges()
    try:
        H = curved.copy()
        nx.connected_double_edge_swap(H, nswap=4 * E, seed=seed)
        return H, "connected_double_edge_swap"
    except Exception as ex:  # noqa: BLE001
        for k in range(5):
            H = curved.copy()
            try:
                nx.double_edge_swap(H, nswap=4 * E, max_tries=200 * E,
                                    seed=seed + 1000 * (k + 1))
            except Exception:
                continue
            if nx.is_connected(H):
                return H, f"double_edge_swap_retry{k}"
        return H, f"SHUFFLE_FAILED:{type(ex).__name__}"


def build_rreg4(n, seed):
    """VERBATIM: random 4-regular expander reference."""
    for k in range(5):
        H = nx.random_regular_graph(4, n, seed=seed + 1000 * k)
        if nx.is_connected(H):
            return H, f"rreg4_try{k}"
    return H, "RREG_DISCONNECTED"


# --------------------------------------------------------------------- linear operators
def to_csr(G):
    try:
        return sp.csr_matrix(nx.to_scipy_sparse_array(G, dtype=np.float64))
    except AttributeError:
        return sp.csr_matrix(nx.to_scipy_sparse_matrix(G, dtype=np.float64))


def metropolis_matrix(A, d):
    """VERBATIM: W = I + sum_edges w_ij (E_ij + E_ji - E_ii - E_jj),
    w_ij = 1/(1+max(d_i,d_j)) -- exactly compute_on_curvature.py gossip_rounds."""
    C = sp.coo_matrix(A)
    w = 1.0 / (1.0 + np.maximum(d[C.row], d[C.col]))
    W = sp.coo_matrix((w, (C.row, C.col)), shape=A.shape).tocsr()
    rowsum = np.asarray(W.sum(axis=1)).ravel()
    return (W + sp.diags(1.0 - rowsum)).tocsr()


def pushsum_matrix(A, d):
    """VERBATIM: column-stochastic B over A+I, B_ij = 1/(d_j + 1)."""
    n = A.shape[0]
    M = sp.coo_matrix(sp.csr_matrix(A) + sp.identity(n, format="csr"))
    vals = M.data * (1.0 / (d + 1.0))[M.col]
    return sp.coo_matrix((vals, (M.row, M.col)), shape=(n, n)).tocsr()


def run_algo(algo, A, x0, maxr, eps_list):
    """VERBATIM (all three branches of the sweep's run_algo)."""
    n = A.shape[0]
    d = np.asarray(A.sum(axis=1)).ravel()
    mu0 = float(x0.mean())
    r0 = max(float(np.linalg.norm(x0 - mu0)), 1e-12)
    eps_sorted = sorted(eps_list, reverse=True)
    hit = {e: 0 for e in eps_list}

    if algo == "heat":
        P = sp.diags(1.0 / np.where(d > 0, d, 1.0)) @ A
        x = x0.copy()

        def step_res():
            nonlocal x
            x = (1.0 - ALPHA) * x + ALPHA * (P @ x)
            return float(np.linalg.norm(x - x.mean())) / r0
    elif algo == "gossip":
        W = metropolis_matrix(A, d)
        x = x0.copy()

        def step_res():
            nonlocal x
            x = W @ x
            return float(np.linalg.norm(x - x.mean())) / r0
    elif algo == "pushsum":
        B = pushsum_matrix(A, d)
        s = x0.copy()
        w = np.ones(n)

        def step_res():
            nonlocal s, w
            s = B @ s
            w = B @ w
            return float(np.linalg.norm(s / w - mu0)) / r0
    else:
        raise ValueError(f"unknown algo {algo}")

    tight = min(eps_list)
    for r in range(1, maxr + 1):
        res = step_res()
        for e in eps_sorted:
            if hit[e] == 0 and res < e:
                hit[e] = r
        if hit[tight]:
            break
    return hit


# -------------------------------------------------------------------------- graph stats
def lambda2_norm(A, n):
    """Second-smallest eigenvalue of the NORMALIZED Laplacian. Dense eigh for
    n <= DENSE_LAMBDA2_MAX_N (identical to the prior sweep); sparse shift-invert
    eigsh above, with dense fallback. Selftest checks sparse == dense."""
    L = csgraph_laplacian(sp.csr_matrix(A), normed=True)
    if n <= DENSE_LAMBDA2_MAX_N:
        evals = eigh(np.asarray(L.todense()), eigvals_only=True, subset_by_index=[0, 1])
        return float(evals[1])
    try:
        vals = eigsh(L.tocsc(), k=2, sigma=-1e-6, which="LM",
                     return_eigenvectors=False, maxiter=20000)
        vals = np.sort(vals)
        if abs(vals[0]) < 1e-7 and vals[1] > 1e-12:
            return float(vals[1])
        raise RuntimeError(f"eigsh insane: {vals}")
    except Exception:
        evals = eigh(np.asarray(L.todense()), eigvals_only=True, subset_by_index=[0, 1])
        return float(evals[1])


def graph_stats(G, rng, delta_samples=DELTA_SAMPLES):
    n = G.number_of_nodes()
    A = to_csr(G)
    d = np.asarray(A.sum(axis=1)).ravel()
    connected = nx.is_connected(G)
    out = dict(nodes=n, edges=G.number_of_edges(), connected=int(connected),
               mean_deg=round(float(d.mean()), 4), max_deg=int(d.max()))
    if not connected:
        out.update(diam=-1, mean_path_len=-1, gromov_delta_max=-1,
                   delta_over_diam=-1, lambda2_norm=-1)
        return out
    D = csgraph_shortest_path(A, method="D", unweighted=True, directed=False)
    diam = int(D.max())
    iu = np.triu_indices(n, k=1)
    mean_l = float(D[iu].mean())
    idx = np.arange(n)
    best = 0.0
    for _ in range(delta_samples):
        a, b, c, e = rng.choice(idx, size=4, replace=False)
        s1, s2, s3 = D[a, b] + D[c, e], D[a, c] + D[b, e], D[a, e] + D[b, c]
        s = sorted((s1, s2, s3))
        best = max(best, (s[2] - s[1]) / 2.0)
    out.update(diam=diam, mean_path_len=round(mean_l, 4),
               gromov_delta_max=float(best),
               delta_over_diam=round(float(best) / max(diam, 1), 4),
               lambda2_norm=round(lambda2_norm(A, n), 8))
    return out


# ------------------------------------------------------------------------------- CSV io
def append_row(path, fields, row):
    new = not os.path.exists(path) or os.path.getsize(path) == 0
    with open(path, "a", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        if new:
            w.writeheader()
        w.writerow(row)
        f.flush()
        os.fsync(f.fileno())


def load_done(path, keyfields):
    done = set()
    if os.path.exists(path):
        with open(path) as f:
            for row in csv.DictReader(f):
                done.add(tuple(str(row[k]) for k in keyfields))
    return done


# ----------------------------------------------------------------------- worker (1 seed)
def work_cell(task):
    """Build all needed graphs for one (side, seed) and run all needed cells.
    Returns (graph_rows, run_rows). Never raises: errors are logged and the
    cell is left unwritten so a resume retries it."""
    side, seed, maxr, need_runs, need_stats = task
    graph_rows, run_rows = [], []
    try:
        n = side * side
        fams = families_for(side)
        need_fams = set(f for f, _ in need_runs) | set(need_stats)
        t0 = time.time()
        graphs = {}     # fam -> (G, note, tally-or-None)
        flat = build_flat(side)
        graphs["flat"] = (flat, "", None)
        curved = None
        if {"curved", "shuffled"} & need_fams:
            tal = {}
            curved = coevolve(flat, random.Random(seed), tally=tal)
            graphs["curved"] = (curved, "", tal)
        if "shuffled" in need_fams and "shuffled" in fams:
            sh, note = build_shuffled(curved, seed)
            graphs["shuffled"] = (sh, note, None)
        if "rreg4" in need_fams and "rreg4" in fams:
            rr, note = build_rreg4(n, seed)
            graphs["rreg4"] = (rr, note, None)
        if "localrand" in need_fams:
            tal = {}
            graphs["localrand"] = (build_localrand(flat, random.Random(1_000_000 + seed),
                                                   tally=tal), "", tal)
        build_secs = round(time.time() - t0, 2)
        log(f"side={side} seed={seed}: built {sorted(need_fams)} in {build_secs}s "
            f"(edges flat={flat.number_of_edges()}"
            + (f" curved={curved.number_of_edges()}" if curved else "")
            + (f" localrand={graphs['localrand'][0].number_of_edges()}"
               if "localrand" in graphs else "") + ")")
        x0 = np.random.default_rng([seed, side]).random(n)
        x0 = x0 - x0.mean()
        for fi, fam in enumerate(fams):
            if fam not in graphs:
                continue
            G, note, tal = graphs[fam]
            md = int(max(d for _, d in G.degree()))
            ne = G.number_of_edges()
            if fam in need_stats:
                t1 = time.time()
                st = graph_stats(G, np.random.default_rng([seed, side, fi]))
                graph_rows.append(dict(side=side, seed=seed, family=fam,
                                       moves_add=(tal or {}).get("add", -1),
                                       moves_rm=(tal or {}).get("rm", -1),
                                       build_secs=build_secs, note=note, **st))
                log(f"  side={side} seed={seed} {fam:9s} stats: lam2={st['lambda2_norm']} "
                    f"max_deg={st['max_deg']}"
                    + (f" adds={tal.get('add')}" if tal else "")
                    + f" ({round(time.time() - t1, 1)}s)")
            conn = nx.is_connected(G)
            Acsr = to_csr(G) if conn else None
            for algo in ALGOS:
                if (fam, algo) not in need_runs:
                    continue
                if not conn:
                    run_rows.append(dict(side=side, n=n, seed=seed, family=fam,
                                         algo=algo, rounds_eps3=maxr, conv_eps3=0,
                                         rounds_eps6=maxr, conv_eps6=0, maxr=maxr,
                                         alpha=ALPHA, secs=0, max_deg=md, edges=ne,
                                         cost3_load=maxr * md, cost6_load=maxr * md,
                                         note="DISCONNECTED"))
                    continue
                t1 = time.time()
                hit = run_algo(algo, Acsr, x0, maxr, EPS_LIST)
                r3 = hit[1e-3] or maxr
                r6 = hit[1e-6] or maxr
                run_rows.append(dict(side=side, n=n, seed=seed, family=fam, algo=algo,
                                     rounds_eps3=r3, conv_eps3=int(bool(hit[1e-3])),
                                     rounds_eps6=r6, conv_eps6=int(bool(hit[1e-6])),
                                     maxr=maxr, alpha=ALPHA,
                                     secs=round(time.time() - t1, 3),
                                     max_deg=md, edges=ne,
                                     cost3_load=r3 * md, cost6_load=r6 * md,
                                     note=note))
                log(f"  side={side} seed={seed} {fam:9s} {algo:7s} "
                    f"eps3={hit[1e-3] or 'CENSORED'} eps6={hit[1e-6] or 'CENSORED'}")
    except Exception as ex:  # noqa: BLE001
        log(f"  side={side} seed={seed} WORKER EXCEPTION {type(ex).__name__}: {ex}")
    return graph_rows, run_rows


# -------------------------------------------------------------------------------- sweep
def sweep(args):
    os.makedirs(args.outdir, exist_ok=True)
    runs_path = os.path.join(args.outdir, args.runs_name)
    graphs_path = os.path.join(args.outdir, args.graphs_name)
    cfg_path = os.path.join(args.outdir, f"decisive_config_{DATE}.json")
    if not os.path.exists(cfg_path):
        with open(cfg_path, "w") as f:
            json.dump(dict(sides=args.sides, seeds=args.seeds,
                           maxr_default=DEFAULT_MAXR, maxr_by_side=MAXR_BY_SIDE,
                           maxr_override=args.maxr, alpha=ALPHA, eps_list=EPS_LIST,
                           families_p1=FAMILIES_P1, families_p2=FAMILIES_P2,
                           algos=ALGOS, delta_samples=DELTA_SAMPLES,
                           coevolve_rounds=14, traffic_per_225=1200,
                           localrand_seed_offset=1_000_000, workers=args.workers,
                           preregistration="v2: Q-LOCAL L1/L2/L3+B1, Q-SCALE S1/S2/S3, "
                                           "Q-COST C1..C4, V0/V1 -- module docstring",
                           started=time.strftime("%Y-%m-%d %H:%M:%S")), f, indent=2)
    done_runs = load_done(runs_path, ("side", "seed", "family", "algo"))
    done_graphs = load_done(graphs_path, ("side", "seed", "family"))
    total = sum(len(families_for(s)) * len(ALGOS) for s in args.sides) * len(args.seeds)
    log(f"decisive sweep v2: sides={args.sides} seeds={args.seeds} "
        f"workers={args.workers} -> {total} run cells ({len(done_runs)} done, resuming)")

    phase1 = [s for s in args.sides if s not in PHASE2_SIDES]
    for side in args.sides:
        tasks = []
        for seed in args.seeds:
            need_runs = set((f_, a_) for f_ in families_for(side) for a_ in ALGOS
                            if (str(side), str(seed), f_, a_) not in done_runs)
            need_stats = set(f_ for f_ in families_for(side)
                             if (str(side), str(seed), f_) not in done_graphs)
            if need_runs or need_stats:
                tasks.append((side, seed, maxr_for(side, args.maxr),
                              need_runs, need_stats))
        if not tasks:
            log(f"side={side}: complete, skip")
        else:
            log(f"side={side}: {len(tasks)} seed-tasks (maxr={maxr_for(side, args.maxr)})")
            if args.serial or args.workers <= 1:
                results = map(work_cell, tasks)
                for graph_rows, run_rows in results:
                    for row in graph_rows:
                        append_row(graphs_path, GRAPHS_FIELDS, row)
                    for row in run_rows:
                        append_row(runs_path, RUNS_FIELDS, row)
            else:
                with mp.Pool(processes=min(args.workers, len(tasks))) as pool:
                    for graph_rows, run_rows in pool.imap_unordered(work_cell, tasks):
                        for row in graph_rows:
                            append_row(graphs_path, GRAPHS_FIELDS, row)
                        for row in run_rows:
                            append_row(runs_path, RUNS_FIELDS, row)
        if phase1 and side == phase1[-1]:
            log("PHASE-1 COMPLETE (sides " + ",".join(map(str, phase1))
                + " done -- Q-LOCAL answerable; run --analyze)")
    log("SWEEP COMPLETE")


# ----------------------------------------------------------------------------- analysis
def geo_mean_ci(vals, rng, nboot=NBOOT):
    logs = np.log(np.asarray(vals, dtype=float))
    gm = float(np.exp(logs.mean()))
    if len(logs) < 2:
        return gm, gm, gm
    idx = rng.integers(0, len(logs), size=(nboot, len(logs)))
    bm = np.exp(logs[idx].mean(axis=1))
    return gm, float(np.percentile(bm, 2.5)), float(np.percentile(bm, 97.5))


def load_csv(path):
    if not os.path.exists(path):
        return []
    with open(path) as f:
        return list(csv.DictReader(f))


def analyze(args):
    runs_path = os.path.join(args.outdir, args.runs_name)
    graphs_path = os.path.join(args.outdir, args.graphs_name)
    runs = load_csv(runs_path)
    if not runs:
        log(f"no runs at {runs_path}")
        return 2
    graphs = load_csv(graphs_path)
    rng = np.random.default_rng(0)
    R = {(r["side"], r["seed"], r["family"], r["algo"]): r for r in runs}
    Gst = {(g["side"], g["seed"], g["family"]): g for g in graphs}
    sides = sorted({int(r["side"]) for r in runs})
    seeds = sorted({int(r["seed"]) for r in runs})
    halt = []

    def cell(side, seed, fam, algo):
        return R.get((str(side), str(seed), fam, algo))

    def paired(side, algo, fam_num, fam_den, tag="eps3", field="rounds"):
        """ratio field(fam_num)/field(fam_den). Sweep convention: censored
        numerator kept at maxr (conservative lower bound on the ratio),
        censored denominator excluded."""
        vals = []
        for seed in seeds:
            a, b = cell(side, seed, fam_num, algo), cell(side, seed, fam_den, algo)
            if not a or not b or a["note"] == "DISCONNECTED" or b["note"] == "DISCONNECTED":
                continue
            if not int(b[f"conv_{tag}"]):
                continue
            fa = f"{field}_{tag}" if field == "rounds" else f"cost{tag[-1]}_load"
            vals.append(int(a[fa]) / int(b[fa]))
        return vals

    print("=" * 88)
    print(f"DECISIVE EXPERIMENT ANALYSIS v2 ({DATE}) -- local-null + N=4096 + cost verdict")
    print(f"sides={sides} seeds={len(seeds)} ({min(seeds)}..{max(seeds)})")
    print("=" * 88)

    # ---- V0 reproduction gate vs the robustness sweep ------------------------------
    robust_runs = load_csv(os.path.join(args.outdir, "results_robustness",
                                        "robust_runs.csv"))
    robust_graphs = load_csv(os.path.join(args.outdir, "results_robustness",
                                          "robust_graphs.csv"))
    if robust_runs:
        old = {(r["side"], r["seed"], r["family"], r["algo"]): r for r in robust_runs}
        mism, matched = [], 0
        for k, r in R.items():
            if k in old and k[2] in ("flat", "curved") and int(k[0]) <= 32:
                if (old[k]["rounds_eps3"], old[k]["rounds_eps6"]) == \
                   (r["rounds_eps3"], r["rounds_eps6"]):
                    matched += 1
                else:
                    mism.append((k, old[k]["rounds_eps3"], r["rounds_eps3"]))
        if matched + len(mism) == 0:
            print("\nV0 REPRODUCTION GATE: no overlapping (side<=32, flat/curved) cells "
                  "yet -- gate skipped")
        else:
            v0 = "PASS" if not mism else "FAIL"
            if mism:
                halt.append(f"V0 reproduction: {len(mism)} mismatches, {matched} matches")
            print(f"\nV0 REPRODUCTION GATE vs robust_runs.csv (flat/curved incl. gossip, "
                  f"sides<=32): {matched} exact, {len(mism)} MISMATCH -- {v0}"
                  + (f" e.g. {mism[:3]}" if mism else ""))
    else:
        print("\nV0 REPRODUCTION GATE: robust_runs.csv not found -- SKIPPED (flag if on box)")

    # ---- V1 validity (R0 discipline) ------------------------------------------------
    disconnected = [k for k, g in Gst.items() if g["connected"] == "0"]
    max_drift = 0.0
    for side in sides:
        for seed in seeds:
            gf, gc = Gst.get((str(side), str(seed), "flat")), \
                Gst.get((str(side), str(seed), "curved"))
            if gf and gc:
                max_drift = max(max_drift, abs(int(gc["edges"]) - int(gf["edges"]))
                                / int(gf["edges"]))
    nonflat = [r for r in runs if r["family"] != "flat" and r["note"] != "DISCONNECTED"]
    cens6 = sum(1 for r in nonflat if not int(r["conv_eps6"])) / max(len(nonflat), 1)
    cens3 = sum(1 for r in nonflat if not int(r["conv_eps3"])) / max(len(nonflat), 1)
    v1_ok = not disconnected and max_drift <= 0.05 and cens6 <= 0.10
    if not v1_ok:
        halt.append(f"V1: disconnected={len(disconnected)} drift={max_drift:.1%} "
                    f"cens6={cens6:.1%}")
    print(f"V1 VALIDITY: {'PASS' if v1_ok else 'FAIL'} -- connected "
          f"{len(Gst) - len(disconnected)}/{len(Gst)}, edge drift {max_drift:.2%} "
          f"(<=5%), censored eps6 {cens6:.1%} (<=10%), eps3 {cens3:.1%}")

    # ---- speedup vs flat table (rounds) ----------------------------------------------
    all_fams = ["curved", "localrand", "shuffled", "rreg4"]
    stats = {}
    print(f"\n--- ROUNDS speedup vs FLAT (rounds_flat / rounds_family), eps3 ---")
    print(f"{'algo':8s} {'family':10s} " + " ".join(f"{'N=' + str(s * s):>22s}" for s in sides))
    for algo in ALGOS:
        for fam in all_fams:
            cells_txt = []
            for side in sides:
                vals = paired(side, algo, "flat", fam)
                if vals:
                    gm, lo, hi = geo_mean_ci(vals, rng)
                    stats[(side, algo, fam)] = (gm, lo, hi, len(vals))
                    cells_txt.append(f"{gm:7.2f}x [{lo:6.2f},{hi:7.2f}]")
                else:
                    cells_txt.append(f"{'--':>22s}")
            print(f"{algo:8s} {fam:10s} " + " ".join(f"{c:>22s}" for c in cells_txt))

    # ---- lambda2 + max_deg tables ------------------------------------------------------
    if graphs:
        for label, key, fmt in (("mean lambda2 (normalized Laplacian)", "lambda2_norm",
                                 "14.6f"), ("mean max_deg", "max_deg", "14.1f")):
            print(f"\n--- {label} per family ---")
            print(f"{'family':10s} " + " ".join(f"{'N=' + str(s * s):>14s}" for s in sides))
            for fam in ["flat"] + all_fams:
                cells_txt = []
                for side in sides:
                    ls = [float(g[key]) for (sd, se, fm), g in Gst.items()
                          if sd == str(side) and fm == fam and float(g[key]) > 0]
                    cells_txt.append(f"{np.mean(ls):{fmt}}" if ls else f"{'--':>14s}")
                print(f"{fam:10s} " + " ".join(cells_txt))

    # ==== Q-LOCAL: pre-registered attribution verdict ===================================
    print("\n" + "=" * 88)
    print("Q-LOCAL: paired R = rounds(localrand)/rounds(curved), eps3 (R>1: curved faster)")
    print("         paired L = lambda2(curved)/lambda2(localrand)   (L>1: curved wider gap)")
    decisive_side = max((s for s in sides if s <= 32), default=None)
    lverdict, l2verdict = {}, {}
    for side in sides:
        # paired per-seed lambda2 ratio
        lvals = []
        for se in seeds:
            gc = Gst.get((str(side), str(se), "curved"))
            gl = Gst.get((str(side), str(se), "localrand"))
            if gc and gl and float(gc["lambda2_norm"]) > 0 and float(gl["lambda2_norm"]) > 0:
                lvals.append(float(gc["lambda2_norm"]) / float(gl["lambda2_norm"]))
        if lvals:
            l2verdict[side] = geo_mean_ci(lvals, rng)
        for algo in MATCHED_ALGOS:
            vals = paired(side, algo, "localrand", "curved")
            if not vals:
                continue
            gm, lo, hi = geo_mean_ci(vals, rng)
            lverdict[(algo, side)] = (gm, lo, hi)
            ltxt = ""
            if side in l2verdict and algo == "heat":
                lg, ll, lh = l2verdict[side]
                ltxt = f"   L={lg:.2f} [{ll:.2f},{lh:.2f}]"
            print(f"  {algo}/N={side * side}: R={gm:.2f} [{lo:.2f},{hi:.2f}] "
                  f"(n={len(vals)}){ltxt}")

    # B1 budget-starvation alibi (turnover from graphs CSV)
    b1 = {}
    for side in sides:
        ac = [int(g["moves_add"]) for (sd, se, fm), g in Gst.items()
              if sd == str(side) and fm == "curved" and int(g.get("moves_add", -1)) >= 0]
        al = [int(g["moves_add"]) for (sd, se, fm), g in Gst.items()
              if sd == str(side) and fm == "localrand" and int(g.get("moves_add", -1)) >= 0]
        if ac and al:
            b1[side] = np.mean(al) / np.mean(ac)
            print(f"  B1 turnover N={side * side}: localrand/curved adds = "
                  f"{np.mean(al):.0f}/{np.mean(ac):.0f} = {b1[side]:.0%} "
                  f"({'ok >= 60%' if b1[side] >= 0.6 else 'ALIBI ACTIVE < 60%'})")

    def qlocal_verdict(side):
        if not all((a, side) in lverdict for a in MATCHED_ALGOS):
            return None
        heat_gm = lverdict[("heat", side)][0]
        lo_ok = all(lverdict[(a, side)][1] > 1.0 for a in MATCHED_ALGOS)
        hi_lt1 = all(lverdict[(a, side)][2] < 1.0 for a in MATCHED_ALGOS)
        lam_tie = side in l2verdict and l2verdict[side][1] <= 1.0
        if lo_ok and heat_gm >= 1.5:
            return ("L2", "THE COEVOLUTION LOOP DOES REAL WORK -- curved beats the "
                          "local-random null (traffic signal is load-bearing)")
        if hi_lt1:
            return ("L3", "TRAFFIC SELECTION IS ACTIVELY HARMFUL -- local-random "
                          "rewiring beats the coevolved graph")
        if lam_tie:
            if b1.get(side, 1.0) < 0.6:
                return ("B1", "rounds+lambda2 tie BUT turnover < 60% -- collapse may "
                              "NOT be declared; run the budget-matched follow-up")
            return ("L1", "CLAIM COLLAPSES to 'any local rewiring delocalizes' -- "
                          "null matches curved on rounds AND lambda2")
        return ("MIXED", "rounds tie but lambda2 separates (or data incomplete) -- "
                         "no collapse declared; investigate readout vs mechanism")

    if decisive_side:
        v = qlocal_verdict(decisive_side)
        if v:
            print(f"\n  PRE-REGISTERED Q-LOCAL VERDICT (N={decisive_side ** 2}): "
                  f"[{v[0]}] {v[1]}")
        if 64 in sides:
            v64 = qlocal_verdict(64)
            if v and v64:
                agree = v[0] == v64[0]
                print(f"  CONSISTENCY CHECK N=4096: [{v64[0]}] "
                      + ("agrees -- verdict stands" if agree else
                         f"DISAGREES ({v[0]} vs {v64[0]}) -- N=4096 GOVERNS (registered)"))

    # ==== Q-SCALE: N=4096 probe ==========================================================
    if 64 in sides:
        print("\n" + "=" * 88)
        print("Q-SCALE: N=4096 probe")
        st = stats.get((64, "heat", "curved"))
        if st:
            gm = st[0]
            kill = gm < 14.2
            print(f"  S1 heat curved-vs-flat @4096: {gm:.2f}x [{st[1]:.2f},{st[2]:.2f}] "
                  f"(predict ~38x [26,55]; continues iff >=28.5; KILL iff <14.2): "
                  + ("KILLED -- growth story dies" if kill else
                     ("CONTINUES" if gm >= 28.5 else "STALLS (survives kill, sub-trend)")))
            # 4-point log-log exponent
            xs = [math.log(s * s) for s in sides if (s, "heat", "curved") in stats]
            ys = [math.log(stats[(s, "heat", "curved")][0]) for s in sides
                  if (s, "heat", "curved") in stats]
            if len(xs) >= 3:
                slope = float(np.polyfit(xs, ys, 1)[0])
                print(f"     log-log fit exponent over {len(xs)} sizes: {slope:.3f} "
                      f"(registered band [0.35, 0.65] for the '~N^0.5' wording): "
                      f"{'IN BAND' if 0.35 <= slope <= 0.65 else 'OUT OF BAND -- reword'}")
        stp = stats.get((64, "pushsum", "curved"))
        if stp:
            print(f"     pushsum curved-vs-flat @4096: {stp[0]:.2f}x [{stp[1]:.2f},"
                  f"{stp[2]:.2f}] (predict ~31x [20,48])")
        vals = paired(64, "heat", "shuffled", "curved")
        if vals:
            gm, lo, hi = geo_mean_ci(vals, rng)
            print(f"  S2 heat shuffled/curved @4096: {gm:.2f} [{lo:.2f},{hi:.2f}] "
                  f"(predict ~0.35 [0.22,0.48]; widens iff CI-hi < 0.52): "
                  f"{'WIDENS' if hi < 0.52 else 'DOES NOT WIDEN'}")
        sg = stats.get((64, "gossip", "curved"))
        if sg:
            print(f"  S3 gossip curved-vs-flat @4096: {sg[0]:.2f}x [{sg[1]:.2f},{sg[2]:.2f}] "
                  f"(predict <1, 0.25-0.55): mismatch penalty "
                  f"{'persists' if sg[2] < 1 else 'DOES NOT persist'}")

    # ==== Q-COST: priced verdict =========================================================
    print("\n" + "=" * 88)
    print("Q-COST: price-A = rounds x 2|E| (total work); "
          "price-B = rounds x max_deg (port-limited)")
    print("        speedup vs flat under each price (>1 = family wins), eps3\n")

    def paired_cost(rows_R, rows_G, side, algo, fam, price):
        vals = []
        Rmap = {(r["side"], r["seed"], r["family"], r["algo"]): r for r in rows_R}
        Gmap = {(g["side"], g["seed"], g["family"]): g for g in rows_G}
        for se in [str(s) for s in seeds]:
            a = Rmap.get((str(side), se, "flat", algo))
            b = Rmap.get((str(side), se, fam, algo))
            ga, gb = Gmap.get((str(side), se, "flat")), Gmap.get((str(side), se, fam))
            if not (a and b and ga and gb) or not int(b["conv_eps3"]):
                continue
            if price == "B":
                num = int(a["rounds_eps3"]) * int(ga["max_deg"])
                den = int(b["rounds_eps3"]) * int(gb["max_deg"])
            else:
                num = int(a["rounds_eps3"]) * int(ga["edges"])
                den = int(b["rounds_eps3"]) * int(gb["edges"])
            vals.append(num / den)
        return vals

    cost_stats = {}
    for price in ("A", "B"):
        print(f"  --- price-{price} ---")
        print(f"  {'algo':8s} {'family':10s} "
              + " ".join(f"{'N=' + str(s * s):>22s}" for s in sides))
        for algo in ALGOS:
            for fam in all_fams:
                cells_txt = []
                for side in sides:
                    # native decisive rows first; robust CSVs for families not run
                    # at this side (shuffled/rreg4 at sides<=32) -- single-source
                    # pairing, never cross-dataset
                    vals = paired_cost(runs, graphs, side, algo, fam, price)
                    src = "d"
                    if not vals and robust_runs:
                        vals = paired_cost(robust_runs, robust_graphs, side, algo,
                                           fam, price)
                        src = "r"
                    if vals:
                        gm, lo, hi = geo_mean_ci(vals, rng)
                        cost_stats[(price, side, algo, fam)] = (gm, lo, hi)
                        cells_txt.append(f"{gm:7.2f}x [{lo:5.2f},{hi:6.2f}]{src}")
                    else:
                        cells_txt.append(f"{'--':>22s}")
                print(f"  {algo:8s} {fam:10s} " + " ".join(f"{c:>22s}" for c in cells_txt))
        print("  (d = decisive rows, r = joined from robust_*.csv -- same builders/seeds)")

    # C1 replication gate
    c1_ok = True
    for algo in MATCHED_ALGOS:
        for side in [s for s in sides if s <= 32]:
            cs = cost_stats.get(("B", side, algo, "curved"))
            if cs and cs[0] >= 1.0:
                c1_ok = False
                halt.append(f"C1: price-B {algo} curved N={side * side} gm={cs[0]:.2f} "
                            f">= 1 -- ada's flip did NOT replicate; reconcile code")
    print(f"\n  C1 REPLICATION (ada's flip, disclosed): "
          f"{'PASS -- flip reproduces' if c1_ok else 'FAIL -- HALT'}")
    # C2 the task's >3x survival question
    c2_cells = [cost_stats[("B", s, "heat", "curved")][0] for s in sides
                if ("B", s, "heat", "curved") in cost_stats]
    surv = bool(c2_cells) and all(v >= 3.0 for v in c2_cells)
    print(f"  C2 '>3x cost-adjusted survival' (registered expectation: FAIL): "
          + ("no data" if not c2_cells else
             "SURVIVES >3x (unexpected -- audit the join)" if surv else "FAILS"))
    cb64 = cost_stats.get(("B", 64, "heat", "curved"))
    if cb64:
        print(f"     BLIND cell price-B heat curved @4096: {cb64[0]:.2f}x "
              f"(predict ~0.22 [0.12,0.35]; trend-continues iff < 0.29): "
              f"{'CONTINUES' if cb64[0] < 0.29 else 'BREAKS TREND'}")
    # C3 anchor
    for side in sides:
        rr_r = stats.get((side, "heat", "rreg4"))
        rr_c = cost_stats.get(("B", side, "heat", "rreg4"))
        if rr_r and rr_c and abs(math.log(rr_c[0] / rr_r[0])) > 0.05:
            halt.append(f"C3 anchor broken: rreg4 price-B {rr_c[0]:.2f} != rounds "
                        f"{rr_r[0]:.2f} at N={side * side} (max_deg 4=4 -- join bug)")
    print(f"  C3 rreg4 anchor (price-B == rounds ratio): "
          f"{'PASS' if not any('C3' in h for h in halt) else 'FAIL -- ' + str(halt)}")

    # ---- mechanism: gap governs (pooled incl. localrand) --------------------------------
    if graphs:
        print()
        for algo in MATCHED_ALGOS:
            xs, ys = [], []
            for r in runs:
                if r["algo"] != algo or not int(r["conv_eps3"]):
                    continue
                g = Gst.get((r["side"], r["seed"], r["family"]))
                if not g or float(g["lambda2_norm"]) <= 0:
                    continue
                xs.append(math.log(int(r["rounds_eps3"])))
                ys.append(math.log(float(g["lambda2_norm"])))
            if len(xs) >= 10:
                rho = float(spearmanr(xs, ys).statistic)
                print(f"  R4-style gap-governs ({algo}): Spearman rho(log rounds, "
                      f"log lambda2) = {rho:.3f} ({len(xs)} runs, localrand included)")

    # ---- raw per-seed dump (heat, eps3) -------------------------------------------------
    print("\n--- RAW per-seed rounds (heat, eps3) / lambda2 ---")
    for side in sides:
        hdr_fams = [f for f in ["flat", "curved", "localrand", "shuffled", "rreg4"]
                    if any(cell(side, se, f, "heat") for se in seeds)]
        print(f"  N={side * side}: seed | " + " | ".join(f"{f} r/l2" for f in hdr_fams))
        for seed in seeds:
            parts = []
            for f in hdr_fams:
                c = cell(side, seed, f, "heat")
                g = Gst.get((str(side), str(seed), f))
                if c:
                    parts.append(f"{c['rounds_eps3']}/"
                                 + (f"{float(g['lambda2_norm']):.5f}" if g else "?"))
                else:
                    parts.append("--")
            print(f"    {seed}: " + " | ".join(parts))

    if halt:
        print("\n" + "!" * 88)
        print("HALT -- validity/replication gates failed; results NOT interpretable:")
        for h in halt:
            print(f"  {h}")
        return 1
    print("\nAll validity gates passed; pre-registered verdicts above are final.")
    return 0


# ------------------------------------------------------------------------------ selftest
def selftest():
    failures = []

    def check(name, ok, detail=""):
        print(f"  [{'ok' if ok else 'FAIL'}] {name} {detail}", flush=True)
        if not ok:
            failures.append(name)

    G = nx.convert_node_labels_to_integers(nx.grid_2d_graph(6, 6))
    G.add_edge(0, 35)
    A = to_csr(G)
    d = np.asarray(A.sum(axis=1)).ravel()
    rng = np.random.default_rng(1)
    x = rng.random(G.number_of_nodes())
    x = x - x.mean()

    # 1) heat step == original diffuse_rounds update
    Adense = np.asarray(A.todense())
    Pref = Adense / np.where(d > 0, d, 1)[:, None]
    xr = x.copy()
    for _ in range(50):
        xr = (1 - ALPHA) * xr + ALPHA * (Pref @ xr)
    P = sp.diags(1.0 / np.where(d > 0, d, 1.0)) @ A
    xs_ = x.copy()
    for _ in range(50):
        xs_ = (1 - ALPHA) * xs_ + ALPHA * (P @ xs_)
    check("heat == original update", np.max(np.abs(xs_ - xr)) < 1e-10)

    # 2) metropolis matrix == original per-node loop (compute_on_curvature.py)
    deg = {i: G.degree(i) for i in G}
    ref = x.copy()
    for i in G:
        for j in G[i]:
            ref[i] += (1.0 / (1 + max(deg[i], deg[j]))) * (x[j] - x[i])
    W = metropolis_matrix(A, d)
    check("metropolis == original loop", np.max(np.abs(W @ x - ref)) < 1e-12,
          f"maxerr={np.max(np.abs(W @ x - ref)):.2e}")

    # 3) push-sum invariants
    B = pushsum_matrix(A, d)
    check("pushsum column-stochastic",
          np.max(np.abs(np.asarray(B.sum(axis=0)).ravel() - 1)) < 1e-12)
    y0 = rng.random(G.number_of_nodes()) * 5 + 2
    s, w = y0.copy(), np.ones(G.number_of_nodes())
    for _ in range(3000):
        s, w = B @ s, B @ w
    check("pushsum -> true mean", np.max(np.abs(s / w - y0.mean())) < 1e-9)

    # 4) rounds monotone in eps (heat + gossip)
    hit = run_algo("heat", A, x, 5000, EPS_LIST)
    check("heat eps6 rounds >= eps3 rounds", hit[1e-6] >= hit[1e-3] > 0,
          f"eps3={hit[1e-3]} eps6={hit[1e-6]}")
    hitg = run_algo("gossip", A, x, 20000, EPS_LIST)
    check("gossip converges + monotone", hitg[1e-6] >= hitg[1e-3] > 0,
          f"eps3={hitg[1e-3]} eps6={hitg[1e-6]}")

    # 5) coevolve determinism / budget / connectivity + tally does not perturb rng
    flat15 = build_flat(15)
    c1 = coevolve(flat15, random.Random(30))
    tal = {}
    c2 = coevolve(flat15, random.Random(30), tally=tal)
    check("coevolve deterministic per seed (tally inert)",
          set(map(tuple, map(sorted, c1.edges()))) == set(map(tuple, map(sorted, c2.edges()))))
    check("coevolve tally counted", tal.get("add", 0) > 50 and tal.get("rm", 0) > 50,
          f"adds={tal.get('add')} rms={tal.get('rm')}")
    drift = abs(c1.number_of_edges() - flat15.number_of_edges()) / flat15.number_of_edges()
    check("coevolve edge drift <= 5%", drift <= 0.05,
          f"{flat15.number_of_edges()} -> {c1.number_of_edges()} ({drift:.1%})")
    check("coevolve connected", nx.is_connected(c1))

    # 6) localrand: THE NULL -- determinism, tally inert, budget, connectivity, rewires
    l1 = build_localrand(flat15, random.Random(1_000_030))
    tal_l = {}
    l2 = build_localrand(flat15, random.Random(1_000_030), tally=tal_l)
    check("localrand deterministic per seed (tally inert)",
          set(map(tuple, map(sorted, l1.edges()))) == set(map(tuple, map(sorted, l2.edges()))))
    check("localrand tally counted", tal_l.get("add", 0) > 30,
          f"adds={tal_l.get('add')} rms={tal_l.get('rm')}")
    ldrift = abs(l1.number_of_edges() - flat15.number_of_edges()) / flat15.number_of_edges()
    check("localrand edge drift <= 5%", ldrift <= 0.05,
          f"{flat15.number_of_edges()} -> {l1.number_of_edges()} ({ldrift:.1%})")
    check("localrand connected", nx.is_connected(l1))
    check("localrand differs from flat", set(map(tuple, map(sorted, l1.edges())))
          != set(map(tuple, map(sorted, flat15.edges()))))
    check("localrand differs from curved", set(map(tuple, map(sorted, l1.edges())))
          != set(map(tuple, map(sorted, c1.edges()))))
    nrewired = len(set(map(tuple, map(sorted, l1.edges())))
                   - set(map(tuple, map(sorted, flat15.edges()))))
    ncrewired = len(set(map(tuple, map(sorted, c1.edges())))
                    - set(map(tuple, map(sorted, flat15.edges()))))
    check("localrand rewiring volume ~ coevolve (same budget)",
          0.4 <= nrewired / max(ncrewired, 1) <= 2.5,
          f"new edges localrand={nrewired} coevolve={ncrewired}")

    # 7) shuffled preserves degree sequence + connectivity
    sh, note = build_shuffled(c1, 30)
    check("shuffled degree sequence preserved",
          sorted(dict(c1.degree()).values()) == sorted(dict(sh.degree()).values()),
          f"({note})")
    check("shuffled connected", nx.is_connected(sh))

    # 8) lambda2 dense == networkx; sparse path == dense path
    st = graph_stats(G, np.random.default_rng(2), delta_samples=500)
    Lnx = nx.normalized_laplacian_matrix(G).todense()
    lam2_ref = float(np.sort(np.linalg.eigvalsh(np.asarray(Lnx)))[1])
    check("lambda2 dense == networkx", abs(st["lambda2_norm"] - lam2_ref) < 1e-6,
          f"{st['lambda2_norm']:.6f} vs {lam2_ref:.6f}")
    global DENSE_LAMBDA2_MAX_N
    g12 = build_flat(12)
    A12 = to_csr(g12)
    dense_v = lambda2_norm(A12, 144)
    saved = DENSE_LAMBDA2_MAX_N
    DENSE_LAMBDA2_MAX_N = 10          # force the sparse eigsh path
    sparse_v = lambda2_norm(A12, 144)
    DENSE_LAMBDA2_MAX_N = saved
    check("lambda2 sparse(eigsh) == dense(eigh)", abs(dense_v - sparse_v) < 1e-8,
          f"{dense_v:.10f} vs {sparse_v:.10f}")
    lr_l = lambda2_norm(to_csr(l1), 225)  # non-grid graph through the same path
    check("lambda2 finite on localrand", 0 < lr_l < 2, f"{lr_l:.6f}")

    # 9) landmark reproduction: flat=689 curved=89 (robust_runs.csv, seed 30)
    x15 = np.random.default_rng([30, 15]).random(225)
    x15 = x15 - x15.mean()
    hf = run_algo("heat", to_csr(flat15), x15, 20000, [1e-3])
    hc = run_algo("heat", to_csr(c1), x15, 20000, [1e-3])
    check("landmark direction: curved faster than flat",
          0 < hc[1e-3] < hf[1e-3], f"flat={hf[1e-3]} curved={hc[1e-3]}")
    check("landmark reproduction: flat=689 curved=89 (robust_runs.csv seed30)",
          hf[1e-3] == 689 and hc[1e-3] == 89, f"flat={hf[1e-3]} curved={hc[1e-3]}")

    print(f"\nselftest: {'ALL PASS' if not failures else 'FAILURES: ' + ', '.join(failures)}",
          flush=True)
    return 0 if not failures else 1


# ---------------------------------------------------------------------------------- main
def parse_int_list(s):
    out = []
    for part in s.split(","):
        part = part.strip()
        if "-" in part and not part.startswith("-"):
            a, b = part.split("-")
            out.extend(range(int(a), int(b) + 1))
        elif part:
            out.append(int(part))
    return out


def main():
    ap = argparse.ArgumentParser(
        description="CDC-lab decisive experiment v2: local-null + N=4096 + cost verdict")
    ap.add_argument("--sides", type=str,
                    default=",".join(map(str, PHASE1_SIDES + PHASE2_SIDES)))
    ap.add_argument("--seeds", type=str, default=f"{DEFAULT_SEEDS[0]}-{DEFAULT_SEEDS[-1]}")
    ap.add_argument("--maxr", type=int, default=None,
                    help="override maxr for ALL sides (default: 40000, side 64: 200000)")
    ap.add_argument("--workers", type=int,
                    default=max(1, min(12, (os.cpu_count() or 4) - 2)))
    ap.add_argument("--serial", action="store_true")
    ap.add_argument("--outdir", type=str,
                    default=os.path.dirname(os.path.abspath(__file__)))
    ap.add_argument("--quick", action="store_true", help="smoke: side 10, seeds 30-31")
    ap.add_argument("--analyze", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()
    args.sides = sorted(parse_int_list(args.sides))
    args.seeds = parse_int_list(args.seeds)
    args.runs_name = f"decisive_results_{DATE}.csv"
    args.graphs_name = f"decisive_graphs_{DATE}.csv"
    if args.quick:
        args.sides, args.seeds, args.maxr = [10], [30, 31], 8000
        args.outdir = os.path.join(args.outdir, "quick_decisive")
    if args.selftest:
        sys.exit(selftest())
    if args.analyze:
        sys.exit(analyze(args))
    sweep(args)


if __name__ == "__main__":
    main()
