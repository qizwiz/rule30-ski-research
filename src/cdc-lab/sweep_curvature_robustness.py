#!/usr/bin/env python3
"""CDC-lab ROBUSTNESS SWEEP for the curvature-as-computation landmark.

Landmark under test (compute_matched.py, 2026-07-07): on a curved graph grown from a
flat 15x15 grid by local traffic-driven rewiring (edge budget ~held), the geometry-
MATCHED algorithm (lazy random-walk heat diffusion, x <- (1-a)x + a*P*x, P = D^-1 A)
reached consensus in 83 rounds vs 570 on the flat grid (6.9x), while naive Metropolis
gossip (hub-penalizing weights) showed no curved win -- the algo-geometry MISMATCH null.

DESIGN MATRIX (defaults):
  sizes     : side in {15, 22, 32}  -> N in {225, 484, 1024}   (>=3 scales)
  seeds     : 30..41 (12 seeds; includes the landmark's original seed 30)
  families  : flat      = side x side grid (the baseline geometry)
              curved    = coevolve(flat, seed)  -- the EXACT landmark construction,
                          traffic scaled proportional to N (1200 * N/225), rounds=14
              shuffled  = degree-preserving randomization of curved (connected double
                          edge swaps; same degree sequence, same edge count) -- tight
                          control: is the resource the SPECIFIC geometry or just the
                          degree sequence + non-local wiring?
              rreg4     = random 4-regular graph (expander reference, ~same edge budget)
  algorithms: heat      = lazy random-walk heat diffusion (the landmark algorithm)
              pushsum   = push-sum averaging (2nd geometry-matched algorithm; computes
                          the TRUE mean, closing the "degree-weighted mean is an easier
                          task on hubs" hole)
              gossip    = Metropolis-weight gossip (the naive/mismatched null)
  pairing   : one x0 per (side, seed), shared across ALL families and algorithms
              -> paired per-seed speedups.

METRICS:
  per run   : rounds-to-eps for eps in {1e-3, 1e-6} (single pass records both),
              convergence flags, wall seconds.  Residual = ||x - mean(x)||_2 / ||x0||_2
              (x0 centered); push-sum residual = ||s/w - true_mean||_2 / ||x0||_2.
  per graph : edges, degree stats, lambda2 of the NORMALIZED Laplacian (the quantity
              the matched algorithms are governed by), Gromov delta_max (4000 sampled
              quadruples), diameter, mean path length, delta/diam, connectivity.
  statistic : per (side, algo): geometric-mean paired speedup rounds(flat)/rounds(fam)
              with bootstrap (10k) 95% CI on log-speedup.

PASS/FAIL (pre-registered; "the landmark is robust" iff R0 and R1 and R2 all pass):
  R0 VALIDITY : all graphs connected; curved edge drift |E_curved - E_flat|/E_flat <= 5%
                per instance; <=10% of curved/control cells censored (non-converged at
                maxr). Censored FLAT runs are kept at rounds=maxr (conservative);
                censored non-flat runs are excluded and counted against R0.
  R1 CORE     : for BOTH matched algos (heat, pushsum), at EVERY size, at BOTH eps:
                geo-mean speedup(curved vs flat) >= 2.0 AND bootstrap CI lower bound
                > 1.5.  Scale trend: per-algo geo-mean speedup at the largest N >=
                0.75 x its value at the smallest N (no decay with scale; growth is
                the theory's prediction and is reported).
  R2 MISMATCH : at every size (eps=1e-3): gossip geo-mean speedup < 1.3 AND gossip CI
                upper bound < heat CI lower bound (the matched/mismatched contrast).
  R3 MECHANISM (characterization, wording-not-fatal): curved-vs-shuffled and
                curved-vs-rreg4 paired ratios with CIs.  Pre-registered readings:
                  - curved ~ shuffled (CI spans 1): resource = degree sequence +
                    delocalized wiring; headline must say "local coevolution buys
                    expander-grade mixing", not "curvature per se".
                  - curved > shuffled: the specific coevolved geometry adds on top.
                  - curved < shuffled: randomization beats the construction; drop the
                    curvature framing (curved>>flat may still stand).
  R4 MECHANISM: pooled Spearman rho(log rounds_eps3, log lambda2) <= -0.9 over all
                converged matched-algo runs ("the normalized-Laplacian gap governs").

OUTPUT (written INCREMENTALLY, flushed + fsynced per row; safe to kill and resume --
completed (side,seed,family,algo) cells are skipped on restart):
  <outdir>/robust_runs.csv    one row per (side, seed, family, algo)
  <outdir>/robust_graphs.csv  one row per (side, seed, family)
  <outdir>/robust_config.json sweep parameters (written once)

USAGE (box env: source ~/cdc-env/bin/activate ; needs numpy, networkx, scipy only):
  python robustness_sweep.py --selftest          # kernel unit checks (~seconds, no CSVs)
  python robustness_sweep.py --quick             # smoke sweep: side=10, 3 seeds, small maxr
  python robustness_sweep.py                     # full sweep (est. 30-90 min)
  python robustness_sweep.py --analyze           # verdict tables + R0..R4 + PASS/FAIL
"""

import argparse
import csv
import json
import math
import os
import random
import sys
import time

import numpy as np
import networkx as nx
import scipy.sparse as sp
from scipy.linalg import eigh
from scipy.sparse.csgraph import laplacian as csgraph_laplacian
from scipy.sparse.csgraph import shortest_path as csgraph_shortest_path
from scipy.stats import spearmanr

# ----------------------------------------------------------------------------- config
DEFAULT_SIDES = [15, 22, 32]
DEFAULT_SEEDS = list(range(30, 42))  # 12 seeds, includes landmark seed 30
DEFAULT_MAXR = 40000
ALPHA = 0.5                          # lazy-walk laziness, as in compute_matched.py
EPS_LIST = [1e-3, 1e-6]              # 1e-3 = landmark criterion; 1e-6 = robustness
EPS_TAG = {1e-3: "eps3", 1e-6: "eps6"}
FAMILIES = ["flat", "curved", "shuffled", "rreg4"]
MATCHED_ALGOS = ["heat", "pushsum"]
ALGOS = ["heat", "pushsum", "gossip"]
DELTA_SAMPLES = 4000
NBOOT = 10000

RUNS_FIELDS = ["side", "n", "seed", "family", "algo",
               "rounds_eps3", "conv_eps3", "rounds_eps6", "conv_eps6",
               "maxr", "alpha", "secs", "note"]
GRAPHS_FIELDS = ["side", "seed", "family", "nodes", "edges", "connected",
                 "mean_deg", "max_deg", "diam", "mean_path_len",
                 "gromov_delta_max", "delta_over_diam", "lambda2_norm",
                 "build_secs", "note"]


def log(msg):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


# ------------------------------------------------------------------------ graph builds
def build_flat(side):
    return nx.convert_node_labels_to_integers(nx.grid_2d_graph(side, side))


def coevolve(G, rng, rounds=14, traffic=None):
    """FAITHFUL copy of the landmark construction (compute_matched.py coevolve),
    with (1) an explicit seeded rng instead of the module-level one and (2) traffic
    scaled proportional to N so the local rule has the same sampling density at every
    scale (1200 pair-routes per round at N=225)."""
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
        for k in pr[:add]:
            if k not in set(map(lambda e: tuple(sorted(e)), nx.bridges(G))):
                G.remove_edge(*k)
    return G


def build_shuffled(curved, seed):
    """Degree-preserving randomization of the curved graph (connectivity kept).
    Same degree sequence, same edge count -- isolates 'specific geometry' from
    'degree sequence + delocalized wiring'."""
    E = curved.number_of_edges()
    try:
        H = curved.copy()
        nx.connected_double_edge_swap(H, nswap=4 * E, seed=seed)
        return H, "connected_double_edge_swap"
    except Exception as ex:  # noqa: BLE001 -- fall back to plain swaps + retries
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
    """Random 4-regular graph: expander reference with ~the grid's edge budget
    (2N vs the grid's 2N - 2*side)."""
    for k in range(5):
        H = nx.random_regular_graph(4, n, seed=seed + 1000 * k)
        if nx.is_connected(H):
            return H, f"rreg4_try{k}"
    return H, "RREG_DISCONNECTED"


# --------------------------------------------------------------------- linear operators
def to_csr(G):
    try:
        return sp.csr_matrix(nx.to_scipy_sparse_array(G, dtype=np.float64))
    except AttributeError:  # very old networkx
        return sp.csr_matrix(nx.to_scipy_sparse_matrix(G, dtype=np.float64))


def metropolis_matrix(A, d):
    """W = I + sum_edges w_ij (E_ij + E_ji - E_ii - E_jj), w_ij = 1/(1+max(d_i,d_j)).
    Exactly the per-node update loop in compute_on_curvature.py gossip_rounds."""
    C = sp.coo_matrix(A)
    w = 1.0 / (1.0 + np.maximum(d[C.row], d[C.col]))
    W = sp.coo_matrix((w, (C.row, C.col)), shape=A.shape).tocsr()
    rowsum = np.asarray(W.sum(axis=1)).ravel()
    return (W + sp.diags(1.0 - rowsum)).tocsr()


def pushsum_matrix(A, d):
    """Column-stochastic B over A+I: node j splits its mass equally over
    neighbors + self, B_ij = 1/(d_j + 1). Mass-conserving (1^T B = 1^T)."""
    n = A.shape[0]
    M = sp.coo_matrix(sp.csr_matrix(A) + sp.identity(n, format="csr"))
    vals = M.data * (1.0 / (d + 1.0))[M.col]
    return sp.coo_matrix((vals, (M.row, M.col)), shape=(n, n)).tocsr()


def run_algo(algo, A, x0, maxr, eps_list):
    """Run one algorithm; return {eps: first round with residual < eps, or 0 if never}."""
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
    L = csgraph_laplacian(sp.csr_matrix(A), normed=True)
    evals = eigh(np.asarray(L.todense()), eigvals_only=True, subset_by_index=[0, 1])
    out.update(diam=diam, mean_path_len=round(mean_l, 4),
               gromov_delta_max=float(best),
               delta_over_diam=round(float(best) / max(diam, 1), 4),
               lambda2_norm=round(float(evals[1]), 8))
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


# -------------------------------------------------------------------------------- sweep
def sweep(args):
    os.makedirs(args.outdir, exist_ok=True)
    runs_path = os.path.join(args.outdir, "robust_runs.csv")
    graphs_path = os.path.join(args.outdir, "robust_graphs.csv")
    cfg_path = os.path.join(args.outdir, "robust_config.json")
    if not os.path.exists(cfg_path):
        with open(cfg_path, "w") as f:
            json.dump(dict(sides=args.sides, seeds=args.seeds, maxr=args.maxr,
                           alpha=ALPHA, eps_list=EPS_LIST, families=FAMILIES,
                           algos=ALGOS, delta_samples=DELTA_SAMPLES,
                           coevolve_rounds=14, traffic_per_225=1200,
                           started=time.strftime("%Y-%m-%d %H:%M:%S")), f, indent=2)
    done_runs = load_done(runs_path, ("side", "seed", "family", "algo"))
    done_graphs = load_done(graphs_path, ("side", "seed", "family"))
    total = len(args.sides) * len(args.seeds) * len(FAMILIES) * len(ALGOS)
    log(f"sweep: sides={args.sides} seeds={args.seeds} maxr={args.maxr} "
        f"-> {total} run cells ({len(done_runs)} already done, resuming)")

    for side in args.sides:
        n = side * side
        flat = build_flat(side)
        for seed in args.seeds:
            need_runs = [(f_, a_) for f_ in FAMILIES for a_ in ALGOS
                         if (str(side), str(seed), f_, a_) not in done_runs]
            need_stats = [f_ for f_ in FAMILIES
                          if (str(side), str(seed), f_) not in done_graphs]
            if not need_runs and not need_stats:
                log(f"side={side} seed={seed}: complete, skip")
                continue
            t0 = time.time()
            curved = coevolve(flat, random.Random(seed))
            shuffled, shuf_note = build_shuffled(curved, seed)
            rreg, rreg_note = build_rreg4(n, seed)
            build_secs = round(time.time() - t0, 2)
            graphs = {"flat": (flat, ""), "curved": (curved, ""),
                      "shuffled": (shuffled, shuf_note), "rreg4": (rreg, rreg_note)}
            log(f"side={side} seed={seed}: built in {build_secs}s "
                f"(edges flat={flat.number_of_edges()} curved={curved.number_of_edges()})")
            # paired initial vector: same x0 for every family and algorithm
            x0 = np.random.default_rng([seed, side]).random(n)
            x0 = x0 - x0.mean()
            for fi, (fam, (G, note)) in enumerate(graphs.items()):
                if fam in need_stats:
                    st = graph_stats(G, np.random.default_rng([seed, side, fi]))
                    append_row(graphs_path, GRAPHS_FIELDS,
                               dict(side=side, seed=seed, family=fam,
                                    build_secs=build_secs, note=note, **st))
                conn = nx.is_connected(G)
                Acsr = to_csr(G) if conn else None
                for algo in ALGOS:
                    if (str(side), str(seed), fam, algo) in done_runs:
                        continue
                    if not conn:
                        append_row(runs_path, RUNS_FIELDS,
                                   dict(side=side, n=n, seed=seed, family=fam,
                                        algo=algo, rounds_eps3=args.maxr, conv_eps3=0,
                                        rounds_eps6=args.maxr, conv_eps6=0,
                                        maxr=args.maxr, alpha=ALPHA, secs=0,
                                        note="DISCONNECTED"))
                        continue
                    t1 = time.time()
                    hit = run_algo(algo, Acsr, x0, args.maxr, EPS_LIST)
                    append_row(runs_path, RUNS_FIELDS,
                               dict(side=side, n=n, seed=seed, family=fam, algo=algo,
                                    rounds_eps3=hit[1e-3] or args.maxr,
                                    conv_eps3=int(bool(hit[1e-3])),
                                    rounds_eps6=hit[1e-6] or args.maxr,
                                    conv_eps6=int(bool(hit[1e-6])),
                                    maxr=args.maxr, alpha=ALPHA,
                                    secs=round(time.time() - t1, 3), note=note))
                    log(f"  side={side} seed={seed} {fam:8s} {algo:7s} "
                        f"eps3={hit[1e-3] or 'CENSORED'} eps6={hit[1e-6] or 'CENSORED'}")
    log("sweep complete")


# ----------------------------------------------------------------------------- analysis
def geo_mean_ci(vals, rng, nboot=NBOOT):
    logs = np.log(np.asarray(vals, dtype=float))
    gm = float(np.exp(logs.mean()))
    if len(logs) < 2:
        return gm, gm, gm
    idx = rng.integers(0, len(logs), size=(nboot, len(logs)))
    bm = np.exp(logs[idx].mean(axis=1))
    return gm, float(np.percentile(bm, 2.5)), float(np.percentile(bm, 97.5))


def analyze(args):
    runs_path = os.path.join(args.outdir, "robust_runs.csv")
    graphs_path = os.path.join(args.outdir, "robust_graphs.csv")
    if not os.path.exists(runs_path):
        log(f"no runs at {runs_path}")
        return 2
    with open(runs_path) as f:
        runs = list(csv.DictReader(f))
    with open(graphs_path) as f:
        graphs = list(csv.DictReader(f))
    rng = np.random.default_rng(0)
    R = {(r["side"], r["seed"], r["family"], r["algo"]): r for r in runs}
    Gst = {(g["side"], g["seed"], g["family"]): g for g in graphs}
    sides = sorted({int(r["side"]) for r in runs})
    seeds = sorted({int(r["seed"]) for r in runs})

    def cell(side, seed, fam, algo):
        return R.get((str(side), str(seed), fam, algo))

    def paired(side, algo, fam_num, fam_den, tag):
        """speedup = rounds(fam_num)/rounds(fam_den); censored numerator kept at maxr
        (conservative when numerator is the slow baseline); censored denominator
        excluded."""
        vals, cens, excl = [], 0, 0
        for seed in seeds:
            a, b = cell(side, seed, fam_num, algo), cell(side, seed, fam_den, algo)
            if not a or not b or a["note"] == "DISCONNECTED" or b["note"] == "DISCONNECTED":
                excl += 1
                continue
            if not int(b[f"conv_{tag}"]):
                excl += 1
                continue
            if not int(a[f"conv_{tag}"]):
                cens += 1
            vals.append(int(a[f"rounds_{tag}"]) / int(b[f"rounds_{tag}"]))
        return vals, cens, excl

    print("=" * 88)
    print("ROBUSTNESS SWEEP ANALYSIS -- curvature-as-computation landmark")
    print(f"sides={sides}  seeds={len(seeds)} ({min(seeds)}..{max(seeds)})")
    print("=" * 88)

    # ---- R0 validity gates -------------------------------------------------------
    r0_ok, r0_msgs = True, []
    max_drift = 0.0
    for side in sides:
        for seed in seeds:
            gf = Gst.get((str(side), str(seed), "flat"))
            gc = Gst.get((str(side), str(seed), "curved"))
            if gf and gc:
                drift = abs(int(gc["edges"]) - int(gf["edges"])) / int(gf["edges"])
                max_drift = max(max_drift, drift)
    if max_drift > 0.05:
        r0_ok = False
        r0_msgs.append(f"FAIL edge budget: max curved-vs-flat drift {max_drift:.1%} > 5%")
    else:
        r0_msgs.append(f"ok edge budget: max drift {max_drift:.1%} <= 5%")
    disconnected = [k for k, g in Gst.items() if g["connected"] == "0"]
    if disconnected:
        r0_ok = False
        r0_msgs.append(f"FAIL connectivity: {len(disconnected)} disconnected graphs {disconnected[:5]}")
    else:
        r0_msgs.append("ok connectivity: all graphs connected")
    nonflat = [r for r in runs if r["family"] != "flat" and r["note"] != "DISCONNECTED"]
    cens_frac = (sum(1 for r in nonflat if not int(r["conv_eps6"])) / max(len(nonflat), 1))
    if cens_frac > 0.10:
        r0_ok = False
        r0_msgs.append(f"FAIL censoring: {cens_frac:.1%} of non-flat cells hit maxr > 10%")
    else:
        r0_msgs.append(f"ok censoring: {cens_frac:.1%} of non-flat cells hit maxr")

    # ---- speedup tables ----------------------------------------------------------
    stats = {}  # (side, algo, fam, tag) -> (gm, lo, hi, n, cens, excl)
    for tag in ("eps3", "eps6"):
        print(f"\n--- speedup vs FLAT (rounds_flat / rounds_family), eps tag {tag} ---")
        print(f"{'algo':8s} {'family':9s} " +
              " ".join(f"{'N=' + str(s * s):>22s}" for s in sides))
        for algo in ALGOS:
            for fam in ("curved", "shuffled", "rreg4"):
                cells_txt = []
                for side in sides:
                    vals, cens, excl = paired(side, algo, "flat", fam, tag)
                    if vals:
                        gm, lo, hi = geo_mean_ci(vals, rng)
                        stats[(side, algo, fam, tag)] = (gm, lo, hi, len(vals), cens, excl)
                        flag = "*" if cens else " "
                        cells_txt.append(f"{gm:6.2f}x [{lo:5.2f},{hi:6.2f}]{flag}")
                    else:
                        cells_txt.append(f"{'no data':>21s} ")
                print(f"{algo:8s} {fam:9s} " + " ".join(f"{c:>22s}" for c in cells_txt))
        print("  (* = includes censored flat runs at maxr: speedup is a LOWER bound)")

    # ---- R1 core landmark --------------------------------------------------------
    r1_ok, r1_msgs = True, []
    for algo in MATCHED_ALGOS:
        for tag in ("eps3", "eps6"):
            for side in sides:
                st = stats.get((side, algo, "curved", tag))
                if not st:
                    r1_ok = False
                    r1_msgs.append(f"FAIL {algo}/{tag}/N={side * side}: no data")
                    continue
                gm, lo, hi, k, cens, excl = st
                if not (gm >= 2.0 and lo > 1.5):
                    r1_ok = False
                    r1_msgs.append(f"FAIL {algo}/{tag}/N={side * side}: gm={gm:.2f} lo={lo:.2f} "
                                   f"(need gm>=2.0, lo>1.5)")
        st_small = stats.get((sides[0], algo, "curved", "eps3"))
        st_large = stats.get((sides[-1], algo, "curved", "eps3"))
        if st_small and st_large:
            if st_large[0] < 0.75 * st_small[0]:
                r1_ok = False
                r1_msgs.append(f"FAIL {algo} scale trend: gm {st_small[0]:.2f} -> {st_large[0]:.2f} "
                               f"(decays > 25% with N)")
            else:
                grow = "GROWS" if st_large[0] > st_small[0] else "holds"
                r1_msgs.append(f"ok {algo} scale trend: gm {st_small[0]:.2f} -> {st_large[0]:.2f} ({grow})")
    if r1_ok and not r1_msgs:
        r1_msgs.append("all matched-algo cells pass gm>=2.0, CI-lo>1.5")

    # ---- R2 mismatch penalty -----------------------------------------------------
    r2_ok, r2_msgs = True, []
    for side in sides:
        sg = stats.get((side, "gossip", "curved", "eps3"))
        sh = stats.get((side, "heat", "curved", "eps3"))
        if not sg or not sh:
            r2_ok = False
            r2_msgs.append(f"FAIL N={side * side}: missing gossip/heat data")
            continue
        gm_g, lo_g, hi_g = sg[0], sg[1], sg[2]
        lo_h = sh[1]
        if not (gm_g < 1.3 and hi_g < lo_h):
            r2_ok = False
            r2_msgs.append(f"FAIL N={side * side}: gossip gm={gm_g:.2f} hi={hi_g:.2f} vs heat lo={lo_h:.2f} "
                           f"(need gossip gm<1.3 and gossip-hi < heat-lo)")
        else:
            r2_msgs.append(f"ok N={side * side}: gossip gm={gm_g:.2f} [<=1.3], "
                           f"contrast gossip-hi {hi_g:.2f} < heat-lo {lo_h:.2f}")

    # ---- R3 mechanism characterization -------------------------------------------
    print("\n--- R3 controls: curved vs shuffled / rreg4 (rounds_control / rounds_curved, eps3) ---")
    r3_msgs = []
    for algo in MATCHED_ALGOS:
        for fam in ("shuffled", "rreg4"):
            for side in sides:
                vals, cens, excl = paired(side, algo, fam, "curved", "eps3")
                if not vals:
                    continue
                gm, lo, hi = geo_mean_ci(vals, rng)
                if lo > 1.0:
                    verdict = "curved FASTER than control (specific geometry adds)"
                elif hi < 1.0:
                    verdict = "control faster (resource is generic randomization/expansion)"
                else:
                    verdict = "statistical tie (resource = degree seq + delocalized wiring)"
                msg = (f"{algo}/N={side * side} curved-vs-{fam}: ratio {gm:.2f} [{lo:.2f},{hi:.2f}] -> {verdict}")
                r3_msgs.append(msg)
                print("  " + msg)

    # ---- R4 gap-governs correlation (per matched algorithm: different algos have
    # different round constants, so pooling them would degrade a true correlation) ----
    r4_ok, r4_parts = True, []
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
            if rho > -0.9:
                r4_ok = False
            r4_parts.append(f"{algo}: rho={rho:.3f} ({len(xs)} runs)")
        else:
            r4_ok = False
            r4_parts.append(f"{algo}: insufficient data")
    r4_msg = ("Spearman(log rounds, log lambda2) per algo, need each <= -0.9 -- "
              + "; ".join(r4_parts))

    # ---- verdict -------------------------------------------------------------------
    print("\n" + "=" * 88)
    for name, ok, msgs in (("R0 VALIDITY", r0_ok, r0_msgs), ("R1 CORE", r1_ok, r1_msgs),
                           ("R2 MISMATCH PENALTY", r2_ok, r2_msgs)):
        print(f"{name}: {'PASS' if ok else 'FAIL'}")
        for m in msgs:
            print(f"    {m}")
    print(f"R3 MECHANISM (characterization, not pass/fail): {len(r3_msgs)} contrasts above")
    print(f"R4 GAP-GOVERNS: {'PASS' if r4_ok else 'FAIL'} -- {r4_msg}")
    robust = r0_ok and r1_ok and r2_ok
    print("\n" + ("LANDMARK IS ROBUST (R0+R1+R2 pass): curvature-matched speedup replicates "
                  "across sizes, seeds, algorithms; mismatch penalty reproduces."
                  if robust else
                  "LANDMARK NOT (YET) ROBUST: see FAIL lines above."))
    print("R3/R4 fix the WORDING of the claim (curvature-specific vs expander-generic).")
    return 0 if robust else 1


# ------------------------------------------------------------------------------ selftest
def selftest():
    """Kernel unit checks against the ORIGINAL loop implementations. No CSVs written."""
    failures = []

    def check(name, ok, detail=""):
        print(f"  [{'ok' if ok else 'FAIL'}] {name} {detail}")
        if not ok:
            failures.append(name)

    G = nx.convert_node_labels_to_integers(nx.grid_2d_graph(6, 6))
    G.add_edge(0, 35)  # break regularity so degree branches are exercised
    A = to_csr(G)
    d = np.asarray(A.sum(axis=1)).ravel()
    rng = np.random.default_rng(1)
    x = rng.random(G.number_of_nodes())
    x = x - x.mean()

    # 1) Metropolis matrix == original per-node loop (compute_on_curvature.py)
    deg = {i: G.degree(i) for i in G}
    ref = x.copy()
    for i in G:
        for j in G[i]:
            ref[i] += (1.0 / (1 + max(deg[i], deg[j]))) * (x[j] - x[i])
    W = metropolis_matrix(A, d)
    check("metropolis == original loop", np.max(np.abs(W @ x - ref)) < 1e-12,
          f"maxerr={np.max(np.abs(W @ x - ref)):.2e}")

    # 2) heat step == original diffuse_rounds update (compute_matched.py)
    Adense = np.asarray(A.todense())
    Pref = Adense / np.where(d > 0, d, 1)[:, None]
    xr = x.copy()
    for _ in range(50):
        xr = (1 - ALPHA) * xr + ALPHA * (Pref @ xr)
    P = sp.diags(1.0 / np.where(d > 0, d, 1.0)) @ A
    xs_ = x.copy()
    for _ in range(50):
        xs_ = (1 - ALPHA) * xs_ + ALPHA * (P @ xs_)
    check("heat == original update", np.max(np.abs(xs_ - xr)) < 1e-10,
          f"maxerr={np.max(np.abs(xs_ - xr)):.2e}")

    # 3) push-sum: column-stochastic, mass-conserving, converges to TRUE mean
    B = pushsum_matrix(A, d)
    colsums = np.asarray(B.sum(axis=0)).ravel()
    check("pushsum column-stochastic", np.max(np.abs(colsums - 1)) < 1e-12)
    y0 = rng.random(G.number_of_nodes()) * 5 + 2  # non-centered on purpose
    s, w = y0.copy(), np.ones(G.number_of_nodes())
    for _ in range(3000):
        s, w = B @ s, B @ w
    check("pushsum mass conserved", abs(s.sum() - y0.sum()) < 1e-8)
    check("pushsum -> true mean", np.max(np.abs(s / w - y0.mean())) < 1e-9,
          f"maxerr={np.max(np.abs(s / w - y0.mean())):.2e}")

    # 4) rounds monotone in eps + heat reproduces original counting
    hit = run_algo("heat", A, x, 5000, EPS_LIST)
    check("eps6 rounds >= eps3 rounds", hit[1e-6] >= hit[1e-3] > 0,
          f"eps3={hit[1e-3]} eps6={hit[1e-6]}")

    # 5) coevolve: deterministic per seed; edge budget within 5% at landmark size
    flat15 = build_flat(15)
    c1 = coevolve(flat15, random.Random(30))
    c2 = coevolve(flat15, random.Random(30))
    check("coevolve deterministic per seed",
          set(map(tuple, map(sorted, c1.edges()))) == set(map(tuple, map(sorted, c2.edges()))))
    drift = abs(c1.number_of_edges() - flat15.number_of_edges()) / flat15.number_of_edges()
    check("coevolve edge drift <= 5%", drift <= 0.05,
          f"{flat15.number_of_edges()} -> {c1.number_of_edges()} ({drift:.1%})")
    check("coevolve connected", nx.is_connected(c1))

    # 6) shuffled preserves degree sequence + connectivity
    sh, note = build_shuffled(c1, 30)
    check("shuffled degree sequence preserved",
          sorted(dict(c1.degree()).values()) == sorted(dict(sh.degree()).values()),
          f"({note})")
    check("shuffled connected", nx.is_connected(sh))
    check("shuffled actually rewired", set(map(tuple, map(sorted, sh.edges())))
          != set(map(tuple, map(sorted, c1.edges()))))

    # 7) lambda2 matches networkx normalized Laplacian
    st = graph_stats(G, np.random.default_rng(2), delta_samples=500)
    Lnx = nx.normalized_laplacian_matrix(G).todense()
    lam2_ref = float(np.sort(np.linalg.eigvalsh(np.asarray(Lnx)))[1])
    check("lambda2 == networkx normalized Laplacian",
          abs(st["lambda2_norm"] - lam2_ref) < 1e-6,
          f"{st['lambda2_norm']:.6f} vs {lam2_ref:.6f}")

    # 8) sanity: curved beats flat on heat at landmark size/seed (directional)
    x15 = np.random.default_rng([30, 15]).random(225)
    x15 = x15 - x15.mean()
    hf = run_algo("heat", to_csr(flat15), x15, 20000, [1e-3])
    hc = run_algo("heat", to_csr(c1), x15, 20000, [1e-3])
    check("landmark direction: curved faster than flat (heat, seed 30)",
          0 < hc[1e-3] < hf[1e-3], f"flat={hf[1e-3]} curved={hc[1e-3]} "
          f"speedup={hf[1e-3] / max(hc[1e-3], 1):.1f}x")

    print(f"\nselftest: {'ALL PASS' if not failures else 'FAILURES: ' + ', '.join(failures)}")
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
    ap = argparse.ArgumentParser(description="CDC-lab curvature-as-computation robustness sweep")
    ap.add_argument("--sides", type=str, default=",".join(map(str, DEFAULT_SIDES)),
                    help="grid side lengths, e.g. '15,22,32' (N = side^2)")
    ap.add_argument("--seeds", type=str, default=f"{DEFAULT_SEEDS[0]}-{DEFAULT_SEEDS[-1]}",
                    help="seeds, e.g. '30-41' or '30,31,32'")
    ap.add_argument("--maxr", type=int, default=DEFAULT_MAXR)
    ap.add_argument("--outdir", type=str,
                    default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                         "results_robustness"))
    ap.add_argument("--quick", action="store_true", help="smoke sweep: side=10, 3 seeds")
    ap.add_argument("--analyze", action="store_true", help="analyze CSVs, print verdict")
    ap.add_argument("--selftest", action="store_true", help="kernel unit checks, no CSVs")
    args = ap.parse_args()
    args.sides = parse_int_list(args.sides)
    args.seeds = parse_int_list(args.seeds)
    if args.quick:
        args.sides, args.seeds, args.maxr = [10], [30, 31, 32], 8000
        args.outdir = os.path.join(args.outdir, "quick")
    if args.selftest:
        sys.exit(selftest())
    if args.analyze:
        sys.exit(analyze(args))
    sweep(args)


if __name__ == "__main__":
    main()
