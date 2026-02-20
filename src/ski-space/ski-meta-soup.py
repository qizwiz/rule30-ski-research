#!/usr/bin/env python3
"""
ski-meta-soup.py

Level 1 meta-soup: strategy genomes competing on a spatial graph.

A GENOME is a parameter vector that defines a complete soup instance:
  - L: tape length (8, 16, 32)
  - k: neighbor count in small-world graph (4, 6, 8)
  - p_rewire: rewiring probability (0.0 - 0.3)
  - pressure_scale: Murray pressure multiplier (16, 32, 64, 128)
  - s_weight: S symbol frequency weight (1-5)
  - k_weight: K symbol frequency weight (1-5)
  - i_weight: I symbol frequency weight (1-3)
  - n_tapes: population size (512, 1024, 2048, 4096)
  - max_nodes_factor: max tree nodes as multiple of L (4, 8, 16)

FITNESS is measured from the soup's telemetry after N_eval epochs:
  - primary: RAF ratio (how far above autocatalytic threshold)
  - secondary: ops/int trend (is computation density rising?)
  - tertiary: cycle count (are 2-cycles forming?)
  - combined: weighted sum, normalized

META-GRAPH: M strategy-nodes on a small-world graph (default M=16, k_meta=4)
  - Each node runs its own SBCL soup instance
  - After each evaluation round, nodes interact with neighbors
  - Loser adopts winner's genome with mutation
  - Meta-graph rewires: winners gain edges, losers shed them (pressure-driven)
  - MCP server exposes meta-state for monitoring

COEVOLUTION: The MCP server genome is also subject to evolution.
  - report_every, window_size, fitness_weights are part of the genome
  - Servers that produce more useful signal survive
  - This is topology IS computation at the meta level
"""

import json
import os
import subprocess
import threading
import time
import random
import math
import copy
import sys
import re
from pathlib import Path
from datetime import datetime

# ─── Constants ────────────────────────────────────────────────────────────────

SBCL        = "/opt/homebrew/Cellar/sbcl/2.6.1/libexec/bin/sbcl"
SBCL_HOME   = "/opt/homebrew/Cellar/sbcl/2.6.1/lib/sbcl"
LISP_FILE   = "/Users/jonathanhill/src/lenia/ski-soup-v10.lisp"
_STATE_DIR   = Path.home() / ".ski-meta"
_STATE_DIR.mkdir(exist_ok=True)
META_LOG     = str(_STATE_DIR / "soup.log")
META_STATE   = str(_STATE_DIR / "state.json")
META_LINEAGE = str(_STATE_DIR / "lineage.jsonl")
N_EVAL_EPOCHS = 10_000_000  # epochs per fitness evaluation
REPORT_EVERY  = 1_000_000   # soup checkpoint interval during eval
META_NODES    = 16           # number of strategy nodes in meta-graph
META_K        = 4            # meta-graph neighbor count
META_P_REWIRE = 0.1          # meta-graph small-world rewiring
MUTATION_RATE = 0.2          # probability of mutating each gene

# ─── Genome ───────────────────────────────────────────────────────────────────

GENOME_SPEC = {
    # name: (type, min, max, choices, lisp_param, lisp_encoder)
    # lisp_param = None means "handled specially" (not a simple setf)
    # lisp_encoder = callable(value, genome) -> Lisp string
    "L":               ("choice", None, None, [8, 16, 32],
                        "*L*", str),
    "k":               ("choice", None, None, [4, 6, 8, 10],
                        None, None),   # used in make-small-world, not setf
    "p_rewire":        ("float",  0.0,  0.3,  None,
                        None, None),   # used in make-small-world, not setf
    "pressure_scale":  ("choice", None, None, [16.0, 32.0, 64.0, 128.0],
                        "*pressure-scale*", str),
    "s_weight":        ("int",    1,    6,    None,
                        None, None),   # combined into *alphabet* vector
    "k_weight":        ("int",    1,    4,    None,
                        None, None),   # combined into *alphabet* vector
    "i_weight":        ("int",    1,    4,    None,
                        None, None),   # combined into *alphabet* vector
    "n_tapes":         ("choice", None, None, [512, 1024, 2048, 4096],
                        None, None),   # used in run-spatial, not setf
    "max_nodes_factor":("choice", None, None, [4, 8, 16],
                        "*max-nodes*", lambda v, g: f"(* {v} ski-soup-v10::*L*)"),
    # Reaction graph memory — how much reaction history the RAF detector sees
    "rxn_window":      ("choice", None, None, [500, 1000, 2000, 5000],
                        "*rxn-window-size*", str),
    # Pressure field depth sensitivity — how fast pressure decays with tree depth
    "murray_exp":      ("float", -1.0,  0.0,  None,
                        "*murray-exponent*", str),  # 2^exp per branch; -2/3 is biological
    # Adaptive topology thresholds — how aggressively the soup rewires itself
    "rewire_high":     ("float",  1.0,  3.0,  None,
                        "*rewire-high-threshold*", str),  # RAF multiplier to gain edge
    "rewire_low":      ("float",  0.1,  0.9,  None,
                        "*rewire-low-threshold*", str),  # RAF multiplier to shed edge
    # Fitness tape: a SKI program that computes fitness from encoded soup stats.
    # This IS the fitness function — it evolves under the same pressure it measures.
    "fitness_tape":    ("tape",   None, None, None,
                        None, None),   # not a Lisp setf
    # Tournament distance distribution: how far does this manifold reach for opponents?
    # Three weights (unnormalized) over [local, regional, global].
    # local    = interact within this manifold only (current BFF behavior)
    # regional = sample opponent from an adjacent manifold's tape pool
    # global   = sample opponent from any manifold's tape pool (transduction)
    "dist_local":      ("float",  0.0,  1.0,  None,
                        None, None),   # Python-only (inter-manifold)
    "dist_regional":   ("float",  0.0,  1.0,  None,
                        None, None),
    "dist_global":     ("float",  0.0,  1.0,  None,
                        None, None),
    # Seed fraction: what fraction of initial pool to fill with immigrants
    "seed_frac":       ("float",  0.0,  0.3,  None,
                        None, None),
    # V9: evolvable interaction protocol parameters
    "n_concat":        ("choice", None, None, [2, 3],
                        "*n-concat*", str),          # tapes per interaction
    "split_point":     ("choice", None, None, ["L", "L2", "L3"],
                        "*split-point*", lambda v, g: {"L": "nil", "L2": "(floor ski-soup-v10::*L* 2)", "L3": "(floor ski-soup-v10::*L* 3)"}[v]),  # asymmetric split
    "birth_death":     ("choice", None, None, ["symmetric", "asymmetric", "net_growth"],
                        "*birth-death-mode*", lambda v, g: f":{v.replace('_','-')}"),
    "pad_mode":        ("choice", None, None, ["random", "repeat", "zero"],
                        "*pad-mode*", lambda v, g: f":{v}"),
    "extra_combinators":("choice",None, None, ["none", "W", "B", "WB"],
                        "*extra-combinators*", lambda v, g: {"none":"nil","W":":W","B":":B","WB":":WB"}[v]),
    # ── Meta-level CA: the evolution process itself is evolvable ──────────────
    # These are Python-side parameters — no Lisp binding needed.
    # The system discovers its own evolvability, evaluation budget, and connectivity.
    "mutation_rate":   ("float",  0.05, 0.5,  None,
                        None, None),   # per-gene mutation probability for offspring
    "n_eval_epochs":   ("choice", None, None, [2_000_000, 5_000_000, 10_000_000, 20_000_000],
                        None, None),   # eval budget: longer = more signal, slower
    "meta_k":          ("choice", None, None, [2, 4, 6, 8],
                        None, None),   # preferred meta-graph degree for this node
}

FITNESS_TAPE_LEN = 16   # length of the SKI fitness program
_SKI = ["S", "K", "I"]

def random_genome():
    g = {}
    for name, spec in GENOME_SPEC.items():
        typ, lo, hi, choices = spec[0], spec[1], spec[2], spec[3]
        if typ == "tape":
            g[name] = [random.choice(_SKI) for _ in range(FITNESS_TAPE_LEN)]
        elif choices:
            g[name] = random.choice(choices)
        elif typ == "float":
            g[name] = round(random.uniform(lo, hi), 3)
        elif typ == "int":
            g[name] = random.randint(lo, hi)
    return g

def mutate(genome):
    """Mutate genome: each gene independently.
    Uses the genome's own mutation_rate — evolvable evolvability."""
    g = copy.deepcopy(genome)
    rate = genome.get("mutation_rate", MUTATION_RATE)
    for name, spec in GENOME_SPEC.items():
        typ, lo, hi, choices = spec[0], spec[1], spec[2], spec[3]
        if random.random() > rate:
            continue
        if typ == "tape":
            # Point-mutate one random position in the tape
            tape = g[name][:]
            pos = random.randrange(len(tape))
            tape[pos] = random.choice(_SKI)
            g[name] = tape
        elif choices:
            g[name] = random.choice(choices)
        elif typ == "float":
            delta = (hi - lo) * random.gauss(0, 0.1)
            g[name] = round(max(lo, min(hi, g[name] + delta)), 3)
        elif typ == "int":
            delta = random.choice([-1, 0, 1])
            g[name] = max(lo, min(hi, g[name] + delta))
    return g

def crossover(g1, g2):
    """Uniform crossover: each gene from g1 or g2 with equal probability.
    Tape genes get element-wise crossover — each symbol independently."""
    child = {}
    for name, spec in GENOME_SPEC.items():
        typ = spec[0]
        if typ == "tape":
            child[name] = [
                a if random.random() < 0.5 else b
                for a, b in zip(g1[name], g2[name])
            ]
        else:
            child[name] = g1[name] if random.random() < 0.5 else g2[name]
    return child

# ─── Lisp expression builder ──────────────────────────────────────────────────

def genome_to_lisp_eval(g, node_id, seeds=None):
    """Build the SBCL --eval expression for a given genome.
    seeds: list of tape symbol-lists to inject as immigrants (transduction).
    """
    pkg = "ski-soup-v10"
    L = g["L"]

    # Build alphabet vector from s/k/i weights (special case)
    alphabet_vec = " ".join(
        [":S"] * g["s_weight"] +
        [":K"] * g["k_weight"] +
        [":I"] * g["i_weight"]
    )

    # Build seed-tapes expression
    if seeds:
        lisp_seeds = []
        for tape in seeds:
            syms = [f":{s}" for s in tape[:L]]
            syms += [":I"] * (L - len(syms))
            lisp_seeds.append(f"'({' '.join(syms)})")
        seed_expr = f":seed-tapes (list {' '.join(lisp_seeds)})"
    else:
        seed_expr = ""

    # Generate setf expressions from GENOME_SPEC — the loop
    # GENOME_SPEC is ordered (Python 3.7+): L comes before max_nodes_factor,
    # rxn_window comes before reset-rxn-graph! (which is inserted explicitly after).
    setfs = []
    for gene, spec in GENOME_SPEC.items():
        typ, lo, hi, choices, lisp_param, encoder = spec[0], spec[1], spec[2], spec[3], spec[4], spec[5]
        if lisp_param is None or encoder is None:
            continue  # handled specially or Python-only
        val = g.get(gene)
        if val is None:
            continue
        # Call encoder with (value, genome) — lambda or str
        try:
            lisp_val = encoder(val, g)
        except TypeError:
            lisp_val = encoder(val)  # fallback for single-arg encoders like str
        setfs.append(f"(setf {pkg}::{lisp_param} {lisp_val})")

    setfs_str = " ".join(setfs)

    return (
        f"(progn"
        f" {setfs_str}"
        f" (setf {pkg}::*alphabet* (vector {alphabet_vec}))"
        f" ({pkg}::reset-rxn-graph!)"
        f" (let ((adj ({pkg}::make-small-world"
        f"              {g['n_tapes']} {g['k']} {g['p_rewire']})))"
        f"   ({pkg}::run-spatial"
        f"     {g['n_tapes']} {g.get('n_eval_epochs', N_EVAL_EPOCHS)} adj"
        f"     :topology-name \"node-{node_id}\""
        f"     :report-every {max(REPORT_EVERY, g.get('n_eval_epochs', N_EVAL_EPOCHS) // 10)}"
        f"     :min-replicate-count 2"
        f"     {seed_expr})))"
    )

# ─── Fitness measurement ──────────────────────────────────────────────────────
#
# Three signals that cannot be faked independently:
#
#   entropy_collapse  — H must DROP from its initial value (max disorder = 0 score)
#   catalysis         — cat > 0 means real autocatalytic interactions occurred
#   cycles            — closed reaction loops (A→B→A) in the rxn graph
#
# fitness = entropy_collapse * catalysis * cycles
#
# Zero on any one term = zero total. A frozen soup (H flat), a non-catalytic
# soup (cat=0), or a non-cyclic soup (cyc=0) all score exactly 0.
# Only a soup that shows selection pressure AND catalytic closure AND loops wins.

def parse_fitness(log_path, genome):
    """Score a completed soup run on three independent signals."""
    from ski_parse import parse_log
    raw = parse_log(log_path)
    readings = [
        {
            "epoch":  r["epoch"],
            "H":      r.get("H",     8.0),
            "ops":    r.get("ops/int", 0.0),
            "cat_p":  r.get("cat",   0.0),
            "cycles": r.get("cyc",   0),
        }
        for r in raw
    ]

    if not readings:
        return 0.0

    # ── 1. Entropy collapse ────────────────────────────────────────────────────
    # H starts near log2(N) (maximum disorder). It must fall as replicators take
    # over. Score = how much it fell, normalized to [0,1].
    # A soup where H never moves scores 0 — no selection pressure at all.
    h_vals  = [r["H"] for r in readings]
    h_first = h_vals[0]
    h_last  = h_vals[-1]
    h_min   = min(h_vals)
    # Reward the maximum drop achieved at any point, not just the final value
    h_drop  = max(0.0, h_first - h_min)
    # Normalize: a drop of 3 bits (e.g. 8→5) is excellent; cap at 5 bits
    entropy_score = min(1.0, h_drop / 3.0)

    # ── 2. Catalysis ──────────────────────────────────────────────────────────
    # cat_p is the empirical fraction of interactions that are catalytic.
    # Score = log-scaled so small but real catalysis is rewarded.
    # cat=0 → 0, cat=0.01 → ~0.15, cat=0.5 → ~0.85, cat=1.0 → 1.0
    cat_last  = readings[-1]["cat_p"]
    cat_max   = max(r["cat_p"] for r in readings)
    cat_score = math.log1p(cat_max * 10.0) / math.log1p(10.0)  # [0,1]

    # ── 3. Autocatalytic cycles ────────────────────────────────────────────────
    # Closed loops in the reaction graph — the RAF signature.
    # Score = log-scaled. 0 cycles → 0. 10 cycles → ~0.5. 500 → ~1.0.
    max_cyc   = max(r["cycles"] for r in readings)
    cyc_score = math.log1p(max_cyc) / math.log1p(500.0)        # [0,1]

    # ── Combined: all three must be nonzero ────────────────────────────────────
    fitness = entropy_score * cat_score * cyc_score

    # Scale to [0, 1] with two decimal places for readability
    return round(fitness, 6)


# ── Minimal SKI interpreter for fitness evaluation ────────────────────────────

import signal as _signal

class _Timeout(Exception): pass

def _ski_reduce(tape, max_steps=2000):
    """Reduce a flat SKI tape under BFF parse → reduce → serialize.
    Returns the serialized output as a list of symbol strings."""
    # Parse: left-spine application tree
    if not tape:
        return ["I"]

    def make_app(l, r): return ("app", l, r)
    def make_sym(s):    return ("sym", s)

    def parse(syms):
        if not syms:
            return make_sym("I")
        tree = make_sym(syms[0])
        for s in syms[1:]:
            tree = make_app(tree, make_sym(s))
        return tree

    _node_count = [0]
    def step(node, depth=0):
        _node_count[0] += 1
        if depth > 100 or node is None or _node_count[0] > 50000:
            return node, False
        if node[0] == "sym":
            return node, False
        f, x = node[1], node[2]
        # I x → x
        if f[0] == "sym" and f[1] == "I":
            return x, True
        # K x y → x
        if (f[0] == "app" and f[1][0] == "sym" and f[1][1] == "K"):
            return f[2], True
        # S x y z → x z (y z)
        if (f[0] == "app" and f[1][0] == "app" and
                f[1][1][0] == "sym" and f[1][1][1] == "S"):
            x2 = f[1][2]   # S's first arg
            y  = f[2]      # S's second arg
            z  = x         # S's third arg
            if x2 is not None and y is not None:
                return make_app(make_app(x2, z), make_app(y, z)), True
            return node, False
        # recurse left then right
        new_f, rf = step(f, depth + 1)
        if rf:
            return make_app(new_f, x), True
        new_x, rx = step(x, depth + 1)
        if rx:
            return make_app(f, new_x), True
        return node, False

    def serialize(node):
        if node is None:
            return []
        if node[0] == "sym":
            return [node[1]]
        return serialize(node[1]) + serialize(node[2])

    tree = parse(tape)
    for _ in range(max_steps):
        new_tree, changed = step(tree)
        if not changed:
            break
        tree = new_tree

    return serialize(tree)

# ─── Inter-manifold tape pool (transduction / vesiduction) ───────────────────
#
# After each eval round, each manifold deposits its top replicating tapes here.
# Before the next eval, manifolds sample from this pool (weighted by distance
# gene) to seed immigrants into their initial population.
#
# Structure: { node_id: [ ["S","K","I",...], ... ] }
# Thread-safe via a lock — nodes run in parallel.

import threading as _threading
_TAPE_POOL      = {}          # node_id → list of tape symbol-lists
_TAPE_POOL_LOCK = _threading.Lock()

TOP_TAPE_RE = re.compile(r"^\s*(\d+)x\s+([SKI ]+)$")

def deposit_tapes(node_id, log_path):
    """Parse top replicating tapes from a finished soup log and deposit into pool."""
    try:
        lines = Path(log_path).read_text().splitlines()
    except FileNotFoundError:
        return
    # Collect all tape lines from the FINAL section only
    in_final = False
    tapes = []
    for line in lines:
        if "═══ FINAL ═══" in line:
            in_final = True
            continue
        if in_final:
            m = TOP_TAPE_RE.match(line)
            if m:
                count = int(m.group(1))
                syms  = m.group(2).strip().split()
                # Deposit once per count (weighted by replicator copy number)
                for _ in range(min(count, 5)):
                    tapes.append(syms)
    if tapes:
        with _TAPE_POOL_LOCK:
            _TAPE_POOL[node_id] = tapes

def sample_immigrants(node_id, adj, genome, n_tapes):
    """Sample seed tapes for this node from the inter-manifold pool.
    Uses the distance gene to weight local/regional/global sources."""
    seed_frac = genome.get("seed_frac", 0.0)
    if seed_frac <= 0.0:
        return []
    n_seeds = max(1, int(n_tapes * seed_frac))

    dl = genome.get("dist_local",    0.5)
    dr = genome.get("dist_regional", 0.3)
    dg = genome.get("dist_global",   0.2)
    total = dl + dr + dg
    if total <= 0:
        return []
    dl, dr, dg = dl/total, dr/total, dg/total

    with _TAPE_POOL_LOCK:
        all_ids  = list(_TAPE_POOL.keys())
        reg_ids  = [j for j in adj if j in _TAPE_POOL]

    if not all_ids:
        return []

    seeds = []
    for _ in range(n_seeds):
        r = random.random()
        if r < dl:
            # Local: sample from own pool (just skip — soup starts fresh anyway)
            continue
        elif r < dl + dr and reg_ids:
            # Regional: sample from adjacent manifold
            src = random.choice(reg_ids)
        else:
            # Global: any manifold (transduction — long-range)
            src = random.choice(all_ids)
        with _TAPE_POOL_LOCK:
            pool = _TAPE_POOL.get(src, [])
        if pool:
            seeds.append(random.choice(pool))
    return seeds

# ─── Strategy node ────────────────────────────────────────────────────────────

_lineage_counter = 0  # global genome-birth counter

def _new_lineage_id():
    global _lineage_counter
    _lineage_counter += 1
    return _lineage_counter

def record_lineage(event):
    """Append one lineage event (dict) to the JSONL file."""
    with open(META_LINEAGE, "a") as f:
        f.write(json.dumps(event) + "\n")

class StrategyNode:
    def __init__(self, node_id, genome=None):
        self.node_id    = node_id
        self.genome     = genome or random_genome()
        self.fitness    = 0.0
        self.age        = 0          # evaluation rounds survived
        self.log_path   = f"/tmp/ski-meta-node-{node_id}.txt"
        self.proc       = None
        self.running    = False
        self.lineage_id = _new_lineage_id()   # unique ID for this genome instance
        self.parent_id  = None                # lineage_id of the genome we descended from
        self.meta_adj   = []                  # adjacency in meta-graph (set by runner)
        # Record birth
        record_lineage({"event": "born", "node": node_id,
                        "lineage": self.lineage_id, "parent": self.parent_id,
                        "genome": self.genome})

    def start_eval(self):
        """Launch SBCL subprocess for this genome's evaluation."""
        if self.running:
            return
        # Sample immigrant tapes from other manifolds
        seeds = sample_immigrants(self.node_id, self.meta_adj,
                                  self.genome, self.genome["n_tapes"])
        # Always truncate log before starting — stale content corrupts parse_fitness
        Path(self.log_path).write_text("")
        env = os.environ.copy()
        env["SBCL_HOME"] = SBCL_HOME
        cmd = [
            SBCL, "--noinform",
            "--load", LISP_FILE,
            "--eval", genome_to_lisp_eval(self.genome, self.node_id, seeds)
        ]
        log = open(self.log_path, "a")
        self.proc    = subprocess.Popen(cmd, stdout=log, stderr=log, env=env)
        self.running = True

    def wait_and_score(self):
        """Wait for SBCL to finish, compute fitness, deposit top tapes to pool."""
        if self.proc:
            self.proc.wait()
        self.running = False
        self.fitness = parse_fitness(self.log_path, self.genome)
        self.age    += 1
        deposit_tapes(self.node_id, self.log_path)   # ← feed the inter-manifold pool
        record_lineage({"event": "scored", "node": self.node_id,
                        "lineage": self.lineage_id, "fitness": self.fitness,
                        "age": self.age})
        return self.fitness

    def kill(self):
        if self.proc and self.proc.poll() is None:
            self.proc.terminate()
        self.running = False

    def to_dict(self):
        return {
            "node_id":    self.node_id,
            "fitness":    self.fitness,
            "age":        self.age,
            "lineage_id": self.lineage_id,
            "parent_id":  self.parent_id,
            "genome":     self.genome,
            "log":        self.log_path,
        }

# ─── Meta-graph ───────────────────────────────────────────────────────────────

def make_meta_adj(n, k, p):
    """Watts-Strogatz small-world adjacency for meta-graph."""
    adj = [set() for _ in range(n)]
    for i in range(n):
        for d in range(1, k // 2 + 1):
            j = (i + d) % n
            adj[i].add(j)
            adj[j].add(i)
    for i in range(n):
        for d in range(1, k // 2 + 1):
            j = (i + d) % n
            if random.random() < p:
                adj[i].discard(j)
                adj[j].discard(i)
                new_j = random.choice([x for x in range(n)
                                       if x != i and x not in adj[i]])
                adj[i].add(new_j)
                adj[new_j].add(i)
    return [sorted(s) for s in adj]

def rewire_meta(adj, nodes):
    """
    Pressure-driven meta-graph rewiring.
    High-fitness nodes gain edges. Low-fitness nodes shed edges.
    Node's meta_k gene sets its preferred degree — topology IS genome.
    """
    n = len(nodes)
    fitnesses = [nd.fitness for nd in nodes]
    mean_fit  = sum(fitnesses) / max(n, 1)

    for i, node in enumerate(nodes):
        preferred_k = node.genome.get("meta_k", META_K)
        current_k   = len(adj[i])
        if node.fitness > mean_fit * 1.2 and current_k < preferred_k:
            # High pressure + wants more edges: attract a new edge
            candidates = [j for j in range(n)
                          if j != i and j not in adj[i]]
            if candidates:
                j = random.choice(candidates)
                adj[i].append(j)
                adj[j].append(i)
        elif (node.fitness < mean_fit * 0.8 or current_k > preferred_k) and len(adj[i]) > 2:
            # Low pressure or over-connected: shed an edge
            j = random.choice(adj[i])
            adj[i].remove(j)
            if i in adj[j]:
                adj[j].remove(i)

# ─── Meta-soup runner ─────────────────────────────────────────────────────────

def log(msg):
    ts  = datetime.now().strftime("%H:%M:%S")
    out = f"[{ts}] {msg}"
    print(out, flush=True)
    with open(META_LOG, "a") as f:
        f.write(out + "\n")

def save_state(nodes, adj, generation):
    state = {
        "generation": generation,
        "timestamp":  datetime.now().isoformat(),
        "nodes":      [n.to_dict() for n in nodes],
        "adj":        adj,
        "best": max(nodes, key=lambda n: n.fitness).to_dict(),
        "mean_fitness": sum(n.fitness for n in nodes) / len(nodes),
    }
    with open(META_STATE, "w") as f:
        json.dump(state, f, indent=2)
    return state

def migrate_genome(g):
    """Fill any missing genes with defaults from GENOME_SPEC (handles schema upgrades)."""
    g = dict(g)
    for name, spec in GENOME_SPEC.items():
        if name in g:
            continue
        typ, lo, hi, choices = spec[0], spec[1], spec[2], spec[3]
        if typ == "tape":
            g[name] = [random.choice(_SKI) for _ in range(FITNESS_TAPE_LEN)]
        elif choices:
            g[name] = choices[0]          # first choice = conservative default
        elif typ == "float":
            g[name] = round((lo + hi) / 2, 3)
        elif typ == "int":
            g[name] = (lo + hi) // 2
    return g


def load_state():
    """Load saved meta-soup state. Returns (nodes, adj, generation) or None."""
    p = Path(META_STATE)
    if not p.exists():
        return None
    try:
        state = json.loads(p.read_text())
        nodes = []
        for nd in state["nodes"]:
            node = StrategyNode(nd["node_id"])
            node.genome     = migrate_genome(nd["genome"])   # ← schema migration
            node.fitness    = nd["fitness"]
            node.age        = nd["age"]
            node.lineage_id = nd["lineage_id"]
            node.parent_id  = nd.get("parent_id")
            nodes.append(node)
        adj = {int(k): v for k, v in state["adj"].items()}
        return nodes, adj, state["generation"]
    except Exception as e:
        print(f"[warn] Could not load state: {e}", flush=True)
        return None

def run_meta_soup(n_generations=50, batch_size=4, resume=False):
    """
    Main meta-soup loop.

    Each generation:
    1. Run batch_size nodes in parallel (SBCL subprocesses)
    2. Score fitness from telemetry
    3. Each node competes with neighbors — loser adopts winner genome + mutation
    4. Meta-graph rewires based on fitness pressure
    5. Save state, repeat
    """
    start_gen = 0

    if resume:
        saved = load_state()
        if saved:
            nodes, adj, start_gen = saved
            log(f"=== SKI Meta-Soup RESUMING from gen {start_gen}: {META_NODES} nodes ===")
        else:
            log("=== No saved state found — starting fresh ===")
            resume = False

    if not resume:
        log(f"=== SKI Meta-Soup starting: {META_NODES} nodes, {n_generations} generations ===")
        nodes = [StrategyNode(i) for i in range(META_NODES)]
        adj   = make_meta_adj(META_NODES, META_K, META_P_REWIRE)

    log(f"Genome space: {len(GENOME_SPEC)} genes")
    log(f"Meta-graph: N={META_NODES}, k={META_K}, p={META_P_REWIRE}")
    log(f"Eval: {N_EVAL_EPOCHS:,} epochs per node, {REPORT_EVERY:,} report interval")

    for gen in range(start_gen, n_generations):
        log(f"\n── Generation {gen+1}/{n_generations} (resumed from {start_gen}) ──" if start_gen > 0 else f"\n── Generation {gen+1}/{n_generations} ──")
        try:
            # Pick batch_size nodes to evaluate (round-robin through all nodes)
            batch_start = (gen * batch_size) % META_NODES
            batch = [nodes[(batch_start + i) % META_NODES] for i in range(batch_size)]

            # Launch in parallel
            for node in batch:
                node.meta_adj = adj[node.node_id]   # give node its neighbor list
                dl = node.genome.get("dist_local",    0.5)
                dr = node.genome.get("dist_regional", 0.3)
                dg = node.genome.get("dist_global",   0.2)
                sf = node.genome.get("seed_frac",     0.0)
                log(f"  Starting node {node.node_id}: L={node.genome['L']} "
                    f"k={node.genome['k']} N={node.genome['n_tapes']} "
                    f"p={node.genome['pressure_scale']} "
                    f"dist=[{dl:.2f}/{dr:.2f}/{dg:.2f}] seed={sf:.2f}")
                node.start_eval()

            # Wait for all in batch to complete
            for node in batch:
                fitness = node.wait_and_score()
                pool_size = len(_TAPE_POOL.get(node.node_id, []))
                log(f"  Node {node.node_id} done: fitness={fitness:.4f} "
                    f"(age={node.age}) pool={pool_size}tapes")

            # Competition: each evaluated node competes with neighbors
            for node in batch:
                neighbors = [nodes[j] for j in adj[node.node_id]
                             if nodes[j].fitness > 0]  # only scored nodes compete
                if not neighbors:
                    continue
                best_neighbor = max(neighbors, key=lambda n: n.fitness)

                if best_neighbor.fitness > node.fitness:
                    # Node loses — adopt winner genome with mutation
                    old_fit      = node.fitness
                    old_lineage  = node.lineage_id
                    node.genome  = mutate(crossover(best_neighbor.genome, node.genome))
                    node.fitness = 0.0  # will be re-scored next round
                    node.lineage_id = _new_lineage_id()
                    node.parent_id  = best_neighbor.lineage_id
                    record_lineage({"event": "adopt", "node": node.node_id,
                                    "old_lineage": old_lineage, "old_fitness": old_fit,
                                    "new_lineage": node.lineage_id,
                                    "parent_lineage": node.parent_id,
                                    "parent_node": best_neighbor.node_id,
                                    "parent_fitness": best_neighbor.fitness,
                                    "genome": node.genome})
                    log(f"  Node {node.node_id} ({old_fit:.4f}) → adopts node "
                        f"{best_neighbor.node_id} ({best_neighbor.fitness:.4f}) genome")
                else:
                    log(f"  Node {node.node_id} ({node.fitness:.4f}) holds its genome")

            # Meta-graph rewiring (pressure-driven)
            scored = [n for n in nodes if n.fitness > 0]
            if len(scored) > 2:
                rewire_meta(adj, nodes)
                log(f"  Meta-graph rewired")

            # Save state
            state = save_state(nodes, adj, gen + 1)
            best  = state["best"]
            log(f"  Best: node {best['node_id']} fitness={best['fitness']:.4f} "
                f"genome={best['genome']}")
            log(f"  Mean fitness: {state['mean_fitness']:.4f}")

        except Exception as e:
            log(f"  ERROR in generation {gen+1}: {e} — continuing")

    log("\n=== Meta-soup complete ===")
    state = save_state(nodes, adj, n_generations)
    log(f"Best genome: {state['best']['genome']}")
    return state

# ─── MCP server for meta-soup ─────────────────────────────────────────────────

META_TOOLS = [
    {
        "name": "get_lineage_tree",
        "description": "Get the phylogenetic tree of genome lineages: who descended from whom, fitness at each node, dominant clades.",
        "inputSchema": {"type": "object", "properties": {}, "required": []}
    },
    {
        "name": "get_meta_status",
        "description": "Get current meta-soup state: generation, all node fitnesses, best genome, mean fitness.",
        "inputSchema": {"type": "object", "properties": {}, "required": []}
    },
    {
        "name": "get_best_genome",
        "description": "Get the highest-fitness strategy genome found so far, with interpretation.",
        "inputSchema": {"type": "object", "properties": {}, "required": []}
    },
    {
        "name": "get_fitness_landscape",
        "description": "Get fitness values for all nodes in the meta-graph, showing the landscape shape.",
        "inputSchema": {"type": "object", "properties": {}, "required": []}
    },
]

def handle_meta_tool(name, args):
    try:
        state = json.loads(Path(META_STATE).read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {"error": "Meta-soup not running or no state yet. Start with --run"}

    if name == "get_lineage_tree":
        try:
            events = [json.loads(l) for l in Path(META_LINEAGE).read_text().splitlines() if l]
        except FileNotFoundError:
            return {"error": "No lineage data yet. Start a run first."}
        # Build tree: lineage_id → {parent, children, best_fitness, node_ids}
        tree = {}
        for e in events:
            lid = e.get("lineage")
            if lid is None:
                continue
            if lid not in tree:
                tree[lid] = {"lineage": lid, "parent": e.get("parent"),
                             "children": [], "best_fitness": 0.0,
                             "node_ids": [], "genome_L": e.get("genome", {}).get("L")}
            if e["event"] == "born":
                tree[lid]["node_ids"].append(e["node"])
            elif e["event"] == "scored":
                tree[lid]["best_fitness"] = max(tree[lid]["best_fitness"], e["fitness"])
            elif e["event"] == "adopt":
                parent = e.get("parent_lineage")
                child  = e.get("new_lineage")
                if parent and child:
                    if parent not in tree:
                        tree[parent] = {"lineage": parent, "parent": None,
                                        "children": [], "best_fitness": 0.0,
                                        "node_ids": [], "genome_L": None}
                    if child not in tree[parent]["children"]:
                        tree[parent]["children"].append(child)
        # Count distinct root lineages (no parent)
        roots = [v for v in tree.values() if not v["parent"]]
        best  = max(tree.values(), key=lambda v: v["best_fitness"], default={})
        # Clade sizes: how many descendants does each root have?
        def clade_size(lid):
            return 1 + sum(clade_size(c) for c in tree.get(lid, {}).get("children", []))
        return {
            "total_lineages": len(tree),
            "root_lineages":  len(roots),
            "best_lineage":   best.get("lineage"),
            "best_fitness":   best.get("best_fitness"),
            "roots": [{"lineage": r["lineage"], "L": r["genome_L"],
                       "clade_size": clade_size(r["lineage"]),
                       "best_fitness": r["best_fitness"]} for r in roots],
            "adoption_events": sum(1 for e in events if e["event"] == "adopt"),
        }

    if name == "get_meta_status":
        return {
            "generation": state["generation"],
            "mean_fitness": state["mean_fitness"],
            "best_node": state["best"]["node_id"],
            "best_fitness": state["best"]["fitness"],
            "nodes": [{"id": n["node_id"], "fitness": n["fitness"],
                       "age": n["age"]} for n in state["nodes"]],
        }
    elif name == "get_best_genome":
        g = state["best"]["genome"]
        return {
            "genome": g,
            "fitness": state["best"]["fitness"],
            "interpretation": {
                "tape_length": f"L={g['L']} symbols per tape",
                "population": f"N={g['n_tapes']} tapes on small-world k={g['k']} p={g['p_rewire']}",
                "pressure": f"Murray scale={g['pressure_scale']} — {'fast decay' if g['pressure_scale'] > 64 else 'slow memory'}",
                "alphabet": f"S:{g['s_weight']} K:{g['k_weight']} I:{g['i_weight']} — "
                            f"{'growth-biased' if g['s_weight'] > 3 else 'balanced'}",
                "fitness_weights": f"RAF:{g['fitness_raf_w']:.2f} ops:{g['fitness_ops_w']:.2f} cyc:{g['fitness_cyc_w']:.2f}",
            }
        }
    elif name == "get_fitness_landscape":
        nodes = state["nodes"]
        fits  = [n["fitness"] for n in nodes]
        return {
            "fitnesses": fits,
            "min": min(fits),
            "max": max(fits),
            "mean": sum(fits) / len(fits),
            "variance": sum((f - sum(fits)/len(fits))**2 for f in fits) / len(fits),
            "adjacency": state["adj"],
        }
    return {"error": f"Unknown tool: {name}"}

def mcp_loop_meta():
    all_tools = META_TOOLS
    while True:
        try:
            line = sys.stdin.readline()
            if not line:
                break
            req = json.loads(line.strip())
        except (json.JSONDecodeError, EOFError):
            break

        rid    = req.get("id")
        method = req.get("method", "")
        params = req.get("params", {})

        if method == "initialize":
            resp = {
                "jsonrpc": "2.0", "id": rid,
                "result": {
                    "protocolVersion": "2024-11-05",
                    "capabilities": {"tools": {}},
                    "serverInfo": {"name": "ski-meta-soup", "version": "1.0"}
                }
            }
        elif method == "tools/list":
            resp = {"jsonrpc": "2.0", "id": rid,
                    "result": {"tools": all_tools}}
        elif method == "tools/call":
            name = params.get("name", "")
            aarg = params.get("arguments", {})
            try:
                result = handle_meta_tool(name, aarg)
                resp = {
                    "jsonrpc": "2.0", "id": rid,
                    "result": {"content": [{"type": "text",
                                            "text": json.dumps(result, indent=2)}]}
                }
            except Exception as e:
                resp = {
                    "jsonrpc": "2.0", "id": rid,
                    "result": {"content": [{"type": "text", "text": f"Error: {e}"}],
                               "isError": True}
                }
        elif method == "notifications/initialized":
            continue
        else:
            resp = {"jsonrpc": "2.0", "id": rid,
                    "error": {"code": -32601, "message": f"Unknown: {method}"}}

        sys.stdout.write(json.dumps(resp) + "\n")
        sys.stdout.flush()

# ─── Entry point ──────────────────────────────────────────────────────────────

if __name__ == "__main__":
    if "--run" in sys.argv or "--resume" in sys.argv:
        n_gen   = 20
        batch   = int(sys.argv[sys.argv.index("--batch") + 1]) if "--batch" in sys.argv else 4
        resume  = "--resume" in sys.argv
        run_meta_soup(n_generations=n_gen, batch_size=batch, resume=resume)
    elif "--mcp" in sys.argv:
        # MCP server mode
        mcp_loop_meta()
    else:
        print(__doc__)
        print("\nUsage:")
        print("  python3 ski-meta-soup.py --run             # run 20 generations (fresh)")
        print("  python3 ski-meta-soup.py --resume          # resume from last checkpoint")
        print("  python3 ski-meta-soup.py --run --batch 2   # smaller batches")
        print("  python3 ski-meta-soup.py --mcp             # MCP server mode")
