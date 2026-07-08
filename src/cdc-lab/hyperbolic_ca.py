#!/usr/bin/env python3
"""CDC-lab experiment 1: does structure GROWN by local CA mechanics become hyperbolic?

The honest test is NOT a single-size ratio (that mislabels flat grids). Hyperbolicity is a
SCALING property: Gromov delta stays BOUNDED as N -> infinity for hyperbolic (tree-like /
negatively-curved) spaces, but GROWS with diameter for flat (Euclidean) ones. So we grow
each structure to several sizes, sample delta_max at each, and read off the scaling.

Two CA growth rules (same framework, different LOCAL rule) to show emergent geometry is
rule-dependent -- i.e. CA mechanics can DISCOVER hyperbolic OR flat structure:
  - BUD: each active frontier cell buds k children (+ sparse local cross-links) -> tree-like
  - LATTICE: a cell fills its local 2D neighborhood -> grid-like
Baselines calibrate the reading: balanced tree (delta=0), 2D grid (flat), BA, gnp.
"""

import random
import networkx as nx


def delta_max(G, samples=3000, seed=30):
    r = random.Random(seed)
    G = G.subgraph(max(nx.connected_components(G), key=len)).copy()
    G = nx.convert_node_labels_to_integers(G)
    d = dict(nx.all_pairs_shortest_path_length(G))
    nodes = list(G)
    diam = max(d[u][v] for u in d for v in d[u])
    best = 0.0
    for _ in range(samples):
        a, b, c, e = r.sample(nodes, 4)
        S = sorted([d[a][b] + d[c][e], d[a][c] + d[b][e], d[a][e] + d[b][c]])
        best = max(best, (S[2] - S[1]) / 2.0)
    return best, diam, G.number_of_nodes()


# ---- CA growth rule BUD: active frontier cells bud k children + occasional local shortcut ----
def grow_bud(target_n, k=2, seed=30):
    r = random.Random(seed)
    G = nx.Graph()
    G.add_node(0)
    active = {0}
    nxt = 1
    while G.number_of_nodes() < target_n and active:
        new_active = set()
        for n in list(active):
            for _ in range(k):
                if G.number_of_nodes() >= target_n:
                    break
                c = nxt
                nxt += 1
                G.add_edge(n, c)
                new_active.add(c)
                # LOCAL rule: sometimes cross-link the child to a 2-hop neighbor (a real graph, not a pure tree)
                if r.random() < 0.30:
                    two_hop = [x for m in G[n] for x in G[m] if x != c and x != n]
                    if two_hop:
                        G.add_edge(c, r.choice(two_hop))
        active = new_active
    return G


# ---- CA growth rule LATTICE: cells fill their local 2D neighborhood (grid-like, should be FLAT) ----
def grow_lattice(target_n):
    G = nx.Graph()
    pos = {(0, 0)}
    G.add_node((0, 0))
    frontier = {(0, 0)}
    while len(G) < target_n and frontier:
        nf = set()
        for x, y in list(frontier):
            for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                p = (x + dx, y + dy)
                if len(G) >= target_n:
                    break
                if p not in pos:
                    pos.add(p)
                    nf.add(p)
                G.add_edge((x, y), p)
        frontier = nf
    return G


print(
    "=== delta_max vs size: BOUNDED => hyperbolic (neg curvature); GROWING => flat ==="
)
sizes = [60, 120, 250, 500]


def sweep(name, fn):
    row = []
    for N in sizes:
        dm, diam, n = delta_max(fn(N))
        row.append((n, diam, dm))
    trend = (
        "BOUNDED -> HYPERBOLIC"
        if row[-1][2] <= row[0][2] + 1.0
        else "GROWS with size -> FLAT/EUCLIDEAN"
    )
    cells = "  ".join(f"N={n} d(max)={dm:.1f}/diam{diam}" for n, diam, dm in row)
    print(f"{name:16} {cells}   ==> {trend}")


sweep("CA-BUD", grow_bud)
sweep("CA-LATTICE", grow_lattice)
print("--- baselines ---")
sweep(
    "balanced-tree",
    lambda N: nx.balanced_tree(2, max(2, int(__import__("math").log2(N)))),
)
sweep("2D-grid", lambda N: nx.grid_2d_graph(int(N**0.5) + 1, int(N**0.5) + 1))
sweep("Barabasi-Albert", lambda N: nx.barabasi_albert_graph(N, 2, seed=30))
sweep("random-gnp", lambda N: nx.gnp_random_graph(N, 3.0 / N, seed=30))
