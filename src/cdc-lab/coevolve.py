#!/usr/bin/env python3
"""CDC-lab rung 2 (co-evolution): a COMPUTATION runs on the substrate and the GEOMETRY responds.

Start FLAT (2D grid). Each round: route traffic between random node pairs (the computation),
tally edge/node usage. Then a LOCAL, CA-style rewiring rule (no global blueprint):
  - a CONGESTED node (high through-traffic) sprouts ONE local shortcut between two of its
    busiest neighbors (closes a triangle / bypasses a local detour) -- "route together, wire together"
  - the least-used non-bridge edges WITHER (pruned)
Edge budget held ~constant (rewire, don't densify). Track Gromov delta (curvature) and mean
path length (efficiency) as geometry co-evolves under the computation.

Falsifiable: if computation curves the flat grid toward hyperbolic, delta should FALL (or the
delta/diam ratio) and mean path length should FALL. If it stays flat, the hypothesis is refuted.
"""

import random
import networkx as nx

random.seed(30)


def sample_delta_and_L(G, samples=1500):
    G = G.subgraph(max(nx.connected_components(G), key=len)).copy()
    d = dict(nx.all_pairs_shortest_path_length(G))
    nodes = list(G)
    diam = max(d[u][v] for u in d for v in d[u])
    tot = 0
    cnt = 0
    for u in d:
        for v in d[u]:
            if u < v:
                tot += d[u][v]
                cnt += 1
    L = tot / max(cnt, 1)
    best = 0
    for _ in range(samples):
        a, b, c, e = random.sample(nodes, 4)
        S = sorted([d[a][b] + d[c][e], d[a][c] + d[b][e], d[a][e] + d[b][c]])
        best = max(best, (S[2] - S[1]) / 2)
    return best, diam, L


def coevolve(G, rounds=14, traffic=1200):
    G = G.copy()
    hist = []
    for rd in range(rounds):
        # --- COMPUTATION: route traffic, tally usage ---
        euse = {tuple(sorted(e)): 0 for e in G.edges()}
        nuse = {n: 0 for n in G}
        nodes = list(G)
        for _ in range(traffic):
            s, t = random.sample(nodes, 2)
            try:
                p = nx.shortest_path(G, s, t)
            except nx.NetworkXNoPath:
                continue
            for a, b in zip(p, p[1:]):
                k = tuple(sorted((a, b)))
                euse[k] = euse.get(k, 0) + 1
            for x in p[1:-1]:
                nuse[x] = nuse.get(x, 0) + 1
        # --- GEOMETRY RESPONDS (local, CA-style) ---
        # 1) congested nodes sprout a local shortcut between their two busiest neighbors
        congested = sorted(nuse, key=lambda x: -nuse[x])[: max(1, len(G) // 15)]
        added = 0
        for x in congested:
            nb = sorted(G[x], key=lambda y: -euse.get(tuple(sorted((x, y))), 0))
            if len(nb) >= 2 and not G.has_edge(nb[0], nb[1]):
                G.add_edge(nb[0], nb[1])
                added += 1
        # 2) least-used non-bridge edges wither (keep edge budget ~constant, stay connected)
        bridges = set(map(lambda e: tuple(sorted(e)), nx.bridges(G)))
        prunable = sorted(
            (k for k in euse if k not in bridges and G.has_edge(*k)),
            key=lambda k: euse[k],
        )
        for k in prunable[:added]:
            if k not in set(map(lambda e: tuple(sorted(e)), nx.bridges(G))):
                G.remove_edge(*k)
        dmax, diam, L = sample_delta_and_L(G)
        hist.append(
            (
                rd,
                G.number_of_edges(),
                dmax,
                diam,
                round(L, 2),
                round(dmax / max(diam, 1), 3),
            )
        )
    return G, hist


start = nx.convert_node_labels_to_integers(nx.grid_2d_graph(15, 15))  # FLAT
d0, diam0, L0 = sample_delta_and_L(start)
print(
    f"START (2D grid, flat): nodes={start.number_of_nodes()} edges={start.number_of_edges()} "
    f"delta_max={d0:.1f} diam={diam0} meanL={L0:.2f} delta/diam={d0 / diam0:.3f}"
)
G2, hist = coevolve(start)
print("round  edges  delta_max  diam  meanL  delta/diam")
for r, e, dm, di, L, ratio in hist:
    print(f"  {r:2}   {e:4}    {dm:5.1f}   {di:3}  {L:5.2f}   {ratio:.3f}")
r, e, dm, di, L, ratio0 = hist[-1]
print(
    f"\nVERDICT: delta/diam {d0 / diam0:.3f} -> {ratio0:.3f}   meanL {L0:.2f} -> {L:.2f}"
)
curved = ratio0 < d0 / diam0 - 0.02
faster = L < L0 - 0.3
print(
    f"  geometry curved toward hyperbolic: {curved}   |   routing more efficient: {faster}"
)
print(
    f"  => {'COMPUTATION SHAPED GEOMETRY (flat -> more hyperbolic + more efficient)' if (curved and faster) else 'no clear co-evolution toward hyperbolic (honest null / partial)'}"
)
