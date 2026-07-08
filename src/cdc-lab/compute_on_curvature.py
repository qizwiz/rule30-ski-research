#!/usr/bin/env python3
"""CDC-lab rung 3 (the hinge): is CURVATURE a COMPUTATIONAL RESOURCE?

Same nodes, same edge budget, two geometries: a FLAT grid vs a co-evolved HYPERBOLIC graph
(exp2). Run the SAME real distributed computation on both -- gossip/consensus averaging, whose
convergence speed is pure geometry (mixing time ~ 1/spectral-gap). If the curved substrate
computes the SAME task in far fewer rounds, curvature is a computational resource.

Fires the brain (brain:activity) at each stage so JH watches it think live on *brain*.
Falsifiable: if flat and curved converge in similar rounds, the claim is refuted.
"""

import socket
import time
import random
import numpy as np
import networkx as nx

random.seed(30)
np.random.seed(30)


def pulse(who, what, kind="compute"):
    try:
        s = socket.create_connection(("127.0.0.1", 6379), timeout=2)

        def enc(*a):
            o = b"*%d\r\n" % len(a)
            for x in a:
                b = str(x).encode()
                o += b"$%d\r\n%s\r\n" % (len(b), b)
            return o

        s.sendall(
            enc(
                "XADD",
                "brain:activity",
                "MAXLEN",
                "~",
                "2000",
                "*",
                "who",
                who,
                "what",
                what,
                "kind",
                kind,
                "ts",
                str(int(time.time())),
            )
        )
        s.close()
    except OSError:
        pass


def coevolve_to_hyperbolic(G, rounds=14, traffic=1200):
    G = G.copy()
    for _ in range(rounds):
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
        congested = sorted(nuse, key=lambda x: -nuse[x])[: max(1, len(G) // 15)]
        added = 0
        for x in congested:
            nb = sorted(G[x], key=lambda y: -euse.get(tuple(sorted((x, y))), 0))
            if len(nb) >= 2 and not G.has_edge(nb[0], nb[1]):
                G.add_edge(nb[0], nb[1])
                added += 1
        br = set(map(lambda e: tuple(sorted(e)), nx.bridges(G)))
        pr = sorted(
            (k for k in euse if k not in br and G.has_edge(*k)), key=lambda k: euse[k]
        )
        for k in pr[:added]:
            if k not in set(map(lambda e: tuple(sorted(e)), nx.bridges(G))):
                G.remove_edge(*k)
    return G


def gossip_rounds(G, eps=1e-3, maxr=2000):
    # distributed averaging with Metropolis weights (doubly stochastic). Rounds to consensus.
    G = nx.convert_node_labels_to_integers(G)
    n = G.number_of_nodes()
    deg = {i: G.degree(i) for i in G}
    x = np.random.rand(n)
    x = x - x.mean()
    x0 = np.linalg.norm(x)
    for r in range(1, maxr + 1):
        nx_ = x.copy()
        for i in G:
            s = x[i]
            for j in G[i]:
                w = 1.0 / (1 + max(deg[i], deg[j]))
                nx_[i] += w * (x[j] - x[i])
        x = nx_
        if np.linalg.norm(x - x.mean()) / max(x0, 1e-9) < eps:
            return r
    return maxr


def spectral_gap(G):
    G = nx.convert_node_labels_to_integers(G)
    try:
        return float(nx.algebraic_connectivity(G, seed=30))  # lambda_2 of Laplacian
    except Exception:
        return float("nan")


pulse(
    "builder",
    "rung3: is curvature a computational resource? building flat vs curved substrate (same N, same edges)",
)
flat = nx.convert_node_labels_to_integers(nx.grid_2d_graph(15, 15))
pulse(
    "builder",
    "co-evolving a copy of the flat grid toward hyperbolic (computation shapes geometry)",
)
hyp = coevolve_to_hyperbolic(flat)
print(
    f"FLAT grid:       {flat.number_of_nodes()} nodes, {flat.number_of_edges()} edges"
)
print(
    f"CURVED (co-ev):  {hyp.number_of_nodes()} nodes, {hyp.number_of_edges()} edges (same budget)"
)

pulse("thomas", "running gossip consensus on the FLAT substrate...")
rf = gossip_rounds(flat)
gf = spectral_gap(flat)
pulse("thomas", f"FLAT: consensus in {rf} rounds (spectral gap {gf:.4f})", "verify")
pulse("thomas", "running the SAME gossip consensus on the CURVED substrate...")
rh = gossip_rounds(hyp)
gh = spectral_gap(hyp)
pulse("thomas", f"CURVED: consensus in {rh} rounds (spectral gap {gh:.4f})", "verify")

print("\n=== SAME computation (gossip consensus to eps=1e-3), two geometries ===")
print(f"  FLAT grid:      {rf:4} rounds   spectral-gap {gf:.4f}")
print(f"  CURVED (co-ev): {rh:4} rounds   spectral-gap {gh:.4f}")
speedup = rf / max(rh, 1)
verdict = (
    f"CURVATURE IS A COMPUTATIONAL RESOURCE: the curved substrate computes the same "
    f"task {speedup:.1f}x faster ({rf}->{rh} rounds), {gh / max(gf, 1e-9):.1f}x bigger spectral gap"
    if rh < rf * 0.7
    else f"NULL: curved not meaningfully faster ({rf} vs {rh} rounds) -- claim refuted at this scale"
)
print("\n" + verdict)
pulse("builder", verdict, "finding")
