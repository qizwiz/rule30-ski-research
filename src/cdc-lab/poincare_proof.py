#!/usr/bin/env python3
"""CDC-lab rung 1 (visual proof): the CA-grown hyperbolic graph EMBEDS in the Poincare disk
with LOW distortion, and in the Euclidean plane with HIGH distortion. That distortion gap
IS the proof it 'lives in' hyperbolic space — not the picture, the numbers. Then render it.
"""

import random
import numpy as np
import torch
import networkx as nx

random.seed(30)
torch.manual_seed(30)
np.random.seed(30)


# --- the CA-BUD growth rule (the hyperbolic one from experiment 1) ---
def grow_bud(target_n, k=2, seed=30):
    r = random.Random(seed)
    G = nx.Graph()
    G.add_node(0)
    active = {0}
    nxt = 1
    depth = {0: 0}
    while G.number_of_nodes() < target_n and active:
        na = set()
        for n in list(active):
            for _ in range(k):
                if G.number_of_nodes() >= target_n:
                    break
                c = nxt
                nxt += 1
                G.add_edge(n, c)
                na.add(c)
                depth[c] = depth[n] + 1
                if r.random() < 0.30:
                    th = [x for m in G[n] for x in G[m] if x != c and x != n]
                    if th:
                        G.add_edge(c, r.choice(th))
        active = na
    return G, depth


G, depth = grow_bud(300, seed=30)  # bigger: hyperbolicity's advantage needs scale
G = nx.convert_node_labels_to_integers(G, label_attribute="old")
n = G.number_of_nodes()
D = np.array(nx.floyd_warshall_numpy(G))
allpairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
rng = random.Random(7)
pairs = rng.sample(allpairs, min(9000, len(allpairs)))  # same pair set for BOTH -> fair
ai = torch.tensor([p[0] for p in pairs])
bi = torch.tensor([p[1] for p in pairs])
Dg = torch.tensor([D[i, j] for i, j in pairs], dtype=torch.float64)


def best_scale_distortion(demb, dg):
    s = (demb * dg).sum() / (dg * dg).sum()
    return float(torch.sqrt(((demb - s * dg) ** 2).sum() / ((s * dg) ** 2).sum()))


# FAIR: both embeddings optimized by the SAME torch Adam, same epochs, same loss.
# Only the distance function differs (Poincare/hyperbolic vs Euclidean). So any gap is GEOMETRY.
def embed(metric, project, epochs=1500):
    X = (torch.randn(n, 2, dtype=torch.float64) * 0.001).requires_grad_(True)
    scale = torch.tensor(0.5, dtype=torch.float64, requires_grad=True)
    opt = torch.optim.Adam([X, scale], lr=0.03)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, epochs)
    for ep in range(epochs):
        opt.zero_grad()
        d = metric(X[ai], X[bi])
        (((d - scale.abs() * Dg) ** 2).mean()).backward()
        opt.step()
        sched.step()
        if project:
            with torch.no_grad():
                nrm = X.norm(dim=1, keepdim=True)
                X.data = torch.where(nrm >= 1 - 1e-4, X.data / nrm * (1 - 1e-3), X.data)
    with torch.no_grad():
        dist = best_scale_distortion(metric(X[ai], X[bi]), Dg)
    return X.detach(), dist


def poincare(u, v):
    nu = (u * u).sum(1).clamp(max=1 - 1e-7)
    nv = (v * v).sum(1).clamp(max=1 - 1e-7)
    return torch.acosh(
        1 + 2 * ((u - v) ** 2).sum(1) / ((1 - nu) * (1 - nv)).clamp(min=1e-9)
    )


def euclid(u, v):
    return (((u - v) ** 2).sum(1)).clamp(min=1e-12).sqrt()


X, hyp_dist = embed(poincare, project=True)
_, euc_dist = embed(euclid, project=False)

print(f"CA-BUD graph: {n} nodes, {G.number_of_edges()} edges, diam={int(D.max())}")
print(f"  distortion in HYPERBOLIC (Poincare disk): {hyp_dist:.3f}")
print(f"  distortion in EUCLIDEAN  (MDS R^2):        {euc_dist:.3f}")
print(
    f"  => hyperbolic fits {euc_dist / max(hyp_dist, 1e-6):.1f}x better "
    + (
        "(PROOF: it lives in hyperbolic space)"
        if hyp_dist < euc_dist * 0.8
        else "(inconclusive)"
    )
)

# --- render the Poincare embedding as an SVG (the picture) ---
P = X.detach().numpy()
R = 300
CX = CY = 320


def sx(p):
    return CX + p[0] * R


def sy(p):
    return CY + p[1] * R


maxd = max(depth.get(G.nodes[i]["old"], 0) for i in range(n)) or 1


def col(i):
    t = depth.get(G.nodes[i]["old"], 0) / maxd
    r = int(110 + t * 145)
    g = int(193 - t * 100)
    b = int(228 - t * 80)
    return f"#{r:02x}{g:02x}{b:02x}"


svg = [
    '<svg xmlns="http://www.w3.org/2000/svg" width="640" height="640" viewBox="0 0 640 640">',
    '<rect width="640" height="640" fill="#0d1530"/>',
    f'<circle cx="{CX}" cy="{CY}" r="{R}" fill="none" stroke="#33506e" stroke-width="1.5"/>',
    '<text x="16" y="28" fill="#6EC1E4" font-family="monospace" font-size="13">CA-grown structure in the Poincare disk (hyperbolic space)</text>',
]
for i, j in [(u, v) for u, v in G.edges()]:
    svg.append(
        f'<line x1="{sx(P[i]):.1f}" y1="{sy(P[i]):.1f}" x2="{sx(P[j]):.1f}" y2="{sy(P[j]):.1f}" stroke="#33506e60" stroke-width="0.6"/>'
    )
for i in range(n):
    svg.append(
        f'<circle cx="{sx(P[i]):.1f}" cy="{sy(P[i]):.1f}" r="{4 if depth.get(G.nodes[i]["old"], 0) == 0 else 2.4}" fill="{col(i)}"/>'
    )
svg.append("</svg>")
open("/Users/jonathanhill/src/cdc-lab/poincare.svg", "w").write("\n".join(svg))
print(
    "  rendered -> ~/src/cdc-lab/poincare.svg (edges near the disk boundary = exponential room = hyperbolic)"
)
