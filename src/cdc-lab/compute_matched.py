#!/usr/bin/env python3
"""CDC-lab: does a GEOMETRY-MATCHED computation let the curved substrate beat flat?
Tonight's Metropolis gossip PENALIZED hubs (curved lost). The fair measure was the
normalized-Laplacian gap (curved 8.1x). So use a computation that gap governs: a lazy
random-walk / heat-diffusion consensus x <- (1-a)x + a P x, P = D^-1 A. Prediction:
curved converges FASTER. Falsifiable: if not, curvature isn't a resource even matched."""
import random, numpy as np, networkx as nx
random.seed(30); np.random.seed(30)
def coevolve(G, rounds=14, traffic=1200):
    G=G.copy()
    for _ in range(rounds):
        eu={tuple(sorted(e)):0 for e in G.edges()}; nu={n:0 for n in G}; nd=list(G)
        for _ in range(traffic):
            s,t=random.sample(nd,2)
            try: p=nx.shortest_path(G,s,t)
            except nx.NetworkXNoPath: continue
            for a,b in zip(p,p[1:]): k=tuple(sorted((a,b))); eu[k]=eu.get(k,0)+1
            for x in p[1:-1]: nu[x]=nu.get(x,0)+1
        cong=sorted(nu,key=lambda x:-nu[x])[:max(1,len(G)//15)]; add=0
        for x in cong:
            nb=sorted(G[x],key=lambda y:-eu.get(tuple(sorted((x,y))),0))
            if len(nb)>=2 and not G.has_edge(nb[0],nb[1]): G.add_edge(nb[0],nb[1]); add+=1
        br=set(map(lambda e:tuple(sorted(e)),nx.bridges(G)))
        pr=sorted((k for k in eu if k not in br and G.has_edge(*k)),key=lambda k:eu[k])
        for k in pr[:add]:
            if k not in set(map(lambda e:tuple(sorted(e)),nx.bridges(G))): G.remove_edge(*k)
    return G
def diffuse_rounds(G, alpha=0.5, eps=1e-3, maxr=5000):
    G=nx.convert_node_labels_to_integers(G); n=G.number_of_nodes()
    A=nx.to_numpy_array(G); d=A.sum(1); P=A/np.where(d>0,d,1)[:,None]
    x=np.random.rand(n); x-=x.mean(); x0=np.linalg.norm(x)
    for r in range(1,maxr+1):
        x=(1-alpha)*x+alpha*(P@x)
        if np.linalg.norm(x-x.mean())/max(x0,1e-9)<eps: return r
    return maxr
flat=nx.convert_node_labels_to_integers(nx.grid_2d_graph(15,15)); hyp=coevolve(flat)
rf=diffuse_rounds(flat); rh=diffuse_rounds(hyp)
print(f"GEOMETRY-MATCHED computation (lazy random-walk / heat diffusion):")
print(f"  FLAT:   {rf} rounds to consensus")
print(f"  CURVED: {rh} rounds to consensus")
print(f"  => {'CURVATURE IS A RESOURCE (matched algo): curved '+str(round(rf/max(rh,1),1))+'x faster' if rh<rf*0.8 else 'still no win — curvature not a resource even matched'}")
