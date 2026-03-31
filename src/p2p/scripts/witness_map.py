import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from collections import Counter

R30 = np.array([0,1,1,1,1,0,0,0], dtype=np.uint8)

def caEvolveNP(steps, tape_arr):
    t = tape_arr.copy()
    for _ in range(steps):
        if len(t) < 3: return t
        idx = (t[:-2] << 2) | (t[1:-1] << 1) | t[2:]
        t = R30[idx]
    return t

def is_sensitive(w, m, np_val):
    N = 2*(np_val+1)+1
    bw = np.zeros(N, dtype=np.uint8); bw[w] = 1
    fw = caEvolveNP(np_val+1, bw)
    if len(fw) == 0 or fw[0] != 0: return False
    tw = np.zeros(N, dtype=np.uint8); tw[w] = 1; tw[m] = 1
    hw = caEvolveNP(np_val+1, tw)
    return len(hw) > 0 and hw[0] == 1

# Period map (shrinking CA, verified)
period_map = {6:16, 8:32, 10:64, 12:128, 14:256, 16:512, 18:256, 20:256, 22:1024}

# Precompute sensitive residues using small base tapes
print("Precomputing sensitive residues (small tapes)...")
sensitive = {}
for w, P in period_map.items():
    sensitive[w] = set()
    for np_val in range(w, P + w):
        if np_val % 8 != 5: continue
        if is_sensitive(w, 4, np_val):
            sensitive[w].add(np_val % P)
    print(f"  w={w:2d}, P={P:4d}: {len(sensitive[w])} residues")

# Build witness map for n' in [3087, 5200), n'≡5 mod 8
print("\nBuilding witness map for n' in [3087, 5200)...")
data = []
for np_val in range(3087, 5200):
    if np_val % 8 != 5: continue
    min_w = None
    for w in sorted(period_map.keys()):
        P = period_map[w]
        if np_val % P in sensitive[w]:
            min_w = w
            break
    # Known level-1 override (n'≡5 mod 1024): w=30 if none found with w≤22
    if min_w is None and np_val % 1024 == 5:
        min_w = 30
    # Known level-2 override (n'≡5 mod 4096): w=34 if none found
    if min_w is None and np_val % 4096 == 5:
        min_w = 34
    # Level 3+ (n'≡5 mod 16384): algebraic needed
    if min_w is None:
        min_w = 38  # sentinel for "needs algebraic proof"
    data.append((np_val, min_w))

data.sort()
nps = [d[0] for d in data]
ws  = [d[1] for d in data]
mods = [n % 64 for n in nps]

cmap = {5:'#e74c3c', 13:'#3498db', 21:'#e67e22',
        29:'#1abc9c', 37:'#9b59b6', 45:'#2ecc71',
        53:'#f39c12', 61:'#34495e'}
colors = [cmap.get(m, 'gray') for m in mods]

fig, axes = plt.subplots(2, 1, figsize=(14, 9))

# Top: overview [3087, 5200)
ax = axes[0]
ax.scatter(nps, ws, c=colors, s=12, alpha=0.8, zorder=3)
ax.axvline(x=4101, color='red', linestyle='--', lw=1.5, alpha=0.6, label="n'≡5 mod 1024 (w=30)")
ax.axvline(x=5125, color='red', linestyle='--', lw=1.5, alpha=0.6)
for wl in [10,12,14,16,18,22,30,34,38]:
    ax.axhline(y=wl, color='gray', linestyle=':', lw=0.5, alpha=0.3)
ax.axhspan(36, 40, color='lightyellow', alpha=0.5, label='level 3+ (algebraic)')
for m, c in sorted(cmap.items()):
    ax.scatter([], [], c=c, s=14, label=f"n'≡{m} mod 64")
ax.set_xlabel("n'  (firing positions, n'≡5 mod 8)", fontsize=10)
ax.set_ylabel("min witness w", fontsize=10)
ax.set_title("SubcaseB m=4: min witness w by firing position [3087, 5200)\n(colored by n' mod 64)", fontsize=10)
ax.set_yticks([6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38])
ax.set_yticklabels(['6','8','10','12','14','16','18','20','22','','','','30','','34','','38'])
ax.legend(fontsize=7, ncol=5, loc='upper right')
ax.grid(True, alpha=0.15)
ax.set_ylim(4, 42)

# Bottom: zoom [3087, 4200)
ax2 = axes[1]
nps2 = [n for n in nps if n < 4200]
ws2  = [w for n, w in zip(nps, ws) if n < 4200]
mods2 = [n % 64 for n in nps2]
colors2 = [cmap.get(m,'gray') for m in mods2]
ax2.scatter(nps2, ws2, c=colors2, s=20, alpha=0.85, zorder=3)
ax2.axvline(x=4101, color='red', linestyle='--', lw=1.5, alpha=0.7, label="n'=4101 (≡5 mod 1024) → w=30")
for wl in [10,12,14,16,18,22]:
    ax2.axhline(y=wl, color='gray', linestyle=':', lw=0.5, alpha=0.3)
for m, c in sorted(cmap.items()):
    ax2.scatter([], [], c=c, s=16, label=f"n'≡{m} mod 64")
ax2.set_xlabel("n'  (firing positions, n'≡5 mod 8)", fontsize=10)
ax2.set_ylabel("min witness w", fontsize=10)
ax2.set_title("Zoom [3087, 4200) — period structure clearly visible", fontsize=10)
ax2.set_yticks([6,8,10,12,14,16,18,20,22,24,26,28,30,34])
ax2.legend(fontsize=7, ncol=5, loc='upper right')
ax2.grid(True, alpha=0.15)
ax2.set_ylim(4, 36)

plt.tight_layout()
plt.savefig('/tmp/witness_map.png', dpi=150, bbox_inches='tight')
print("Saved → /tmp/witness_map.png")

cnt = Counter(ws)
print("Witness distribution:", dict(sorted(cnt.items())))
print(f"  w=38 (level3+ algebraic): {cnt.get(38,0)} positions")
