"""
Generate publication-quality figures for prize3_paper.tex
Figure 1: Two panels
  (a) Rule 30 causal cone from single black cell e_n, n=30
  (b) Rule 30 from spike at m=8, showing F(n,m) correctly
Figure 2: SubcaseB period structure — active m-set with period doubling
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyArrowPatch

# ---- Rule 30 helpers ----

def rule30_step_finite(row):
    n = len(row)
    out = np.zeros(n, dtype=np.uint8)
    for i in range(n):
        l = row[i-1] if i > 0 else 0
        c = row[i]
        r = row[i+1] if i < n-1 else 0
        out[i] = l ^ (c | r)
    return out

def evolve(initial, steps):
    rows = [initial.copy()]
    tape = initial.copy()
    for _ in range(steps):
        tape = rule30_step_finite(tape)
        rows.append(tape.copy())
    return np.array(rows)

# =====================================================================
# FIGURE 1
# =====================================================================

N = 30  # generations

# Panel (a): single black cell e_n
size_a = 2*N + 1
tape_a = np.zeros(size_a, dtype=np.uint8)
tape_a[N] = 1  # center spike
grid_a = evolve(tape_a, N)

# Panel (b): spike at m=8
m = 8
tape_b = np.zeros(size_a, dtype=np.uint8)
tape_b[m] = 1
grid_b = evolve(tape_b, N)

fig, axes = plt.subplots(1, 2, figsize=(12, 7))
fig.patch.set_facecolor('white')

for ax, grid, title, panel_label in [
    (axes[0], grid_a, f'(a) Single-spike input $e_n$, $n={N}$', 'a'),
    (axes[1], grid_b, f'(b) Spike at $m={m}$: SubcaseB read point $F(n,m)$', 'b'),
]:
    # Plot CA
    ax.imshow(grid, cmap='binary', interpolation='nearest', aspect='equal',
              origin='upper', vmin=0, vmax=1)
    ax.set_xlabel('cell position', fontsize=11)
    ax.set_ylabel('generation $n$', fontsize=11)
    ax.set_title(title, fontsize=11, pad=8)
    ax.tick_params(labelsize=9)

# Panel (a): draw causal cone
ax = axes[0]
# cone narrows from (0,N) and (2N,N) up to apex at (N,0)
# In imshow coordinates: x = cell position, y = generation (top=0)
cone_left_x  = [N - N, N]   # [0, N]
cone_left_y  = [0, N]
cone_right_x = [N + N, N]   # [2N, N]
cone_right_y = [0, N]
ax.plot(cone_left_x,  cone_left_y,  color='#E87722', lw=1.8, label='Causal cone boundary')
ax.plot(cone_right_x, cone_right_y, color='#E87722', lw=1.8)
# orange circle at center output
ax.plot(N, N, 'o', color='#E87722', markersize=8, zorder=5,
        label=f'$s({N}) = \\mathtt{{rule30}}_{N}(e_{N})$')
ax.legend(fontsize=8, loc='upper right', framealpha=0.9)

# Panel (b): draw spike location and F(n,m) read point
ax = axes[1]
# cone from spike at m=8
cone_left_x_b  = [m, max(0, m - N)]
cone_left_y_b  = [0, min(N, m)]
cone_right_x_b = [m, m + N]
cone_right_y_b = [0, N]
ax.plot(cone_left_x_b,  cone_left_y_b,  color='#888888', lw=1.2, ls='--', alpha=0.6)
ax.plot(cone_right_x_b, cone_right_y_b, color='#888888', lw=1.2, ls='--', alpha=0.6)

# Spike marker at (m, 0)
ax.plot(m, 0, 's', color='#CC3300', markersize=9, zorder=5, label=f'Spike at $m={m}$')

# F(n,m) read point: center cell (position N) at generation N
# (this is the center of the tape of size 2N+1 after N+1 steps)
ax.plot(N, N, '^', color='#1166CC', markersize=9, zorder=5,
        label=f'$F(n,m)$: center cell at gen $n+1$')
ax.annotate(f'$F({N},{m})$',
            xy=(N, N), xytext=(N+4, N-3),
            fontsize=9, color='#1166CC',
            arrowprops=dict(arrowstyle='->', color='#1166CC', lw=1.2))

ax.legend(fontsize=8, loc='upper right', framealpha=0.9)

plt.tight_layout(pad=2.0)
plt.savefig('/Users/jonathanhill/src/p2p/rule30_figure.pdf', dpi=200,
            bbox_inches='tight', facecolor='white')
plt.savefig('/Users/jonathanhill/src/p2p/rule30_figure.png', dpi=150,
            bbox_inches='tight', facecolor='white')
plt.close()
print("Figure 1 saved.")

# =====================================================================
# FIGURE 2: SubcaseB period structure
# =====================================================================

# Active m-set and periods
active_m   = [4, 6, 8, 10, 12, 14, 16, 20, 22, 24, 26, 28, 30, 34, 36, 38]
periods    = [8, 16, 32, 64, 64, 64, 256, 256, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768]
inactive_m = [2, 18, 32]

fig, axes = plt.subplots(1, 2, figsize=(13, 5))
fig.patch.set_facecolor('white')

# --- Left: period vs m (log scale) ---
ax = axes[0]
ax.semilogy(active_m, periods, 'o-', color='#1155AA', lw=2, ms=7,
            label='Active $m$ (SubcaseB occurs)', zorder=3)
for im in inactive_m:
    ax.axvline(im, color='#CC3300', lw=1.2, ls=':', alpha=0.7)
# annotate inactive
for im in inactive_m:
    ax.text(im+0.4, 12, f'$m={im}$\n(inactive)', fontsize=7.5,
            color='#CC3300', va='bottom')

# doubling reference line from m=22 onwards
m_dbl = [22, 24, 26, 28, 30, 34, 36, 38]
p_dbl = [256, 512, 1024, 2048, 4096, 8192, 16384, 32768]
ax.semilogy(m_dbl, p_dbl, '--', color='#888888', lw=1.2, label='Period doubles (×2 per active step)')

ax.set_xlabel('tape position $m$', fontsize=11)
ax.set_ylabel('SubcaseB cluster period $P_m$', fontsize=11)
ax.set_title('(a) Period doubling in the active $m$-set', fontsize=11)
ax.set_xticks(active_m)
ax.set_xticklabels([str(m) for m in active_m], rotation=45, fontsize=8)
ax.yaxis.set_major_formatter(matplotlib.ticker.FuncFormatter(
    lambda x, _: f'$2^{{{int(np.log2(x))}}}$' if x > 0 and np.log2(x) == int(np.log2(x)) else f'{int(x)}'))
ax.legend(fontsize=8.5, loc='upper left')
ax.grid(True, which='both', ls=':', alpha=0.4)
ax.set_xlim(0, 42)

# --- Right: SubcaseB hits for m=4 (period 8), showing periodic structure ---
ax = axes[1]

def compute_F(n_prime, m_val):
    size = 2 * n_prime + 3
    tape = np.zeros(size, dtype=np.uint8)
    tape[m_val] = 1
    t = tape.copy()
    for _ in range(n_prime + 1):
        t = rule30_step_finite(t)
    return int(t[size // 2])

def compute_G(n_prime, m_val):
    size = 2 * n_prime + 3
    tape = np.zeros(size, dtype=np.uint8)
    tape[m_val] = 1
    tape[size - 1] = 1
    t = tape.copy()
    for _ in range(n_prime + 1):
        t = rule30_step_finite(t)
    return int(t[size // 2])

# Show SubcaseB pattern for m=4 (period 8) in [3087, 3087+32]
n_range = range(3087, 3087 + 32)
m4 = 4
F_vals = [compute_F(np_, m4) for np_ in n_range]
G_vals = [compute_G(np_, m4) for np_ in n_range]
subcaseB = [f == 0 and g == 1 for f, g in zip(F_vals, G_vals)]

colors = []
labels_used = set()
for f, g, sb in zip(F_vals, G_vals, subcaseB):
    if sb:
        colors.append('#CC3300')
    elif f == 0 and g == 0:
        colors.append('#1155AA')
    else:
        colors.append('#AAAAAA')

ns = list(n_range)
for i, (n_, sb, f, g) in enumerate(zip(ns, subcaseB, F_vals, G_vals)):
    lbl = None
    tag = 'SubcaseB: $F=0,G=1$' if sb else ('$F=0,G=0$' if f==0 and g==0 else '$F=1$')
    if tag not in labels_used:
        lbl = tag
        labels_used.add(tag)
    ax.bar(i, 1, color=colors[i], label=lbl, edgecolor='white', linewidth=0.3)

ax.set_xlabel(f"$n'$ (offset from 3087)", fontsize=11)
ax.set_ylabel('')
ax.set_title(f'(b) SubcaseB pattern for $m=4$ (period $P_4=8$)', fontsize=11)
ax.set_xticks(range(0, 32, 4))
ax.set_xticklabels([f'+{i}' for i in range(0, 32, 4)], fontsize=9)
ax.set_yticks([])
ax.legend(fontsize=8.5, loc='upper right')
period_marks = [i for i in range(0, 32, 8)]
for p in period_marks:
    ax.axvline(p, color='black', lw=1.0, ls='-', alpha=0.4)
ax.text(4, 1.03, 'period', fontsize=7.5, ha='center', va='bottom', color='#444444')
ax.annotate('', xy=(8, 1.05), xytext=(0, 1.05),
            arrowprops=dict(arrowstyle='<->', color='#444444', lw=1.0))
ax.set_xlim(-0.5, 31.5)
ax.set_ylim(0, 1.15)

plt.tight_layout(pad=2.0)
plt.savefig('/Users/jonathanhill/src/p2p/rule30_subcaseB_figure.pdf', dpi=200,
            bbox_inches='tight', facecolor='white')
plt.savefig('/Users/jonathanhill/src/p2p/rule30_subcaseB_figure.png', dpi=150,
            bbox_inches='tight', facecolor='white')
plt.close()
print("Figure 2 saved.")
