#!/usr/bin/env python3
"""
Generate Figure 1 for prize3_paper.tex:
  Left panel:  Rule 30 space-time diagram, n=30 steps from single black cell e_n,
               with the causal cone boundary highlighted.
  Right panel: Same, but with a spike at position k=8 (active m), showing
               how the spike's effect propagates to center (lifting lemma illustration).

Output: rule30_figure.pdf (publication-quality, grayscale + accent colour)
"""
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.colors import ListedColormap
import matplotlib.gridspec as gridspec

# ── helpers ──────────────────────────────────────────────────────────────────

def rule30_step(row):
    """One step of Rule 30. Input/output are 1D arrays; shrinks by 2."""
    l, c, r = row[:-2], row[1:-1], row[2:]
    return l ^ (c | r)


def evolve(init, n):
    """Evolve init for n steps; return list of rows (each shorter by 2 than prev)."""
    rows = [np.array(init, dtype=np.uint8)]
    a = np.array(init, dtype=np.uint8)
    for _ in range(n):
        a = rule30_step(a)
        rows.append(a)
    return rows


def pad_rows(rows, width):
    """Left-align rows into a fixed-width array (pad right with NaN for display)."""
    arr = np.full((len(rows), width), np.nan)
    for i, r in enumerate(rows):
        arr[i, :len(r)] = r
    return arr


def center_rows(rows, total_width):
    """Center each row in a fixed-width array (pad both sides with NaN)."""
    arr = np.full((len(rows), total_width), np.nan)
    for i, r in enumerate(rows):
        start = (total_width - len(r)) // 2
        arr[i, start:start+len(r)] = r
    return arr


# ── figure setup ─────────────────────────────────────────────────────────────

N = 28           # number of steps
W = 2*N + 1      # initial width = 57

# Panel A: single black cell e_N
e_N = np.zeros(W, dtype=np.uint8)
e_N[N] = 1       # center cell
rows_A = evolve(e_N, N)
arr_A = center_rows(rows_A, W)

# Panel B: spike at position m=8 (active, well-studied)
# We run from a spike-at-8 initial condition (same width)
m_spike = 8
e_spike = np.zeros(W, dtype=np.uint8)
e_spike[m_spike] = 1
rows_B = evolve(e_spike, N)
arr_B = center_rows(rows_B, W)

# ── colour maps ──────────────────────────────────────────────────────────────
# 0 = white, 1 = near-black, NaN = white (outside cone)
cmap_bw = ListedColormap(['white', '#1a1a2e'])
cmap_spike = ListedColormap(['white', '#c0392b'])   # red for spike panel

fig = plt.figure(figsize=(10, 7.5))
gs = gridspec.GridSpec(1, 2, wspace=0.14, left=0.07, right=0.97, top=0.91, bottom=0.16)

# ── subplot A: e_N evolution ─────────────────────────────────────────────────
ax1 = fig.add_subplot(gs[0])

# mask NaN for display
A_disp = np.where(np.isnan(arr_A), -1, arr_A)
im1 = ax1.imshow(A_disp, cmap=ListedColormap(['white', 'white', '#1a1a2e']),
                 vmin=-1, vmax=1, aspect='auto',
                 interpolation='nearest', origin='upper')

# draw causal-cone boundary lines
for step in range(N+1):
    left  = (W - (W - 2*step)) // 2
    right = left + (W - 2*step) - 1
    # left boundary line segment
    if step > 0:
        prev_left  = (W - (W - 2*(step-1))) // 2
        prev_right = prev_left + (W - 2*(step-1)) - 1
        ax1.plot([prev_left - 0.5, left - 0.5], [step-1-0.5, step-0.5],
                 color='#e67e22', linewidth=1.2, alpha=0.85)
        ax1.plot([prev_right + 0.5, right + 0.5], [step-1-0.5, step-0.5],
                 color='#e67e22', linewidth=1.2, alpha=0.85)

# mark the center output cell (position 0 in final row = column N in display)
final_row = N
ax1.plot(N, final_row, 'o', color='#e67e22', markersize=6, markeredgecolor='white',
         markeredgewidth=0.8, zorder=5)

ax1.set_title(r'(a) Single black cell $e_n$, $n={}$'.format(N), fontsize=11, pad=6)
ax1.set_xlabel('cell position', fontsize=9)
ax1.set_ylabel('generation', fontsize=9)
ax1.set_xticks([0, N//2, N, 3*N//2, 2*N])
ax1.set_xticklabels(['0', str(N//2), str(N), str(3*N//2), str(2*N)], fontsize=8)
ax1.set_yticks([0, N//2, N])
ax1.set_yticklabels(['0', str(N//2), str(N)], fontsize=8)

# ── subplot B: spike-at-m evolution ──────────────────────────────────────────
ax2 = fig.add_subplot(gs[1])

B_disp = np.where(np.isnan(arr_B), -1, arr_B)
im2 = ax2.imshow(B_disp, cmap=ListedColormap(['white', 'white', '#c0392b']),
                 vmin=-1, vmax=1, aspect='auto',
                 interpolation='nearest', origin='upper')

# mark spike origin
ax2.plot(m_spike, 0, 's', color='#c0392b', markersize=6, markeredgecolor='white',
         markeredgewidth=0.8, zorder=5)

# draw causal-cone boundary of spike (tight cone from position m_spike)
# The spike-m output F(n, m_spike) reads the leftmost cell after n steps from spike
# Mark the center of the full array at each step
for step in range(1, N+1):
    left  = (W - (W - 2*step)) // 2
    prev_left  = (W - (W - 2*(step-1))) // 2
    prev_right = prev_left + (W - 2*(step-1)) - 1
    right = left + (W - 2*step) - 1
    ax2.plot([prev_left - 0.5, left - 0.5], [step-1-0.5, step-0.5],
             color='#7f8c8d', linewidth=0.8, alpha=0.5, linestyle='--')
    ax2.plot([prev_right + 0.5, right + 0.5], [step-1-0.5, step-0.5],
             color='#7f8c8d', linewidth=0.8, alpha=0.5, linestyle='--')

# mark position 0 at final generation (F-value read point)
ax2.plot(N, N, '^', color='#2980b9', markersize=6, markeredgecolor='white',
         markeredgewidth=0.8, zorder=5)

ax2.set_title(r'(b) Spike at $m={}$: $F(n,m)$ = leftmost cell at gen $n$'.format(m_spike),
              fontsize=11, pad=6)
# annotate F-value read location clearly
ax2.annotate(r'$F(n,m)$', xy=(N, N), xytext=(N+5, N-3),
             fontsize=8, color='#2980b9',
             arrowprops=dict(arrowstyle='->', color='#2980b9', lw=1.1))
ax2.set_xlabel('cell position', fontsize=9)
ax2.set_ylabel('generation', fontsize=9)
ax2.set_xticks([0, N//2, N, 3*N//2, 2*N])
ax2.set_xticklabels(['0', str(N//2), str(N), str(3*N//2), str(2*N)], fontsize=8)
ax2.set_yticks([0, N//2, N])
ax2.set_yticklabels(['0', str(N//2), str(N)], fontsize=8)

# ── shared legend ────────────────────────────────────────────────────────────
orange_line = mpatches.Patch(color='#e67e22', label='Causal cone boundary')
red_sq   = mpatches.Patch(color='#1a1a2e', label='Active cell (panel a)')
red_patch = mpatches.Patch(color='#c0392b', label='Active cell (panel b)')
blue_tri = mpatches.Patch(color='#2980b9', label=r'$F(n,m)$ read point (position 0, gen $n$)')

fig.legend(handles=[orange_line, red_sq, red_patch, blue_tri],
           loc='lower center', ncol=2, fontsize=8.5,
           bbox_to_anchor=(0.5, 0.01), frameon=True,
           columnspacing=1.2, handlelength=1.4)

fig.suptitle('Rule~30 Space-Time Diagram: Causal Cone and Spike Propagation',
             fontsize=12, y=0.97)

plt.savefig('/Users/jonathanhill/src/p2p/rule30_figure.pdf', dpi=150, bbox_inches='tight')
plt.savefig('/Users/jonathanhill/src/p2p/rule30_figure.png', dpi=150, bbox_inches='tight')
print("Saved: rule30_figure.pdf and rule30_figure.png")
print(f"Figure size: {fig.get_size_inches()}")
