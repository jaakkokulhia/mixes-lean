"""Figure for the note: the peeling of the density with vertices (0,0), (0.2,2), (0.6,3), (1,1)."""
import numpy as np
import matplotlib
matplotlib.use("Agg")
from matplotlib import font_manager
import matplotlib.pyplot as plt
from concave14 import PLDensity, solve

for path in ["/usr/share/texmf/fonts/opentype/public/lm/lmroman10-regular.otf",
             "/usr/share/texmf/fonts/opentype/public/lm/lmroman10-italic.otf"]:
    try:
        font_manager.fontManager.addfont(path)
    except Exception:
        pass
INK, INK2, HAIR = "#0b0b0b", "#52514e", "#e1e0d9"
BLUE, ORANGE = "#2a78d6", "#eb6834"
plt.rcParams.update({"font.family": "Latin Modern Roman", "mathtext.fontset": "cm", "font.size": 8.5,
                     "axes.edgecolor": INK2, "axes.labelcolor": INK2, "xtick.color": INK2,
                     "ytick.color": INK2, "axes.linewidth": 0.6, "xtick.major.width": 0.6,
                     "ytick.major.width": 0.6, "pdf.fonttype": 42})

P = PLDensity([0, 0.2, 0.6, 1], [0, 2, 3, 1])
S = solve(P, n=4000)
U, A, B, beta = S["U"], P.mu - S["l"], P.mu + S["r"], S["beta"]
sw = S["switches"]

def tint(c, t):
    c = np.array([int(c[i:i + 2], 16) for i in (1, 3, 5)]) / 255.0
    return tuple(t * c + (1 - t))

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(150 / 25.4, 64 / 25.4), gridspec_kw=dict(width_ratios=[1.15, 1]))
x = P.xs
h1 = ax1.fill_between(x, 0, P.ys, color=tint(ORANGE, 0.55), lw=0)
h2 = ax1.fill_betweenx(U, A, B, color=tint(BLUE, 0.55), lw=0)
ax1.plot(x, P.ys, color=INK, lw=1.0)
ax1.axvline(P.mu, color=INK2, lw=0.6, ls=(0, (4, 3)))
for i, s in enumerate(sw):
    ax1.axhline(s, color=INK2, lw=0.5, ls=(0, (1, 2)))
    ax1.text(1.01, s, r"$U_%d$" % (i + 1), color=INK2, va="center", ha="left")
ax1.plot([P.mu], [P.fmu], "o", ms=3.0, color=INK)
ax1.text(P.mu + 0.015, 0.05, r"$\mu$", color=INK2)
ax1.set_xlim(0, 1); ax1.set_ylim(0, 1.6)
ax1.set_xlabel(r"$x$"); ax1.set_ylabel(r"$f(x)$; level $U$")
for spine in ("top", "right"):
    ax1.spines[spine].set_visible(False)

edges = [0.0] + list(sw) + [P.fmu]
first = S["first"]
ax2.plot(U, beta, color=INK, lw=1.1)
for i in range(len(edges) - 1):
    side = first if i % 2 == 0 else ("R" if first == "L" else "L")
    mid = 0.5 * (edges[i] + edges[i + 1])
    ax2.text(mid, 3.04, "left end\ncut" if side == "L" else "right end\ncut", color=INK2, ha="center",
             va="bottom", fontsize=7.5, linespacing=1.0)
for i, s in enumerate(sw):
    ax2.axvline(s, color=INK2, lw=0.5, ls=(0, (1, 2)))
    ax2.text(s + 0.012, 2.83, r"$U_%d$" % (i + 1), color=INK2, ha="left", va="center")
ax2.axhline(3, color=HAIR, lw=0.8, zorder=0)
ax2.set_xlim(0, P.fmu); ax2.set_ylim(1.9, 3.25)
ax2.set_yticks([2.0, 2.2, 2.4, 2.6, 2.8, 3.0])
ax2.set_xlabel(r"level $U$"); ax2.set_ylabel(r"$\beta(U)$")
for spine in ("top", "right"):
    ax2.spines[spine].set_visible(False)
fig.legend([h2, h1], ["horizontal parts (uniform distributions)", "vertical parts (atoms)"], loc="upper center",
           ncol=2, frameon=False, fontsize=8, labelcolor=INK, bbox_to_anchor=(0.5, 1.0))
fig.tight_layout(w_pad=2.5, rect=(0, 0, 1, 0.92))
fig.savefig("fig_peel.pdf")
print("switch levels", sw, "mu", P.mu, "f(mu)", P.fmu)
