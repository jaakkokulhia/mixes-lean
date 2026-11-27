"""Trapezoids: the slicing construction of Theorem 5.

T = {(x, y): 0 <= x <= 1, g(x) <= y <= g(x) + h(x)}, g(x) = SHEAR * x, h(x) = q + (1 - q) x (0 <= q <= 1).
Part A  the polygon inequality for chord lengths: on a fine grid of n-tuples with sum n*c (c the centroid
        abscissa), the largest chord is at most the sum of the others (smallest slack reported).
Part B  end-to-end simulation for n = 3, 4, 5: abscissae from the explicit complete mix of the linear density
        (Algorithm 1 of the earlier note, module concave14), ordinates from the joint mix of the uniform
        distributions on the vertical chords (Lemma arch). Reports the largest deviation of the two coordinate
        sums from their constant values and Kolmogorov-Smirnov distances of the first point's abscissa and
        of its relative height (y - g(x))/h(x) from their targets.
Writes data/trap15.json.
"""
import json, os, time, numpy as np
from scipy.stats import kstest
import concave14 as c14

SEED = int(os.environ.get("SEED", "2026")); MC = int(os.environ.get("MC", "200000"))
SHEAR = 0.3
rng = np.random.default_rng(SEED)
out = {"parts": []}
t0 = time.time()

def centroid_x(q):
    # density of the abscissa proportional to h(x) = q + (1-q) x
    return (q / 2 + (1 - q) / 3) / (q + (1 - q) / 2)

# ---------------- Part A ----------------
minslack = np.inf; ntup = 0
for q in np.linspace(0, 1, 41):
    c = centroid_x(q)
    h = lambda x: q + (1 - q) * x
    for n in (3, 4, 5, 6):
        # worst case: largest abscissa x_max, the others summing to n c - x_max; with h affine the sum of
        # the other chords depends only on that sum, so a grid over x_max suffices
        xm = np.linspace(0, 1, 2001)
        rest = n * c - xm
        ok = (rest >= 0) & (rest <= (n - 1) * xm + 1e-15)   # the others lie in [0, x_max]
        others = (n - 1) * q + (1 - q) * rest
        slack = np.where(ok, others - h(xm), np.inf)
        minslack = min(minslack, float(slack.min())); ntup += int(ok.sum())
out["partA"] = dict(cases=ntup, min_slack=minslack)
print("Part A: smallest slack of the polygon inequality", minslack, "over", ntup, "cases", flush=True)

# ---------------- Part B ----------------
for q in (0.0, 0.25, 0.5, 1.0):
    for n in (3, 4, 5):
        P = c14.PLDensity([0.0, 1.0], [q, 1.0], name="linear q=%g" % q)
        S = c14.solve(P)
        X, _ = c14.algorithm(P, S, n, MC, rng)
        g = SHEAR * X; h = q + (1 - q) * X
        poly = np.min(np.sum(h, axis=1) - 2 * np.max(h, axis=1))
        Y = c14.arch_mix(g, g + h, rng)
        sx = X.sum(axis=1); sy = Y.sum(axis=1)
        devx = float(np.max(np.abs(sx - n * P.mu)))
        devy = float(np.max(np.abs(sy - np.sum(g + h / 2, axis=1))))   # = n * (centroid ordinate)
        cy = float(np.mean(np.sum(g + h / 2, axis=1)))
        devy_const = float(np.max(np.abs(np.sum(g + h / 2, axis=1) - cy)))
        x1 = X[:, 0]; v1 = (Y[:, 0] - SHEAR * x1) / (q + (1 - q) * x1)
        cdf = lambda t: (q * t + (1 - q) * t * t / 2) / (q + (1 - q) / 2)
        ksx = kstest(x1, cdf); ksv = kstest(v1, "uniform")
        rec = dict(q=q, n=n, mc=MC, poly_min_slack=float(poly), dev_sum_x=devx, dev_sum_y=max(devy, devy_const),
                   ks_x=float(ksx.statistic), p_x=float(ksx.pvalue), ks_v=float(ksv.statistic), p_v=float(ksv.pvalue),
                   corr_xv=float(np.corrcoef(x1, v1)[0, 1]))
        out["parts"].append(rec)
        print(rec, flush=True)
out["seconds"] = time.time() - t0
json.dump(out, open("data/trap15.json", "w"), indent=1)
print("done in %.1f s" % (time.time() - t0))
