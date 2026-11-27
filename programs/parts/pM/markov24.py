"""Checks for Section 24: Markov joint mixes of the ball kernels k_rho(x, .) = U(B(rho x, 1 - rho |x|)) in the plane.

Part A simulates, for rho = 0.3, 0.5, 0.7 and n = ceil(2/(1-rho)) = 3, 4, 7, the Markov joint mix of the corollary on
balls: each step is the joint mix of Theorem 51 of the uniform distributions on the discs B(rho x_j, 1 - rho |x_j|),
built from the polygon of Lemma 49 (with the grouping of Lemma 1), the radius R = sqrt(V) and the random frame of
Lemma 50.  From X(0) = 0 it runs a burn-in of 200 steps and then T steps, and records the largest |sum_j Y_j(t)|;
Kolmogorov-Smirnov tests that the normalised innovations w = (Y_j(t+1) - rho Y_j(t)) / (1 - rho |Y_j(t)|) of every
coordinate have |w|^2 ~ U[0,1] and an angle ~ U[0, 2 pi); the correlation of |w|^2 with |Y_j(t)|; two-sample tests that
|Y_j|^2, thinned, has the same distribution for all coordinates and for an independent single chain with kernel k_rho;
and the lag-one regression slope of Y_j(t+1) on Y_j(t), which is rho for this kernel.
Part B computes the lower bound of the proposition on the price of smooth masks for these kernels: the average over
the invariant distribution of TV(U(B(c, r)), U(B(c + delta, r))) with r = 1 - rho |y|, for several rho and |delta|,
from a long run of one chain, against the value for independent uniform masks on the disc (rho = 0).
Writes data/markov24.json.
"""
import json, math, time
import numpy as np
from scipy import stats

t0 = time.time()


def polygon(lam):
    """Lemma 49 with the grouping of Lemma 1: vectors v_j in the plane with |v_j| = lam_j and sum 0"""
    n = len(lam)
    k = int(np.argmax(lam))
    others = [j for j in range(n) if j != k]
    tot = lam[others].sum()
    pre = np.concatenate([[0.0], np.cumsum(lam[others])])
    s = int(np.argmin(np.abs(2 * pre - tot)))
    G, H = others[:s], others[s:]
    S, T, lk = pre[s], tot - pre[s], lam[k]
    Ek = np.array([lk, 0.0])
    if S <= 0:
        EG, EH = np.zeros(2), -Ek
    elif T <= 0:
        EG, EH = -Ek, np.zeros(2)
    else:
        c = np.clip((T * T - lk * lk - S * S) / (2 * lk * S), -1.0, 1.0)
        EG = S * np.array([c, math.sqrt(1 - c * c)])
        EH = -Ek - EG
    v = np.zeros((n, 2))
    v[k] = Ek
    for j in G:
        v[j] = lam[j] / S * EG
    for j in H:
        v[j] = lam[j] / T * EH
    return v


def frame(rng):
    """Lemma 50 for j = 2"""
    z1, z2 = rng.normal(size=2), rng.normal(size=2)
    g1 = z1 / np.linalg.norm(z1)
    z2 = z2 - (z2 @ g1) * g1
    return g1, z2 / np.linalg.norm(z2)


def step(x, rho, rng):
    """one step of the Markov joint mix: the joint mix of Theorem 51 of U(B(rho x_j, 1 - rho |x_j|))"""
    lam = 1 - rho * np.linalg.norm(x, axis=1)
    v = polygon(lam)
    g1, g2 = frame(rng)
    R = math.sqrt(rng.random())
    return rho * x + R * (v[:, :1] * g1 + v[:, 1:] * g2)


def single_chain(rho, T, rng, burn=200):
    y = np.zeros(2)
    out = np.empty((T, 2))
    for t in range(burn + T):
        r = 1 - rho * np.linalg.norm(y)
        th = 2 * math.pi * rng.random()
        y = rho * y + r * math.sqrt(rng.random()) * np.array([math.cos(th), math.sin(th)])
        if t >= burn:
            out[t - burn] = y
    return out


def partA(T=20000, burn=200, thin=25):
    rows = []
    pvals = []
    for rho in (0.3, 0.5, 0.7):
        n = math.ceil(2 / (1 - rho) - 1e-12)
        rng = np.random.default_rng(int(rho * 100) + 7)
        x = np.zeros((n, 2))
        for _ in range(burn):
            x = step(x, rho, rng)
        Y = np.empty((T + 1, n, 2)); Y[0] = x
        for t in range(T):
            Y[t + 1] = step(Y[t], rho, rng)
        sumdev = float(np.abs(Y.sum(1)).max())
        norms = np.linalg.norm(Y, axis=2)                               # (T+1, n)
        W = (Y[1:] - rho * Y[:-1]) / (1 - rho * norms[:-1])[..., None]  # normalised innovations
        r2 = (W ** 2).sum(2); ang = np.mod(np.arctan2(W[..., 1], W[..., 0]), 2 * math.pi)
        p_in, corr, slope = [], 0.0, 0.0
        for j in range(n):
            p_in.append(stats.kstest(r2[:, j], "uniform").pvalue)
            p_in.append(stats.kstest(ang[:, j] / (2 * math.pi), "uniform").pvalue)
            corr = max(corr, abs(float(np.corrcoef(r2[:, j], norms[:-1, j])[0, 1])))
            num = (Y[1:, j] * Y[:-1, j]).sum(); den = (Y[:-1, j] ** 2).sum()
            slope = max(slope, abs(float(num / den) - rho))
        ref = single_chain(rho, T, np.random.default_rng(int(rho * 100) + 99))
        refs = (ref[::thin] ** 2).sum(1)
        p_st = []
        base = norms[::thin, 0] ** 2
        for j in range(1, n):
            p_st.append(stats.ks_2samp(base, norms[::thin, j] ** 2).pvalue)
        p_st.append(stats.ks_2samp(base, refs).pvalue)
        pvals += p_in + p_st
        rows.append({"rho": rho, "n": n, "T": T, "sum_dev": sumdev, "p_innov_min": float(min(p_in)),
                     "n_innov_tests": len(p_in), "p_stat_min": float(min(p_st)), "n_stat_tests": len(p_st),
                     "corr_max": corr, "slope_dev_max": slope, "mean_sq": float((norms[1:] ** 2).mean())})
        print(rows[-1], round(time.time() - t0, 1), flush=True)
    m = len(pvals); pmin = min(pvals)
    return {"rows": rows, "tests": m, "pmin": float(pmin), "chance": float(1 - (1 - pmin) ** m)}


def tv_discs(r, d):
    """total variation between the uniform distributions on two discs of radius r whose centres are d apart"""
    r = np.asarray(r, float)
    out = np.ones_like(r)
    m = d < 2 * r
    rr = r[m]
    ov = 2 * rr ** 2 * np.arccos(d / (2 * rr)) - 0.5 * d * np.sqrt(4 * rr ** 2 - d * d)
    out[m] = 1 - ov / (math.pi * rr ** 2)
    return out


def partB(T=200000):
    rows = []
    for rho in (0.0, 0.3, 0.5, 0.7, 0.9):
        y = single_chain(rho, T, np.random.default_rng(int(rho * 100) + 1234))
        r = 1 - rho * np.linalg.norm(y, axis=1)
        row = {"rho": rho, "n_min": math.ceil(2 / (1 - rho) - 1e-12), "mean_sq": float((y ** 2).sum(1).mean())}
        for d in (0.05, 0.1, 0.2):
            row["lb_%g" % d] = float(tv_discs(r, d).mean())
        rows.append(row)
        print(row, round(time.time() - t0, 1), flush=True)
    return rows


if __name__ == "__main__":
    A = partA()
    B = partB()
    json.dump({"partA": A, "partB": B, "seconds": round(time.time() - t0, 1)}, open("data/markov24.json", "w"), indent=1)
    print("done in", round(time.time() - t0, 1), "s")
