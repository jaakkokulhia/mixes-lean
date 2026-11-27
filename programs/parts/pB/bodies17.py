"""Convex bodies: checks of the sections on balls, products, frusta and bodies with homothetic sections
(Part IV of the merged paper).

Part A  exact (rational arithmetic):
  A1  the constants of frusta: mu_{k,q} = k(1-q^(k+1))/((k+1)(1-q^k)) and a_{k,q} = (1-q)/(1-mu_{k,q}); the
      identity a_{k,q} = (k+1) sum_j q^j / sum_j (j+1) q^j, the bounds k/(k+1) <= mu < 1, 2 < a <= k+1 (k >= 2)
      and the thresholds of the corollaries on frusta, on a grid of rational q;
  A2  the slicing of truncated simplices: the moments E[z^alpha] of the construction (level with density
      proportional to s^(k-1) on [q,1], fibre the construction for the (k-1)-simplex) against the closed form
      (1-q^(k+|alpha|))/(1-q^k) * k! alpha_1! ... alpha_k! / (k+|alpha|)! of the uniform distribution;
  A3  the joint mixes of Part II in the setting of the frustum theorem: random rational q and scales with
      (1-q) max lambda <= (1-mu) sum lambda, a share with equality; the level laws H_i are replaced by step
      distributions with the same right end (1-q) lambda_i and the same mean (1-mu) lambda_i, the joint mix of
      Part II is built exactly, and its weights, its sum and its marginals are checked exactly (as jm12.part3);
  A4  the mean of a density proportional to g^(d-1) on [0,1], g concave and nonnegative, is at least 1/(d+1):
      exact for random piecewise-linear concave g and d <= 6 (the integrals are polynomials).
Part B  simulation (floating point): the polygons of the polygon lemma; joint mixes of scaled balls; complete mixes
      of balls, truncated simplices, frusta over cubes and over balls, prisms and cylinders, a half-ball and a
      paraboloid of revolution (homothetic sections), and the join of two discs; joint mixes of scaled truncated
      simplices. Sums, membership and Kolmogorov-Smirnov tests of levels and fibres.
Writes data/bodies17.json.
Environment: KMOM (default 5), DEGMOM (5), NLEVEL (600), NCONC (300), MC (40000), MCB (200000), SEED (2026).
"""
import itertools, json, math, os, random, sys, time
from fractions import Fraction as Fr
import numpy as np
from scipy.stats import kstest, beta as Beta

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "p12"))
sys.path.insert(0, os.path.join(HERE, "..", "p14"))
sys.path.insert(0, os.path.join(HERE, "..", "pS"))
import jm12
from concave14 import arch_mix
import cones16

KMOM = int(os.environ.get("KMOM", 5)); DEGMOM = int(os.environ.get("DEGMOM", 5))
NLEVEL = int(os.environ.get("NLEVEL", 600)); NCONC = int(os.environ.get("NCONC", 300))
MC = int(os.environ.get("MC", 40000)); MCB = int(os.environ.get("MCB", 200000)); SEED = int(os.environ.get("SEED", 2026))


# ------------------------------------------------------------------ constants of frusta
def mu_kq(k, q):
    """Mean of the level of the unit frustum: density proportional to s^(k-1) on [q, 1]."""
    if q == 0:
        return Fr(k, k + 1) if isinstance(q, Fr) else k / (k + 1)
    return k * (1 - q ** (k + 1)) / ((k + 1) * (1 - q ** k))

def a_kq(k, q):
    return (1 - q) / (1 - mu_kq(k, q))


# ------------------------------------------------------------------ Part A
def partA1():
    t0 = time.time(); count = 0; thr = {}
    for k in range(1, 11):
        for i in range(0, 60):
            q = Fr(i, 60)
            mu, a = mu_kq(k, q), a_kq(k, q)
            assert a == (k + 1) * sum(q ** j for j in range(k)) / sum((j + 1) * q ** j for j in range(k))
            assert Fr(k, k + 1) <= mu < 1 and a <= k + 1 and (a == k + 1) == (q == 0 or k == 1)
            if k >= 2:
                assert a > 2
            # truncated simplex: n-CM iff n >= max(a, k/mu); this threshold is k+1
            n_simplex = max(math.ceil(a), math.ceil(Fr(k) / mu))
            assert n_simplex == k + 1
            # frusta over cubes and balls (k >= 2): n-CM iff n >= max(a, 2/mu) = a (2/mu <= 3 <= ceil(a))
            if k >= 2:
                assert 2 / mu <= 3 and math.ceil(a) >= 3
                thr.setdefault(k, {})[str(q)] = math.ceil(a)
            count += 1
    # q at which the threshold of frusta over cubes or balls drops below k+1, for the table
    for k in range(2, 11):                                           # a_{k,q} decreases in q on the grid
        vals = [a_kq(k, Fr(i, 60)) for i in range(60)]
        assert all(x > y for x, y in zip(vals, vals[1:]))
    table = {}
    for k in range(2, 9):
        row = []
        for n in range(3, k + 2):
            # least q in the grid 0, 1/1000, ... with ceil(a_{k,q}) <= n
            qs = [Fr(i, 1000) for i in range(0, 1000)]
            ok = [q for q in qs if a_kq(k, q) <= n]
            row.append(str(ok[0]) if ok else None)
        table[k] = row
    out = dict(cases=count, k_max=10, grid=60, first_q=table, seconds=round(time.time() - t0, 2))
    print("Part A1:", {kk: v for kk, v in out.items() if kk != "first_q"}, flush=True)
    return out

def moment_frustum_closed(alpha, q):
    k = len(alpha); D = sum(alpha)
    return (1 - q ** (k + D)) / (1 - q ** k) * cones16.moment_closed(alpha)

def moment_frustum_rec(alpha, q):
    """E[z^alpha], z = S (V, 1 - sum V): S with density proportional to s^(k-1) on [q, 1], V the construction for the
    (k-1)-simplex (moments by cones16.moment_rec, which uses only the slicing of cones)."""
    k = len(alpha); head, a = alpha[:-1], alpha[-1]; D = sum(alpha)
    ES = Fr(k, k + D) * (1 - q ** (k + D)) / (1 - q ** k)          # E[S^D]
    tot = Fr(0)
    for j in range(a + 1):
        cj = math.comb(a, j) * (-1) ** j
        for beta in cones16.compositions(j, k - 1):
            tot += cj * cones16.multinomial(j, beta) * cones16.moment_rec(tuple(h + b for h, b in zip(head, beta)))
    return ES * tot

def partA2():
    t0 = time.time(); count = 0
    qs = [Fr(1, 3), Fr(1, 2), Fr(5, 7), Fr(9, 10)]
    for q in qs:
        for k in range(1, KMOM + 1):
            for deg in range(DEGMOM + 1):
                for alpha in cones16.compositions(deg, k):
                    assert moment_frustum_rec(alpha, q) == moment_frustum_closed(alpha, q), (q, k, alpha)
                    count += 1
    out = dict(k_max=KMOM, degree_max=DEGMOM, q_values=[str(q) for q in qs], moments=count, seconds=round(time.time() - t0, 2))
    print("Part A2:", out, flush=True)
    return out

def step_law_frustum(lam, k, q, rng):
    """Finite slab law with right end B = (1-q) lam and mean (1-mu) lam (slab mean 2 (1-mu) lam = (2/a) B)."""
    B = (1 - q) * lam
    target = 2 / a_kq(k, q)                                     # slab mean / B, in (2/(k+1), 1] ; = 1 iff k = 1
    if target == 1:
        return {B: Fr(1)}
    J = 2 if rng.random() < 1 / 3 else 1
    rs = sorted(set(Fr(rng.randint(1, 59), 60) * target for _ in range(J)))
    ws = [Fr(rng.randint(1, 9)) for _ in rs]
    tot = sum(ws); ws = [w / tot for w in ws]
    rbar = sum(r * w for r, w in zip(rs, ws))
    wt = (target - rbar) / (1 - rbar)
    law = {B * r: (1 - wt) * w for r, w in zip(rs, ws)}
    law[B] = law.get(B, 0) + wt
    return law

def frustum_scales(k, q, n, rng):
    mu, a = mu_kq(k, q), a_kq(k, q)
    mode = rng.random()
    if n >= a and mode < 0.2:
        return [Fr(1)] * n, "equal"
    while True:
        lams = [Fr(rng.randint(1, 40), 40) for _ in range(n)]
        if mode < 0.55:
            others = lams[:-1]
            top = (1 - mu) * sum(others) / ((1 - q) - (1 - mu))     # (1-q) top = (1-mu) (sum others + top)
            if top >= max(others):
                lams[-1] = top
                return lams, "tight"
            continue
        if (1 - q) * max(lams) <= (1 - mu) * sum(lams):
            return lams, ("tight" if (1 - q) * max(lams) == (1 - mu) * sum(lams) else "generic")

def partA3():
    t0 = time.time(); rng = random.Random(SEED + 2)
    done = 0; modes = {}; nseg = 0; ntup = 0; kinds = {}; cells = 0; nmax = 0
    while done < NLEVEL:
        k = rng.randint(2, 4)
        q = Fr(rng.randint(1, 9), 10)
        a = a_kq(k, q)
        n = rng.randint(max(3, math.ceil(a)), max(3, math.ceil(a)) + 2)
        lams, mode = frustum_scales(k, q, n, rng)
        pis = [step_law_frustum(l, k, q, rng) for l in lams]
        s, segs, st = jm12.assemble(pis)
        assert s == (1 - mu_kq(k, q)) * sum(lams)
        assert max(max(pi) for pi in pis) == (1 - q) * max(lams) <= s
        cells += jm12.check_mixture(segs, s, [jm12.slab_target(pi) for pi in pis])
        for kk, v in st["stats"].items():
            key = kk.split("/")[0]; kinds[key] = kinds.get(key, 0) + v
        done += 1; modes[mode] = modes.get(mode, 0) + 1
        nseg += len(segs); ntup += st["tuples"]; nmax = max(nmax, n)
    out = dict(cases=done, modes=modes, k_max=4, n_max=nmax, tuples=ntup, segments=nseg, cells=cells, leaf_kinds=kinds,
               seconds=round(time.time() - t0, 1))
    print("Part A3:", out, flush=True)
    return out

def poly_int(coefs, lo, hi):
    """Integral over [lo, hi] of the polynomial with coefficients coefs (constant first)."""
    return sum(c * (hi ** (i + 1) - lo ** (i + 1)) / (i + 1) for i, c in enumerate(coefs))

def poly_mul(p, r):
    out = [Fr(0)] * (len(p) + len(r) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(r):
            out[i + j] += x * y
    return out

def partA4():
    """Mean of g^(d-1) on [0,1] >= 1/(d+1) for random piecewise-linear concave g >= 0 (exact)."""
    t0 = time.time(); rng = random.Random(SEED + 4); worst = {}; done = 0
    while done < NCONC:
        d = rng.randint(2, 6); m = rng.randint(1, 5)
        xs = [Fr(0)] + sorted(set(Fr(rng.randint(1, 99), 100) for _ in range(m - 1))) + [Fr(1)]
        # concave: decreasing slopes; values >= 0
        slopes = sorted((Fr(rng.randint(-40, 40), 10) for _ in range(len(xs) - 1)), reverse=True)
        ys = [Fr(rng.randint(0, 30), 10)]
        for i in range(len(xs) - 1):
            ys.append(ys[-1] + slopes[i] * (xs[i + 1] - xs[i]))
        shift = -min(ys)
        if shift > 0:
            ys = [y + shift for y in ys]
        if max(ys) == 0:
            continue
        done += 1
        mass = Fr(0); mom = Fr(0)
        for i in range(len(xs) - 1):
            x0, x1, y0, y1 = xs[i], xs[i + 1], ys[i], ys[i + 1]
            sl = (y1 - y0) / (x1 - x0)
            lin = [y0 - sl * x0, sl]
            p = [Fr(1)]
            for _ in range(d - 1):
                p = poly_mul(p, lin)
            mass += poly_int(p, x0, x1); mom += poly_int(poly_mul(p, [Fr(0), Fr(1)]), x0, x1)
        mean = mom / mass
        assert Fr(1, d + 1) <= mean <= Fr(d, d + 1), (xs, ys, d, mean)
        r = min(mean - Fr(1, d + 1), Fr(d, d + 1) - mean)
        worst[d] = min(worst.get(d, Fr(1)), r)
    out = dict(cases=NCONC, min_slack={d: float(v) for d, v in sorted(worst.items())}, seconds=round(time.time() - t0, 2))
    print("Part A4:", out, flush=True)
    return out


# ------------------------------------------------------------------ Part B: simulation
def polygon(lam):
    """The vectors v_i in R^2 of the polygon lemma (from the triangle of Lemma 1): |v_i| = lam_i, sum v_i = 0."""
    lam = np.asarray(lam, float); n = len(lam)
    k = int(np.argmax(lam)); others = [j for j in range(n) if j != k]
    lo = lam[others]; pref = np.concatenate([[0.0], np.cumsum(lo)]); L = pref[-1]
    s = int(np.argmin(np.abs(2 * pref - L))); S = pref[s]; T = L - S; lk = lam[k]
    x = (lk ** 2 + T ** 2 - S ** 2) / (2 * lk)
    # y = (T^2 - x^2)^(1/2) in the factored form of Heron's formula, which is stable when the triangle is flat
    y = math.sqrt(max((S + T - lk) * (S - T + lk) * (lk + T - S) * (lk + T + S), 0.0)) / (2 * lk)
    EG = np.array([x - lk, y]) if S > 0 else np.zeros(2)
    EH = -np.array([x, y]) if T > 0 else np.zeros(2)
    v = np.zeros((n, 2)); v[k] = [lk, 0.0]
    for idx, j in enumerate(others):
        if idx < s:
            v[j] = lam[j] / S * EG if S > 0 else 0.0
        else:
            v[j] = lam[j] / T * EH if T > 0 else 0.0
    return v

def random_frame(N, j, rng):
    """Gram-Schmidt of two independent standard normal vectors in R^j: (g1, g2), each of shape (N, j)."""
    Z1 = rng.normal(size=(N, j)); Z2 = rng.normal(size=(N, j))
    g1 = Z1 / np.linalg.norm(Z1, axis=1, keepdims=True)
    Z2 = Z2 - (Z2 * g1).sum(1, keepdims=True) * g1
    g2 = Z2 / np.linalg.norm(Z2, axis=1, keepdims=True)
    return g1, g2

def ball_fibres(sig, j, rng, R=None):
    """Joint mixes of U(sig_i B_j) for the rows of sig (N, n) with 2 max <= sum; j >= 2; returns (N, n, j)."""
    N, n = sig.shape
    assert np.all(2 * sig.max(1) <= sig.sum(1) * (1 + 1e-12)), "polygon inequality fails"
    V = np.stack([polygon(row) for row in sig])                     # (N, n, 2)
    if R is None:
        R = rng.random(N) ** (1.0 / j)
    g1, g2 = random_frame(N, j, rng)
    return R[:, None, None] * (V[:, :, 0, None] * g1[:, None, :] + V[:, :, 1, None] * g2[:, None, :])

def ks_list(tests):
    ps = [kstest(x, cdf).pvalue for x, cdf in tests]
    return len(ps), float(min(ps))

def part_polygon(rng):
    worst = 0.0; m = 0
    while m < 20000:
        n = int(rng.integers(2, 10)); lam = rng.random(n)
        if rng.random() < 0.3:
            lam[-1] = lam[:-1].sum()                                # tight case: 2 max = sum
        if 2 * lam.max() > lam.sum() * (1 + 1e-12):
            continue
        v = polygon(lam)
        worst = max(worst, float(np.abs(np.linalg.norm(v, axis=1) - lam).max()), float(np.abs(v.sum(0)).max()))
        m += 1
    return dict(cases=m, max_error=worst)

def sim_balls(rng):
    rows = []
    for j in (2, 3, 5):
        for n in (2, 3, 4, 5):
            lam = np.ones(n)
            X = ball_fibres(np.tile(lam, (MCB, 1)), j, rng)
            rows.append(ball_row("ball", j, n, X, lam, rng))
    for j in (2, 3):
        lam = np.array([1.0, 0.8, 0.5, 0.4, 0.3])
        X = ball_fibres(np.tile(lam, (MCB, 1)), j, rng)
        rows.append(ball_row("scaled balls", j, len(lam), X, lam, rng))
    return rows

def ball_row(name, j, n, X, lam, rng):
    tests = []
    for i in range(n):
        Y = X[:, i] / lam[i]
        tests.append(((np.linalg.norm(Y, axis=1)) ** j, lambda t: np.clip(t, 0, 1)))
        tests.append((Y[:, 0] ** 2, Beta(0.5, (j + 1) / 2).cdf) if j >= 2 else (Y[:, 0], lambda t: np.clip((t + 1) / 2, 0, 1)))
    m, pmin = ks_list(tests)
    inside = float((np.linalg.norm(X, axis=2) / lam[None, :] - 1).max())
    return dict(body=name, d=j, n=n, samples=len(X), max_sum_dev=float(np.abs(X.sum(1)).max()), outside=inside,
                tests=m, min_p=pmin)

def law_frustum_level(lam, k, q):
    """The law H of T = lam - S for the frustum of scale lam: density k (lam - t)^(k-1) / (lam^k (1-q^k)) on
    [0, (1-q) lam], as used by jm12.sample_algorithm (a draw from its slab measure)."""
    B = (1 - q) * lam; mu = (1 - mu_kq(k, q)) * lam
    c = k / (lam ** k * (1 - q ** k))
    def draw(rng):
        if k == 1:
            return B
        S = lam * (q ** k + (1 - q ** k) * rng.random()) ** (1.0 / k)
        T = lam - S
        Y = rng.random() * c * (lam - T) ** (k - 1)               # uniform point below the graph of the density
        if Y <= c * (lam - B) ** (k - 1):
            return B
        return min(B, lam - (Y / c) ** (1.0 / (k - 1)))
    cdf = lambda x: ((lam ** k - (lam - np.clip(x, 0, B)) ** k) / (lam ** k * (1 - q ** k)))
    return dict(name="frustum level", B=B, mu=mu, draw=draw, cdf=cdf)

def frustum_levels(lams, k, q, rng):
    laws = [law_frustum_level(l, k, q) for l in lams]
    T, kinds = jm12.sample_algorithm(laws, 1, rng)
    return np.asarray(lams, float) - T[0]

def level_cdf(k, q):
    return lambda s: np.clip((np.clip(s, q, 1) ** k - q ** k) / (1 - q ** k), 0, 1)

def sim_truncated_simplex(k, q, lams, N, rng, name="truncated simplex"):
    """Joint mix of U(lam_i Delta_k^q), Delta_k^q = {x >= 0, q <= sum x <= 1} in R^k."""
    lams = np.asarray(lams, float); n = len(lams)
    Z = np.empty((N, n, k))
    for t in range(N):
        S = frustum_levels(lams, k, q, rng)
        if k == 1:
            Z[t] = S[:, None]
        else:
            w = cones16.simplex_mix(S, k - 1, rng)                  # joint mix of U(S_i Delta_{k-1})
            Z[t] = np.concatenate([w, (S - w.sum(1))[:, None]], 1)
    mu = float(mu_kq(k, Fr(q).limit_denominator(1000)))
    target = mu * lams.sum() / k
    S = Z.sum(2) / lams[None, :]
    tests = [(S[:, i], level_cdf(k, q)) for i in range(n)]
    if k >= 2:
        Y = Z / (S * lams[None, :])[:, :, None]
        tests += [(Y[:, i, j], Beta(1, k - 1).cdf) for i in range(n) for j in range(k)]
    m, pmin = ks_list(tests)
    slack = min(float(Z.min()), float((S - q).min()), float((1 - S).min()))
    return dict(body=name, d=k, q=q, n=n, samples=N, max_sum_dev=float(np.abs(Z.sum(1) - target).max()),
                min_coord=slack, tests=m, min_p=pmin)

def sim_frustum_cube(d, q, n, N, rng):
    """Frustum {(y, s): q <= s <= 1, 0 <= y_j <= s} of the pyramid over the cube [0,1]^(d-1)."""
    S = np.array([frustum_levels(np.ones(n), d, q, rng) for _ in range(N)])
    Y = np.stack([arch_mix(np.zeros_like(S), S, rng) for _ in range(d - 1)], 2)
    mu = float(mu_kq(d, Fr(q).limit_denominator(1000)))
    sums = np.concatenate([Y.sum(1), S.sum(1)[:, None]], 1)
    target = np.array([n * mu / 2] * (d - 1) + [n * mu])
    U = Y / S[:, :, None]
    tests = [(S[:, i], level_cdf(d, q)) for i in range(n)]
    tests += [(U[:, i, j], lambda t: np.clip(t, 0, 1)) for i in range(n) for j in range(d - 1)]
    m, pmin = ks_list(tests)
    slack = min(float(Y.min()), float((S[:, :, None] - Y).min()), float((S - q).min()), float((1 - S).min()))
    return dict(body="frustum over a cube", d=d, q=q, n=n, samples=N, max_sum_dev=float(np.abs(sums - target).max()),
                min_coord=slack, tests=m, min_p=pmin)

def sim_frustum_ball(d, q, n, N, rng):
    """Truncated circular cone {(y, s): q <= s <= 1, |y| <= s}, y in R^(d-1)."""
    S = np.array([frustum_levels(np.ones(n), d, q, rng) for _ in range(N)])
    if d - 1 >= 2:
        Y = ball_fibres(S, d - 1, rng)
    else:
        Y = arch_mix(-S, S, rng)[:, :, None]
    mu = float(mu_kq(d, Fr(q).limit_denominator(1000)))
    sums = np.concatenate([Y.sum(1), S.sum(1)[:, None]], 1)
    target = np.array([0.0] * (d - 1) + [n * mu])
    rad = np.linalg.norm(Y, axis=2) / S
    tests = [(S[:, i], level_cdf(d, q)) for i in range(n)]
    tests += [(rad[:, i] ** (d - 1), lambda t: np.clip(t, 0, 1)) for i in range(n)]
    if d - 1 >= 2:
        tests += [((Y[:, i, 0] / S[:, i]) ** 2, Beta(0.5, d / 2).cdf) for i in range(n)]
    m, pmin = ks_list(tests)
    slack = min(float((1 - rad).min()), float((S - q).min()), float((1 - S).min()))
    return dict(body="frustum over a ball", d=d, q=q, n=n, samples=N, max_sum_dev=float(np.abs(sums - target).max()),
                min_coord=slack, tests=m, min_p=pmin)

def sim_prism(n, N, rng):
    """Triangular prism Delta_2 x [0,1] (d = 3): product of the simplex mix and Lemma 1."""
    W = np.array([cones16.simplex_mix(np.ones(n), 2, rng) for _ in range(N)])          # (N, n, 2)
    H = arch_mix(np.zeros((N, n)), np.ones((N, n)), rng)
    bary = np.concatenate([W, 1 - W.sum(2, keepdims=True)], 2)
    sums = np.concatenate([W.sum(1), H.sum(1)[:, None]], 1)
    target = np.array([n / 3, n / 3, n / 2])
    tests = [(bary[:, i, j], Beta(1, 2).cdf) for i in range(n) for j in range(3)] + [(H[:, i], lambda t: np.clip(t, 0, 1)) for i in range(n)]
    m, pmin = ks_list(tests)
    return dict(body="triangular prism", d=3, q=None, n=n, samples=N, max_sum_dev=float(np.abs(sums - target).max()),
                min_coord=min(float(bary.min()), float(H.min()), float((1 - H).min())), tests=m, min_p=pmin)

def sim_cylinder(n, N, rng):
    X = ball_fibres(np.ones((N, n)), 2, rng)
    H = arch_mix(np.zeros((N, n)), np.ones((N, n)), rng)
    sums = np.concatenate([X.sum(1), H.sum(1)[:, None]], 1)
    target = np.array([0.0, 0.0, n / 2])
    rad = np.linalg.norm(X, axis=2)
    tests = [(rad[:, i] ** 2, lambda t: np.clip(t, 0, 1)) for i in range(n)] + [(H[:, i], lambda t: np.clip(t, 0, 1)) for i in range(n)]
    m, pmin = ks_list(tests)
    return dict(body="cylinder", d=3, q=None, n=n, samples=N, max_sum_dev=float(np.abs(sums - target).max()),
                min_coord=min(float((1 - rad).min()), float(H.min()), float((1 - H).min())), tests=m, min_p=pmin)

def law_halfball_level():
    """Level of the half-ball in R^3: density (3/2)(1 - s^2) on [0, 1] (non-increasing); slab draw."""
    c = 1.5
    def draw(rng):
        while True:
            s = rng.random()
            if rng.random() <= 1 - s * s:
                break
        Y = rng.random() * c * (1 - s * s)
        return math.sqrt(max(0.0, 1 - Y / c))
    return dict(name="half-ball level", B=1.0, mu=3 / 8, draw=draw, cdf=lambda x: np.clip(1.5 * (x - x ** 3 / 3), 0, 1))

def sim_halfball(n, N, rng):
    """Half-ball {(s, y): 0 <= s <= 1, |y| <= sqrt(1 - s^2)} in R^3: levels by Part II, discs by the polygon lemma."""
    law = law_halfball_level()
    S = np.array([jm12.sample_algorithm([law] * n, 1, rng)[0][0] for _ in range(N)])
    r = np.sqrt(np.clip(1 - S ** 2, 0, None))
    Y = ball_fibres(r, 2, rng)
    sums = np.concatenate([S.sum(1)[:, None], Y.sum(1)], 1)
    target = np.array([n * 3 / 8, 0.0, 0.0])
    rad = np.linalg.norm(Y, axis=2) / np.where(r > 0, r, 1)
    ang = (np.arctan2(Y[:, :, 1], Y[:, :, 0]) / (2 * np.pi)) % 1.0
    tests = [(S[:, i], law["cdf"]) for i in range(n)] + [(rad[:, i] ** 2, lambda t: np.clip(t, 0, 1)) for i in range(n)]
    tests += [(ang[:, i], lambda t: np.clip(t, 0, 1)) for i in range(n)]
    m, pmin = ks_list(tests)
    slack = min(float(S.min()), float((1 - S).min()), float((1 - (S ** 2 + np.linalg.norm(Y, axis=2) ** 2)).min()))
    return dict(body="half-ball", d=3, q=None, n=n, samples=N, max_sum_dev=float(np.abs(sums - target).max()),
                min_coord=slack, tests=m, min_p=pmin)

def sim_paraboloid(n, N, rng):
    """Paraboloid of revolution {(s, y): |y|^2 <= s <= 1} in R^3: level density 2s on [0,1], T = 1 - S power law."""
    law = jm12.law_power(1, 1.0)
    T = np.array([jm12.sample_algorithm([law] * n, 1, rng)[0][0] for _ in range(N)])
    S = 1 - T
    r = np.sqrt(np.clip(S, 0, None))
    Y = ball_fibres(r, 2, rng)
    sums = np.concatenate([S.sum(1)[:, None], Y.sum(1)], 1)
    target = np.array([n * 2 / 3, 0.0, 0.0])
    rad = np.linalg.norm(Y, axis=2) / np.where(r > 0, r, 1)
    tests = [(S[:, i], lambda s: np.clip(s, 0, 1) ** 2) for i in range(n)] + [(rad[:, i] ** 2, lambda t: np.clip(t, 0, 1)) for i in range(n)]
    m, pmin = ks_list(tests)
    slack = min(float(S.min()), float((1 - S).min()), float((S - np.linalg.norm(Y, axis=2) ** 2).min()))
    return dict(body="paraboloid", d=3, q=None, n=n, samples=N, max_sum_dev=float(np.abs(sums - target).max()),
                min_coord=slack, tests=m, min_p=pmin)

def sim_join_discs(n, N, rng):
    """Join of two discs: {((1-t)u, t v, t): u, v in B_2, 0 <= t <= 1} in R^5. Level t ~ Beta(3,3), mixed through
    the slabs [1/2 - w, 1/2 + w] of its density and Lemma 1; fibres by the polygon lemma."""
    t0 = rng.beta(3, 3, N); Yh = rng.random(N) * 30 * (t0 * (1 - t0)) ** 2
    w = np.sqrt(np.clip(0.25 - np.sqrt(Yh / 30), 0, None))
    th = arch_mix(np.repeat((0.5 - w)[:, None], n, 1), np.repeat((0.5 + w)[:, None], n, 1), rng)
    U = ball_fibres(1 - th, 2, rng); V = ball_fibres(th, 2, rng)
    sums = np.concatenate([U.sum(1), V.sum(1), th.sum(1)[:, None]], 1)
    target = np.array([0, 0, 0, 0, n / 2])
    ru = np.linalg.norm(U, axis=2) / (1 - th); rv = np.linalg.norm(V, axis=2) / th
    tests = [(th[:, i], Beta(3, 3).cdf) for i in range(n)] + [(ru[:, i] ** 2, lambda t: np.clip(t, 0, 1)) for i in range(n)]
    tests += [(rv[:, i] ** 2, lambda t: np.clip(t, 0, 1)) for i in range(n)]
    m, pmin = ks_list(tests)
    slack = min(float((1 - ru).min()), float((1 - rv).min()), float(th.min()), float((1 - th).min()))
    return dict(body="join of two discs", d=5, q=None, n=n, samples=N, max_sum_dev=float(np.abs(sums - target).max()),
                min_coord=slack, tests=m, min_p=pmin)

def partB():
    t0 = time.time(); rng = np.random.default_rng(SEED + 5); pyr = random.Random(SEED + 6); rows = []
    poly = part_polygon(rng); print("Part B polygons:", poly, flush=True)
    for r in sim_balls(rng):
        rows.append(r); print("Part B:", r, flush=True)
    for k, q in ((2, 0.3), (2, 0.7), (3, 0.3), (3, 0.7), (4, 0.5)):
        r = sim_truncated_simplex(k, q, np.ones(k + 1), MC, rng); rows.append(r); print("Part B:", r, flush=True)
    # joint mix of scaled truncated simplices: k = 3, q = 1/2; scales with both conditions of the corollary
    k, q = 3, Fr(1, 2); mu, a = mu_kq(k, q), a_kq(k, q)
    lams = [Fr(1), Fr(9, 10), Fr(4, 5), Fr(7, 10), Fr(1, 2)]
    assert (1 - q) * max(lams) <= (1 - mu) * sum(lams) and k * max(lams) <= mu * sum(lams)
    r = sim_truncated_simplex(k, float(q), np.array([float(l) for l in lams]), MC, rng, "scaled truncated simplices")
    rows.append(r); print("Part B:", r, flush=True)
    for d, q, ns in ((3, 0.5, (3, 4)), (4, 0.5, (3, 4))):
        for n in ns:
            r = sim_frustum_cube(d, q, n, MC, rng); rows.append(r); print("Part B:", r, flush=True)
            r = sim_frustum_ball(d, q, n, MC, rng); rows.append(r); print("Part B:", r, flush=True)
    for n in (3, 4):
        r = sim_prism(n, MC, rng); rows.append(r); print("Part B:", r, flush=True)
    for n in (2, 3):
        r = sim_cylinder(n, MCB, rng); rows.append(r); print("Part B:", r, flush=True)
    for n in (4, 5):
        r = sim_halfball(n, MC, rng); rows.append(r); print("Part B:", r, flush=True)
    for n in (3, 4):
        r = sim_paraboloid(n, MC, rng); rows.append(r); print("Part B:", r, flush=True)
    for n in (4, 5):
        r = sim_join_discs(n, MCB, rng); rows.append(r); print("Part B:", r, flush=True)
    m = sum(r["tests"] for r in rows); pmin = min(r["min_p"] for r in rows)
    out = dict(polygons=poly, rows=rows, tests=m, min_p=pmin, chance_min_p=1 - (1 - pmin) ** m,
               seconds=round(time.time() - t0, 1))
    print("Part B: tests", m, "smallest p", pmin, flush=True)
    return out


if __name__ == "__main__":
    t0 = time.time()
    OUT = dict(partA1=partA1(), partA2=partA2(), partA4=partA4())
    OUT["partB"] = partB()
    OUT["partA3"] = partA3()
    OUT["seconds"] = round(time.time() - t0, 1)
    OUT["settings"] = dict(KMOM=KMOM, DEGMOM=DEGMOM, NLEVEL=NLEVEL, NCONC=NCONC, MC=MC, MCB=MCB, SEED=SEED)
    os.makedirs(os.path.join(HERE, "data"), exist_ok=True)
    with open(os.path.join(HERE, "data", "bodies17.json"), "w") as fh:
        json.dump(OUT, fh, indent=1, default=str)
    print("all checks passed in %.0f s" % OUT["seconds"])
