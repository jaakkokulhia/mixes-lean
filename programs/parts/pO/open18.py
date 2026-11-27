"""Verification program for the section on one-dimensional projections, bipyramids, and what remains of
Open Problem 5.

Part A  the theorem on densities with a concave p-th root: the peeling of Part III for test densities f = g^p
        with g concave, for the densities of one-dimensional projections of polytopes in R^3, and for random
        ones; largest ratio beta along the peeling against p + 2; Monte Carlo of Algorithm 37 at n = p + 2.
Part B  the lemma on the levels: alpha_k for the bipyramids, k = 3..KMAX, by exact antiderivatives; its sign,
        its mass and the identity alpha + 2 b = 3 n; the closed form for k = 3; the condition (*) for examples.
Part C  Monte Carlo of the complete mixes of the theorem on bipyramids: regular octahedron (n = 3 and 5),
        double cone over a disc, bipyramid over a cube in R^4, elongated octahedron.
Part D  Linear programmes on grids of the levels of planar bodies with an axis of symmetry: least L1 distance
        from a 3-complete mix of the levels, with and without the polygon condition on the chords.
Results go to data/open18.json; the log goes to stdout.
Environment: MC (default 200000), NRAND (300), KMAX (16), SEED (2026).
"""
import json, math, os, sys, time
import numpy as np
import scipy.sparse as sp
from scipy.integrate import quad
from scipy.optimize import linprog
from scipy.stats import kstest, kstwo

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "p14"))
sys.path.insert(0, os.path.join(HERE, "..", "pB"))
from concave14 import PLDensity, solve, algorithm, arch_mix          # noqa: E402
from bodies17 import ball_fibres                                     # noqa: E402

MC = int(os.environ.get("MC", 200000)); NRAND = int(os.environ.get("NRAND", 300))
KMAX = int(os.environ.get("KMAX", 16)); SEED = int(os.environ.get("SEED", 2026))


# ===================================================================== Part A: concave p-th roots
def simplex_projection_density(t):
    """density of u.X, X uniform on a k-simplex whose vertices project to the distinct values t_0..t_k:
    the B-spline k sum_j (t_j - x)_+^(k-1) / prod_{i != j} (t_j - t_i)."""
    t = np.asarray(t, float); k = len(t) - 1
    den = np.array([np.prod([t[j] - t[i] for i in range(k + 1) if i != j]) for j in range(k + 1)])
    return lambda x: k * np.sum(np.clip(t[None, :] - np.asarray(x, float)[:, None], 0, None) ** (k - 1) / den[None, :], axis=1)


def cube_projection_density(u):
    """density of u1 U1 + u2 U2 + u3 U3 with independent uniform U_i on [0,1] and u_i > 0."""
    u = np.asarray(u, float)
    def f(x):
        x = np.asarray(x, float); s = np.zeros_like(x)
        for m in range(8):
            S = [i for i in range(3) if m >> i & 1]
            s += (-1) ** len(S) * np.clip(x - sum(u[i] for i in S), 0, None) ** 2
        return s / (2 * np.prod(u))
    return f


def octahedron_projection_density(u):
    """density of u.X, X uniform on the regular octahedron |x|+|y|+|z| <= 1: the octahedron is the union of
    the eight simplices conv(0, s1 e1, s2 e2, s3 e3), which have equal volume."""
    u = np.asarray(u, float); parts = []
    for m in range(8):
        s = np.array([1 if m >> i & 1 else -1 for i in range(3)], float)
        parts.append(simplex_projection_density([0.0] + list(s * u)))
    return lambda x: sum(p(x) for p in parts) / 8.0


def tabulated(f, lo, hi, N=4000):
    xs = np.linspace(lo, hi, N + 1)
    ys = np.clip(f(xs), 0, None)
    ys = np.round(ys / ys.max(), 12)            # removes rounding noise on flat parts (cube projections)
    return PLDensity(xs, ys)


def beta_star(P, nlev=3000):
    S = solve(P, n=nlev)
    return float(np.max(S["beta"])), S


def partA():
    t0 = time.time(); rows = []; sols = {}
    tests = []
    for p in (1.0, 1.5, 2.0, 3.0, 5.0, 8.0):
        tests.append(("$(1-x)^{%s}$" % ("%g" % p), "linear", p, lambda x, p=p: (1 - x) ** p))
    for p in (2.0, 3.0, 4.0):
        tests.append(("tent, mode $\\frac14$, $p=%g$" % p, "tent", p,
                      lambda x, p=p: np.minimum(x / 0.25, (1 - x) / 0.75) ** p))
    tests.append(("$(1-x^2)^2$", "quartic", 2.0, lambda x: (1 - x ** 2) ** 2))
    tests.append(("$\\sin(\\pi x/2)^3$", "sine", 3.0, lambda x: np.sin(np.pi * x / 2) ** 3))
    for p in (2.0, 4.0):
        tests.append(("$(x(1-x))^{%g}$" % (p / 2), "symmetric", p, lambda x, p=p: (x * (1 - x)) ** (p / 2)))
    rng = np.random.default_rng(SEED)
    # projections of polytopes in R^3 onto random directions: p = 2 by Brunn's theorem
    for name, key, maker in (("tetrahedron", "tetra", lambda u: simplex_projection_density(
                                  [0.0, u[0], u[1], u[2]])),
                             ("cube", "cube", lambda u: cube_projection_density(np.abs(u))),
                             ("octahedron", "octa", lambda u: octahedron_projection_density(u))):
        for j in range(3):
            u = rng.normal(size=3); u /= np.linalg.norm(u)
            f = maker(u)
            if key == "tetra":
                tt = np.array([0.0, u[0], u[1], u[2]]); lo, hi = tt.min(), tt.max()
            elif key == "cube":
                lo, hi = 0.0, float(np.abs(u).sum())
            else:
                lo, hi = -float(np.abs(u).sum()), float(np.abs(u).sum())
            tests.append(("projection of the %s, direction %d" % (name, j + 1), key, 2.0,
                          lambda x, f=f, lo=lo, hi=hi: f(lo + x * (hi - lo))))
    for label, key, p, fun in tests:
        P = tabulated(fun, 0.0, 1.0)
        assert P.unimodal
        b, S = beta_star(P)
        rows.append(dict(label=label, key=key, p=p, beta=b, ratio=b / (p + 2), mu=P.mu,
                         beta0=float(S["beta"][0])))
        sols[label] = (P, S)
        print("Part A:", rows[-1], flush=True)
    # random concave g (piecewise linear, positive inside), random p in [1, 6]
    worst = 0.0; worst_case = None; t1 = time.time()
    for i in range(NRAND):
        k = int(rng.integers(1, 6))
        xs = np.sort(np.concatenate([[0.0, 1.0], rng.uniform(0, 1, k)]))
        sl = np.sort(rng.normal(0, 4, len(xs) - 1))[::-1]
        ys = np.concatenate([[0.0], np.cumsum(sl * np.diff(xs))])
        ys = ys - ys.min() + rng.uniform(0, 1) * rng.integers(0, 2)
        p = float(rng.uniform(1, 6))
        g = lambda x, xs=xs, ys=ys: np.interp(x, xs, ys)
        P = tabulated(lambda x: g(x) ** p, 0.0, 1.0, N=2000)
        b, _ = beta_star(P, nlev=1500)
        if b / (p + 2) > worst:
            worst, worst_case = b / (p + 2), dict(p=p, beta=b, nodes=xs.tolist(), values=ys.tolist())
    rand = dict(n=NRAND, max_ratio=worst, worst=worst_case, seconds=round(time.time() - t1, 1))
    print("Part A random:", {k: v for k, v in rand.items() if k != "worst"}, flush=True)
    # Monte Carlo of Algorithm 37 at n = ceil(p + 2)
    mrows = []
    rngm = np.random.default_rng(SEED + 1)
    for label in ["$(1-x)^{3}$", "tent, mode $\\frac14$, $p=2$", "projection of the tetrahedron, direction 1",
                  "projection of the octahedron, direction 1"]:
        P, S = sols[label]
        p = [r["p"] for r in rows if r["label"] == label][0]
        n = int(math.ceil(p + 2 - 1e-12))
        assert float(np.max(S["beta"])) <= n * (1 + 1e-9), (label, float(np.max(S["beta"])))
        X, _ = algorithm(P, S, n, MC, rngm)
        sums = float(np.abs(X.sum(1) - n * P.mu).max())
        ps = []
        for i in range(n):
            x1 = np.sort(X[:, i]); Fx = P.cdf(x1); ii = np.arange(1, MC + 1)
            ks = float(max(np.max(ii / MC - Fx), np.max(Fx - (ii - 1) / MC)))
            ps.append(float(kstwo.sf(ks, MC)))
        mrows.append(dict(label=label, p=p, n=n, samples=MC, sumerr=sums, tests=n, min_p=min(ps),
                          inrange=bool(np.all(X >= -1e-12) and np.all(X <= 1 + 1e-12))))
        print("Part A MC:", mrows[-1], flush=True)
    return dict(rows=rows, random=rand, mc=mrows, seconds=round(time.time() - t0, 1))


# ===================================================================== Part B: levels of the bipyramids
def alpha_tent(k, x):
    """alpha_k(x) for 0 < x <= 1/2 by exact antiderivatives of the integrand
    3k [(k-1)(1-t)^(k-2) + 2 (1/2 - t)^(k-2)] / t^2  (polynomials divided by t^2)."""
    x = np.asarray(x, float)
    c = 3 * k * (k - 3) * 2.0 ** (3 - k) / (k - 1)
    # coefficients of (k-1)(1-t)^(k-2) + 2(1/2-t)^(k-2) in powers of t
    m = k - 2
    coef = np.zeros(m + 1)
    for j in range(m + 1):
        coef[j] = (k - 1) * math.comb(m, j) * (-1) ** j + 2 * math.comb(m, j) * 0.5 ** (m - j) * (-1) ** j
    # int_x^{1/2} coef_j t^(j-2) dt
    I = np.zeros_like(x)
    for j in range(m + 1):
        if j == 0:
            I += coef[0] * (1 / x - 2.0)
        elif j == 1:
            I += coef[1] * (math.log(0.5) - np.log(x))
        else:
            e = j - 1
            I += coef[j] * (0.5 ** e - x ** e) / e
    return x * x * (c + 3 * k * I)


def alpha_tent_full(k, x):
    x = np.asarray(x, float)
    out = np.where(x > 0.5, 3 * k * (1 - x) ** (k - 1), 0.0)
    small = (x > 0) & (x <= 0.5)
    out[small] = alpha_tent(k, x[small])
    return out


def b_from_alpha(alpha, n, x):
    """density of B at x in [0, 1/2]: int_x^{1/2} alpha(a)/a da + int_{1/2}^{x+1/2} 3 n(a)/(1-a) da."""
    out = []
    for xx in x:
        i1 = quad(lambda a: alpha(np.array([a]))[0] / a, xx, 0.5, limit=200, epsabs=1e-13, epsrel=1e-12)[0]
        i2 = quad(lambda a: 3 * n(a) / (1 - a), 0.5, xx + 0.5, limit=200, epsabs=1e-13, epsrel=1e-12)[0]
        out.append(i1 + i2)
    return np.array(out)


def partB():
    t0 = time.time(); res = []
    xs = np.concatenate([np.geomspace(1e-6, 1e-2, 60), np.linspace(1e-2, 0.5, 300)])
    for k in range(3, KMAX + 1):
        al = alpha_tent(k, xs)
        nfun = lambda a, k=k: k * (1 - a) ** (k - 1)
        mass = quad(lambda a: alpha_tent(k, np.array([a]))[0], 0, 0.5, limit=200, epsabs=1e-13)[0] \
            + 3 * 0.5 ** k
        xi = np.linspace(0.005, 0.5, 40)
        b = b_from_alpha(lambda a, k=k: alpha_tent_full(k, a), nfun, xi)
        ident = float(np.max(np.abs(alpha_tent(k, xi) + 2 * b - 3 * nfun(xi))))
        a_half = float(alpha_tent(k, np.array([0.5]))[0])
        res.append(dict(k=k, min_alpha_over_x=float(np.min(al / xs)), alpha_half=a_half,
                        alpha_half_formula=3 * k * (k - 3) * 2.0 ** (1 - k) / (k - 1), mass_err=abs(mass - 1),
                        identity_err=ident))
        print("Part B:", res[-1], flush=True)
    x3 = np.linspace(1e-4, 0.5, 2000)
    closed = float(np.max(np.abs(alpha_tent(3, x3) - (27 * x3 - 54 * x3 ** 2 + 36 * x3 ** 2 * np.log(2 * x3)))))
    # condition (*): n(1/2) >= 2 int_{1/2}^1 n(a)/(1-a) da for profiles r (n proportional to r^(k-1))
    def star(r, k):
        lhs = r(0.5) ** (k - 1)
        rhs = 2 * quad(lambda a: r(a) ** (k - 1) / (1 - a), 0.5, 1, limit=400)[0]
        return dict(lhs=lhs, rhs=rhs, holds=bool(lhs >= rhs * (1 - 1e-12)))
    ex = {}
    for k in (2, 3, 4, 8):
        ex["tent k=%d" % k] = star(lambda a: 1 - a, k)
    for h in (0.25, 0.5):
        ex["elongated h=%g k=3" % h] = star(lambda a, h=h: min(1.0, (1 - a) / (1 - h)), 3)
    ex["elongated h=0.6 k=3"] = star(lambda a: min(1.0, (1 - a) / 0.4), 3)
    for k in (3, 6, 7, 8):
        ex["ball k=%d" % k] = star(lambda a: math.sqrt(max(1 - a * a, 0.0)), k)
    for key, v in ex.items():
        print("Part B (*):", key, v, flush=True)
    return dict(rows=res, closed_k3=closed, star=ex, seconds=round(time.time() - t0, 1))


# ===================================================================== Part C: Monte Carlo of the bipyramids
class Levels:
    """3-complete mix of the levels of the lemma on the levels, for an absolute level density n on [0,1] given on a grid."""

    def __init__(self, nfun, dnfun, N=200000):
        # alpha(1/2) and alpha on a grid; alpha(x) = x^2 [4 alpha(1/2) + int_x^{1/2} g(t) t^{-2} dt] on (0, 1/2]
        tail = quad(lambda a: nfun(a) / (1 - a), 0.5, 1, limit=400, epsabs=1e-14)[0]
        self.a_half = 3 * nfun(0.5) - 6 * tail
        assert self.a_half >= -1e-12, "condition (*) fails"
        g = lambda t: -3 * dnfun(t) + 6 * nfun(t + 0.5) / (0.5 - t)
        xs = np.concatenate([np.geomspace(1e-7, 0.01, 400)[:-1], np.linspace(0.01, 0.5 - 1e-9, 4000)])
        # cumulative integral from the right of g(t)/t^2, Simpson on each cell
        F = np.zeros_like(xs)
        for i in range(len(xs) - 2, -1, -1):
            a, b = xs[i], xs[i + 1]; m = 0.5 * (a + b)
            F[i] = F[i + 1] + (b - a) / 6 * (g(a) / a ** 2 + 4 * g(m) / m ** 2 + g(b) / b ** 2)
        al = xs ** 2 * (4 * self.a_half + F)
        xr = np.linspace(0.5, 1.0, 3001)
        self.x = np.concatenate([[0.0], xs, xr]); self.al = np.concatenate([[0.0], al, 3 * nfun(xr)])
        self.min_alpha = float(al.min())
        cdf = np.concatenate([[0.0], np.cumsum(0.5 * (self.al[1:] + self.al[:-1]) * np.diff(self.x))])
        self.mass = float(cdf[-1]); self.cdf = cdf / cdf[-1]

    def sample(self, N, rng):
        A = np.interp(rng.random(N), self.cdf, self.x)
        delta = np.minimum(A, 1 - A) / 2
        D = (2 * rng.random(N) - 1) * delta
        B, C = A / 2 + D, A / 2 - D
        eps = np.where(rng.random(N) < 0.5, 1.0, -1.0)
        Z = np.stack([eps * A, -eps * B, -eps * C], 1)
        perm = np.argsort(rng.random((N, 3)), axis=1)
        return np.take_along_axis(Z, perm, axis=1)


def level_cdf(nfun):
    """cdf of the symmetric level law with absolute density n on [0,1]."""
    grid = np.linspace(0, 1, 20001); dens = nfun(grid)
    c = np.concatenate([[0.0], np.cumsum(0.5 * (dens[1:] + dens[:-1]) * np.diff(grid))]); c /= c[-1]
    return lambda z: np.where(np.asarray(z) >= 0, 0.5 + 0.5 * np.interp(np.abs(z), grid, c),
                              0.5 - 0.5 * np.interp(np.abs(z), grid, c))


def box_fibres(r, dim, rng):
    """joint mix of U(r_i [-1,1]^dim) by Lemma 1 in each coordinate; r of shape (N, n)."""
    return np.stack([arch_mix(-r, r, rng) for _ in range(dim)], axis=2)


def uniform01(t):
    return np.clip(t, 0, 1)


def sim_body(name, k, profile, nfun, dnfun, fibre, n, N, rng, Lv):
    Z3 = Lv.sample(N, rng)
    r3 = profile(np.abs(Z3))
    assert np.all(2 * r3.max(1) <= r3.sum(1) * (1 + 1e-12) + 1e-15), "fibre condition fails"
    assert np.all(np.sort(np.abs(Z3), axis=1)[:, 1] <= 0.5 + 1e-15), "two levels are not central"
    W3 = fibre(r3, rng)
    if n == 3:
        Z, W = Z3, W3
    else:                                       # n = 5: the 3-complete mix and a 2-complete mix (Y, -Y)
        grid = np.linspace(-1, 1, 40001); Fz = level_cdf(nfun)(grid)
        z = np.interp(rng.random(N), Fz, grid)           # level of a uniform point
        rz = profile(np.abs(z))
        w = fibre(np.stack([rz, rz], 1), rng)[:, 0]      # a uniform point of its section
        Z = np.concatenate([Z3, z[:, None], -z[:, None]], 1)
        W = np.concatenate([W3, w[:, None], -w[:, None]], 1)
    perm = np.argsort(rng.random((N, n)), axis=1)
    Z = np.take_along_axis(Z, perm, axis=1); W = np.take_along_axis(W, perm[:, :, None], axis=1)
    r = profile(np.abs(Z))
    sums = float(max(np.abs(Z.sum(1)).max(), np.abs(W.sum(1)).max()))
    Fz = level_cdf(nfun)
    pv = lambda x, F: float(kstwo.sf(kstest(x, F).statistic, len(x)))   # exact p-value of the KS statistic
    tests = []
    for i in range(n):
        tests.append(pv(Z[:, i], Fz))
        rel = W[:, i] / np.where(r[:, i] > 0, r[:, i], 1)[:, None]
        if name.startswith("double cone"):
            tests.append(pv(np.linalg.norm(rel, axis=1) ** 2, uniform01))
            tests.append(pv((np.arctan2(rel[:, 1], rel[:, 0]) + np.pi) / (2 * np.pi), uniform01))
            outside = float((np.linalg.norm(W, axis=2) - r).max())
        else:
            for c in range(rel.shape[1]):
                tests.append(pv((rel[:, c] + 1) / 2, uniform01))
            outside = float((np.abs(W).max(axis=2) - r).max())
    return dict(body=name, k=k, n=n, samples=N, max_sum_dev=sums, outside=outside, tests=len(tests),
                min_p=float(min(tests)), alpha_min=Lv.min_alpha, alpha_mass_err=abs(Lv.mass - 1))


def partC():
    t0 = time.time(); rng = np.random.default_rng(SEED + 5); rows = []
    tent3 = (lambda a: 3 * (1 - a) ** 2, lambda a: -6 * (1 - a))
    tent4 = (lambda a: 4 * (1 - a) ** 3, lambda a: -12 * (1 - a) ** 2)
    L3 = Levels(*tent3); L4 = Levels(*tent4)
    # elongated octahedron: profile min(1, 2(1-|z|)), level density proportional to profile^2
    Zel = quad(lambda a: min(1.0, 2 * (1 - a)) ** 2, 0, 1, points=[0.5])[0]
    nel = lambda a: np.minimum(1.0, 2 * (1 - np.asarray(a, float))) ** 2 / Zel
    dnel = lambda a: np.where(np.asarray(a, float) > 0.5, -4 * 2 * (1 - np.asarray(a, float)) / Zel, 0.0)
    Lel = Levels(nel, dnel)
    tent = lambda a: 1 - a
    elong = lambda a: np.minimum(1.0, 2 * (1 - a))
    diamond = lambda r, rng: box_fibres(r, 2, rng)                      # (u, v) = (x + y, x - y)
    disc = lambda r, rng: ball_fibres(r, 2, rng)
    cube = lambda r, rng: box_fibres(r, 3, rng)
    for name, k, prof, nf, Lv, fib, ns in (
            ("regular octahedron", 3, tent, tent3, L3, diamond, (3, 5)),
            ("double cone over a disc", 3, tent, tent3, L3, disc, (3,)),
            ("bipyramid over a cube", 4, tent, tent4, L4, cube, (3,)),
            ("elongated octahedron", 3, elong, (nel, dnel), Lel, diamond, (3,))):
        for n in ns:
            row = sim_body(name, k, prof, nf[0], nf[1], fib, n, MC, rng, Lv)
            rows.append(row); print("Part C:", row, flush=True)
    m = sum(r["tests"] for r in rows); pmin = min(r["min_p"] for r in rows)
    return dict(rows=rows, tests=m, min_p=pmin, chance_min_p=1 - (1 - pmin) ** m, seconds=round(time.time() - t0, 1))


# ===================================================================== Part D: linear programmes on the levels
def level_lp(rfun, n, m, J, tol=1e-12):
    """least L1 distance between the grid version of the level law (density r on [0,1]) and the marginals of a
    mixture of n-tuples of grid points with the integer sum closest to n times the mean; with m > 0 only
    tuples with m max r(s_i) <= sum r(s_i)."""
    h = 1.0 / J; s = h * np.arange(J + 1)
    edges = np.concatenate([[0.0], (s[:-1] + s[1:]) / 2, [1.0]])
    w = np.array([quad(lambda x: float(rfun(x)), edges[i], edges[i + 1])[0] for i in range(J + 1)])
    w /= w.sum(); mean = float((w * s).sum())
    tot = int(round(n * mean / h)); rv = np.array([float(rfun(x)) for x in s])
    T = []
    def rec(prefix, start, remaining, cnt):
        if cnt == n - 1:
            if start <= remaining <= J:
                tup = prefix + [remaining]; rr = rv[tup]
                if m == 0 or m * rr.max() <= rr.sum() + tol:
                    T.append(tup)
            return
        for a in range(start, J + 1):
            if a * (n - cnt) > remaining:
                break
            rec(prefix + [a], a, remaining - a, cnt + 1)
    rec([], 0, tot, 0)
    T = np.array(T); M = len(T); N = J + 1
    Aq = sp.csr_matrix((np.full(n * M, 1.0 / n), (T.T.ravel(), np.tile(np.arange(M), n))), shape=(N, M))
    Aeq = sp.vstack([sp.hstack([Aq, sp.eye(N), -sp.eye(N)]),
                     sp.hstack([sp.csr_matrix(np.ones((1, M))), sp.csr_matrix((1, 2 * N))])]).tocsr()
    res = linprog(np.concatenate([np.zeros(M), np.ones(2 * N)]), A_eq=Aeq, b_eq=np.concatenate([w, [1.0]]),
                  bounds=(0, None), method="highs")
    assert res.status == 0
    return float(res.fun), M


def pentagon_profile():
    th = 2 * np.pi / 5
    V = np.array([[np.cos(np.pi / 2 + j * th), np.sin(np.pi / 2 + j * th)] for j in range(5)])
    ytop, ybot = V[:, 1].max(), V[:, 1].min()
    def r(x):
        y = ytop - min(max(float(x), 0.0), 1.0) * (ytop - ybot); xs = []
        for j in range(5):
            p, q = V[j], V[(j + 1) % 5]
            if (p[1] - y) * (q[1] - y) <= 0 and p[1] != q[1]:
                t = (y - p[1]) / (q[1] - p[1]); xs.append(p[0] + t * (q[0] - p[0]))
        return (max(xs) - min(xs)) / 2 if xs else 0.0
    return r


def partD():
    t0 = time.time()
    bodies = [("half-disc", lambda x: math.sqrt(max(1 - x * x, 0.0))),
              ("regular pentagon", pentagon_profile()),
              ("kite", lambda x: min(x / 0.3, (1 - x) / 0.7)),
              ("triangle", lambda x: 1 - x),
              ("disc", lambda x: math.sqrt(max(x * (1 - x), 0.0)))]
    rows = []
    for name, r in bodies:
        for J in (120, 240, 480, 960):
            a, Ma = level_lp(r, 3, 2, J); b, Mb = level_lp(r, 3, 0, J)
            rows.append(dict(body=name, n=3, J=J, constrained=a, free=b, tuples=Ma, tuples_free=Mb))
            print("Part D:", rows[-1], flush=True)
    more = []
    for name, r in bodies[:3]:
        for n, Js in ((4, (60, 120)), (5, (40, 80))):
            for J in Js:
                a, Ma = level_lp(r, n, 2, J); b, Mb = level_lp(r, n, 0, J)
                more.append(dict(body=name, n=n, J=J, constrained=a, free=b, tuples=Ma, tuples_free=Mb))
                print("Part D:", more[-1], flush=True)
    return dict(rows=rows, more=more, seconds=round(time.time() - t0, 1))


if __name__ == "__main__":
    t0 = time.time()
    OUT = dict(partA=partA(), partB=partB(), partC=partC(), partD=partD())
    OUT["seconds"] = round(time.time() - t0, 1)
    OUT["settings"] = dict(MC=MC, NRAND=NRAND, KMAX=KMAX, SEED=SEED)
    os.makedirs(os.path.join(HERE, "data"), exist_ok=True)
    with open(os.path.join(HERE, "data", "open18.json"), "w") as fh:
        json.dump(OUT, fh, indent=1, default=str)
    print("done in %.0f s" % OUT["seconds"])
