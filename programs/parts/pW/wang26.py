"""Checks for Sections 25 to 28: all large n and windows in aggregation sets, projections onto proper subspaces,
the norm condition and unimodal densities, and lattice distributions.

Part A (Section 25).
  A1  exact: the two-step tilt P_{1,gamma} of Lemma 125 (density (1-gamma)/2 on (-1,0), (1+gamma)/2 on (0,1)) is
      the marginal of a mixture of at most three admissible tuples of Theorem 6 (routine tuples of mono11.py)
      with midpoints adding up to m*gamma/2, for m >= 4 and |gamma| <= 1 and for m = 3 and |gamma| <= 2/3, on a
      rational grid.
  A2  exact: the sequential countermonotone coupling of Lemma 127(a) for different discrete laws keeps the sum
      in an interval no longer than the longest support, with exact marginals; the quantile grid of Lemma 127(b).
  A3  floating point: simulations of Corollary 129 (a density with a gap, a law with atoms, an increasing
      density), of Proposition 126 (prescribed distributions of the sum of uniform variables), of Proposition 133
      (families of arbitrary laws completed to a joint mix by four or five uniform variables) and of Theorem 128
      in the plane (the uniform distribution on an L-shaped region).
  A4  the explicit bound N*_d of Corollary 131.
  A5  exact: the selection of Theorem 138 (the identity (30), the shifts of the first group and their means, the
      systematic sample) for all choices in 24 configurations; floating point: simulations of Proposition 133 with
      two repeated distributions and three other laws, with a prescribed distribution of the sum, and of the joint
      mix of Theorem 138 for pairwise different laws: the
      least numbers of Corollary 139 (33 laws on [0,1], each at least 1/3 U[0,1]) and 54 laws on different
      intervals with a sum that is uniform on a window; every marginal is tested.
  A6  exact: the two distributions of a pair in Proposition 135 for m = 3, 4, 5, 8 on a rational grid (P_+ is a
      probability density with the right mean, the mixture is uniform, and the tuples of Theorem 6 have the marginal
      g_{a,b}); floating point: prescribed sums of three, four and eight uniform variables on intervals that are not
      centred at the mean, the complete mixes of Corollary 136 (three uniform variables for densities bounded below,
      the theorem of Puccetti, Wang and Wang (2013); R/H uniform variables in general), and five laws completed to a
      joint mix by three uniform variables.
Part B (Section 26).  exact: the constants of Lemma 142 for d = 2,...,6 and the centres of Lemma 143;
      floating point: the integrals over affine subspaces in closed form, and the density of Q on a planar grid.
Part C (Section 27).  exact: the convex order X - mu <=_cx -(n-1)(X - mu) for the law p delta_c + (1-p) U[0,1]
      of Proposition 149 and for the density f_1 of Theorem 151 by their call functions, and for f_2 on a grid;
      the lower bound (34) of Lemma 147 for the probability that a sum differs from n mu; the least n of
      Corollary 150 and the case n_0 = 6 of Corollary 152, with the convex order for n = 3,...,40; floating
      point: linear programmes on a lattice for n = 3, and simulations of the complete mixes of Proposition
      149(a) and of Corollary 136(b) for a density of Corollary 152; the criterion of Theorem 36 and lattice linear
      programmes for random unimodal cubic densities with mean in [1/3, 2/3] (uses concave14.py).
Part D (Section 28).  exact, with certificates: complete mixability of binomial laws (Proposition 159), of laws
      on three points (Proposition 157) and of two laws for Theorem 158, by the simplex method in rational
      arithmetic; the occupancy laws of Theorem 156; the operations of Proposition 155; a log-concave law that is
      not 3-completely mixable; and, for Remark 160, the necessary conditions of Section 27 (the convex order,
      Lemma 147 for all subsets, Lemma 148, and the tail inequalities of Komisarski and Labuschagne) against the
      exact answer, for three examples and for all laws with given denominators on four and five consecutive
      integers.
Writes data/wang26.json and data/binomial_mixes.json, the weights of the complete mixes of Proposition 159, which
check_binomial.py verifies independently.  Environment: MC (default 20000), SEED (2026), NBIN (12), NBOX (10), NCUB (300).
"""
import json, math, os, sys, time, itertools
from fractions import Fraction as Fr
from decimal import Decimal, getcontext
import numpy as np
from scipy import stats
from scipy.optimize import linprog

here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, "..", "p11")); sys.path.insert(0, os.path.join(here, "..", "p14"))
import mono11

MC = int(os.environ.get("MC", 20000)); SEED = int(os.environ.get("SEED", 2026))
NCUB = int(os.environ.get("NCUB", 300))
NBIN = int(os.environ.get("NBIN", 12)); NBOX = int(os.environ.get("NBOX", 10))
OUT = {}
PVALS = []                                  # all p-values of Part A3 and Part C
CERTS = []                                  # the complete mixes of the binomial laws: [N, n, M, [[count vector, weight]]]


# ============================================================ two-step tilts (Lemma 125)
def tilt_tuples(m, gamma):
    """mixture of admissible tuples (weight, intervals in [-1,1]) with marginal P_{1,gamma}; exact for Fractions"""
    g = Fr(gamma)
    if g == 0:
        return [(Fr(1), [(Fr(-1), Fr(1))] * m)]
    if g < 0:
        if g == -1:
            return [(Fr(1), [(Fr(-1), Fr(0))] * m)]
        a = 2 / (2 + g); b = 2 * a; mu = (2 + g) / 2     # (X + 1)/mu has the density g_{a,b} of Section 4
        case, parts = mono11.tuples(m, a, b)
        return [(w, [(mu * l - 1, mu * r - 1) for l, r in iv]) for w, iv in parts if w != 0]
    return [(w, [(-r, -l) for l, r in iv]) for w, iv in tilt_tuples(m, -g)]


def check_tilt(m, gamma):
    parts = tilt_tuples(m, gamma); g = Fr(gamma)
    assert sum(w for w, _ in parts) == 1
    for w, iv in parts:
        assert w > 0 and len(iv) == m
        assert sum(l + r for l, r in iv) == m * g
        L = [r - l for l, r in iv]
        assert min(L) > 0 and 2 * max(L) <= sum(L) and all(-1 <= l and r <= 1 for l, r in iv)
    bps = sorted(set([Fr(-1), Fr(0), Fr(1)] + [e for w, iv in parts for I in iv for e in I]))
    for lo, hi in zip(bps[:-1], bps[1:]):
        x = (lo + hi) / 2
        dens = sum(w * sum(Fr(1, m) / (r - l) for l, r in iv if l < x < r) for w, iv in parts)
        assert dens == ((1 - g) / 2 if x < 0 else (1 + g) / 2)
    return len(parts)


def partA1():
    t0 = time.time(); cnt = 0; mx = 0
    for m in range(4, 21):
        for k in range(-60, 61):
            mx = max(mx, check_tilt(m, Fr(k, 60))); cnt += 1
    c3 = 0
    for k in range(-40, 41):
        mx = max(mx, check_tilt(3, Fr(k, 60))); c3 += 1
    OUT["A1"] = dict(cases=cnt, cases_m3=c3, max_tuples=mx, mmax=20, seconds=time.time() - t0)
    print("A1", OUT["A1"], flush=True)


def tilt_mix(m, gamma, rng):
    """one m-complete mix of P_{1,gamma} (floats), uniformly permuted; its sum is m*gamma/2"""
    parts = tilt_tuples(m, Fr(float(gamma)))
    w = np.array([float(p[0]) for p in parts])
    iv = parts[int(rng.choice(len(parts), p=w / w.sum()))][1]
    x = mono11.project([(float(l), float(r)) for l, r in iv], rng)
    return rng.permutation(x)


# ============================================================ laws on the line: mixtures of uniforms and atoms
class Law:
    """sum of weights w on uniform distributions on [lo, hi] (an atom if lo == hi)"""

    def __init__(self, comps):
        self.comps = [(float(w), float(lo), float(hi)) for w, lo, hi in comps if w > 0]
        tot = sum(w for w, _, _ in self.comps)
        self.comps = [(w / tot, lo, hi) for w, lo, hi in self.comps]
        xs = sorted(set([lo for _, lo, _ in self.comps] + [hi for _, _, hi in self.comps]))
        self.xs = np.array(xs)
        self.Fr_ = np.array([self._cdf(x) for x in xs])                  # right limits
        self.atoms = {lo: 0.0 for _, lo, hi in self.comps if lo == hi}
        for w, lo, hi in self.comps:
            if lo == hi:
                self.atoms[lo] += w
        self.Fl_ = np.array([self.Fr_[i] - self.atoms.get(x, 0.0) for i, x in enumerate(xs)])
        self.mean = sum(w * (lo + hi) / 2 for w, lo, hi in self.comps)
        self.lo, self.hi = xs[0], xs[-1]

    def _cdf(self, x):
        s = 0.0
        for w, lo, hi in self.comps:
            s += w * (1.0 if x >= hi else 0.0 if x < lo else (x - lo) / (hi - lo))
        return s

    def cdf(self, x):
        x = np.asarray(x, float); s = np.zeros_like(x)
        for w, lo, hi in self.comps:
            s += w * (np.where(x >= hi, 1.0, 0.0) if lo == hi else np.clip((x - lo) / (hi - lo), 0.0, 1.0))
        return s

    def quantile(self, u):
        u = np.asarray(u, float)
        k = np.searchsorted(self.Fr_, u, side="left")
        k = np.clip(k, 0, len(self.xs) - 1)
        out = np.empty_like(u)
        at = u > self.Fl_[k] - 1e-15                                     # in the jump at xs[k]
        out[at] = self.xs[k[at]]
        r = ~at
        k0 = np.clip(k[r] - 1, 0, None)
        den = self.Fl_[k[r]] - self.Fr_[k0]
        frac = np.where(den > 0, (u[r] - self.Fr_[k0]) / np.where(den > 0, den, 1.0), 0.0)
        out[r] = self.xs[k0] + frac * (self.xs[k[r]] - self.xs[k0])
        return out

    def tests(self, sample):
        """p-values: Kolmogorov-Smirnov for the part without atoms, and normal tests of the masses of the atoms"""
        ps = []; sample = np.asarray(sample, float); N = len(sample)
        mask = np.zeros(N, bool); am = 0.0
        for a, w in self.atoms.items():
            hit = np.abs(sample - a) < 1e-12
            z = (hit.sum() - N * w) / math.sqrt(N * w * (1 - w))
            ps.append(float(2 * stats.norm.sf(abs(z)))); mask |= hit; am += w
        if am < 1 - 1e-12:
            cont = Law([(w, lo, hi) for w, lo, hi in self.comps if lo < hi])
            ps.append(float(stats.kstest(sample[~mask], cont.cdf).pvalue))
        return ps


def grid_coupling(law, k, rng):
    """quantile grid: k variables with the given law whose sum is within the length of the support of its mean"""
    W = rng.random(); sig = rng.permutation(k)
    return law.quantile((sig + W) / k)


# ============================================================ A2: sequential countermonotone coupling (exact)
def counter_rows(cols):
    """cols: list of lists of equal length M (the M equally likely values of each law).  Returns the M rows of the
    sequential countermonotone coupling: column j is sorted against the partial sums of the columns before it."""
    M = len(cols[0])
    rows = [[v] for v in sorted(cols[0])]
    sums = sorted(cols[0])
    order = list(range(M))
    for col in cols[1:]:
        order = sorted(range(M), key=lambda i: sums[i])                  # increasing partial sums
        desc = sorted(col, reverse=True)
        for rank, i in enumerate(order):
            rows[i].append(desc[rank]); sums[i] = sums[i] + desc[rank]
    return rows, sums


def partA2():
    t0 = time.time(); rng = np.random.default_rng(SEED + 11); worst = Fr(0); fam = 0
    for _ in range(400):
        r = int(rng.integers(2, 9)); M = int(rng.choice([6, 12, 20, 30, 60]))
        cols = []; lens = []
        for j in range(r):
            lo = Fr(int(rng.integers(-20, 20)), 10); ln = Fr(int(rng.integers(1, 21)), 20)      # length <= 1
            vals = [lo + ln * Fr(int(rng.integers(0, 13)), 12) for _ in range(M)]
            if rng.random() < 0.3:
                vals = [lo if rng.random() < 0.6 else lo + ln for _ in range(M)]             # two-point law
            cols.append(vals); lens.append(max(vals) - min(vals))
        rows, sums = counter_rows(cols)
        for j in range(r):
            assert sorted(row[j] for row in rows) == sorted(cols[j])                         # exact marginals
        osc = max(sums) - min(sums)
        assert osc <= max(lens)
        if max(lens) > 0:
            worst = max(worst, osc / max(lens))
        fam += 1
    # the quantile grid for k copies of one discrete law: the sum is within the length of the support of k mu
    grids = 0; gworst = Fr(0)
    for _ in range(300):
        k = int(rng.integers(1, 13)); na = int(rng.integers(2, 6)); den = k * int(rng.integers(1, 5)) * 6
        cut = sorted(set([0, den] + [int(v) for v in rng.integers(1, den, na - 1)]))
        wts = [Fr(b - a, den) for a, b in zip(cut[:-1], cut[1:])]
        vals = sorted(Fr(int(rng.integers(0, 41)), 40) for _ in wts)
        if vals[-1] == vals[0]:
            continue
        mu = sum(w * v for w, v in zip(wts, vals)); cum = [Fr(c_, den) for c_ in cut]
        Q = lambda u: vals[max(i for i in range(len(vals)) if cum[i] < u)] if u > 0 else vals[0]
        # the sum over the grid (j + W)/k is constant in W between the points where some (j + W)/k crosses a cut
        br = sorted(set([Fr(0), Fr(1)] + [(k * c_) % 1 for c_ in cum]))
        for a, b in zip(br[:-1], br[1:]):
            W = (a + b) / 2
            S = sum(Q((j + W) / k) for j in range(k))
            dev = abs(S - k * mu)
            assert dev <= vals[-1] - vals[0]
            gworst = max(gworst, dev / (vals[-1] - vals[0]))
        grids += 1
    OUT["A2"] = dict(families=fam, worst_ratio=float(worst), grids=grids, grid_worst=float(gworst),
                     seconds=time.time() - t0)
    print("A2", OUT["A2"], flush=True)


def counter_sample(laws, M, rng):
    """one row of the sequential countermonotone coupling of the laws, each discretised by a quantile grid of M
    points with its own random offset; every coordinate has its law exactly"""
    cols = [list(L.quantile((np.arange(M) + rng.random()) / M)) for L in laws]
    rows, sums = counter_rows(cols)
    i = int(rng.integers(M))
    return np.array(rows[i]), max(sums) - min(sums)


# ============================================================ A3: simulations
def pv_summary(ps):
    ps = [p for p in ps if p == p]
    pmin = min(ps)
    return dict(tests=len(ps), pmin=pmin, chance=1 - (1 - pmin) ** len(ps))


def window_tuple(core, m, tau, rng):
    """m uniform variables on core = (c, H) with sum m*c + tau: an m-complete mix of the tilt gamma = 2 tau/(m H)"""
    c, H = core
    g = 2 * tau / (m * H)
    assert abs(g) <= 1 + 1e-9, g
    g = max(-1.0, min(1.0, g))
    if m == 3:
        assert abs(g) <= 2 / 3 + 1e-9
    return c + H * tilt_mix(m, g, rng), g


def sim_law(name, F, core, q, n, rng, target=None, N=None):
    """Corollary 129: F >= q U[c-H, c+H]; n copies with sum drawn from target (default: constant)."""
    N = N or MC; c, H = core
    m = int(math.floor(q * n + 1e-12)); k = n - m
    Fm = F.mean
    if k > 0:                                                            # T_n = (n F - m U)/k
        comps = []; left = m / n
        for w, lo, hi in F.comps:
            if left > 0 and abs(lo - (c - H)) < 1e-12 and abs(hi - (c + H)) < 1e-12:
                take = min(w, left); w -= take; left -= take
            comps.append((w, lo, hi))
        assert left < 1e-12
        T = Law(comps)
    X = np.empty((N, n)); gmax = 0.0; dev = 0.0; serr = 0.0
    for s in range(N):
        Z = n * Fm if target is None else target(rng)
        Y = grid_coupling(T, k, rng) if k > 0 else np.zeros(0)
        S = Y.sum()
        if k > 0:
            dev = max(dev, abs(S - k * T.mean))
        V, g = window_tuple(core, m, Z - S - m * c, rng)
        gmax = max(gmax, abs(g))
        x = np.concatenate([Y, V]); serr = max(serr, abs(x.sum() - Z))
        X[s] = rng.permutation(x)
    ps = F.tests(X[:, 0]) + F.tests(X[:, n // 2])
    PVALS.extend(ps)
    R = F.hi - F.lo
    row = dict(name=name, n=n, m=m, k=k, R=R, H=H, q=q, bound=math.ceil(2 * R / H - 1e-9) / q, tuples=N,
               max_sum_error=serr, max_tilt=gmax, max_rest_dev=dev, pmin=min(ps), tests=len(ps))
    print("A3", row, flush=True)
    return row


def partA3():
    t0 = time.time(); rng = np.random.default_rng(SEED + 12); rows = []
    # (i) a density with a gap: uniform on [0,1/3] and [2/3,1]
    F = Law([(0.5, 0.0, 1 / 3), (0.5, 2 / 3, 1.0)])
    rows.append(sim_law("gap", F, (1 / 6, 1 / 6), 0.5, 24, rng))
    rows.append(sim_law("gap", F, (1 / 6, 1 / 6), 0.5, 25, rng))
    # (ii) atoms: 3/10 U[0,1] + 1/2 delta_0 + 1/5 delta_3
    F = Law([(0.3, 0.0, 1.0), (0.5, 0.0, 0.0), (0.2, 3.0, 3.0)])
    rows.append(sim_law("atoms", F, (0.5, 0.5), 0.3, 40, rng))
    rows.append(sim_law("atoms", F, (0.5, 0.5), 0.3, 41, rng))
    # (iii) a density bounded below on its interval: 1/2 + x on [0,1] contains 1/2 U[0,1]; the rest has density 2x
    rows.extend(sim_tri(rng))
    # (iv) prescribed sums of m uniform variables on [0,1] (Proposition 126)
    win = []
    for name, m, draw in [("two points m/4, 3m/4", 8, lambda r: 2.0 if r.random() < 0.5 else 6.0),
                          ("uniform on [m/4, 3m/4]", 8, lambda r: 2.0 + 4.0 * r.random()),
                          ("three points", 4, lambda r: [1.0, 2.0, 3.0][int(r.choice(3, p=[0.25, 0.5, 0.25]))]),
                          ("m = 3, two points 1, 2", 3, lambda r: 1.0 if r.random() < 0.5 else 2.0)]:
        X = np.empty((MC, m)); serr = 0.0; Zs = np.empty(MC)
        for s in range(MC):
            Z = draw(rng); V, g = window_tuple((0.5, 0.5), m, Z - m / 2, rng)
            serr = max(serr, abs(V.sum() - Z)); X[s] = V; Zs[s] = Z
        ps = [float(stats.kstest(X[:, j], "uniform").pvalue) for j in (0, m - 1)]
        PVALS.extend(ps)
        win.append(dict(name=name, m=m, tuples=MC, max_sum_error=serr, pmin=min(ps), tests=len(ps),
                        corr_first_sum=float(np.corrcoef(X[:, 0], Zs)[0, 1])))
        print("A3 window", win[-1], flush=True)
    # (v) completion of arbitrary laws on intervals of length at most 1 by N uniform variables
    comp = []
    disc = [Law([(0.7, 0.0, 0.0), (0.3, 1.0, 1.0)]), Law([(1 / 3, 0.0, 0.0), (1 / 3, 0.5, 0.5), (1 / 3, 1.0, 1.0)]),
            Law([(0.25, 0.2, 0.2), (0.75, 0.9, 0.9)]), Law([(0.5, -0.5, -0.5), (0.5, 0.5, 0.5)]),
            Law([(0.1, 2.0, 2.0), (0.9, 3.0, 3.0)])]
    mixed = disc + [Law([(1.0, 0.0, 1.0)]), Law([(0.5, 0.0, 0.2), (0.5, 0.6, 1.0)]),
                    Law([(0.2, 0.0, 0.0), (0.8, 0.0, 1.0)]), Law([(1.0, 5.0, 5.5)])]
    for name, laws, Nu, M in [("five discrete laws", disc, 4, 60), ("nine laws", mixed, 5, 240)]:
        r = len(laws); K = sum(L.mean for L in laws) + Nu / 2
        NS = MC // 4
        X = np.empty((NS, r + Nu)); serr = 0.0; gmax = 0.0; oscmax = 0.0
        for s in range(NS):
            Y, osc = counter_sample(laws, M, rng); oscmax = max(oscmax, osc)
            V, g = window_tuple((0.5, 0.5), Nu, K - Y.sum() - Nu / 2, rng); gmax = max(gmax, abs(g))
            X[s] = np.concatenate([Y, V]); serr = max(serr, abs(X[s].sum() - K))
        ps = []
        for j, L in enumerate(laws):
            ps += L.tests(X[:, j])
        ps += [float(stats.kstest(X[:, r + j], "uniform").pvalue) for j in range(Nu)]
        PVALS.extend(ps)
        comp.append(dict(name=name, laws=r, uniforms=Nu, grid=M, tuples=NS, max_sum_error=serr, max_tilt=gmax,
                         max_osc=oscmax, pmin=min(ps), tests=len(ps)))
        print("A3 completion", comp[-1], flush=True)
    # (vi) the L-shaped region [0,2]^2 minus (1,2]^2 with n = 25
    Lrow = sim_Lshape(rng)
    OUT["A3"] = dict(rows=rows, windows=win, completion=comp, Lshape=Lrow, seconds=time.time() - t0)


def sim_tri(rng):
    """density 1/2 + x on [0,1]: F = 1/2 U[0,1] + 1/2 (density 2x); q = 1/2, c = H = 1/2, R = 1; n = 8 and 9"""
    out = []
    Fcdf = lambda x: 0.5 * np.clip(x, 0, 1) + 0.5 * np.clip(x, 0, 1) ** 2
    mean = 0.25 + 1 / 3
    for n in (8, 9):
        m = n // 2; k = n - m
        wU = (n / 2 - m) / k                                           # weight of U[0,1] in T_n
        X = np.empty((MC, n)); serr = 0.0; gmax = 0.0
        # quantile function of T_n = wU U[0,1] + (1-wU) (2x): cdf wU x + (1-wU) x^2
        def quant(u, wU=wU):
            if wU == 0:
                return np.sqrt(u)
            a = 1 - wU
            return (-wU + np.sqrt(wU * wU + 4 * a * u)) / (2 * a)
        mT = wU / 2 + (1 - wU) * 2 / 3
        for s in range(MC):
            W = rng.random(); Y = quant((rng.permutation(k) + W) / k); S = Y.sum()
            V, g = window_tuple((0.5, 0.5), m, n * mean - S - m / 2, rng); gmax = max(gmax, abs(g))
            x = np.concatenate([Y, V]); serr = max(serr, abs(x.sum() - n * mean)); X[s] = rng.permutation(x)
        ps = [float(stats.kstest(X[:, j], Fcdf).pvalue) for j in (0, n // 2)]
        PVALS.extend(ps)
        out.append(dict(name="density 1/2 + x", n=n, m=m, k=k, R=1.0, H=0.5, q=0.5, bound=8.0, tuples=MC,
                        max_sum_error=serr, max_tilt=gmax, pmin=min(ps), tests=len(ps)))
        print("A3", out[-1], flush=True)
    return out


def uniform_mix(k, rng):
    """k uniform variables on [0,1] with sum k/2 (k >= 2), by Lemma 1 for k equal intervals; one variable if k = 1"""
    if k == 0:
        return np.zeros(0)
    if k == 1:
        return rng.random(1)
    return 0.5 + 0.5 * tilt_mix(k, 0.0, rng)


def sim_Lshape(rng):
    """uniform distribution on K = [0,2]^2 without (1,2]^2, n = 25: core [0,1]^2 with q = 1/3, m = 8 in two blocks"""
    n, m = 25, 8; k = n - m
    corners = np.array([[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]])
    mean = np.array([5 / 6, 5 / 6])
    N = MC; P = np.empty((N, n, 2)); serr = 0.0; gmax = 0.0; devmax = 0.0
    for s in range(N):
        cnt = [(0, 8, 9), (0, 9, 8), (1, 8, 8)][int(rng.integers(3))]       # systematic counts, means (1/3,25/3,25/3)
        pts = []
        for j in range(3):
            if cnt[j]:
                xy = np.stack([uniform_mix(cnt[j], rng), uniform_mix(cnt[j], rng)], axis=1)
                pts.append(corners[j] + xy)
        Y = np.concatenate(pts); S = Y.sum(0)
        tau = n * mean - S - m * np.array([0.5, 0.5])
        devmax = max(devmax, float(np.abs(tau).max()))
        blocks = []
        for i in range(2):                                              # block i absorbs coordinate i
            Vi, g = window_tuple((0.5, 0.5), 4, tau[i], rng); gmax = max(gmax, abs(g))
            other = uniform_mix(4, rng)
            blocks.append(np.stack([Vi, other], axis=1) if i == 0 else np.stack([other, Vi], axis=1))
        allp = np.concatenate([Y] + blocks)
        serr = max(serr, float(np.abs(allp.sum(0) - n * mean).max()))
        P[s] = allp[rng.permutation(n)]
    ps = []
    for j in (0, 12):
        p = P[:, j, :]
        reg = np.where(p[:, 0] > 1, 1, np.where(p[:, 1] > 1, 2, 0))
        cnts = np.bincount(reg, minlength=3)
        ps.append(float(stats.chisquare(cnts).pvalue))
        loc = p - corners[reg]
        for r_ in range(3):
            for c_ in range(2):
                ps.append(float(stats.kstest(loc[reg == r_, c_], "uniform").pvalue))
        ps.append(float(stats.kstest(loc[:, 0] + (loc[:, 1] > 0.5), lambda z: np.clip(z, 0, 2) / 2).pvalue))
    PVALS.extend(ps)
    row = dict(n=n, m=m, tuples=N, max_sum_error=serr, max_tilt=gmax, max_dev=devmax, pmin=min(ps), tests=len(ps))
    print("A3 L-shape", row, flush=True)
    return row


# ============================================================ A4: the explicit bound for convex bodies
def partA4():
    getcontext().prec = 60
    pi = Decimal("3.14159265358979323846264338327950288419716939937510582097494")
    rows = []
    for d in range(2, 9):
        # |B^d| = pi^{d/2} / Gamma(d/2 + 1)
        if d % 2 == 0:
            vol = pi ** (d // 2) / Decimal(math.factorial(d // 2))
        else:
            h = (d - 1) // 2                                             # Gamma(h + 3/2) = (2h+2)! sqrt(pi) / (4^{h+1} (h+1)!)
            vol = pi ** h * Decimal(4) ** (h + 1) * Decimal(math.factorial(h + 1)) / Decimal(math.factorial(2 * h + 2))
        dd = Decimal(d)
        blocks = (Decimal(8) * dd ** Decimal("2.5")).to_integral_value(rounding="ROUND_CEILING")   # ceil(8 d^{5/2})
        q = (Decimal(2) / dd.sqrt()) ** d / (dd ** d * vol)             # |Q| / (d^d |B^d|)
        val = dd * blocks / q
        Nd = int(val.to_integral_value(rounding="ROUND_CEILING"))
        assert abs(val - Nd) > Decimal("1e-20") or val == Nd
        rows.append(dict(d=d, ball=float(vol), q=float(q), per_block=int(blocks), N=Nd))
    OUT["A4"] = dict(rows=rows)
    print("A4", rows, flush=True)


# ============================================================ A5: repeated types and different distributions
def rest_law(F, core, m, N):
    """T = (N F - m U(core))/(N - m) for a law F one of whose components is uniform on the core"""
    c, H = core; comps = []; left = m / N
    for w, lo, hi in F.comps:
        if left > 0 and abs(lo - (c - H)) < 1e-12 and abs(hi - (c + H)) < 1e-12:
            take = min(w, left); w -= take; left -= take
        comps.append((w, lo, hi))
    assert left < 1e-12
    return Law(comps)


def sim_types(rng):
    """Proposition 133 with two repeated distributions and three other laws: 17 copies of the density
    with a gap (core U[0,1/3], q = 1/2, m = 8), 7 copies of 3/5 U[0,1] + 2/5 delta_{1/4} (core U[0,1], m = 4) and
    three laws on intervals of length at most 1; capacity 8/12 + 1 = 5/3, window 5/3 - 1 = 2/3"""
    G = [Law([(0.5, 0.0, 1 / 3), (0.5, 2 / 3, 1.0)]), Law([(0.6, 0.0, 1.0), (0.4, 0.25, 0.25)])]
    cores = [(1 / 6, 1 / 6), (0.5, 0.5)]; Ns = [17, 7]; qs = [0.5, 0.6]
    ms = [int(math.floor(q * N + 1e-12)) for q, N in zip(qs, Ns)]
    extras = [Law([(0.7, 0.0, 0.0), (0.3, 1.0, 1.0)]), Law([(1.0, 2.0, 2.5)]),
              Law([(0.5, -1.0, -0.6), (0.5, -0.2, -0.2)])]
    ell = 1.0; cap = sum(m * H / 2 for m, (c, H) in zip(ms, cores)); rho = cap - ell
    theta = [m * H / 2 / cap for m, (c, H) in zip(ms, cores)]
    Ts = [rest_law(F, core, m, N) for F, core, m, N in zip(G, cores, ms, Ns)]
    laws = [Ts[0]] * (Ns[0] - ms[0]) + [Ts[1]] * (Ns[1] - ms[1]) + extras
    s = sum(N * F.mean for N, F in zip(Ns, G)) + sum(E.mean for E in extras)
    C = sum(m * c for m, (c, H) in zip(ms, cores))
    assert abs(sum(L.mean for L in laws) + C - s) < 1e-12
    half = 0.55; M = 240; NS = MC // 5; out = []                        # the grid of 240 points costs 15/240 of the window
    assert half + ell + len(laws) / M <= cap
    for name, draw in [("constant", lambda r: s), ("two points", lambda r: s - half if r.random() < 0.5 else s + half),
                       ("uniform", lambda r: s + half * (2 * r.random() - 1))]:
        X = np.empty((NS, sum(Ns) + len(extras))); serr = 0.0; gmax = 0.0
        k0 = Ns[0] - ms[0]; k1 = Ns[1] - ms[1]
        for it in range(NS):
            Y, osc = counter_sample(laws, M, rng)
            Z = draw(rng); D = Z - Y.sum() - C
            V0, g0 = window_tuple(cores[0], ms[0], theta[0] * D, rng)
            V1, g1 = window_tuple(cores[1], ms[1], theta[1] * D, rng)
            gmax = max(gmax, abs(g0), abs(g1))
            x = np.concatenate([rng.permutation(np.concatenate([Y[:k0], V0])),
                                rng.permutation(np.concatenate([Y[k0:k0 + k1], V1])), Y[k0 + k1:]])
            serr = max(serr, abs(x.sum() - Z)); X[it] = x
        ps = G[0].tests(X[:, 0]) + G[0].tests(X[:, Ns[0] - 1]) + G[1].tests(X[:, Ns[0]]) + G[1].tests(X[:, sum(Ns) - 1])
        for j, E in enumerate(extras):
            ps += E.tests(X[:, sum(Ns) + j])
        PVALS.extend(ps)
        out.append(dict(name=name, copies=Ns, uniform=ms, others=len(extras), capacity=cap, rho=rho, half_width=half,
                        grid=M, tuples=NS, max_sum_error=serr, max_tilt=gmax, pmin=min(ps), tests=len(ps)))
        print("A5 types", out[-1], flush=True)
    return out


def hetero_mix(cs, Ts, extras, b, m1, m2, H, rng, NS, M, half=0.0):
    """the joint mix of Theorem 138 for pairwise different distributions F_i = (1/b) U[c_i-H, c_i+H] + (1-1/b) T_i,
    i < b (m1 + m2), and of the laws in extras; the sum is uniform on [s - half, s + half]"""
    n = len(Ts); m = m1 + m2; assert n == b * m and m1 >= 2 and m2 >= 4
    cs = np.array(cs, float)
    a = np.array([T.mean for T in Ts]) - cs
    blocks = np.argsort(a, kind="stable").reshape(m, b); abar = a[blocks].mean(axis=1)
    s = float((cs + (1 - 1 / b) * a).sum() + sum(E.mean for E in extras))
    X = np.empty((NS, n + len(extras))); info = dict(max_sum_error=0.0, max_tilt=0.0, max_shift=0.0, max_rest_dev=0.0)
    for it in range(NS):
        o = blocks[np.arange(m), rng.integers(b, size=m)]              # the selection: one index from every block
        chosen = np.zeros(n, bool); chosen[o] = True
        e = a[o] - abar
        rest = [i for i in range(n) if not chosen[i]]
        laws = [Ts[i] for i in rest] + extras
        Y, osc = counter_sample(laws, M, rng)
        eps = Y.sum() - sum(L.mean for L in laws)
        # first group: individual shifts t_k, none of which depends on the choice made in its own block
        t = np.array([(e[:m1].sum() - e[k]) / (m1 - 1) + e[m1:].sum() / m1 for k in range(m1)])
        assert abs(t.sum() - e.sum()) < 1e-9
        pi = 0.5 + t / H
        assert pi.min() >= -1e-12 and pi.max() <= 1 + 1e-12
        cum = np.concatenate([[0.0], np.cumsum(pi)]); kappa = cum[-1]; w0 = rng.random()
        xi = np.ceil(cum[1:] - w0) - np.ceil(cum[:-1] - w0)             # systematic sampling: a point of w0 + Z
        assert xi.min() >= 0 and xi.max() <= 1 and abs(xi.sum() - kappa) < 1 + 1e-9
        V1 = cs[o[:m1]] + (xi - 0.5) * H + (H / 2) * tilt_mix(m1, 0.0, rng)
        # second group: a common tilt absorbs the rest
        Z = s + half * (2 * rng.random() - 1)
        tau = (Z - s) - eps - H * (xi.sum() - kappa)
        V2, g = window_tuple((0.0, H), m2, tau, rng)
        x = np.empty(n + len(extras))
        x[rest] = Y[:len(rest)]; x[o[:m1]] = V1; x[o[m1:]] = cs[o[m1:]] + V2; x[n:] = Y[len(rest):]
        info["max_sum_error"] = max(info["max_sum_error"], abs(x.sum() - Z))
        info["max_tilt"] = max(info["max_tilt"], abs(g)); info["max_shift"] = max(info["max_shift"], np.abs(2 * t / H).max())
        info["max_rest_dev"] = max(info["max_rest_dev"], abs(eps))
        X[it] = x
    return X, s, info


def sim_hetero(rng):
    out = []
    # (a) the least numbers of Corollary 139: 33 pairwise different laws on [0,1], each at least 1/3 U[0,1], and two
    # further laws; H = 1/2, l = 1, b = 3, m1 = 5, m2 = 6, window 0.  The other parts are discrete with masses that
    # are multiples of 1/60, so that the grid of 60 points is exact.
    b, m1, m2, H = 3, 5, 6, 0.5; n = b * (m1 + m2); Ts = []; seen = set()
    while len(Ts) < n:
        k = int(rng.integers(1, 4)); cut = sorted(set([0, 60] + [int(v) for v in rng.integers(1, 60, k)]))
        pts = sorted(set(int(v) for v in rng.integers(0, 21, len(cut) - 1)))
        if len(pts) != len(cut) - 1 or (tuple(cut), tuple(pts)) in seen:
            continue
        seen.add((tuple(cut), tuple(pts)))
        Ts.append(Law([((q_ - p_) / 60, x / 20, x / 20) for p_, q_, x in zip(cut[:-1], cut[1:], pts)]))
    extras = [Law([(0.7, 0.0, 0.0), (0.3, 1.0, 1.0)]), Law([(1 / 3, 0.0, 0.0), (1 / 3, 0.5, 0.5), (1 / 3, 1.0, 1.0)])]
    assert (m1 - 1) * H >= 4 * (1 - H) and m2 * H / 2 - 1 - H >= 0
    NS = MC // 4
    X, s, info = hetero_mix([0.5] * n, Ts, extras, b, m1, m2, H, rng, NS, 60)
    assert info["max_rest_dev"] <= 1 + 1e-9
    ps = []
    for i in range(n):
        ps += Law([(1 / b, 0.0, 1.0)] + [((1 - 1 / b) * w, lo, hi) for w, lo, hi in Ts[i].comps]).tests(X[:, i])
    for j, E in enumerate(extras):
        ps += E.tests(X[:, n + j])
    PVALS.extend(ps)
    out.append(dict(name="common interval", n=n, others=len(extras), b=b, m1=m1, m2=m2, H=H, ell=1.0, rho=0.0,
                    half_width=0.0, grid=60, tuples=NS, pmin=min(ps), tests=len(ps), **info))
    print("A5 different", out[-1], flush=True)
    # (b) 54 pairwise different laws on different intervals of length 1, each at least 1/2 U[c_i - 1/4, c_i + 1/4],
    # and three further laws; H = 1/4, l = 1, b = 2, m1 = 13, m2 = 14, window 1/2; the sum is uniform on a window
    b, m1, m2, H = 2, 13, 14, 0.25; n = b * (m1 + m2); Ts = []; cs = []
    assert (m1 - 1) * H >= 4 * (1 - H); rho = m2 * H / 2 - 1 - H; assert rho >= 0
    for i in range(n):
        u = float(rng.integers(-20, 21)) / 10; c = u + 0.25 + 0.5 * float(rng.integers(0, 11)) / 10
        comps = []
        for _ in range(int(rng.integers(1, 4))):
            lo = u + float(rng.integers(0, 10)) / 10; hi = lo if rng.random() < 0.4 else u + float(rng.integers(int(round((lo - u) * 10)) + 1, 11)) / 10
            comps.append((float(rng.integers(1, 5)), lo, hi))
        Ts.append(Law(comps)); cs.append(c)
    extras = [Law([(0.2, 0.0, 0.0), (0.8, 0.0, 1.0)]), Law([(1.0, 5.0, 5.5)]), Law([(0.25, 0.2, 0.2), (0.75, 0.9, 0.9)])]
    M = 120; half = 0.2; NS = MC // 5
    assert half + (n - m1 - m2 + len(extras)) / M <= rho                  # the grid costs at most (number of laws)/M
    X, s, info = hetero_mix(cs, Ts, extras, b, m1, m2, H, rng, NS, M, half=half)
    ps = []
    for i in range(n):
        ps += Law([(1 / b, cs[i] - H, cs[i] + H)] + [((1 - 1 / b) * w, lo, hi) for w, lo, hi in Ts[i].comps]).tests(X[:, i])
    for j, E in enumerate(extras):
        ps += E.tests(X[:, n + j])
    ps.append(float(stats.kstest((X.sum(axis=1) - s) / half, stats.uniform(-1, 2).cdf).pvalue))
    PVALS.extend(ps)
    out.append(dict(name="different intervals", n=n, others=len(extras), b=b, m1=m1, m2=m2, H=H, ell=1.0, rho=rho,
                    half_width=half, grid=M, tuples=NS, pmin=min(ps), tests=len(ps), **info))
    print("A5 different", out[-1], flush=True)
    return out


def check_selection():
    """exact: the selection of Theorem 138 for random rational data.  For every choice of one index from each
    group: the identity (30); the shifts t_k add up to sum e_j and are at most (a_max - a_min)/(m1 - 1) in absolute
    value; the mean of pi_k = 1/2 + t_k/H over the choices in the other groups is 1/2 for every choice in the
    own group; and, for a sample of the choices, the indicators of the systematic sample have the probabilities
    pi_k and a sum next to kappa."""
    rng = np.random.default_rng(SEED + 16); confs = 0; sels = 0; samples = 0; worst = Fr(0)
    for b, m1, m2 in [(2, 2, 4), (2, 5, 6), (3, 3, 4), (3, 5, 4), (2, 6, 4), (4, 3, 4), (2, 4, 7), (3, 2, 6)]:
        for rep in range(3):
            m = m1 + m2; n = b * m
            ell = Fr(1); H = Fr(int(rng.integers(1, 6)), 10)                         # H <= 1/2 = ell/2
            a = sorted(Fr(int(rng.integers(-60, 61)), 60) * (ell - H) for _ in range(n))    # |a_i| <= ell - H
            if rep == 2:
                a = sorted([a[0]] * b + a[b:])                                       # a group with equal numbers
            c = [Fr(int(rng.integers(-30, 31)), 10) for _ in range(n)]
            extra = Fr(int(rng.integers(-9, 10)), 7)                                 # the sum of the other means
            s_ = sum(c[i] + (1 - Fr(1, b)) * a[i] for i in range(n)) + extra
            blocks = [list(range(k * b, (k + 1) * b)) for k in range(m)]
            abar = [sum(a[i] for i in B) / b for B in blocks]
            om = a[-1] - a[0]
            scale = Fr(1) if (m1 - 1) * H >= 2 * om else (m1 - 1) * H / (2 * om)     # shrink a so that |t_k| <= H/2
            if scale != 1:
                a = [v * scale for v in a]; abar = [v * scale for v in abar]; om = om * scale
                s_ = sum(c[i] + (1 - Fr(1, b)) * a[i] for i in range(n)) + extra
            cond = {}                                                                # (k, own choice) -> sum of pi_k
            for o in itertools.product(range(b), repeat=m):
                sel = [blocks[k][o[k]] for k in range(m)]
                e = [a[sel[k]] - abar[k] for k in range(m)]
                ES = sum(c[i] + a[i] for i in range(n) if i not in sel) + extra
                assert s_ - ES - sum(c[i] for i in sel) == sum(e)                    # the identity (30)
                t = [(sum(e[:m1]) - e[k]) / (m1 - 1) + sum(e[m1:]) / m1 for k in range(m1)]
                assert sum(t) == sum(e) and all(abs(v) * (m1 - 1) <= om for v in t) and all(2 * abs(v) <= H for v in t)
                if om > 0:
                    worst = max(worst, max(abs(v) for v in t) * (m1 - 1) / om)
                pi = [Fr(1, 2) + v / H for v in t]
                for k in range(m1):
                    key = (k, o[k]); cond[key] = cond.get(key, Fr(0)) + pi[k]
                sels += 1
                if sels % 97 == 0:                                                   # the systematic sample, exactly
                    cum = [sum(pi[:k]) for k in range(m1 + 1)]; kappa = cum[-1]
                    cuts = sorted(set([Fr(0), Fr(1)] + [v % 1 for v in cum]))
                    prob = [Fr(0)] * m1
                    for lo, hi in zip(cuts[:-1], cuts[1:]):
                        w0 = (lo + hi) / 2
                        xi = [math.ceil(cum[k + 1] - w0) - math.ceil(cum[k] - w0) for k in range(m1)]
                        assert all(v in (0, 1) for v in xi) and abs(sum(xi) - kappa) < 1
                        for k in range(m1):
                            prob[k] += xi[k] * (hi - lo)
                    assert prob == pi
                    samples += 1
            assert all(v == Fr(b ** (m - 1), 2) for v in cond.values()) and len(cond) == m1 * b
            confs += 1
    return dict(configurations=confs, selections=sels, samples=samples, worst_ratio=float(worst))


def partA5():
    t0 = time.time(); rng = np.random.default_rng(SEED + 15)
    sel = check_selection()
    print("A5 selection", sel, flush=True)
    OUT["A5"] = dict(selection=sel, types=sim_types(rng), different=sim_hetero(rng), seconds=time.time() - t0)


# ============================================================ A6: sums in an interval about the mean (Proposition 135)
def pair_laws(m, u, v):
    """the pair construction of Proposition 135 in units H = 1/2 (variables on [0,1]) for 0 < u, v with u + v <= m/2 and v <= (m-2)/2:
    theta, the weights w_-, w_+, the two steps of P_+ on (0, theta) and (theta, 1), and (a, b) of g_{a,b}; exact"""
    u, v = Fr(u), Fr(v); theta = 1 - 2 * u / m; wm = v / (u + v); wp = u / (u + v)
    assert theta >= wm > 0
    return theta, wm, wp, (1 - wm / theta) / wp, 1 / wp, 4 * u / (m - 2 * v), 2 * m / (m - 2 * v)


def check_pairs():
    """exact: for m = 3, 4, 5, 8 and pairs (u, v) on a rational grid in the range of Proposition 135, the measure
    P_+ = (U - w_- P_-)/w_+ is a probability density with mean 1/2 + v/m, and its reflection, scaled to mean 1, is
    g_{a,b} with 0 < a < 2 < b <= m, for which the tuples of Theorem 6 are admissible and have the marginal g_{a,b}"""
    cases = 0; boundary = 0; mx = 0
    for m in (3, 4, 5, 8):
        Lm = Fr(1) if m == 3 else Fr(m, 2); step = Fr(1, 24) if m <= 4 else Fr(1, 8)
        pts = [step * i for i in range(1, int(Fr(m, 2) / step) + 1)]
        for u in pts:
            for v in pts:
                ok = u + v <= Lm or (m == 3 and ((u <= Fr(1, 2) and v <= 1) or (u <= 1 and v <= Fr(1, 2))))
                if not ok:
                    continue
                uu, vv = (u, v) if v <= Fr(m - 2, 2) else (v, u)          # the reflection exchanges u and v
                assert vv <= Fr(m - 2, 2) and uu + vv <= Fr(m, 2)
                theta, wm, wp, lo, hi, a, b = pair_laws(m, uu, vv)
                assert lo >= 0 and lo * theta + hi * (1 - theta) == 1    # P_+ is a probability density
                assert lo * theta ** 2 / 2 + hi * (1 - theta ** 2) / 2 == Fr(1, 2) + vv / m       # its mean
                assert wm / theta + wp * lo == 1 and wp * hi == 1        # w_- P_- + w_+ P_+ is uniform
                assert theta / 2 == Fr(1, 2) - uu / m                    # the mean of P_-
                if uu + vv == Fr(m, 2):
                    assert lo == 0; boundary += 1                        # P_+ is uniform on [theta, 1]
                else:
                    assert 0 < a < 2 < b <= m
                    mean = Fr(1, 2) - vv / m                             # the mean of 1 - Y for Y ~ P_+
                    h1, h2 = mono11.h12(a, b)
                    assert h1 == mean * hi and h2 == mean * lo and a * mean == 1 - theta and b * mean == 1
                    case, parts = mono11.tuples(m, a, b)
                    mx = max(mx, mono11.check_tuples(m, a, b, parts, lambda x: h1 if x < a else h2))
                cases += 1
    return dict(cases=cases, boundary=boundary, max_tuples=mx)


def pair_mix(m, u, v, sign, rng):
    """m variables on [0,1] with sum m/2 - u (sign < 0) or m/2 + v (sign > 0): the complete mix of P_- or of P_+
    for the pair (u, v); mixed over the sign with the probabilities v/(u+v) and u/(u+v) each of them is uniform"""
    if v > (m - 2) / 2:
        return 1.0 - pair_mix(m, v, u, -sign, rng)
    theta = 1 - 2 * u / m
    if sign < 0:
        return theta * uniform_mix(m, rng)
    uf, vf = Fr(float(u)), Fr(float(v))
    if uf + vf >= Fr(m, 2):
        return theta + (1 - theta) * uniform_mix(m, rng)
    case, parts = mono11.tuples(m, 4 * uf / (m - 2 * vf), 2 * m / (m - 2 * vf))
    w = np.array([float(pp[0]) for pp in parts])
    iv = parts[int(rng.choice(len(parts), p=w / w.sum()))][1]
    y = rng.permutation(mono11.project([(float(l), float(r)) for l, r in iv], rng))      # mean 1, sum m
    return 1.0 - (0.5 - v / m) * y


def interval_tuple(core, m, d, draw, dpos, dneg, rng, count=None):
    """m uniform variables on core = (c, H) with sum m c + d (Proposition 135).  The partner of d is drawn from the distribution of
    the deviation on the other side of 0, weighted by its size, by rejection from draw(rng); dpos and dneg bound
    the deviation above and below."""
    c, H = core; x = d / (2 * H)
    if max(dpos, dneg) < 1e-12 * H or abs(x) < 1e-13:
        V = uniform_mix(m, rng)
    else:
        while True:
            e = draw(rng)
            if count is not None:
                count[0] += 1
            assert -dneg * (1 + 1e-9) - 1e-12 <= e <= dpos * (1 + 1e-9) + 1e-12
            if x < 0 and e > 0 and rng.random() * dpos < e:
                break
            if x > 0 and e < 0 and rng.random() * dneg < -e:
                break
        V = pair_mix(m, -x, e / (2 * H), -1, rng) if x < 0 else pair_mix(m, -e / (2 * H), x, 1, rng)
    return c - H + 2 * H * V


def sim_law3(name, F, core, q, n, rng, N=None):
    """the complete mix of Corollary 136: F >= q U[c-H, c+H] on an interval of length R,
    m = floor(q n) >= max(4, R/H), or m = 3 and R = 2H; q is a Fraction"""
    N = N or MC // 2; c, H = core
    m = int(Fr(q) * n // 1); k = n - m; R = F.hi - F.lo
    assert (m >= 4 and m * H >= R - 1e-12) or (m == 3 and abs(2 * H - R) < 1e-12)
    target = n * F.mean - m * c
    if k > 0:
        T = rest_law(F, core, m, n)
        dev = lambda r: target - grid_coupling(T, k, r).sum()
        dpos = target - T.quantile((np.arange(k) + 1e-12) / k).sum()
        dneg = T.quantile((np.arange(k) + 1 - 1e-12) / k).sum() - target
        assert dpos >= -1e-12 and dneg >= -1e-12 and dpos + dneg <= R + 1e-9
        dpos, dneg = max(dpos, 0.0) * (1 + 1e-9), max(dneg, 0.0) * (1 + 1e-9)
    X = np.empty((N, n)); serr = 0.0; cnt = [0]; dmax = 0.0
    for s_ in range(N):
        if k > 0:
            Y = grid_coupling(T, k, rng); d = target - Y.sum()
            V = interval_tuple(core, m, d, dev, dpos, dneg, rng, cnt)
        else:
            Y = np.zeros(0); d = 0.0; V = c - H + 2 * H * uniform_mix(m, rng)
        dmax = max(dmax, abs(d))
        x = np.concatenate([Y, V]); serr = max(serr, abs(x.sum() - n * F.mean)); X[s_] = rng.permutation(x)
    assert X.min() >= F.lo - 1e-12 and X.max() <= F.hi + 1e-12
    ps = F.tests(X[:, 0]) + F.tests(X[:, n // 2])
    PVALS.extend(ps)
    row = dict(name=name, n=n, m=m, k=k, R=R, H=H, q=float(q), bound_window=math.ceil(2 * R / H - 1e-9) / float(q),
               tuples=N, max_sum_error=serr, max_dev=dmax, partner_draws=cnt[0] / N, pmin=min(ps), tests=len(ps))
    print("A6", row, flush=True)
    return row


def partA6():
    t0 = time.time(); rng = np.random.default_rng(SEED + 17)
    chk = check_pairs()
    print("A6 pairs", chk, flush=True)
    # (i) prescribed sums of m uniform variables on [0,1] in an interval about m/2 that is not centred there
    win = []
    for name, m, draw, dpos, dneg in [
            ("m = 3, two points", 3, lambda r: -0.9 if r.random() < 0.1 else 0.1, 0.1, 0.9),
            ("m = 3, beta", 3, lambda r: r.beta(1, 8) - 1 / 9, 8 / 9, 1 / 9),
            ("m = 4, two points, centred", 4, lambda r: -1.0 if r.random() < 0.5 else 1.0, 1.0, 1.0),
            ("m = 4, two points", 4, lambda r: -1.9 if r.random() < 0.05 else 0.1, 0.1, 1.9),
            ("m = 8, beta", 8, lambda r: 4 * (r.beta(1, 7) - 1 / 8), 3.5, 0.5)]:
        X = np.empty((MC, m)); serr = 0.0
        for s_ in range(MC):
            d = draw(rng)
            V = interval_tuple((0.5, 0.5), m, d, draw, dpos, dneg, rng)
            serr = max(serr, abs(V.sum() - m / 2 - d)); X[s_] = V
        assert X.min() >= -1e-12 and X.max() <= 1 + 1e-12
        ps = [float(stats.kstest(X[:, j], "uniform").pvalue) for j in (0, m - 1)]
        PVALS.extend(ps)
        win.append(dict(name=name, m=m, length=dpos + dneg, tuples=MC, max_sum_error=serr, pmin=min(ps), tests=len(ps)))
        print("A6 window", win[-1], flush=True)
    # (ii) complete mixes with three uniform variables (densities bounded below) and with R/H uniform variables
    rows = [sim_law3("steps", Law([(0.5, 0.0, 1.0), (0.3, 0.6, 1.0), (0.2, 0.0, 0.1)]), (0.5, 0.5), Fr(1, 2), 6, rng),
            sim_law3("steps", Law([(0.5, 0.0, 1.0), (0.3, 0.6, 1.0), (0.2, 0.0, 0.1)]), (0.5, 0.5), Fr(1, 2), 7, rng),
            sim_law3("atom", Law([(0.32, 0.0, 1.0), (0.68, 0.47, 0.47)]), (0.5, 0.5), Fr(8, 25), 10, rng),
            sim_law3("gap", Law([(0.5, 0.0, 1 / 3), (0.5, 2 / 3, 1.0)]), (1 / 6, 1 / 6), Fr(1, 2), 12, rng),
            sim_law3("atoms", Law([(0.3, 0.0, 1.0), (0.5, 0.0, 0.0), (0.2, 3.0, 3.0)]), (0.5, 0.5), Fr(3, 10), 21, rng)]
    # (iii) five discrete laws on intervals of length at most 1 completed by three uniform variables
    disc = [Law([(0.7, 0.0, 0.0), (0.3, 1.0, 1.0)]), Law([(1 / 3, 0.0, 0.0), (1 / 3, 0.5, 0.5), (1 / 3, 1.0, 1.0)]),
            Law([(0.25, 0.2, 0.2), (0.75, 0.9, 0.9)]), Law([(0.5, -0.5, -0.5), (0.5, 0.5, 0.5)]),
            Law([(0.1, 2.0, 2.0), (0.9, 3.0, 3.0)])]
    ES = sum(L.mean for L in disc); NS = MC // 4; r = len(disc)
    dev = lambda rr: ES - counter_sample(disc, 60, rr)[0].sum()
    X = np.empty((NS, r + 3)); serr = 0.0; cnt = [0]
    for s_ in range(NS):
        Y, osc = counter_sample(disc, 60, rng); assert osc <= 1 + 1e-9
        V = interval_tuple((0.5, 0.5), 3, ES - Y.sum(), dev, 1.0, 1.0, rng, cnt)
        X[s_] = np.concatenate([Y, V]); serr = max(serr, abs(X[s_].sum() - ES - 1.5))
    ps = []
    for j, L in enumerate(disc):
        ps += L.tests(X[:, j])
    ps += [float(stats.kstest(X[:, r + j], "uniform").pvalue) for j in range(3)]
    PVALS.extend(ps)
    comp = dict(laws=r, uniforms=3, grid=60, tuples=NS, max_sum_error=serr, partner_draws=cnt[0] / NS, pmin=min(ps),
                tests=len(ps))
    print("A6 completion", comp, flush=True)
    OUT["A6"] = dict(pairs=chk, windows=win, rows=rows, completion=comp, seconds=time.time() - t0)


# ============================================================ Part B: projections
def partB():
    t0 = time.time()
    kap, eps, wl = Fr(9, 10), Fr(1, 4), Fr(3, 10)
    rows = []
    for d in range(2, 7):
        c = kap * eps ** d
        onE = Fr(1, 2) + c - kap                                         # mu on E
        assert onE < 0 and Fr(1, 2) + c <= 1
        assert 2 * wl + eps <= 1 and 2 * wl >= 2 * eps                  # E + 2w inside D and disjoint from E
        qE = onE + (1 - Fr(1, 2) - c)                                    # density of |D| Q on E + w
        assert qE == 1 - kap and qE > 0
        assert Fr(1, 2) - c > 0 and Fr(1, 2) - c + kap > 0
        # fibres of dimension j at distance rho from 0: (1/2 + c)(1 - rho^2)^{j/2} >= kap (eps^2 - rho^2)^{j/2};
        # squared and for j = 1 (the worst case), exactly on a rational grid of rho
        slack = None
        for i in range(0, 101):
            rho = eps * Fr(i, 100)
            lhs = (Fr(1, 2) + c) ** 2 * (1 - rho ** 2); rhs = kap ** 2 * (eps ** 2 - rho ** 2)
            assert lhs > rhs
            s = lhs - rhs
            slack = s if slack is None else min(slack, s)
        # total mass of mu: (1/2 + c) - kap eps^d = 1/2 of |D|
        assert Fr(1, 2) + c - kap * eps ** d == Fr(1, 2)
        rows.append(dict(d=d, c=str(c), mu_on_E=float(onE), Q_on_shift=float(qE), min_fibre_slack=float(slack)))
    # floating point: fibre integrals of mu over random affine subspaces of dimension j in R^d, in closed form
    rng = np.random.default_rng(SEED + 21); worst = 1.0; nf = 0
    def ballvol(j):
        return math.pi ** (j / 2) / math.gamma(j / 2 + 1)
    for d in range(2, 7):
        c = float(kap) * float(eps) ** d
        for _ in range(4000):
            j = int(rng.integers(1, d)); rho = rng.random()
            vD = ballvol(j) * max(1 - rho * rho, 0.0) ** (j / 2)
            vE = ballvol(j) * max(float(eps) ** 2 - rho * rho, 0.0) ** (j / 2)
            val = (0.5 + c) * vD - float(kap) * vE
            assert val >= 0 and val <= vD + 1e-15
            if vD > 0 and vE > 0:
                worst = min(worst, val / vD); nf += 1
    # floating point: |D| Q >= 0 on a grid of the plane (d = 2)
    c2 = float(kap) * float(eps) ** 2; w = float(wl); e = float(eps)
    g = np.linspace(-1.4, 1.4, 1401); Xg, Yg = np.meshgrid(g, g)
    def mu(x, y):
        r2 = x * x + y * y
        return np.where(r2 <= 1, 0.5 + c2, 0.0) - np.where(r2 <= e * e, float(kap), 0.0)
    def ind(x, y):
        return (x * x + y * y <= 1).astype(float)
    Qd = mu(Xg - w, Yg) + ind(Xg + w, Yg) - mu(Xg + w, Yg)
    cell = (g[1] - g[0]) ** 2
    OUT["B"] = dict(rows=rows, kappa=str(kap), eps=str(eps), w=str(wl), fibres=nf, min_fibre_ratio=worst,
                    Q_min=float(Qd.min()), Q_mass_over_pi=float(Qd.sum() * cell / math.pi),
                    m_mass_over_pi=float(mu(Xg, Yg).sum() * cell / math.pi), seconds=time.time() - t0)
    # the centres a_i = (2n+1)^{i-1} (i < n), a_n = -sum: only the count vector (1,...,1) has sum 0
    cl = []
    for n in range(3, 8):
        a = [(2 * n + 1) ** i for i in range(n - 1)]; a.append(-sum(a))
        bad = 0; tot = 0; mn = None
        for ks in itertools.combinations_with_replacement(range(n), n):   # multisets of n clusters
            cnt = [ks.count(i) for i in range(n)]
            s = sum(k_ * a_ for k_, a_ in zip(cnt, a)); tot += 1
            if cnt == [1] * n:
                assert s == 0
            else:
                assert s != 0
                mn = abs(s) if mn is None else min(mn, abs(s))
        cl.append(dict(n=n, multisets=tot, min_nonzero=mn))
    OUT["B"]["clusters"] = cl
    print("B", OUT["B"], flush=True)


# ============================================================ Part C: unimodal densities and the convex order
def call_uniform(lo, hi, t):
    """E (U - t)_+ for U uniform on [lo, hi] (exact)"""
    if t <= lo:
        return (lo + hi) / 2 - t
    if t >= hi:
        return Fr(0)
    return (hi - t) ** 2 / (2 * (hi - lo))


def cx_check(n, p, c):
    """exact: minimum over t of E(Y-t)_+ - E(X-t)_+ for X ~ p delta_c + (1-p) U[0,1], Y = n mu - (n-1) X"""
    p, c = Fr(p), Fr(c); q = 1 - p; mu = p * c + q / 2
    y0 = n * mu - (n - 1) * c; Lo = n * mu - (n - 1); Hi = n * mu
    CX = lambda t: p * max(c - t, Fr(0)) + q * call_uniform(Fr(0), Fr(1), t)
    CY = lambda t: p * max(y0 - t, Fr(0)) + q * call_uniform(Lo, Hi, t)
    D = lambda t: CY(t) - CX(t)
    bps = sorted(set([Lo, Hi, Fr(0), Fr(1), c, y0]))
    assert D(bps[0] - 1) == 0 and D(bps[-1] + 1) == 0
    mins = []
    for a, b in zip(bps[:-1], bps[1:]):
        m_ = (a + b) / 2                                                # D is a quadratic on [a, b]
        Da, Dm, Db = D(a), D(m_), D(b)
        h = (b - a) / 2
        A2 = (Da - 2 * Dm + Db) / (2 * h * h); A1 = (Db - Da) / (2 * h)  # D(m + s) = Dm + A1 s + A2 s^2
        for s in (Fr(1, 3), Fr(-1, 3), Fr(1, 7)):                      # confirm that it is a quadratic
            assert D(m_ + s * h) == Dm + A1 * s * h + A2 * (s * h) ** 2
        cand = [Da, Db]
        if A2 > 0:
            s0 = -A1 / (2 * A2)
            if -h < s0 < h:
                cand.append(Dm + A1 * s0 + A2 * s0 * s0)
        mins.append(min(cand))
    inner = [D(Fr(i, 200)) for i in range(1, 200)]
    return dict(min_all=min(mins), min_inside=min(inner), mu=mu, y0=y0)


def cx_min_mixture(comps, n):
    """exact: minimum over t of E(Y-t)_+ - E(X-t)_+ for X a mixture of uniform distributions and atoms,
    comps = [(weight, lo, hi)], and Y = n mu - (n-1) X; the difference is a quadratic between breakpoints"""
    mu = sum(w * (lo + hi) / 2 for w, lo, hi in comps)
    call = lambda lo, hi, t: max(lo - t, Fr(0)) if lo == hi else call_uniform(lo, hi, t)
    CX = lambda t: sum(w * call(lo, hi, t) for w, lo, hi in comps)
    CY = lambda t: sum(w * call(n * mu - (n - 1) * hi, n * mu - (n - 1) * lo, t) for w, lo, hi in comps)
    D = lambda t: CY(t) - CX(t)
    bps = sorted(set([v for w, lo, hi in comps for v in (lo, hi, n * mu - (n - 1) * lo, n * mu - (n - 1) * hi)]))
    assert D(bps[0] - 1) == 0 and D(bps[-1] + 1) == 0
    best = Fr(0)
    for a, b in zip(bps[:-1], bps[1:]):
        m_ = (a + b) / 2; h = (b - a) / 2
        Da, Dm, Db = D(a), D(m_), D(b)
        A2 = (Da - 2 * Dm + Db) / (2 * h * h); A1 = (Db - Da) / (2 * h)
        assert D(m_ + h / 3) == Dm + A1 * h / 3 + A2 * (h / 3) ** 2
        cand = [Da, Db]
        if A2 > 0 and -h < -A1 / (2 * A2) < h:
            s0 = -A1 / (2 * A2); cand.append(Dm + A1 * s0 + A2 * s0 * s0)
        best = min(best, min(cand))
    return best


def cx_grid_convolution(n, p, c, eta, pts=2000):
    """exact values on a grid: E(Y-t)_+ - E(X-t)_+ for X = X_0 + eta W, X_0 ~ p delta_c + (1-p) U[0,1], W uniform
    on [-1,1], and Y = n mu - (n-1) X.  The call function of U[lo,hi] + s W is the difference quotient of the
    antiderivative G of the call function of U[lo,hi]."""
    q = 1 - p; mu = p * c + q / 2; R = n * mu
    def G(lo, hi, t):                                                  # antiderivative of t -> E(U[lo,hi] - t)_+
        if t <= lo:
            return (lo + hi) / 2 * (t - lo) - (t * t - lo * lo) / 2
        if t >= hi:
            return (hi - lo) ** 2 / 6
        return (hi - lo) ** 2 / 6 - (hi - t) ** 3 / (6 * (hi - lo))
    smooth = lambda lo, hi, s, t: (G(lo, hi, t + s) - G(lo, hi, t - s)) / (2 * s)
    CX = lambda t: p * call_uniform(c - eta, c + eta, t) + q * smooth(Fr(0), Fr(1), eta, t)
    y0 = R - (n - 1) * c; s2 = (n - 1) * eta
    CY = lambda t: p * call_uniform(y0 - s2, y0 + s2, t) + q * smooth(R - (n - 1), R, s2, t)
    lo = min(-eta, R - (n - 1) - s2) - Fr(1, 10); hi = max(1 + eta, R + s2) + Fr(1, 10)
    vals = [CY(lo + (hi - lo) * Fr(i, pts)) - CX(lo + (hi - lo) * Fr(i, pts)) for i in range(pts + 1)]
    assert vals[0] == 0 and vals[-1] == 0
    return min(vals)


def partC():
    t0 = time.time(); rng = np.random.default_rng(SEED + 31)
    cases = [(3, Fr(2, 5), Fr(9, 20), Fr(1, 50)), (4, Fr(3, 5), Fr(9, 20), Fr(1, 100)),
             (5, Fr(7, 10), Fr(9, 20), Fr(1, 100)), (10, Fr(9, 10), Fr(9, 20), Fr(1, 400)),
             (3, Fr(1, 2), Fr(12, 25), Fr(1, 200)), (3, Fr(9, 10), Fr(49, 100), Fr(1, 2000))]
    rows = []
    for n, p, c, eta in cases:
        q = 1 - p; dl = Fr(1, 2) - c; mu = p * c + q / 2
        r = cx_check(n, p, c)
        assert r["min_all"] >= 0
        suff = (n * mu) ** 2 >= n - 1                                  # n mu >= sqrt(n-1)
        assert suff
        assert p > 1 - Fr(2, n)
        # the unimodal density X = X_0 + eta W, W uniform on [-1,1], and the count of Lemma 147: with A
        # variables in I and B in J, A <= n - 2 + B + 2 * 1{sum != n mu}, so that
        # P(sum != n mu) >= (n/2) (F(I) - F(J)) - (n-2)/2 = - E h(X) for h = -1 on I, 1 on J, (n-2)/n elsewhere
        assert eta < q * dl and eta <= c / 2
        PI = p + q * 2 * eta                       # P(X in I) for uniform W (I inside [eta, 1-eta])
        xs = n * mu - (n - 1) * c
        Jlo, Jhi = xs - (n - 1) * eta, xs + (n - 1) * eta
        assert Jlo > c + eta                                          # I and J are disjoint
        # P(X in J) = q * P(U + eta W in J): the trapezoid density is at most 1
        PJ_up = q * (Jhi - Jlo)
        Eh_up = Fr(n - 2, 2) - Fr(n, 2) * (PI - PJ_up)                 # an upper bound of E h(X)
        assert Eh_up < 0
        etamax = min(q * dl, (p - 1 + Fr(2, n)) / (2 * (n - 1) * q), c / 2)
        assert eta < etamax
        # the bound of the proof, valid for every W: E h(X) <= (n/2) (1 - 2/n - p + 2 (n-1) q eta)
        Eh_proof = Fr(n, 2) * (1 - Fr(2, n) - p + 2 * (n - 1) * q * eta)
        assert Eh_up <= Eh_proof < 0
        # the two densities of the theorem with W uniform: (i) the mixture p U[c-eta,c+eta] + q U[0,1], exact;
        # (ii) the convolution X_0 + eta W, exact values on a grid
        cx_i = cx_min_mixture([(p, c - eta, c + eta), (q, Fr(0), Fr(1))], n)
        cx_ii = cx_grid_convolution(n, p, c, eta)
        assert cx_i >= 0 and cx_ii >= 0
        rows.append(dict(n=n, p=str(p), c=str(c), eta=str(eta), mu=str(mu), n_mu=float(n * mu),
                         sqrt=math.sqrt(n - 1), cx_min_inside=float(r["min_inside"]), cx_min=float(r["min_all"]),
                         cx_min_mixture=float(cx_i), cx_min_convolution=float(cx_ii),
                         Eh_upper=float(Eh_up), Eh_proof=float(Eh_proof), eta_max=float(etamax),
                         miss_lower=float(-Eh_proof), miss_lower_uniform=float(-Eh_up),
                         n_sufficient=math.ceil(3 / q),
                         density_min=float(q), density_max=float(q + p / (2 * eta))))
        print("C", rows[-1], flush=True)
    # the convex order fails for a law far from the centre: a control
    ctrl = cx_check(3, Fr(2, 5), Fr(1, 10))
    assert ctrl["min_all"] < 0 and cx_min_mixture([(Fr(2, 5), Fr(2, 25), Fr(3, 25)), (Fr(3, 5), Fr(0), Fr(1))], 3) < 0
    # the two routines agree for the law with an atom
    assert cx_min_mixture([(Fr(2, 5), Fr(9, 20), Fr(9, 20)), (Fr(3, 5), Fr(0), Fr(1))], 3) == \
        cx_check(3, Fr(2, 5), Fr(9, 20))["min_all"]
    # linear programmes on the lattice {0, 1/N, ..., 1}: least L1 distance from a 3-complete mix
    lps = []
    for NL in (300, 600):
        for p, cnum in [(Fr(3, 10), 130), (Fr(1, 3), 135), (Fr(2, 5), 135), (Fr(1, 2), 132)]:
            cL = cnum * NL // 300
            target = np.full(NL + 1, float(1 - p) / (NL + 1)); target[cL] += float(p)
            mean_num = p * cL + (1 - p) * Fr(NL, 2)                     # mean in lattice units
            S3 = 3 * mean_num
            assert S3.denominator == 1
            lps.append(dict(N=NL, p=str(p), c=cL / NL, dist=lp_distance3(target, int(S3))))
            print("C lp", lps[-1], flush=True)
    # a lattice version of the density f_1 of the first case: the mass p evenly on the lattice points of I
    lpf = []
    n, p, c, eta = cases[0]
    for NL in (300, 600):
        lo = int((c - eta) * NL); hi = int((c + eta) * NL)
        assert Fr(lo, NL) == c - eta and Fr(hi, NL) == c + eta
        target = np.full(NL + 1, float(1 - p) / (NL + 1)); target[lo:hi + 1] += float(p) / (hi - lo + 1)
        S3 = 3 * (p * c * NL + (1 - p) * Fr(NL, 2))
        assert S3.denominator == 1
        # Lemma 147 for this lattice distribution: F(I) - F(J) > 1/3 with J = 3 mu - 2 I
        FI = p + (1 - p) * Fr(hi - lo + 1, NL + 1); Jlo, Jhi = int(S3) - 2 * hi, int(S3) - 2 * lo
        assert Jlo > hi and Jhi <= NL
        assert FI - (1 - p) * Fr(Jhi - Jlo + 1, NL + 1) > Fr(1, 3)
        lpf.append(dict(N=NL, dist=lp_distance3(target, int(S3))))
        print("C lp f1", lpf[-1], flush=True)
        assert lpf[-1]["dist"] > 1e-6
    # simulations of the complete mixes of Proposition 149(a) for p <= 1 - 2/n
    sims = []
    for n, p, c in [(3, 0.3, 0.45), (3, 1 / 3, 0.2), (4, 0.4, 0.4), (4, 0.5, 0.1), (5, 0.5, 0.25), (6, 0.37, 0.1),
                    (7, 0.6, 0.0), (5, 0.45, 0.3)]:
        sims.append(sim_atom_uniform(n, p, c, rng))
    # Corollary 150 (the least n): p delta_c + (1-p) U[0,1] with c = 47/100 satisfies the convex order for every
    # n >= 3 (checked for n <= 40) and is n-completely mixable exactly from n* = ceil(2/(1-p)) on
    least = []
    for p in (Fr(2, 5), Fr(11, 20), Fr(7, 10), Fr(17, 20)):
        c = Fr(47, 100); nst = math.ceil(2 / (1 - p))
        assert p <= 1 - Fr(2, nst) and p > 1 - Fr(2, nst - 1)
        assert (Fr(1, 2) - c) * 3 * p <= Fr(3, 2) - Fr(14143, 10000)   # beta <= (3/2 - sqrt 2)/(3p)
        cxmin = min(cx_check(n, p, c)["min_all"] for n in range(3, 41))
        assert cxmin >= 0
        miss = [Fr(n, 2) * p - Fr(n - 2, 2) for n in range(3, nst)]     # lower bounds of P(sum != n mu) for n < n*
        assert all(v > 0 for v in miss)
        row = sim_atom_uniform(nst, float(p), float(c), rng)
        least.append(dict(p=str(p), c=str(c), n_least=nst, n_corollary=math.ceil(3 / (1 - p)),
                          miss_at_3=float(miss[0]), miss_before=float(miss[-1]), sim=row))
        print("C least", least[-1], flush=True)
    # Corollary 152 for n0 = 6: one density f_1 satisfies the convex order for every n >= 3 (checked
    # for n <= 40), fails the condition on peaks for n = 3,...,6, and is n-completely mixable for n >= 3/q
    n0 = 6; p = Fr(7, 10); q = 1 - p; beta = Fr(1, 25); c = Fr(1, 2) - beta; eta = Fr(1, 100)
    assert 1 - Fr(2, n0) < p < 1 and beta * 3 * p <= Fr(3, 2) - Fr(14143, 10000)
    assert eta < min(q * beta, (p - 1 + Fr(2, n0)) / (2 * (n0 - 1) * q), c / 2)
    comps = [(p, c - eta, c + eta), (q, Fr(0), Fr(1))]; mu = p * c + q / 2; bounds = []
    for n in range(3, 41):
        assert cx_min_mixture(comps, n) >= 0 and cx_check(n, p, c)["min_all"] >= 0
    for n in range(3, n0 + 1):
        I = (c - eta, c + eta); J = (n * mu - (n - 1) * I[1], n * mu - (n - 1) * I[0])
        assert J[0] > I[1] and J[1] <= 1                               # J is disjoint from I and lies in [0,1]
        FI = p + q * 2 * eta; FJ = q * (J[1] - J[0])
        bounds.append(Fr(n, 2) * (FI - FJ) - Fr(n - 2, 2))
        assert bounds[-1] > 0 and (n * mu) ** 2 >= n - 1
    nsuf = math.ceil(3 / q)
    Fl = Law([(float(q), 0.0, 1.0), (float(p), float(c - eta), float(c + eta))])
    simrow = sim_law3("f_1, all n <= 6", Fl, (0.5, 0.5), q, nsuf, rng, N=MC // 2)
    simrow2 = sim_law3("f_1, all n <= 6", Fl, (0.5, 0.5), q, nsuf + 1, rng, N=MC // 2)
    alln = dict(n0=n0, p=str(p), c=str(c), eta=str(eta), cx_checked_to=40, miss_bounds=[float(v) for v in bounds],
                n_sufficient=nsuf, sim=simrow, sim_next=simrow2)
    print("C all n", alln, flush=True)
    OUT["C"] = dict(rows=rows, control_min=float(ctrl["min_all"]), lps=lps, lps_f1=lpf, sims=sims, least=least,
                    alln=alln, seconds=time.time() - t0)


def partC2():
    """random unimodal cubic densities on [0,1] with an interior mode and mean in [1/3, 2/3]: the largest ratio
    beta* of the peeling (Theorem 36 needs beta* <= 3 for n = 3; the ratio equals 3 at the top levels, where the
    interpolant is linear near its mean), and for those with beta* > 3 the least L1 distance of a lattice version
    from a 3-complete mix"""
    import concave14 as c14
    t0 = time.time(); rng = np.random.default_rng(SEED + 32)
    x = np.linspace(0.0, 1.0, 2001); res = []; tries = 0
    while len(res) < NCUB:
        tries += 1
        co = rng.normal(0, 3, 4)
        y = co[0] + co[1] * x + co[2] * x * x + co[3] * x ** 3
        if y.min() < 0:
            continue
        I = co[0] + co[1] / 2 + co[2] / 3 + co[3] / 4
        if I <= 0:
            continue
        co = co / I; y = y / I
        mu = co[0] / 2 + co[1] / 3 + co[2] / 4 + co[3] / 5
        dy = np.diff(y); im = int(np.argmax(y))
        if not (1 / 3 <= mu <= 2 / 3) or im in (0, len(x) - 1):
            continue
        if not (np.all(dy[:im] >= 0) and np.all(dy[im:] <= 0)):
            continue
        P = c14.PLDensity(x, y); S = c14.solve(P, n=1500)
        res.append((float(np.max(S["beta"])), float(mu), [float(v) for v in co]))
    tol = 1e-6                                                       # separates rounding at the value 3 from an excess
    fail = [r for r in res if r[0] > 3 + tol]
    near = [r for r in res if abs(r[0] - 3) <= tol]
    dists = []; tilts = []
    for b, mu, co in fail:
        for NL in (150, 300):
            edges = np.linspace(0.0, 1.0, NL + 1)
            Fc = co[0] * edges + co[1] * edges ** 2 / 2 + co[2] * edges ** 3 / 3 + co[3] * edges ** 4 / 4
            pm = np.diff(Fc); pm = pm / pm.sum(); idx = np.arange(NL)
            S3 = int(round(3 * float(np.sum(idx * pm))))
            lo, hi = -1e-2, 1e-2                                        # a small tilt makes three times the mean S3
            for _ in range(200):
                th = (lo + hi) / 2
                w = pm * np.exp(th * (idx - NL / 2)); w /= w.sum()
                if 3 * np.sum(idx * w) < S3:
                    lo = th
                else:
                    hi = th
            dists.append(lp_distance3(w, S3)); tilts.append(abs(th) * NL)
    OUT["C2"] = dict(densities=len(res), tries=tries, beta_max=max(r[0] for r in res),
                     beta_over_3=len(fail), lp_cases=len(dists), lp_max_dist=max(dists) if dists else 0.0,
                     tilt_max=max(tilts) if tilts else 0.0, mean_of_worst=max(res)[1],
                     at_3=len(near), below_3=len(res) - len(near) - len(fail),
                     noise=max(abs(r[0] - 3) for r in near) if near else 0.0,
                     min_excess=min(r[0] - 3 for r in fail) if fail else 0.0, seconds=time.time() - t0)
    print("C2", OUT["C2"], flush=True)


def lp_distance3(target, S):
    """least sum_x |f(x) - target(x)| over marginals f of mixtures of triples i <= j <= k with i + j + k = S"""
    L = len(target); cols = []; trip = []
    for i in range(L):
        for j in range(i, L):
            k = S - i - j
            if j <= k < L:
                trip.append((i, j, k))
    nv = len(trip)
    rows_i = []; cols_i = []; vals = []
    for t, (i, j, k) in enumerate(trip):
        for x in (i, j, k):
            rows_i.append(x); cols_i.append(t); vals.append(1 / 3)
    from scipy.sparse import coo_matrix, hstack, identity, vstack, csr_matrix
    A = coo_matrix((vals, (rows_i, cols_i)), shape=(L, nv)).tocsr()
    I = identity(L, format="csr")
    # f - e+ + e- = target, sum w = 1
    Aeq = vstack([hstack([A, -I, I]), hstack([csr_matrix(np.ones((1, nv))), csr_matrix((1, 2 * L))])]).tocsr()
    beq = np.concatenate([target, [1.0]])
    cost = np.concatenate([np.zeros(nv), np.ones(2 * L)])
    res = linprog(cost, A_eq=Aeq, b_eq=beq, bounds=(0, None), method="highs")
    assert res.status == 0
    return float(res.fun)


def two_step_mix(k, a0, h1, h2, rng):
    """k-complete mix of the non-increasing density h1 on [0,a0], h2 on [a0,1] (k >= 3; mean condition assumed)"""
    if h2 <= 1e-14:                                                    # uniform on [0, a0]
        return a0 * uniform_mix(k, rng)
    mean = h1 * a0 * a0 / 2 + h2 * (1 - a0 * a0) / 2
    a, b = a0 / mean, 1.0 / mean
    case, parts = mono11.tuples(k, Fr(a), Fr(b))
    w = np.array([float(pp[0]) for pp in parts])
    iv = parts[int(rng.choice(len(parts), p=np.clip(w, 0, None) / np.clip(w, 0, None).sum()))][1]
    return rng.permutation(mean * mono11.project([(float(l), float(r)) for l, r in iv], rng))


def sim_atom_uniform(n, p, c, rng):
    """complete mix of p delta_c + (1-p) U[0,1], 0 <= c < 1/2, p <= 1 - 2/n (Proposition 149(a))"""
    q = 1 - p; mu = p * c + q / 2; N = MC
    npj = n * p
    j = int(math.floor(npj + 1e-12))
    if abs(npj - round(npj)) < 1e-12:
        j = int(round(npj)); levels = [(1.0, j)]
    else:
        levels = [(j + 1 - npj, j), (npj - j, j + 1)]
    X = np.empty((N, n)); serr = 0.0
    muj = lambda jj: (n * mu - jj * c) / (n - jj)
    for s in range(N):
        jj = levels[int(rng.choice(len(levels), p=[w for w, _ in levels]))][1]
        k = n - jj
        if len(levels) == 1:
            V = uniform_mix(k, rng)                                    # mean 1/2 exactly
        elif levels[1][1] == n - 2:                                    # levels n-3 and n-2
            s2 = n * mu - (n - 2) * c
            if jj == n - 2:
                y = (s2 - 1) + (2 - s2) * rng.random(); V = np.array([y, s2 - y])
            else:
                A2 = levels[1][0] * 2 / n; A1 = levels[0][0] * 3 / n
                a0 = s2 - 1
                V = two_step_mix(3, a0, q / A1, (q - A2 / (2 - s2)) / A1, rng)
        else:
            g = 4 * (muj(jj) - 0.5)
            V, _ = window_tuple((0.5, 0.5), k, k * g / 4, rng)
        x = np.concatenate([np.full(jj, c), V]); serr = max(serr, abs(x.sum() - n * mu)); X[s] = rng.permutation(x)
    F = Law([(p, c, c), (q, 0.0, 1.0)])
    ps = F.tests(X[:, 0]) + F.tests(X[:, n - 1])
    PVALS.extend(ps)
    row = dict(n=n, p=p, c=c, levels=[jj for _, jj in levels], tuples=N, max_sum_error=serr, pmin=min(ps), tests=len(ps))
    print("C sim", row, flush=True)
    return row


# ============================================================ Part D: lattice distributions
def count_vectors(n, N, M):
    """count vectors k in Z^{N+1}, sum k = n, sum x k_x = M: the multisets of n values in {0..N} with sum M"""
    out = []
    def parts(maxpart, remaining, slots):
        if slots == 0:
            if remaining == 0:
                yield ()
            return
        for v in range(min(maxpart, remaining), -1, -1):
            if v * slots < remaining:
                break
            for rest in parts(v, remaining - v, slots - 1):
                yield (v,) + rest
    for t in parts(N, M, n):
        k = [0] * (N + 1)
        for v in t:
            k[v] += 1
        out.append(k)
    return out


def exact_feasible(cols, b, order):
    """Exact phase 1 of the simplex method (rational arithmetic, Bland's rule) for  sum_j lam_j cols[j] = b,
    lam >= 0.  cols: integer vectors of length r; b: Fractions >= 0; order: the order in which the columns are
    priced.  Returns (True, {j: lam_j}) or (False, z) with z . cols[j] >= 0 for all j and z . b < 0."""
    r = len(b); C = np.array(cols, dtype=object).reshape(len(cols), r)[order]
    Binv = [[Fr(int(i == l)) for i in range(r)] for l in range(r)]
    xB = [Fr(v) for v in b]; basis = [-(l + 1) for l in range(r)]       # negative: artificial variables
    pos = {j: t for t, j in enumerate(order)}
    while True:
        art = [l for l in range(r) if basis[l] < 0]
        if all(xB[l] == 0 for l in art):
            return True, {basis[l]: xB[l] for l in range(r) if basis[l] >= 0 and xB[l] > 0}
        y = [sum((Binv[l][i] for l in art), Fr(0)) for i in range(r)]
        D = 1
        for v in y:
            D = D * v.denominator // math.gcd(D, v.denominator)
        Y = np.array([int(v * D) for v in y], dtype=object)
        red = C.dot(Y)                                                 # entering: first column with y . col > 0
        enter = next((t for t in range(len(order)) if red[t] > 0), None)
        if enter is None:
            return False, [-v for v in y]
        j = order[enter]; col = cols[j]
        u = [sum((Binv[l][i] * col[i] for i in range(r) if col[i]), Fr(0)) for l in range(r)]
        best = None
        for l in range(r):
            if u[l] > 0:
                key = (xB[l] / u[l], pos.get(basis[l], -1 - l) if basis[l] >= 0 else basis[l])
                if best is None or key < best[0]:
                    best = (key, l)
        l0 = best[1]; pv = u[l0]
        Binv[l0] = [v / pv for v in Binv[l0]]; xB[l0] = xB[l0] / pv
        for l in range(r):
            if l != l0 and u[l] != 0:
                f = u[l]; Binv[l] = [a_ - f * b_ for a_, b_ in zip(Binv[l], Binv[l0])]; xB[l] = xB[l] - f * xB[l0]
        basis[l0] = j


def lattice_mixable(pm, n, want=False):
    """pm: list of Fractions on {0..N}.  Decides exactly whether pm is a mixture of the vectors k/n over the
    count vectors k (n values in {0..N} with sum n * mean), that is, whether pm is n-completely mixable.
    Returns (True, number of count vectors used) or (False, 0).  Either answer is confirmed by an exact
    certificate that is checked here: the weights, or a vector z with z . k >= 0 for all k and z . pm < 0.
    A floating-point linear programme only supplies the order in which the columns are tried."""
    N = len(pm) - 1
    M = sum(Fr(x) * pm[x] for x in range(N + 1)) * n
    if M.denominator != 1:
        return False, 0
    M = int(M); xs = [x for x in range(N + 1) if pm[x] > 0]
    if len(xs) == N + 1:
        T = count_vectors(n, N, M)
    else:                                                              # count vectors on the support only
        T = []
        def rec(i, left, rest, acc):
            if i == len(xs):
                if left == 0 and rest == 0:
                    k = [0] * (N + 1)
                    for x, c in zip(xs, acc):
                        k[x] = c
                    T.append(k)
                return
            x = xs[i]
            if i == len(xs) - 1:
                if x == 0:
                    if rest == 0:
                        rec(i + 1, 0, 0, acc + [left])
                elif rest % x == 0 and rest // x == left:
                    rec(i + 1, 0, 0, acc + [left])
                return
            for c in range(left + 1):
                if c * x > rest:
                    break
                rec(i + 1, left - c, rest - c * x, acc + [c])
        rec(0, n, M, [])
    if not T:
        return False, 0
    order = list(range(len(T)))
    if len(T) > N + 1:
        A = np.array(T, dtype=float).T / n
        res = linprog(np.zeros(A.shape[1]), A_eq=A, b_eq=[float(v) for v in pm], bounds=(0, None),
                      method="highs-ds")
        if res.status == 0:
            order = sorted(order, key=lambda j: -res.x[j])
    bvec = [n * v for v in pm]
    ok, cert = exact_feasible(T, bvec, order)
    if ok:
        assert all(l > 0 for l in cert.values())
        for x in range(N + 1):                                         # exact check of the marginal
            assert sum(l * T[j][x] for j, l in cert.items()) == bvec[x]
        if want:                                                       # the count vectors and their weights
            return True, [(T[j], l) for j, l in sorted(cert.items())]
        return True, len(cert)
    assert all(sum(z * kx for z, kx in zip(cert, k)) >= 0 for k in T)  # exact Farkas certificate
    assert sum(z * v for z, v in zip(cert, bvec)) < 0
    return False, 0


def three_point_criterion(xs, f, n):
    """the criterion of Proposition 157 for a law with masses f on integers x0 < x1 < x2: the equations k0 + k1 + k2 = n and
    sum x_i k_i = n mu have integer solutions, and n f_i is at least the least nonnegative value r_i of k_i"""
    x0, x1, x2 = xs; d = (x2 - x1, x2 - x0, x1 - x0); g = math.gcd(d[0], d[2])
    Mp = n * (sum(x * v for x, v in zip(xs, f)) - x0)
    if Mp.denominator != 1 or int(Mp) % g:
        return False
    Mp = int(Mp); sol = None
    for k2 in range(d[2] // g + 1):                                    # k1 (x1 - x0) + k2 (x2 - x0) = n (mu - x0)
        r = Mp - k2 * d[1]
        if r % d[2] == 0:
            sol = (n - r // d[2] - k2, r // d[2], k2); break
    assert sol is not None
    return all(n * f[i] >= sol[i] % (d[i] // g) for i in range(3))


def lattice_cx(pm, n):
    """the convex order X - mu <=_cx -(n-1)(X - mu) for a law on {0,...,N}: the call functions at all kinks"""
    N = len(pm) - 1; xs = [x for x in range(N + 1) if pm[x] > 0]
    mu = sum(x * pm[x] for x in xs); ys = [n * mu - (n - 1) * x for x in xs]
    for t in sorted(set([Fr(x) for x in xs] + ys)):
        if sum(pm[x] * max(Fr(x) - t, 0) for x in xs) > sum(pm[x] * max(y - t, 0) for x, y in zip(xs, ys)):
            return False
    return True


def peak_violation(pm, n):
    """the condition of Lemma 147 for every proper subset I of the support for which n mu is not a sum of n points of
    I: F(I) <= 1 - 2/n + F(J minus I), J = n mu - (n-1) I.  Returns a violating set or None."""
    N = len(pm) - 1; xs = [x for x in range(N + 1) if pm[x] > 0]
    S = n * sum(x * pm[x] for x in xs)
    if S.denominator != 1:
        return None
    S = int(S)
    for r in range(1, len(xs)):
        for I in itertools.combinations(xs, r):
            sums = {0}
            for _ in range(n - 1):
                sums = {s_ + x for s_ in sums for x in I}
            if any((S - s_) in I for s_ in sums):                       # n mu is a sum of n points of I
                continue
            J = {S - s_ for s_ in sums}
            if sum(pm[x] for x in I) > 1 - Fr(2, n) + sum(pm[x] for x in J if 0 <= x <= N and x not in I):
                return I
    return None


def counting_violation(pm, n):
    """the conditions of Lemma 148: intervals {u,...,v} below the mean and 1 <= r <= n-1 with (n-r+1) v + (r-1) b < n mu
    need F([u,v]) <= 1 - (r+1)/n + F([w,b]), w = (n mu - (n-r) v)/r; and the reflected conditions.
    Returns (reflected, u, v, r) or None."""
    for refl in (False, True):
        p = pm[::-1] if refl else pm
        N = len(p) - 1; mu = sum(x * p[x] for x in range(N + 1)); b = max(x for x in range(N + 1) if p[x] > 0)
        for v in range(N + 1):
            if not v < mu:
                break
            for u in range(v + 1):
                FI = sum(p[u:v + 1])
                for r in range(1, n):
                    if (n - r + 1) * v + (r - 1) * b < n * mu:
                        w = (n * mu - (n - r) * v) / r
                        if FI > 1 - Fr(r + 1, n) + sum(p[x] for x in range(max(math.ceil(w), 0), N + 1)):
                            return (refl, u, v, r)
    return None


def tail_violation(pm, n):
    """the tail inequalities of Komisarski and Labuschagne (2024, Corollary 2) for n variables with the law pm and
    sum t = n mu: sum_{j != i} P(X_j < a_j) >= P(X_i > t - sum_{j != i} a_j); sum_j P(X_j > a_j) >= 1 if
    sum_j a_j < t; and their reflections.  Integer thresholds suffice on a lattice.  Returns True if one fails."""
    for p in (pm, pm[::-1]):
        N = len(p) - 1; t = n * sum(x * p[x] for x in range(N + 1))
        lt = lambda c_: sum(p[x] for x in range(0, min(max(c_, 0), N + 1)))            # P(X < c)
        gt = lambda y: sum(p[x] for x in range(N + 1) if x > y)                        # P(X > y)
        for cs in itertools.combinations_with_replacement(range(0, N + 2), n - 1):
            if sum(lt(c_) for c_ in cs) < gt(t - sum(cs)):
                return True
        for fs in itertools.combinations_with_replacement(range(-1, N + 1), n):
            if sum(fs) < t and sum(gt(f_) for f_ in fs) < 1:
                return True
    return False


def partD():
    t0 = time.time()
    # (i) binomial laws
    cases = 0; mixable = 0; agree = 0; maxused = 0; nonint = 0; byN = {}
    for N in range(1, NBIN + 1):
        for n in range(2, NBOX + 1):
            for M in range(1, n * N):
                p = Fr(M, n * N)
                pm = [Fr(math.comb(N, x)) * p ** x * (1 - p) ** (N - x) for x in range(N + 1)]
                ok, cert = lattice_mixable(pm, n, want=True)
                used = len(cert) if ok else 0
                if ok:
                    CERTS.append([N, n, M, [[k, "%d/%d" % (l.numerator, l.denominator)] for k, l in cert]])
                conj = N <= M <= (n - 1) * N
                cases += 1; mixable += ok; agree += (ok == conj); maxused = max(maxused, used)
                if ok and (n * p).denominator != 1:
                    nonint += 1
                byN[N] = byN.get(N, 0) + 1
        print("D binomial N =", N, "cases so far", cases, "agree", agree, flush=True)
    OUT["D_binomial"] = dict(Nmax=NBIN, nmax=NBOX, cases=cases, mixable=mixable, agree=agree, max_vectors=maxused,
                             mixable_np_not_integer=nonint)
    # (ii) laws on {0,1,2}: n-completely mixable iff n mu integer and (n mu even or f_1 >= 1/n)
    c3 = 0; a3 = 0
    for n in range(2, 13):
        for den in (12, 30):
            for i in range(0, den + 1):
                for j in range(0, den + 1 - i):
                    f = [Fr(den - i - j, den), Fr(i, den), Fr(j, den)]
                    M = n * (f[1] + 2 * f[2])
                    crit = M.denominator == 1 and (int(M) % 2 == 0 or f[1] >= Fr(1, n))
                    if M.denominator != 1:
                        ok = False
                    else:
                        ok, _ = lattice_mixable(f, n)
                    c3 += 1; a3 += (ok == crit)
    OUT["D_three"] = dict(cases=c3, agree=a3)
    print("D three-point", OUT["D_three"], flush=True)
    # (iii) allocations by random subsets of shifts: the occupancy law is the Poisson binomial law
    rng = np.random.default_rng(SEED + 41); chk = 0
    for _ in range(60):
        n = int(rng.integers(2, 6)); j = int(rng.integers(1, n + 1))
        while True:                                                    # rational z in [0,1]^n with sum j
            z = [Fr(int(rng.integers(0, 13)), 12) for _ in range(n)]
            if sum(z) == j:
                break
        # systematic sampling: D = { d : floor(u + z_0 + ... + z_d) > floor(u + z_0 + ... + z_{d-1}) }, u uniform
        cum = [sum(z[:d]) for d in range(n + 1)]
        cuts = sorted(set([Fr(0), Fr(1)] + [(-c_) % 1 for c_ in cum]))
        subs = {}
        for lo, hi in zip(cuts[:-1], cuts[1:]):
            if hi <= lo:
                continue
            u = (lo + hi) / 2
            Dset = tuple(d for d in range(n) if math.floor(u + cum[d + 1]) > math.floor(u + cum[d]))
            assert len(Dset) == j
            subs[Dset] = subs.get(Dset, Fr(0)) + (hi - lo)
        for d in range(n):
            assert sum(pr for Ds, pr in subs.items() if d in Ds) == z[d]   # inclusion probabilities
        # occupancy of box 0 when the ball of box i goes to the boxes i + D_i (mod n), D_i independent: the ball
        # of box i reaches box 0 with probability z_{(-i) mod n}; the law is the Poisson binomial law of z
        pb = [Fr(1)]
        for d in range(n):
            pb = [(pb[x] if x < len(pb) else 0) * (1 - z[d]) + (pb[x - 1] if x >= 1 else 0) * z[d]
                  for x in range(len(pb) + 1)]
        assert sum(pb) == 1 and sum(x * v for x, v in enumerate(pb)) == j
        ok, _ = lattice_mixable(pb, n)                                 # independent confirmation
        assert ok
        chk += 1
    OUT["D_alloc"] = dict(cases=chk)
    # (iv) sampling, reinforcement and relocation applied to complete mixes found above stay completely mixable
    ops = 0
    for (N, n, M) in [(2, 4, 3), (3, 3, 4), (3, 4, 5), (4, 3, 5), (4, 5, 7), (5, 3, 7)]:
        p = Fr(M, n * N)
        pm = [Fr(math.comb(N, x)) * p ** x * (1 - p) ** (N - x) for x in range(N + 1)]
        # sampling M' of the M balls
        for M2 in range(1, M):
            f = [Fr(0)] * (N + 1)
            for x in range(N + 1):
                for y in range(0, min(x, M2) + 1):
                    if M2 - y <= M - x:
                        f[y] += pm[x] * Fr(math.comb(x, y) * math.comb(M - x, M2 - y), math.comb(M, M2))
            assert sum(f) == 1
            ok, _ = lattice_mixable(f, n); assert ok; ops += 1
        # reinforcement: X + Bernoulli(X / M)
        f = [Fr(0)] * (N + 2)
        for x in range(N + 1):
            f[x] += pm[x] * (1 - Fr(x, M)); f[x + 1] += pm[x] * Fr(x, M)
        ok, _ = lattice_mixable(f, n); assert ok; ops += 1
        # relocation with theta = 1/2: Bin(X, 1 - theta + theta/n) + Bin(M - X, theta/n)
        th = Fr(1, 2); a_ = 1 - th + th / n; b_ = th / n
        f = [Fr(0)] * (M + 1)
        for x in range(N + 1):
            for u in range(x + 1):
                for v in range(M - x + 1):
                    f[u + v] += pm[x] * math.comb(x, u) * a_ ** u * (1 - a_) ** (x - u) * math.comb(M - x, v) * b_ ** v * (1 - b_) ** (M - x - v)
        assert sum(f) == 1
        ok, _ = lattice_mixable(f, n); assert ok; ops += 1
    OUT["D_ops"] = dict(cases=ops)
    # (v) the law (12/25, 1/25, 12/25) on {0,1,2}: all even n, and the odd n >= 25
    f = [Fr(12, 25), Fr(1, 25), Fr(12, 25)]
    mix = [n for n in range(2, 41) if lattice_mixable(f, n)[0]]
    OUT["D_large"] = dict(law="12/25, 1/25, 12/25", nmax=40, mixable=mix,
                          not_mixable=[n for n in range(2, 41) if n not in mix])
    # (vi) a law on {0, 2, 3, 7}: the lattice of the theorem has the basis (1,-3,2,0), (2,-2,-1,1), so that
    # n f_x >= (3, 5, 3, 1) suffices when n mu is an integer; the exact answers for the multiples of 10
    f = [Fr(3, 10), 0, Fr(1, 5), Fr(2, 5), 0, 0, 0, Fr(1, 10)]; xs = [0, 2, 3, 7]; beta = [3, 5, 3, 1]
    b1 = (1, -3, 2, 0); b2 = (2, -2, -1, 1)
    assert sum(b1) == 0 and sum(b2) == 0 and sum(x * v for x, v in zip(xs, b1)) == 0
    assert sum(x * v for x, v in zip(xs, b2)) == 0
    minors = [b1[i] * b2[j] - b1[j] * b2[i] for i in range(4) for j in range(i + 1, 4)]
    assert math.gcd(*minors) == 1                                      # a basis of the lattice, not of a sublattice
    assert beta == [abs(u) + abs(v) for u, v in zip(b1, b2)]
    mu4 = sum(x * f[x] for x in xs)
    adm = [n for n in range(2, 101) if (n * mu4).denominator == 1]
    mix4 = [n for n in adm if lattice_mixable(f, n)[0]]
    bound4 = min(n for n in adm if all(n * f[x] >= bb for x, bb in zip(xs, beta)))
    assert all(n in mix4 for n in adm if n >= bound4)
    OUT["D_four"] = dict(support=xs, law="3/10, 1/5, 2/5, 1/10", admissible=adm, mixable=mix4, bound=bound4,
                         first_mixable=min(mix4))
    # (vii) a log-concave law on {0,1,2,3} with 3 mu = 4, strictly inside the mean condition, that is not
    # 3-completely mixable (a 3 needs a 0 beside it, and f_3 > f_0)
    f = [Fr(1, 27), Fr(18, 27), Fr(6, 27), Fr(2, 27)]
    assert f[1] ** 2 >= f[0] * f[2] and f[2] ** 2 >= f[1] * f[3] and sum(x * v for x, v in enumerate(f)) == Fr(4, 3)
    ok, _ = lattice_mixable(f, 3)
    assert not ok and f[3] > f[0]
    OUT["D_logconcave"] = dict(law="1/27, 18/27, 6/27, 2/27", n=3, mixable=bool(ok))
    # (viii) three points x0 < x1 < x2 in general: the criterion against the exact answer
    c3g = 0; a3g = 0
    for xs in itertools.combinations(range(0, 9), 3):
        if xs[0] != 0:
            continue
        for den in (6, 10):
            for i in range(1, den):
                for j in range(1, den - i):
                    f = [Fr(den - i - j, den), Fr(i, den), Fr(j, den)]
                    pm = [Fr(0)] * (xs[2] + 1)
                    for x, v in zip(xs, f):
                        pm[x] = v
                    for n in range(2, 11):
                        crit = three_point_criterion(xs, f, n)
                        if (n * sum(x * v for x, v in zip(xs, f))).denominator != 1:
                            ok = False
                        else:
                            ok, _ = lattice_mixable(pm, n)
                        c3g += 1; a3g += (ok == crit)
    OUT["D_three_general"] = dict(cases=c3g, agree=a3g, xmax=8)
    print("D three points, general", OUT["D_three_general"], flush=True)
    assert a3g == c3g
    # (ix) Remark 160: necessary conditions against the exact answer.  Three laws with n = 3:
    #   A (log-concave)  (1,18,6,2)/27 on 0..3:          convex order holds, the condition on peaks fails for I = {1}
    #   B (unimodal)     (1,18,11,7,6,3,2)/48 on 0..6:   convex order, peaks and tail inequalities hold, a counting
    #                                                    condition fails; every count vector has k_0 >= k_6
    #   C (unimodal)     (1,3,3,4,9,15,4)/39 on 0..6:    all these conditions hold; every count vector has
    #                                                    k_6 >= 2 k_0 + k_1, and f_6 < 2 f_0 + f_1
    ex = {}
    for name, w in (("A", [1, 18, 6, 2]), ("B", [1, 18, 11, 7, 6, 3, 2]), ("C", [1, 3, 3, 4, 9, 15, 4])):
        den = sum(w); pm = [Fr(v, den) for v in w]; N = len(w) - 1; S = 3 * sum(x * pm[x] for x in range(N + 1))
        assert S.denominator == 1
        up = max(range(N + 1), key=lambda x: w[x])
        assert all(w[x] <= w[x + 1] for x in range(up)) and all(w[x] >= w[x + 1] for x in range(up, N))   # unimodal
        ok, _ = lattice_mixable(pm, 3)
        ex[name] = dict(weights=w, denominator=den, sum=int(S), mixable=bool(ok), convex_order=lattice_cx(pm, 3),
                        peak=peak_violation(pm, 3), counting=counting_violation(pm, 3), tail=tail_violation(pm, 3))
        ex[name]["count_vectors"] = len(count_vectors(3, N, int(S)))
    assert not ex["A"]["mixable"] and ex["A"]["convex_order"] and ex["A"]["peak"] == (1,)
    assert not ex["B"]["mixable"] and ex["B"]["convex_order"] and ex["B"]["peak"] is None and not ex["B"]["tail"]
    assert ex["B"]["counting"] == (True, 0, 0, 2)
    assert all(k[0] >= k[6] for k in count_vectors(3, 6, 7)) and 1 < 2
    assert not ex["C"]["mixable"] and ex["C"]["convex_order"] and ex["C"]["peak"] is None
    assert ex["C"]["counting"] is None and not ex["C"]["tail"]
    assert all(k[6] >= 2 * k[0] + k[1] for k in count_vectors(3, 6, 12)) and 4 < 2 * 1 + 3
    # on six consecutive integers the condition on peaks no longer decides: (6,6,1,1,1,5)/20 with n = 4, n mu = 8
    pm = [Fr(v, 20) for v in (6, 6, 1, 1, 1, 5)]
    assert 4 * sum(x * pm[x] for x in range(6)) == 8
    ok, _ = lattice_mixable(pm, 4)
    assert not ok and peak_violation(pm, 4) is None
    ex["E"] = dict(weights=[6, 6, 1, 1, 1, 5], denominator=20, n=4, sum=8, mixable=bool(ok), peak=None,
                   convex_order=lattice_cx(pm, 4), counting=counting_violation(pm, 4), tail=tail_violation(pm, 4))
    # all laws with positive masses and a given denominator on four and on five consecutive integers: the laws
    # that are not n-completely mixable although n mu is an integer, and those among them that satisfy the
    # condition on peaks for every subset of the support; and no completely mixable law violates a condition
    search = []; sane = 0
    for N, dens, nlist in ((3, (12, 15, 18), (3, 4, 5, 6)), (4, (10, 12), (3, 4, 5))):
        adm = 0; non = 0; unexplained = 0; cxfail = 0
        for den in dens:
            for cuts in itertools.combinations(range(1, den), N):
                w = [b_ - a_ for a_, b_ in zip((0,) + cuts, cuts + (den,))]
                pm = [Fr(v, den) for v in w]; mu = sum(x * pm[x] for x in range(N + 1))
                for n in nlist:
                    if (n * mu).denominator != 1:
                        continue
                    adm += 1
                    ok, _ = lattice_mixable(pm, n)
                    if ok:
                        assert lattice_cx(pm, n) and peak_violation(pm, n) is None
                        assert counting_violation(pm, n) is None and not tail_violation(pm, n)
                        sane += 1
                    else:
                        non += 1; unexplained += peak_violation(pm, n) is None; cxfail += not lattice_cx(pm, n)
        search.append(dict(points=N + 1, denominators=list(dens), n=list(nlist), admissible=adm, not_mixable=non,
                           without_peak_violation=unexplained, convex_order_fails=cxfail))
        print("D necessary", search[-1], flush=True)
    OUT["D_necessary"] = dict(examples=ex, search=search, mixable_checked=sane)
    OUT["D_seconds"] = time.time() - t0
    print("D", {k: v for k, v in OUT.items() if k.startswith("D_")}, flush=True)


if __name__ == "__main__":
    T0 = time.time()
    partA1(); partA2(); partA3(); partA4(); partA5(); partA6(); partB(); partC(); partC2(); partD()
    OUT["pvalues"] = pv_summary(PVALS)
    OUT["settings"] = dict(MC=MC, SEED=SEED, NBIN=NBIN, NBOX=NBOX, NCUB=NCUB)
    OUT["seconds"] = time.time() - T0
    os.makedirs(os.path.join(here, "data"), exist_ok=True)
    json.dump(CERTS, open(os.path.join(here, "data", "binomial_mixes.json"), "w"), separators=(",", ":"))
    json.dump(OUT, open(os.path.join(here, "data", "wang26.json"), "w"), indent=1)
    print("done", OUT["pvalues"], "seconds", OUT["seconds"])
